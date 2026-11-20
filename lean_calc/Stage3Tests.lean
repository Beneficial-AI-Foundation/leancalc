import Presentation
import AdvancedTests
namespace Stage3Tests
open Lean Phase2
open AdvancedTests (check)
def must {α : Type} (v : Except String α) : IO α := match v with | .ok a => pure a | .error e => throw <| IO.userError e

def filled (cache : Incremental.Cache) (si : Nat := 0) : Incremental.Cache := Id.run do
  let mut cache := cache
  for i in [:2600] do cache := (Incremental.display cache si i).2
  return cache

def run : IO Unit := do
  AdvancedTests.count.set 0
  let b := singleBook (put (put (put (put emptySheet 0 "1") 1 "=A1*2") 2 "=B1+1") 3 "=SUM(10,20)")
  let first := filled (Incremental.synchronize {} b)
  check "Initial incremental display agrees with full evaluation" ((List.range 2600).all fun i => (Incremental.display first 0 i).1 == cellDisplay b 0 i)
  let unchanged := filled (Incremental.synchronize {first with calculations:=0} b)
  check "Unchanged workbook reuses every displayed result" (unchanged.calculations == 0)
  let changed := b.set! 0 {b[0]! with cells:=put b[0]!.cells 0 "2"}
  let next := filled (Incremental.synchronize first changed)
  check "An edit recalculates only its transitive dependents" (next.calculations == 3 && next.values[2]! == some "5" && next.values[3]! == some "30")
  let removed := changed.set! 0 {changed[0]! with cells:=put changed[0]!.cells 1 "10"}
  let next := filled (Incremental.synchronize next removed)
  let removed := removed.set! 0 {removed[0]! with cells:=put removed[0]!.cells 0 "8"}
  let next := filled (Incremental.synchronize next removed)
  check "Replacing a formula removes obsolete dependencies" (next.calculations == 1 && next.values[2]! == some "11")
  let cycle := b.set! 0 {b[0]! with cells:=put b[0]!.cells 0 "=C1"}
  let cycled := filled (Incremental.synchronize first cycle)
  check "Dependency cycles terminate and display cycle errors" (cycled.values[0]! == some "#CYCLE!" && cycled.values[2]! == some "#CYCLE!")
  let restored := filled (Incremental.synchronize cycled b)
  check "Undoing a cycle invalidates all affected cached errors" (restored.values[0]! == some "1" && restored.values[2]! == some "3")
  let cross := b.push {name:="Other",cells:=put emptySheet 0 "=Sheet1!C1"}
  let c1 := filled (filled (Incremental.synchronize {} cross)) 1
  let cross2 := cross.set! 0 {cross[0]! with cells:=put cross[0]!.cells 0 "7"}
  let c2 := filled (Incremental.synchronize c1 cross2) 1
  check "Cross-sheet edits invalidate cached dependents on another sheet" (c2.values[26000]! == some "15")
  let conditional := singleBook (put (put (put emptySheet 0 "0") 1 "10") 2 "=IF(A1,B1,3)")
  let c1 := filled (Incremental.synchronize {} conditional)
  let c2book := conditional.set! 0 {conditional[0]! with cells:=put (put conditional[0]!.cells 0 "1") 1 "12"}
  let c2 := filled (Incremental.synchronize c1 c2book)
  check "IF branch dependencies remain safe when the condition changes" (c2.values[2]! == some "12")
  let mut cache := first
  let mut book := b
  let mut agrees := true
  for n in [:40] do
    book := book.set! 0 {book[0]! with cells:=put book[0]!.cells (n%2) (if n%2 == 0 then toString n else "=A1*"++toString (n+1))}
    cache := filled (Incremental.synchronize cache book)
    agrees := agrees && (List.range 2600).all (fun i => (Incremental.display cache 0 i).1 == cellDisplay book 0 i)
  check "Forty edit sequences match the full-calculation oracle" agrees
  let rows := put (put (put (put (put (put emptySheet 0 "2") 1 "first") 26 "1") 27 "second") 52 "2") 53 "third"
  let m : Model := {book:=singleBook rows}
  let rect := rectangle 0 53
  let sorted ← must (Presentation.sortRows m rect 0 false)
  check "Sorting is numeric and stable for equal keys" (sorted.sheet[1]! == "second" && sorted.sheet[27]! == "first" && sorted.sheet[53]! == "third")
  check "Sorting remains a single undoable edit" ((undoModel sorted).book == m.book && sorted.undo.length == 1)
  let down ← must (Presentation.sortRows m rect 0 true)
  check "Descending sort preserves equal-key row order" (down.sheet[1]! == "first" && down.sheet[27]! == "third" && down.sheet[53]! == "second")
  check "Search wraps and is case insensitive" (Presentation.findCell m "SECOND" 30 == some 27 && Presentation.findCell m "first" 2 == some 1)
  check "Filtering matches display text without changing the workbook" (Presentation.filterRows m 1 "ir" == [0,2])
  let styled := Presentation.formatCells m (rectangle 0 0) "currency"
  check "Currency display does not change the stored value" (Presentation.formatted styled.book[0]! 0 "2" == "$2.00" && styled.sheet[0]! == "2")
  let styled := Presentation.formatCells styled (rectangle 0 0) "percent"
  check "Percent display multiplies only the displayed value" (Presentation.formatted styled.book[0]! 0 "2" == "200.00%" && styled.sheet[0]! == "2")
  check "Fixed formatting rounds negative ties away from zero" (Presentation.fixed (mkRat (-125) 100) 1 == "-1.3")
  let styled := Presentation.columnStyle styled 0 180 "e"
  let (decoded,_) ← must (decodeBook (encodeBook styled.book 0))
  check "Cell formats and column widths survive native save and reopen" (decoded == styled.book)
  check "Formatting is undoable without altering cell contents" ((undoModel styled).book != styled.book && (undoModel styled).sheet == styled.sheet)
  let escapedModel :=  {m with book:=singleBook (put emptySheet 0 "<script>alert(1)</script>")}
  let html := Presentation.printHTML escapedModel
  check "Printable HTML escapes workbook text and includes print layout" ((html.splitOn "&lt;script&gt;").length > 1 && (html.splitOn "<script>").length == 1 && (html.splitOn "@page").length > 1)
  let large : Model := {book:=#[{cells:=put (put (Array.replicate 26000 "") 25974 "123") 25999 "=A1000+1"}]}
  check "Expanded sheets calculate references in row 1000" (cellDisplay large.book 0 25999 == "124")
  let encoded := encodeBook large.book 0
  let (restored,_) ← must (decodeBook encoded)
  check "Expanded sparse native files round-trip without empty-cell bloat" (restored == large.book && encoded.length < 1000)
  let largeCache := Incremental.synchronize {} large.book
  let (shown,largeCache) := Incremental.display largeCache 0 25999
  let changed := large.book.set! 0 {large.book[0]! with cells:=put large.sheet 25974 "456"}
  let largeCache := Incremental.synchronize largeCache changed
  check "Incremental invalidation reaches expanded-sheet references" (shown == "124" && (Incremental.display largeCache 0 25999).1 == "457")
  check "CSV export includes populated rows beyond row 100" (((exportCSV large ',').splitOn "123").length > 1)
  let rowStyle := Presentation.formatCells m (rectangle 0 1) "currency"
  let sorted ← must (Presentation.sortRows rowStyle rect 0 false)
  check "Sort carries formatting with the moved row" ((Presentation.styleAt sorted.book[0]! 26).numberFormat == "currency" && (Presentation.styleAt sorted.book[0]! 0).numberFormat == "general")
  let inserted ← must (structureEdit rowStyle true true 0)
  check "Row insertion shifts cell formatting with contents" ((Presentation.styleAt inserted.book[0]! 26).numberFormat == "currency")
  let pasted ← must (pasteTable rowStyle 52 (extract rowStyle.sheet (rectangle 0 1)))
  let pasted := Presentation.transferStyles pasted rowStyle.book 0 (rectangle 0 1) 52 false
  check "Copying a rectangle carries cell formatting in one undo step" ((Presentation.styleAt pasted.book[0]! 52).numberFormat == "currency" && pasted.undo.length == rowStyle.undo.length+1)
  let fonted := Presentation.formatCells rowStyle (rectangle 0 0) "font:mono"
  let fonted := Presentation.formatCells fonted (rectangle 0 0) "size:16"
  check "Font choices survive native serialization" ((← must (decodeBook (encodeBook fonted.book 0))).1 == fonted.book)
  let filled ← must (fillRect rowStyle (rectangle 0 52) true)
  check "Fill copies formats with values in one undo step" ((Presentation.styleAt filled.book[0]! 52).numberFormat == "currency" && filled.undo.length == rowStyle.undo.length+1)
  let legacy ← IO.FS.readFile "lean_calc/examples/Phase2-workbook.lcalc"
  let (legacyBook,_) ← must (decodeBook legacy)
  check "Existing Phase 2 example opens without new style fields" (legacyBook.size == 2)
  IO.println s!"{← AdvancedTests.count.get} Phase 3 checks passed."
end Stage3Tests
