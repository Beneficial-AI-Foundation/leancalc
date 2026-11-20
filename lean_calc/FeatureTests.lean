import OpenDocument
import AdvancedTests
open Lean Phase2
namespace FeatureTests
open AdvancedTests (check)
def must {α : Type} (v : Except String α) : IO α := IO.ofExcept v
def expect (b : Book) (formula result : String) : IO Unit := do
  let b := b.set! 0 {b[0]! with cells:=put b[0]!.cells 25 formula}
  let actual := cellDisplay b 0 25
  check (formula ++ " returns " ++ result) (actual == result)

def run : IO Unit := do
  AdvancedTests.count.set 0
  let mut cells := Sheet.blank 26000
  cells := put (put (put (put (put (put cells 0 "10") 26 "20") 52 "30") 1 "Apple") 27 "pear") 53 "APPLE"
  let b := singleBook cells
  for (formula,result) in [
    ("=COUNTIF(A1:A3,\">15\")","2"), ("=SUMIF(B1:B3,\"apple\",A1:A3)","40"),
    ("=AVERAGEIF(A1:A3,\">10\")","25"),("=SUMPRODUCT(A1:A3,A1:A3)","1400"),
    ("=SUMPRODUCT(A1:A3,A1:A2)","#VALUE!"),("=INDEX(A1:B3,2,2)","pear"),
    ("=INDEX(A1:B3,0,1)","#REF!"),("=MATCH(\"PEAR\",B1:B3,0)","2"),
    ("=MATCH(999,A1:A3,0)","#N/A"),("=MATCH(10,A1:A3,1)","#N/A"),
    ("=VLOOKUP(20,A1:B3,2,FALSE)","pear"),("=VLOOKUP(20,A1:B3,3,FALSE)","#REF!"),
    ("=LEN(\"λx\")","2"),("=LEFT(\"abcd\",2)","ab"),("=RIGHT(\"abcd\",2)","cd"),
    ("=MID(\"abcd\",2,2)","bc"),("=LEFT(\"abcd\",-1)","#VALUE!"),
    ("=UPPER(\"apple\")","APPLE"),("=LOWER(\"PEAR\")","pear"),
    ("=TRIM(\"  one   two  \")","one two"),("=CONCATENATE(\"Total \",A1)","Total 10"),
    ("=SUBSTITUTE(\"one two one\",\"one\",\"1\")","1 two 1"),
    ("=DATE(1900,1,1)","2"),("=DATE(1900,2,29)","#NUM!"),
    ("=YEAR(DATE(2024,2,29))","2024"),("=MONTH(DATE(2024,2,29))","2"),
    ("=DAY(DATE(2024,2,29))","29"),("=YEAR(DATE(9999,12,31))","9999"),
    ("=DAY(60)","28"),("=YEAR(1)","#NUM!"),("=SUMIF(A1:A3,\">99\")","0"),
    ("=AVERAGEIF(A1:A3,\">99\")","#DIV/0!"),("=NO_SUCH_FUNCTION(1)","#NAME?")
  ] do expect b formula result
  let m : Model := {book:=b}
  let named ← must (Features.addObject m {kind:="name",title:="Revenue",first:=0,last:=52})
  expect named.book "=SUM(revenue)" "60"
  expect named.book "=Revenue+1" "#VALUE!"
  let named ← must (Features.addObject named {kind:="name",title:="Rate",first:=0,last:=0})
  expect named.book "=Rate*2" "20"
  check "Named ranges reject case-insensitive duplicates" ((Features.addObject named {kind:="name",title:="REVENUE"}).toOption.isNone)
  check "Named ranges reject built-in names" ((Features.addObject named {kind:="name",title:="SIN"}).toOption.isNone)
  let nbook := named.book.set! 0 {named.book[0]! with cells:=put named.sheet 25 "=SUM(Revenue)"}
  let c := (Incremental.display (Incremental.synchronize {} nbook) 0 25).2
  let nbook := nbook.set! 0 {nbook[0]! with cells:=put nbook[0]!.cells 0 "11"}
  check "Named-range dependencies invalidate cached sums" ((Incremental.display (Incremental.synchronize c nbook) 0 25).1 == "61")
  let inserted ← must (structureEdit named true true 0)
  expect inserted.book "=SUM(Revenue)" "60"
  check "Named ranges track inserted rows" (inserted.book[0]!.objects[0]!.first == 26 && inserted.book[0]!.objects[0]!.last == 78)
  let renamed ← must (renameSheet named "Income")
  expect renamed.book "=SUM(Revenue)" "60"
  let fn ← must (Features.addObject named {kind:="function",title:="DOUBLE",options:=#["X"],data:="X*2"})
  expect fn.book "=DOUBLE(SUM(Revenue))" "120"
  expect fn.book "=DOUBLE(1,2)" "#VALUE!"
  let recursive ← must (Features.addObject fn {kind:="function",title:="RECUR",options:=#["X"],data:="RECUR(X)"})
  expect recursive.book "=RECUR(1)" "#LIMIT!"
  let exported := Features.exportFunctions fn
  let imported ← must (Features.importFunctions m exported)
  expect imported.book "=DOUBLE(9)" "18"
  check "Function packs reject unrelated objects" ((Features.importFunctions m (exported.replace "\"function\"" "\"image\"")).toOption.isNone)
  let validation ← must (Features.addObject m {kind:="validation",title:="0 to 100",first:=0,last:=52,options:=#["number","0","100"]})
  check "Validation accepts in-range values" ((validateBook (editCell validation 0 "50").book).isOk)
  check "Validation rejects out-of-range values" ((validateBook (editCell validation 0 "101").book).toOption.isNone)
  check "Validation rejects bad pasted data atomically" ((pasteTable validation 0 #[#["101"]]).toOption.isNone)
  check "Validation permits blank cells" ((validateBook (editCell validation 0 "").book).isOk)
  let whole ← must (Features.addObject m {kind:="validation",title:="Whole",options:=#["whole","0","100"]})
  check "Whole-number validation rejects fractions" ((validateBook (editCell whole 0 "=1/2").book).toOption.isNone)
  let list ← must (Features.addObject m {kind:="validation",title:="Fruit",first:=1,last:=1,options:=#["list","Apple","pear"]})
  check "List validation accepts choices and rejects other text" ((validateBook (editCell list 1 "pear").book).isOk && (validateBook (editCell list 1 "plum").book).toOption.isNone)
  let condition ← must (Features.addObject fn {kind:="condition",title:="High",first:=0,last:=52,options:=#[">","15","#dcfce7"]})
  check "Conditional colors reflect evaluated numeric values" (Features.colorAt condition.book 0 0 == "" && Features.colorAt condition.book 0 26 == "#dcfce7")
  check "Conditional formats appear in printable output" (((Presentation.printHTML condition).splitOn "background:#dcfce7").length > 1)
  let chart ← must (Features.addObject condition {kind:="chart",title:="Revenue < &",first:=0,last:=52,options:=#["bar"]})
  let series ← must (Features.series chart.book 0 chart.book[0]!.objects[4]!)
  check "Charts read a live source series" (series.map (·.2) == #[10,20,30])
  let svg ← must (Features.svg chart.book 0 chart.book[0]!.objects[4]!)
  check "Chart export escapes labels and creates SVG" (svg.startsWith "<svg" && (svg.splitOn "Revenue &lt; &amp;").length > 1)
  let chartChanged := editCell chart 26 "40"
  check "Charts update after source edits" ((← must (Features.series chartChanged.book 0 chartChanged.book[0]!.objects[4]!))[1]!.2 == 40)
  let image ← must (Features.addObject chart {kind:="image",title:="Pixel",data:="iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGMQa83+DwADwQIGhkJ1vwAAAABJRU5ErkJggg=="})
  let (reopened,_) ← must (decodeBook (encodeBook image.book 0))
  check "Native version 4 preserves all workbook objects exactly" (reopened == image.book)
  check "Removing an object is undoable" ((undoModel (← must (Features.removeObject image 5))).book == image.book)
  check "ODS refuses to silently drop native workbook objects" ((OpenDocument.content image.book).toOption.isNone)
  let pivotSource := put (put (put (put (put (put (put (put emptySheet 0 "Fruit") 1 "Amount") 26 "Apple") 27 "10") 52 "Pear") 53 "20") 78 "Apple") 79 "30"
  let pm : Model := {book:=singleBook pivotSource}
  let pivot ← must (Features.createPivot pm "Summary" (rectangle 0 79) 0 1 "SUM")
  check "Pivot tables group repeated labels and sum values" (cellDisplay pivot.book 1 26 == "Apple" && cellDisplay pivot.book 1 27 == "40" && cellDisplay pivot.book 1 53 == "20")
  check "Pivot creation is one undo transaction" (pivot.undo.length == 1 && (undoModel pivot).book == pm.book)
  let pivot := {pivot with book:=pivot.book.set! 0 {pivot.book[0]! with cells:=put pivot.book[0]!.cells 27 "15"}}
  let refreshed ← must (Features.refreshPivot pivot)
  check "Pivot refresh reads changed source values" (cellDisplay refreshed.book 1 27 == "45")
  let avg ← must (Features.createPivot pm "Average" (rectangle 0 79) 0 1 "AVERAGE")
  check "Pivot averages retain exact numeric results" (cellDisplay avg.book 1 27 == "20")
  let (pivotBack,_) ← must (decodeBook (encodeBook refreshed.book refreshed.active))
  check "Pivot definitions survive native reopen and refresh" ((← must (Features.refreshPivot {book:=pivotBack,active:=1})).book == pivotBack)
  let sparse := Sheet.blank 26000 |>.set! 25999 "1"
  check "A sparse working sheet stores only populated cells" (sparse.entries.size == 1 && sparse.size == 26000)
  check "Clearing a sparse cell releases its entry" ((sparse.set! 25999 "").entries.isEmpty)
  let cache := Incremental.synchronize {} (singleBook sparse)
  let cache := (List.range 26000).foldl (fun c i => (Incremental.display c 0 i).2) cache
  check "The display cache stores no blank-cell results" (cache.values.size == 1 && cache.calculations == 1)
  let moved ← must (moveRect named 0 (rectangle 0 52) 2)
  expect moved.book "=SUM(Revenue)" "60"
  check "Cut moves complete named ranges with their cells" (moved.book[0]!.objects[0]!.first == 2 && moved.book[0]!.objects[0]!.last == 54)
  check "Cut rejects partial named-range moves" ((moveRect named 0 (rectangle 0 0) 2).toOption.isNone)
  let renamedSource ← must (renameSheet {refreshed with active:=0} "Fruit sales")
  let renamedPivot ← must (Features.refreshPivot {renamedSource with active:=1})
  check "Pivot sources follow sheet renames" (cellDisplay renamedPivot.book 1 27 == "45")
  let shiftedSource ← must (structureEdit {refreshed with active:=0} false true 0)
  let shiftedPivot ← must (Features.refreshPivot {shiftedSource with active:=1})
  check "Pivot sources follow inserted source columns" (cellDisplay shiftedPivot.book 1 27 == "45")
  check "Deleting a pivot key column is rejected explicitly" ((structureEdit {refreshed with active:=0} false false 0).toOption.isNone)
  let cbook := fn.book.set! 0 {fn.book[0]! with cells:=put fn.sheet 25 "=DOUBLE(Rate)"}
  let cache := (Incremental.display (Incremental.synchronize {} cbook) 0 25).2
  let changed := cbook.set! 0 {cbook[0]! with cells:=put cbook[0]!.cells 0 "12"}
  check "Custom functions recalculate after named inputs change" ((Incremental.display (Incremental.synchronize cache changed) 0 25).1 == "24")
  check "CSV replacement obeys validation rules" ((importCSV validation "200" ',').toOption.isNone)
  let date := Presentation.formatCells (editCell m 0 "=DATE(2024,2,29)") (rectangle 0 0) "date"
  check "Date formatting preserves serial values and displays ISO dates" (Presentation.formatted date.book[0]! 0 (cellDisplay date.book 0 0) == "2024-02-29" && date.sheet[0]! == "=DATE(2024,2,29)")
  let (dates,_) ← must (decodeBook (encodeBook date.book 0))
  check "Date formatting survives native reopen" (dates == date.book)
  let sparseBook := (List.range 32).toArray.map fun i => ({name:="Sheet"++toString (i+1),cells:=sparse} : NamedSheet)
  check "Thirty-two large sparse sheets retain only thirty-two populated entries" ((sparseBook.foldl (fun n s => n+s.cells.entries.size) 0) == 32 && (encodeBook sparseBook 0).length < 10000)
  let line : SheetObject := {kind:="chart",title:="One point",options:=#["line"]}
  check "Line charts render a marker for a single data point" (((← must (Features.svg m.book 0 line)).splitOn "<circle").length == 2)
  IO.FS.writeFile "lean_calc/examples/Features-gallery.lcalc" (encodeBook image.book 0)
  IO.FS.writeFile "lean_calc/examples/Pivot-gallery.lcalc" (encodeBook refreshed.book 1)
  IO.FS.writeFile "lean_calc/examples/Functions.json" exported
  IO.FS.writeFile "lean_calc/examples/Features-print.html" (Presentation.printHTML image)
  IO.println s!"{← AdvancedTests.count.get} Phase 5 checks passed."
end FeatureTests
