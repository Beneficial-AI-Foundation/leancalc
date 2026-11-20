import Phase2
open Lean Phase2
namespace Phase2Tests
private def sample : Sheet := put (put (put (put emptySheet 0 "1") 1 "2") 26 "3") 27 "4"
initialize count : IO.Ref Nat ← IO.mkRef 0
private def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw <| IO.userError ("FAIL: " ++ name)
  count.modify (·+1)
  IO.println ("PASS: " ++ name)
private def must {α : Type} (v : Except String α) : IO α :=
  match v with | .ok a => pure a | .error e => throw <| IO.userError e
private def error {α : Type} (v : Except String α) := match v with | .error _ => true | _ => false
private def result (f : String) : String := cellDisplay (singleBook (put emptySheet 2599 ("="++f))) 0 2599
private def b : Book := #[{name:="Sheet1",cells:=put (put (put emptySheet 0 "2") 26 "4") 1 "text"}, {name:="Annual total",cells:=put emptySheet 0 "=Sheet1!A1+Sheet1!A2"}]
private def structural : Model := {book:=#[{cells:=put (put (put (put emptySheet 0 "10") 26 "20") 52 "30") 1 "=SUM(A1:A3)"}, {name:="Sheet2",cells:=put emptySheet 0 "=Sheet1!$A$2"}]}

def run : IO Unit := do
  count.set 0
  check "Phase 2 arithmetic precedence and exact decimals" (result "0.1+0.2*3" == "0.7" && result "(2+3)*4" == "20")
  check "Unary signs and subtraction remain compatible" (result "-2*-3+4-1" == "9")
  check "All comparison operators" (result "2<3" == "1" && result "2>3" == "0" && result "2<=2" == "1" && result "3>=3" == "1" && result "2<>3" == "1" && result "2=2" == "1")
  check "Comparison precedence follows arithmetic" (result "1+2*3=7" == "1")
  check "IF evaluates only the chosen branch" (result "IF(1,7,1/0)" == "7" && result "IF(0,1/0,8)" == "8")
  check "IF returns text and accepts nested conditions" (result "IF(2>1,\"yes\",\"no\")" == "yes" && result "IF(0,1,IF(TRUE,2,3))" == "2")
  check "Quoted strings preserve punctuation and escaped quotes" (result "IF(1,\"A1,+ \"\"yes\"\"\",0)" == "A1,+ \"yes\"")
  check "IF rejects missing or extra arguments" (result "IF(1,2)" == "#PARSE!" && result "IF(1,2,3,4)" == "#PARSE!")
  check "MIN MAX AVERAGE COUNT and variadic SUM" (result "MIN(3,1,2)" == "1" && result "MAX(3,1,2)" == "3" && result "AVERAGE(1,2)" == "1.5" && result "COUNT(1,2,\"text\")" == "2" && result "SUM(1,2,3)" == "6")
  check "Empty aggregates have defined results" (result "SUM()" == "0" && result "MIN()" == "0" && result "MAX()" == "0" && result "COUNT()" == "0" && result "AVERAGE()" == "#DIV/0!")
  check "Aggregate errors propagate" (result "SUM(1,1/0)" == "#DIV/0!" && result "COUNT(1,1/0)" == "#DIV/0!")
  check "Unknown functions and malformed argument lists fail" (result "BOGUS(1)" == "#NAME?" && result "SUM(1,)" == "#PARSE!")
  let rangeBook := b.set! 0 {b[0]! with cells:=put (put (put (put b[0]!.cells 2 "=MIN(A1:B2)") 3 "=MAX(A1:B2)") 4 "=AVERAGE(A1:B2)") 5 "=COUNT(A1:B2)"}
  check "Range functions skip blank and literal text cells" (cellDisplay rangeBook 0 2 == "2" && cellDisplay rangeBook 0 3 == "4" && cellDisplay rangeBook 0 4 == "3" && cellDisplay rangeBook 0 5 == "2")
  check "Cross-sheet formulas calculate" (cellDisplay b 1 0 == "6")
  let quoted := b.set! 0 {b[0]! with cells:=put b[0]!.cells 2 "='Annual total'!$A$1"}
  check "Quoted sheet names and absolute references calculate" (cellDisplay quoted 0 2 == "6")
  let mixed := b.set! 0 {b[0]! with cells:=put b[0]!.cells 2 "=SUM('Annual total'!A1:A2)"}
  check "Range endpoints inherit the first sheet qualifier" (cellDisplay mixed 0 2 == "6")
  let caseBook := b.set! 0 {b[0]! with cells:=put b[0]!.cells 2 "='annual TOTAL'!a1"}
  check "Sheet and cell lookup is case-insensitive" (cellDisplay caseBook 0 2 == "6")
  check "Unknown sheets report REF" (result "Missing!A1" == "#REF!")
  let cycle := #[{name:="A",cells:=put emptySheet 0 "=B!A1"},{name:="B",cells:=put emptySheet 0 "=A!A1"}]
  check "Cross-sheet cycles are detected" (cellDisplay cycle 0 0 == "#CYCLE!")
  let safe := cycle.set! 0 {cycle[0]! with cells:=put emptySheet 0 "=IF(0,B!A1,5)"}
  check "Unchosen IF branches do not cause cross-sheet cycles" (cellDisplay safe 0 0 == "5")
  check "Formula length budget remains enforced" (result (String.ofList (List.replicate 513 '1')) == "#LIMIT!")
  check "Relative absolute and mixed copy adjustments" (shiftFormula "=A1+$A$1+A$1+$A1" 2 3 == "=D3+$A$1+D$1+$A3")
  check "Copy adjusts qualified references" (shiftFormula "=Other!A1" 1 1 == "='Other'!B2")
  check "Copy preserves formula string literals" (shiftFormula "=IF(A1,\"A1\",\"B2\")" 1 0 == "=IF(A2,\"A1\",\"B2\")")
  check "Out-of-bounds relative copies become REF" (shiftFormula "=A1+$A$1" (-1) 0 == "=#REF!+$A$1")
  check "Range copies preserve endpoint anchors" (shiftFormula "=SUM($A1:B$2)" 1 1 == "=SUM($A2:C$2)")
  let m : Model := {book:=b}
  let added ← must (addSheet m "Bob's data")
  check "Adding a sheet activates it" (added.active == 2 && added.book[2]!.name == "Bob's data")
  check "Duplicate names are rejected case-insensitively" (error (addSheet m "sHEET1"))
  check "Invalid sheet names are rejected" (error (addSheet m "Bad/name") && error (addSheet m " ") && error (addSheet m (String.ofList (List.replicate 32 'a'))))
  let apostrophe := added.book.set! 2 {added.book[2]! with cells:=put emptySheet 0 "9"}
  let apostrophe := apostrophe.set! 0 {apostrophe[0]! with cells:=put emptySheet 0 "='Bob''s data'!A1"}
  check "Quoted sheet names escape apostrophes" (cellDisplay apostrophe 0 0 == "9")
  let renamed ← must (renameSheet {m with active:=0} "Inputs")
  check "Renaming updates references in every sheet" (cellDisplay renamed.book 1 0 == "6" && renamed.book[1]!.cells[0]! == "='Inputs'!A1+'Inputs'!A2")
  check "Renaming to another sheet name is rejected" (error (renameSheet m "Annual total"))
  let deleted ← must (deleteSheet m)
  check "Deleting a sheet invalidates its references" (deleted.book.size == 1 && cellDisplay deleted.book 0 0 == "#REF!")
  check "Last sheet cannot be deleted" (error (deleteSheet {}))
  let edited := editCell {added with active:=0} 0 "99"
  check "Undo crosses sheets and restores active sheet" ((undoModel edited).active == 0 && (undoModel edited).sheet[0]! == "2" && (undoModel (undoModel edited)).book.size == 2)
  check "Redo restores workbook operations" ((redoModel (undoModel edited)).book == edited.book)
  check "Editing after undo clears workbook redo" ((editCell (undoModel edited) 1 "changed").redo.isEmpty)
  let table := #[#["1","=A1*2"],#["3","=A2*2"]]
  let pasted ← must (pasteTable {} 0 table)
  check "Rectangular paste fills all cells" (pasted.sheet[0]! == "1" && pasted.sheet[27]! == "=A2*2" && cellDisplay pasted.book 0 27 == "6")
  let copied ← must (pasteTable pasted 2 table (some (0,0)))
  check "Rectangle copy adjusts relative formulas" (copied.sheet[3]! == "=C1*2" && cellDisplay copied.book 0 29 == "6")
  check "Paste rejects overflow and ragged tables" (error (pasteTable {} 25 table) && error (pasteTable {} 0 #[#["1"],#["2","3"]]))
  check "Paste is one undo step" ((undoModel pasted).sheet == emptySheet)
  let fillBase : Model := {book:=singleBook (put (put emptySheet 0 "1") 1 "=$A1*2")}
  let filled ← must (fillRect fillBase (rectangle 0 53) true)
  check "Fill Down copies the first row and adjusts mixed references" (filled.sheet[52]! == "1" && filled.sheet[53]! == "=$A3*2" && cellDisplay filled.book 0 53 == "2")
  let right ← must (fillRect {book:=singleBook (put emptySheet 0 "=A$2")} (rectangle 0 2) false)
  check "Fill Right adjusts columns and preserves absolute rows" (right.sheet[2]! == "=C$2")
  check "Clear rectangle preserves outside cells" ((clearRect copied (rectangle 0 27)).sheet[3]! == "=C1*2" && (clearRect copied (rectangle 0 27)).sheet[27]! == "")
  let moved ← must (moveRect pasted 0 (rectangle 0 27) 28)
  check "Overlapping Cut uses the original rectangle" (moved.sheet[0]! == "" && moved.sheet[28]! == "1" && moved.sheet[55]! == "=C3*2" && cellDisplay moved.book 0 55 == "6")
  let moveBase : Model := {book:=#[{cells:=put (put emptySheet 0 "5") 1 "=$A$1"},{name:="Other",cells:=put emptySheet 0 "=Sheet1!A1"}],active:=1}
  let crossMove ← must (moveRect moveBase 0 (rectangle 0 0) 27)
  check "Cut across sheets updates outside and anchored references" (crossMove.book[0]!.cells[1]! == "='Other'!$B$2" && cellDisplay crossMove.book 1 0 == "5" && crossMove.sheet[27]! == "5")
  let outgoing : Model := {book:=#[{cells:=put (put emptySheet 0 "5") 1 "=A1"},{name:="Other"}],active:=1}
  let outgoing ← must (moveRect outgoing 0 (rectangle 1 1) 0)
  check "Moved formula retains references outside its block" (outgoing.sheet[0]! == "='Sheet1'!A1" && cellDisplay outgoing.book 1 0 == "5")
  check "Cut move is one undo operation" ((undoModel crossMove).book == moveBase.book)
  let inserted ← must (structureEdit structural true true 1)
  check "Insert row shifts data without truncation" (inserted.sheet[26]! == "" && inserted.sheet[52]! == "20" && inserted.sheet[78]! == "30")
  check "Insert row expands a spanning range" (inserted.sheet[1]! == "=SUM(A1:A4)" && cellDisplay inserted.book 0 1 == "60")
  check "Structural changes shift absolute cross-sheet references" (inserted.book[1]!.cells[0]! == "='Sheet1'!$A$3" && cellDisplay inserted.book 1 0 == "20")
  let removed ← must (structureEdit structural true false 1)
  check "Delete row shrinks ranges and shifts data" (removed.sheet[26]! == "30" && removed.sheet[1]! == "=SUM(A1:A2)" && cellDisplay removed.book 0 1 == "40")
  check "Deleted single-cell reference becomes REF" (cellDisplay removed.book 1 0 == "#REF!")
  let boundary : Model := {book:=singleBook (put (put (put emptySheet 0 "1") 26 "2") 2 "=SUM(A1:A2)")}
  let boundary ← must (structureEdit boundary true false 0)
  check "Deleting a range boundary retains surviving cells" (boundary.sheet[0]! == "2")
  let reversed : Model := {book:=singleBook (put (put emptySheet 0 "1") 2 "=SUM(A3:A1)")}
  let reversed ← must (structureEdit reversed true false 1)
  check "Reversed ranges shrink correctly" (reversed.sheet[2]! == "=SUM(A2:A1)")
  let one : Model := {book:=singleBook (put emptySheet 1 "=SUM(A2:A2)")}
  let one ← must (structureEdit one true false 1)
  check "Deleting a whole referenced range becomes REF" (cellDisplay one.book 0 1 == "#REF!")
  let columns ← must (structureEdit structural false true 0)
  check "Insert column shifts formulas and their references" (columns.sheet[1]! == "10" && columns.sheet[2]! == "=SUM(B1:B3)" && cellDisplay columns.book 1 0 == "20")
  let columns ← must (structureEdit columns false false 0)
  check "Delete column reverses a prior empty insertion" (columns.sheet == structural.sheet && cellDisplay columns.book 1 0 == "20")
  let edge : Model := {book:=singleBook (put emptySheet 2599 "keep")}
  check "Insertion cannot discard nonempty edge cells" (error (structureEdit edge true true 0) && error (structureEdit edge false true 0))
  check "Structural operation is one undo step" ((undoModel inserted).book == structural.book)
  let (migrated,active) ← must (decodeBook (encode sample))
  check "Phase 1 files migrate without losing cells" (migrated == singleBook sample && active == 0)
  let (roundtrip,active) ← must (decodeBook (encodeBook b 1))
  check "Phase 2 round-trip preserves sheets and active sheet" (roundtrip == b && active == 1)
  check "Version and active-sheet validation" (error (decodeBook ((encodeBook b 0).replace "LeanCalc-2" "LeanCalc-99")) && error (decodeBook (encodeBook b 3)))
  check "Workbook format rejects duplicate names and invalid shapes" (error (decodeBook (encodeBook #[{},{}] 0)) && error (decodeBook (encodeBook #[{cells:=#["x"]}] 0)))
  let csv ← must (parseDelimited "\uFEFFa,\"b,c\",\"d\"\"e\"\r\n1,\"two\nlines\",3\r\n" ',')
  check "CSV handles BOM quoted delimiters doubled quotes and newlines" (csv == #[#["a","b,c","d\"e"],#["1","two\nlines","3"]])
  check "CSV round-trip preserves embedded CR LF quotes and Unicode" ((parseDelimited (encodeDelimited #[#["λ","a\r\nb","\"",""],#["x,y","z","","tail"]] ',') ',').toOption == some #[#["λ","a\r\nb","\"",""],#["x,y","z","","tail"]])
  check "Semicolon delimiter is explicit" ((parseDelimited "a;\"b;c\"\n" ';').toOption == some #[#["a","b;c"]])
  check "CSV accepts CR LF and CRLF record endings" ((parseDelimited "a\rb\nc\r\n" ',').toOption == some #[#["a"],#["b"],#["c"]])
  check "CSV preserves trailing empty fields" ((parseDelimited "a,,\r\n" ',').toOption == some #[#["a","",""]])
  check "CSV rejects malformed quoting" (error (parseDelimited "\"unclosed" ',') && error (parseDelimited "\"x\"z" ',') && error (parseDelimited "a\"b" ','))
  check "CSV rejects too many rows or columns" (error (parseDelimited (String.intercalate "\n" (List.replicate 101 "x")) ',') && error (parseDelimited (String.intercalate "," (List.replicate 27 "x")) ','))
  check "CSV rejects NUL and oversized fields" (error (parseDelimited "a\u0000b" ',') && error (parseDelimited (String.ofList (List.replicate 4097 'x')) ','))
  let imported ← must (importCSV m "1,=2+3\n4\n" ',')
  check "CSV import pads shorter rows and keeps formulas literal" (imported.sheet[27]! == "" && cellDisplay imported.book 0 1 == "=2+3")
  check "CSV import preserves other sheets" (imported.book[1]! == m.book[1]!)
  check "CSV import is one undo step" ((undoModel imported).book == m.book)
  check "CSV export writes displayed values and CRLF" (exportCSV {book:=#[b[1]!]} ',' == "#REF!\r\n" && exportCSV {book:=b,active:=1} ',' == "6\r\n")
  check "Blank sheet CSV exports one empty cell" (exportCSV {} ',' == "\r\n")
  let literal ← must (importCSV {} "'=1,\"=2+2\"" ',')
  check "CSV literal apostrophes survive import and export" (exportCSV literal ',' == "'=1,=2+2\r\n")
  let table := #[#["a\tb","line\nnext","\"quote\""]]
  check "Clipboard TSV round-trip preserves tabs newlines and quotes" ((parseDelimited (encodeDelimited table '\t') '\t').toOption == some table)
  let blankRef := singleBook (put emptySheet 1 "=COUNT(A1)")
  check "COUNT ignores a blank scalar reference" (cellDisplay blankRef 0 1 == "0")
  let bangs : Book := #[{name:="Bang!",cells:=put emptySheet 0 "8"},{name:="Result",cells:=put emptySheet 0 "='Bang!'!A1"}]
  check "Quoted sheet names can contain exclamation marks" (cellDisplay bangs 1 0 == "8")
  let splitRange : Model := {book:=singleBook (put (put emptySheet 0 "1") 3 "=SUM(A1:C1)")}
  check "Cut refuses to split a referenced range" (error (moveRect splitRange 0 (rectangle 1 1) 27))
  let startBoundary : Model := {book:=singleBook (put (put (put emptySheet 0 "1") 26 "2") 79 "=SUM(A1:A2)")}
  let startBoundary ← must (structureEdit startBoundary true false 0)
  check "Deleting the first range row preserves a surviving formula" (startBoundary.sheet[53]! == "=SUM(A1:A1)" && cellDisplay startBoundary.book 0 53 == "2")
  let endBoundary : Model := {book:=singleBook (put (put (put emptySheet 0 "1") 26 "2") 79 "=SUM(A1:A2)")}
  let endBoundary ← must (structureEdit endBoundary true false 1)
  check "Deleting the last range row preserves a surviving formula" (endBoundary.sheet[53]! == "=SUM(A1:A1)" && cellDisplay endBoundary.book 0 53 == "1")
  let many := (List.range 32).toArray.map (fun i => ({name:="Sheet"++toString i} : NamedSheet))
  check "Workbook enforces its 32-sheet limit" (error (addSheet {book:=many} "Extra"))
  let mut history : Model := {}
  for i in [0:110] do history := editCell history 0 (toString i)
  check "Workbook undo history remains bounded" (history.undo.length == 100)
  let compatible := (List.range 11).all fun x => (List.range 7).all fun y =>
    ["+","-","*","/"].all fun op =>
      let formula := "=(" ++ toString (Int.ofNat x-5) ++ ")" ++ op ++ "(" ++ toString (Int.ofNat y-3) ++ ")"
      let sheet := put emptySheet 0 formula
      cellDisplay (singleBook sheet) 0 0 == display sheet 0
  check "Phase 2 agrees with the Phase 1 arithmetic oracle across 308 cases" compatible
  IO.println s!"{← count.get} Phase 2 checks passed."
end Phase2Tests
