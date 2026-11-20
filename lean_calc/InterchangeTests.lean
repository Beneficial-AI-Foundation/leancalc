import OpenDocument
import Stage3Tests
namespace InterchangeTests
@[extern "calc_peak_rss"] opaque peakRSS : IO Nat
open Lean Phase2
open AdvancedTests (check)
def parseXML (xml : String) : IO OpenDocument.Node := do
  let tree ← OpenDocument.xmlTree xml
  IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse tree)))
def fails (action : IO α) : IO Bool := do
  try discard <| action; return false catch _ => return true

def run : IO Unit := do
  AdvancedTests.count.set 0
  let cells := put (put (put (put emptySheet 0 "2") 1 "=SIN(PI()/2)+A1") 26 "λ  & <text>\tend") 27 "'001"
  let m : Model := {book:=(singleBook cells).push {name:="Annual total",cells:=put emptySheet 0 "=SUM(Sheet1!A1:B1)"}}
  let m := Presentation.formatCells m (rectangle 0 0) "currency"
  let m := Presentation.formatCells m (rectangle 0 0) "bold"
  let m := Presentation.columnStyle m 0 180 "e"
  let xml ← IO.ofExcept (OpenDocument.content m.book)
  let root ← parseXML xml
  let book ← IO.ofExcept (OpenDocument.decode root)
  check "ODS values and formula results round-trip across sheets" (cellDisplay book 0 0 == "2" && cellDisplay book 0 1 == "3" && cellDisplay book 1 0 == "5")
  check "ODS text preserves Unicode XML punctuation and literal leading zeroes" (cellDisplay book 0 26 == "λ  & <text>\tend" && cellDisplay book 0 27 == "001")
  check "ODS basic number formats and bold style round-trip" ((Presentation.styleAt book[0]! 0).numberFormat == "currency" && (Presentation.styleAt book[0]! 0).bold)
  check "ODS column widths and alignment round-trip" (book[0]!.columns == m.book[0]!.columns)
  check "OpenFormula conversion preserves string delimiters" ((OpenDocument.formulaIn "of:=IF([.A1]>0;\"a;b\";\"x\")").toOption == some "=IF(A1>0,\"a;b\",\"x\")")
  check "OpenFormula conversion preserves anchored quoted references" ((OpenDocument.formulaIn "of:=['Annual total'.$A$1]+[.$B2]").toOption == some "='Annual total'!$A$1+$B2")
  check "ODS XML parsing resolves namespace URIs rather than literal prefixes" ((← parseXML (xml.replace "<office:" "<o:" |>.replace "</office:" "</o:" |>.replace " office:" " o:" |>.replace "xmlns:office=" "xmlns:o=")).tag == "office:document-content")
  check "ODS rejects DTD and external entities" (← fails (parseXML "<!DOCTYPE a [<!ENTITY x SYSTEM 'file:///etc/passwd'>]><a>&x;</a>"))
  check "ODS rejects malformed XML" (← fails (parseXML "<office:document-content>"))
  let merged := xml.replace "<table:table-cell table:style-name=" "<table:table-cell table:number-columns-spanned=\"2\" table:style-name="
  check "ODS rejects merged cells without modifying a workbook" (← fails (do let root ← parseXML merged; IO.ofExcept (OpenDocument.decode root)))
  let unsupported := xml.replace "of:=SIN" "of:=BOGUS"
  check "ODS rejects unsupported formulas rather than importing wrong results" (← fails (do let root ← parseXML unsupported; IO.ofExcept (OpenDocument.decode root)))
  IO.FS.withTempDir fun dir => do
    let file := dir / "roundtrip.ods"
    IO.FS.writeBinFile file (← OpenDocument.bytes m.book)
    check "ODS package has the spreadsheet MIME type" ((← OpenDocument.zipText file.toString "mimetype") == "application/vnd.oasis.opendocument.spreadsheet")
    let imported ← OpenDocument.read file.toString
    check "Packaged ODS opens through the actual ZIP and XML reader" (cellDisplay imported 1 0 == "5" && imported.size == 2)
  for (name,diagnostic) in [("sampledata.ods","table:content-validations"),("SubtotalsSampleFile.ods","Unsupported text style property")] do
    let result ← try discard <| OpenDocument.read ("lean_calc/fixtures/ods/"++name); pure "accepted" catch e => pure e.toString
    check ("Apache OpenOffice corpus rejects unsupported content explicitly: "++name) ((result.splitOn diagnostic).length > 1)
  IO.FS.writeBinFile "lean_calc/examples/Interoperability.ods" (← OpenDocument.bytes m.book)
  IO.FS.writeFile "lean_calc/examples/Advanced-workbook.lcalc" (encodeBook m.book 0)
  IO.println s!"{← AdvancedTests.count.get} OpenDocument checks passed."

def benchmark : IO Unit := do
  let mut cells := Sheet.blank 26000
  cells := put cells 0 "1"
  for i in [1:501] do cells := put cells i ("=A1*"++toString i)
  let book : Book := #[{cells:=cells}]
  let start ← IO.monoNanosNow
  let mut cache := Incremental.synchronize {} book
  for i in [:26000] do cache := (Incremental.display cache 0 i).2
  let warm ← IO.monoNanosNow
  let changed := book.set! 0 {book[0]! with cells:=put cells 0 "2"}
  cache := Incremental.synchronize cache changed
  for i in [:26000] do cache := (Incremental.display cache 0 i).2
  let finish ← IO.monoNanosNow
  if cache.calculations != 501 || cache.values[500]! != some "1000" then throw <| IO.userError "Incremental benchmark failed."
  IO.println s!"Peak resident memory: {(← peakRSS)/1024/1024} MiB."
  IO.println s!"1,000 rows x 26 columns, 500 dependent formulas: warm {(warm-start)/1000000} ms; input edit {(finish-warm)/1000000} ms; {cache.calculations} recalculated cells / 26000; output oracle=1000."
end InterchangeTests
