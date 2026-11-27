import Presentation
namespace OpenDocument
open Lean Phase2
@[extern "calc_zip_text"] opaque zipText (path entry : @& String) : IO String
@[extern "calc_xml_tree"] opaque xmlTree (text : @& String) : IO String
structure Node where
  tag : String
  attrs : Array (String × String)
  text : String
  children : Array Node
  deriving Inhabited, FromJson

def attr (n : Node) (key : String) (fallback : String := "") :=
  ((n.attrs.find? (·.1 == key)).map (·.2)).getD fallback
partial def descendants (n : Node) (tag : String) : List Node :=
  (if n.tag == tag then [n] else []) ++ n.children.toList.flatMap (fun c => descendants c tag)
def escape := Presentation.htmlEscape
def textXML (s : String) : String := String.join (s.toList.map fun c =>
  if c == ' ' then "<text:s/>" else if c == '\t' then "<text:tab/>" else escape (String.singleton c))

def refText (r : Ref) :=
  (r.sheet.map quoteName |>.getD "") ++ "." ++ (if r.absCol then "$" else "") ++
  String.singleton (Char.ofNat (65+r.col)) ++ (if r.absRow then "$" else "") ++ toString (r.row+1)
def supportedExprFuel : Nat → Phase2.Expr → Bool
  | 0,_ => false
  | fuel+1,e => match e with
    | .named _ => false
    | .call n args => MathFunctions.supported n && args.all (fun a => supportedExprFuel fuel a)
    | .neg a => supportedExprFuel fuel a
    | .bin _ a b => supportedExprFuel fuel a && supportedExprFuel fuel b
    | _ => true
def supportedExpr := supportedExprFuel 128

def formulaOut (raw : String) : Except String String := do
  let e ← parse (String.ofList (trim raw).toList.tail)
  if !supportedExpr e then throw "Unsupported ODS function or named expression."
  let ts ← tokens (String.ofList (trim raw).toList.tail)
  let mut out := "of:="
  let mut rest := ts
  while !rest.isEmpty do
    match rest with
    | a::":"::b::tail =>
      let some a := parseRef a | throw "Unsupported ODS range."
      let some b := parseRef b | throw "Unsupported ODS range."
      out := out ++ "[" ++ refText a ++ ":" ++ refText b ++ "]"
      rest := tail
    | t::tail =>
      out := out ++ (if t == "," then ";" else match parseRef t with | some r => "["++refText r++"]" | none => if t.toUpper == "SAVERAGE" then "AVERAGE" else t)
      rest := tail
    | _ => pure ()
  return out

def refIn (text : String) : Except String String := do
  if text.startsWith "." then return String.ofList text.toList.tail
  let mut quote := false
  let mut lastDot : Option Nat := none
  for (c,i) in text.toList.zipIdx do
    if c == '\'' then quote := !quote
    if c == '.' && !quote then lastDot := some i
  let some p := lastDot | throw "Unsupported OpenFormula reference."
  let sheet := String.ofList (text.toList.take p)
  let sheet := if sheet.startsWith "$" then String.ofList sheet.toList.tail else sheet
  return sheet ++ "!" ++ String.ofList (text.toList.drop (p+1))
def formulaIn (raw : String) : Except String String := do
  if !raw.startsWith "of:=" then throw "Only OpenFormula (of:=) formulas are supported."
  let mut cs := raw.toList.drop 4
  let mut quoted := false
  let mut out := "="
  while !cs.isEmpty do
    let c := cs.head!
    cs := cs.tail
    if c == '"' then quoted := !quoted; out := out.push c
    else if !quoted && c == '[' then
      let r := cs.takeWhile (· != ']')
      if r.length == cs.length then throw "Unclosed OpenFormula reference."
      cs := cs.drop (r.length+1)
      let parts := (String.ofList r).splitOn ":"
      out := out ++ String.intercalate ":" (← parts.mapM refIn)
    else out := out.push (if !quoted && c == ';' then ',' else c)
  let e ← parse (String.ofList out.toList.tail)
  if !supportedExpr e then throw "Unsupported ODS function or named expression."
  return out

def repeated (n : Node) (key : String) : Except String Nat := do
  let some count := (attr n key "1").toNat? | throw "Invalid repeated rows or cells."
  if count == 0 || count > 1048576 then throw "Repeated rows or cells exceed limits."
  return count

def readStyle (root : Node) (name : String) (cell : Nat) : Except String CellStyle := do
  if name == "" then return {cell:=cell}
  let some style := (descendants root "style:style").find? (fun n => attr n "style:name" == name) | throw ("Unknown cell style: "++name)
  let props := (descendants style "style:text-properties").headD default
  for (key,_) in props.attrs do
    if !["fo:font-weight","fo:font-family","fo:font-size","style:font-name"].contains key then throw ("Unsupported text style property: "++key)
  if !(descendants style "style:paragraph-properties").isEmpty then throw "Per-cell paragraph alignment is outside the supported ODS subset."
  if !(descendants style "style:table-cell-properties").isEmpty then throw "Cell background/border styles are outside the supported ODS subset."
  let family := attr props "fo:font-family" (attr props "style:font-name")
  let size := attr props "fo:font-size" "13pt"
  let some sizeQ := MathFunctions.literal (size.replace "pt" "") | throw "Unsupported font size."
  let dataName := attr style "style:data-style-name"
  let numberFormat ← if dataName == "" then pure "general" else do
    let choices := [("number:number-style","number"),("number:currency-style","currency"),("number:percentage-style","percent"),("number:number-style","number")]
    let mut found := ""
    for (tag,format) in choices do
      if let some dataStyle := (descendants root tag).find? (fun n => attr n "style:name" == dataName) then
        for number in descendants dataStyle "number:number" do
          if attr number "number:decimal-places" "0" != "2" then throw "Only two-decimal ODS number styles are currently supported."
        if format == "currency" && (descendants dataStyle "number:currency-symbol").any (fun n => n.text != "$") then throw "Only dollar-symbol ODS currency styles are currently supported."
        found := if !(descendants dataStyle "number:fraction").isEmpty then "fraction" else format
    if found == "" then throw ("Unsupported number format: "++dataName)
    pure found
  return {cell:=cell,numberFormat:=numberFormat,bold:=(attr props "fo:font-weight" == "bold"), fontFamily:=if family == "Times" || family == "serif" then "serif" else if family == "Menlo" || family == "monospace" then "mono" else "default",fontSize:=sizeQ.floor.toNat}

def decode (root : Node) : Except String Book := do
  if root.tag != "office:document-content" then throw "Not an ODS content document."
  for tag in ["draw:frame","table:covered-table-cell","table:named-expressions","table:content-validations","office:script","office:annotation","table:database-ranges","table:tracked-changes","table:shapes","table:data-pilot-tables","table:table-source","table:consolidation","table:scenario","table:cell-range-source","table:detective","text:a","text:span"] do
    if !(descendants root tag).isEmpty then throw ("Unsupported ODS feature: "++tag++". The original file is unchanged.")
  for n in descendants root "table:null-date" do
    if attr n "table:date-value" != "1899-12-30" then throw "Unsupported ODS date epoch."
  let tables := descendants root "table:table"
  if tables.isEmpty || tables.length > 32 then throw "ODS needs 1 to 32 sheets."
  let mut book := #[]
  for table in tables do
    let mut cells := Sheet.blank 26000
    let mut styles := #[]
    let mut columns := #[]
    let mut columnIndex := 0
    for c in descendants table "table:table-column" do
      let count ← repeated c "table:number-columns-repeated"
      let name := attr c "table:style-name"
      if name != "" then
        let some st := (descendants root "style:style").find? (fun n => attr n "style:name" == name) | throw "Unknown column style."
        let prop := (descendants st "style:table-column-properties").headD default
        let length := attr prop "style:column-width" "78.75pt"
        let unit := if length.endsWith "cm" then "cm" else if length.endsWith "in" then "in" else "pt"
        let some q := MathFunctions.literal (length.replace unit "") | throw "Unsupported column width."
        let pixels := q*(if unit == "cm" then mkRat 9600 254 else if unit == "in" then 96 else mkRat 4 3)
        let width := max 35 (min 600 (pixels+mkRat 1 2).floor.toNat)
        let cellName := attr c "table:default-cell-style-name"
        let cellStyle := ((descendants root "style:style").find? (fun n => attr n "style:name" == cellName)).getD default
        let para := (descendants cellStyle "style:paragraph-properties").headD default
        let align := attr para "fo:text-align" "start"
        for col in [columnIndex:min 26 (columnIndex+count)] do
          columns := columns.push {column:=col,width:=width,alignment:=if align == "center" then "center" else if align == "end" || align == "right" then "e" else "w"}
      columnIndex := columnIndex+count
    let mut row := 0
    let mut bottom := 0
    for r in descendants table "table:table-row" do
      let repeatRows ← repeated r "table:number-rows-repeated"
      let mut column := 0
      for c in r.children do
        if c.tag != "table:table-cell" then throw ("Unsupported row element: "++c.tag)
        if attr c "table:number-columns-spanned" "1" != "1" || attr c "table:number-rows-spanned" "1" != "1" then throw "Merged ODS cells are not supported."
        let repeatCols ← repeated c "table:number-columns-repeated"
        let formula := attr c "table:formula"
        let kind := attr c "office:value-type"
        let text := String.intercalate "\n" ((descendants c "text:p").map (·.text))
        let raw ← if formula != "" then formulaIn formula else
          match kind with
          | "" => pure ""
          | "float" | "currency" | "percentage" =>
            let value := attr c "office:value"
            if (MathFunctions.literal value).isNone then throw "Invalid ODS numeric value."
            pure value
          | "boolean" => pure (if attr c "office:boolean-value" == "true" then "1" else "0")
          | "string" =>
            let value := attr c "office:string-value" text
            pure (if (trim value).startsWith "=" || value.startsWith "'" || (MathFunctions.literal value).isSome then "'"++value else value)
          | _ => throw ("Unsupported ODS cell type: "++kind)
        if raw != "" && (row+repeatRows > 1000 || column+repeatCols > 26) then throw "ODS data exceeds 1,000 rows or 26 columns."
        if !validCell raw then throw "ODS cell exceeds text limit."
        for rr in [row:min 1000 (row+repeatRows)] do
          for cc in [column:min 26 (column+repeatCols)] do
            let i := rr*26+cc
            if raw != "" then cells := cells.set! i raw; bottom := max bottom (rr+1)
            if attr c "table:style-name" != "" then
              styles := styles.push (← readStyle root (attr c "table:style-name") i)
              bottom := max bottom (rr+1)
        column := column+repeatCols
      row := row+repeatRows
    let rows := max 100 bottom
    cells := cells.extract 0 (rows*26)
    book := book.push {name:=attr table "table:name",cells:=cells,styles:=styles,columns:=columns}
  validateBook book
  return book

def content (book : Book) : Except String String := do
  validateBook book
  if book.any (fun s => s.styles.any (fun st => st.numberFormat == "date")) then throw "ODS date formatting is outside the supported style subset; save .lcalc to preserve it."
  if book.any (fun s => !s.objects.isEmpty) then throw "ODS export does not yet preserve named ranges, rules, charts, images, pivots or custom functions. Save as .lcalc to preserve these objects."
  let mut xml := "<?xml version=\"1.0\" encoding=\"UTF-8\"?><office:document-content xmlns:office=\"urn:oasis:names:tc:opendocument:xmlns:office:1.0\" xmlns:table=\"urn:oasis:names:tc:opendocument:xmlns:table:1.0\" xmlns:text=\"urn:oasis:names:tc:opendocument:xmlns:text:1.0\" xmlns:style=\"urn:oasis:names:tc:opendocument:xmlns:style:1.0\" xmlns:number=\"urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0\" xmlns:fo=\"urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0\" xmlns:of=\"urn:oasis:names:tc:opendocument:xmlns:of:1.2\" office:version=\"1.3\"><office:automatic-styles>"
  xml := xml ++ "<number:number-style style:name=\"nnumber\"><number:number number:decimal-places=\"2\" number:min-integer-digits=\"1\"/></number:number-style><number:currency-style style:name=\"ncurrency\"><number:currency-symbol>$</number:currency-symbol><number:number number:decimal-places=\"2\" number:min-integer-digits=\"1\"/></number:currency-style><number:percentage-style style:name=\"npercent\"><number:number number:decimal-places=\"2\" number:min-integer-digits=\"1\"/><number:text>%</number:text></number:percentage-style><number:number-style style:name=\"nfraction\"><number:fraction number:min-numerator-digits=\"1\" number:min-denominator-digits=\"1\"/></number:number-style>"
  for si in [:book.size] do
    for st in book[si]!.styles do
      let dataStyle := if st.numberFormat == "general" then "" else " style:data-style-name=\"n"++st.numberFormat++"\""
      let family := if st.fontFamily == "serif" then "Times" else if st.fontFamily == "mono" then "Menlo" else "Helvetica"
      xml := xml ++ "<style:style style:name=\"s"++toString si++"c"++toString st.cell++"\" style:family=\"table-cell\""++dataStyle++"><style:text-properties fo:font-weight=\""++(if st.bold then "bold" else "normal")++"\" fo:font-family=\""++family++"\" fo:font-size=\""++toString st.fontSize++"pt\"/></style:style>"
  for si in [:book.size] do
    for col in book[si]!.columns do
      let name := "col"++toString si++"c"++toString col.column
      let align := if col.alignment == "e" then "end" else if col.alignment == "center" then "center" else "start"
      xml := xml ++ "<style:style style:name=\""++name++"\" style:family=\"table-column\"><style:table-column-properties style:column-width=\""++MathFunctions.display (mkRat (Int.ofNat (col.width*3)) 4)++"pt\"/></style:style><style:style style:name=\"a"++name++"\" style:family=\"table-cell\"><style:paragraph-properties fo:text-align=\""++align++"\"/></style:style>"
  xml := xml ++ "</office:automatic-styles><office:body><office:spreadsheet>"
  for si in [:book.size] do
    let sheet := book[si]!
    let rect := Presentation.usedRect sheet.cells
    let rect := sheet.styles.foldl (fun r st => {r with bottom:=max r.bottom (st.cell/26),right:=max r.right (st.cell%26)}) rect
    let rect := sheet.columns.foldl (fun r col => {r with right:=max r.right col.column}) rect
    xml := xml ++ "<table:table table:name=\"" ++ escape sheet.name ++ "\">"
    for col in [:rect.right+1] do
      let name := "col"++toString si++"c"++toString col
      xml := xml ++ (if sheet.columns.any (·.column == col) then "<table:table-column table:style-name=\""++name++"\" table:default-cell-style-name=\"a"++name++"\"/>" else "<table:table-column/>")
    for row in [:rect.bottom+1] do
      xml := xml ++ "<table:table-row>"
      for col in [:rect.right+1] do
        let i := row*26+col
        let raw := sheet.cells[i]!
        let style := if sheet.styles.any (·.cell == i) then " table:style-name=\"s"++toString si++"c"++toString i++"\"" else ""
        let f ← if (trim raw).startsWith "=" then pure (" table:formula=\""++escape (← formulaOut raw)++"\"") else pure ""
        if raw == "" then xml := xml ++ "<table:table-cell"++style++"/>"
        else
          let value := cellValue book si i
          let attrs ← match value with
            | .ok (.number q) =>
              let numeric := MathFunctions.floatText (MathFunctions.asFloat q)
              if (MathFunctions.literal numeric).isNone then throw "Numeric value is outside the ODS floating-point range."
              pure (" office:value-type=\"float\" office:value=\""++numeric++"\"")
            | _ => pure " office:value-type=\"string\""
          let text := cellDisplay book si i
          let paragraphs := String.join ((text.splitOn "\n").map (fun line => "<text:p>"++textXML line++"</text:p>"))
          xml := xml ++ "<table:table-cell"++style++f++attrs++">"++paragraphs++"</table:table-cell>"
      xml := xml ++ "</table:table-row>"
    xml := xml ++ "</table:table>"
  return xml ++ "</office:spreadsheet></office:body></office:document-content>"

def read (path : String) : IO Book := do
  if (← zipText path "mimetype") != "application/vnd.oasis.opendocument.spreadsheet" then throw <| IO.userError "Not an ODS spreadsheet."
  let tree ← xmlTree (← zipText path "content.xml")
  let json ← IO.ofExcept (Json.parse tree)
  let root : Node ← IO.ofExcept (fromJson? json)
  IO.ofExcept (decode root)

def bytes (book : Book) : IO ByteArray := IO.FS.withTempDir fun dir => do
  let xml ← IO.ofExcept (content book)
  IO.FS.createDirAll (dir / "META-INF")
  IO.FS.writeFile (dir / "mimetype") "application/vnd.oasis.opendocument.spreadsheet"
  IO.FS.writeFile (dir / "content.xml") xml
  IO.FS.writeFile (dir / "META-INF/manifest.xml") "<?xml version=\"1.0\"?><manifest:manifest xmlns:manifest=\"urn:oasis:names:tc:opendocument:xmlns:manifest:1.0\" manifest:version=\"1.3\"><manifest:file-entry manifest:full-path=\"/\" manifest:version=\"1.3\" manifest:media-type=\"application/vnd.oasis.opendocument.spreadsheet\"/><manifest:file-entry manifest:full-path=\"content.xml\" manifest:media-type=\"text/xml\"/></manifest:manifest>"
  -- Fixed timestamps make the same workbook always produce the same bytes.
  let touched ← IO.Process.output {cmd:="/usr/bin/touch",args:=#["-t","202601010000","mimetype","content.xml","META-INF/manifest.xml"],cwd:=some dir}
  if touched.exitCode != 0 then throw <| IO.userError ("ODS packaging failed: "++touched.stderr)
  for args in [#["-X","-0","book.ods","mimetype"],#["-X","book.ods","content.xml","META-INF/manifest.xml"]] do
    let result ← IO.Process.output {cmd:="/usr/bin/zip",args:=args,cwd:=some dir}
    if result.exitCode != 0 then throw <| IO.userError ("ODS packaging failed: "++result.stderr)
  IO.FS.readBinFile (dir / "book.ods")
end OpenDocument
