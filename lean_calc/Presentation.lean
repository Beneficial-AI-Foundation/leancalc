import Features
namespace Presentation
open Lean Phase2

def styleAt (s : NamedSheet) (i : Nat) : CellStyle :=
  (s.styles.find? (·.cell == i)).getD {cell:=i}
def fixed (q : Rat) (digits : Nat := 2) : String := Id.run do
  let scaled := ((MathFunctions.absQ q)*Rat.ofInt (Int.ofNat (10^digits))+mkRat 1 2).floor.toNat
  let text := toString scaled
  let padded := String.ofList (List.replicate (digits+1-text.length) '0') ++ text
  let cs := padded.toList
  return (if q < 0 && scaled != 0 then "-" else "") ++ String.ofList (cs.take (cs.length-digits)) ++
    (if digits == 0 then "" else "." ++ String.ofList (cs.drop (cs.length-digits)))
def formatted (s : NamedSheet) (i : Nat) (value : String) : String := Id.run do
  let fmt := (styleAt s i).numberFormat
  if fmt == "general" || s.cells[i]!.startsWith "'" then return value
  let parsed := match value.splitOn "/" with
    | [a,b] => do
      let x ← MathFunctions.literal a
      let y ← MathFunctions.literal b
      if y == 0 then none else some (x/y)
    | _ => MathFunctions.literal value
  let some q := parsed | return value
  return match fmt with
    | "date" =>
      if q.den != 1 || q < 2 || q > Rat.ofInt (dateSerial 9999 12 31) then "#NUM!" else
      let (y,m,d) := serialDate q.num.toNat
      let pad := fun n => (if n < 10 then "0" else "") ++ toString n
      toString y ++ "-" ++ pad m ++ "-" ++ pad d
    | "number" => fixed q
    | "currency" => "$" ++ fixed q
    | "percent" => fixed (q*100) ++ "%"
    | "fraction" => toString q
    | "scientific" => MathFunctions.floatText (MathFunctions.asFloat q)
    | _ => value

def formatCells (m : Model) (rect : Rect) (format : String) : Model := Id.run do
  let s := m.book[m.active]!
  let mut styles := s.styles
  for i in rect.indices do
    let previous := styleAt s i
    let next := if format == "bold" then {previous with bold:=!previous.bold}
      else if format.startsWith "font:" then {previous with fontFamily:=format.drop 5 |>.toString}
      else if format.startsWith "size:" then {previous with fontSize:=(format.drop 5 |>.toString.toNat?).getD 13}
      else {previous with numberFormat:=format}
    styles := (styles.filter (·.cell != i)).push next
  return updateBook m (m.book.set! m.active {s with styles:=styles}) m.active

def columnStyle (m : Model) (column : Nat) (width : Nat) (alignment : String) : Model :=
  let s := m.book[m.active]!
  let columns := (s.columns.filter (·.column != column)).push {column:=column,width:=width,alignment:=alignment}
  updateBook m (m.book.set! m.active {s with columns:=columns}) m.active

def usedRect (s : Sheet) : Rect := Id.run do
  let mut bottom := 0
  let mut right := 0
  for (i,_) in s.entries.toList do
    if s[i]! != "" then bottom := max bottom (i/26); right := max right (i%26)
  return {top:=0,left:=0,bottom:=bottom,right:=right}

def findCell (m : Model) (query : String) (afterCell : Nat) : Option Nat := Id.run do
  if query == "" then return none
  for offset in [1:m.sheet.size+1] do
    let i := (afterCell+offset)%m.sheet.size
    if (m.sheet[i]!.toLower.splitOn query.toLower).length > 1 ||
       ((cellDisplay m.book m.active i).toLower.splitOn query.toLower).length > 1 then return some i
  return none

def compareValue (a b : Except String Value) : Ordering :=
  match a,b with
  | .ok (.number x),.ok (.number y) => if x < y then .lt else if x > y then .gt else .eq
  | .ok (.number _),_ => .lt
  | _,.ok (.number _) => .gt
  | _,_ =>
    let text := fun v => match v with | .ok (.text s) => s.toLower | .error e => e | _ => ""
    compare (text a) (text b)

def sortRows (m : Model) (rect : Rect) (column : Nat) (descending : Bool) : Except String Model := do
  if rect.bottom <= rect.top then throw "Select at least two rows to sort."
  if column < rect.left || column > rect.right then throw "Sort column is outside the selection."
  let rows := (List.range (rect.bottom-rect.top+1)).map (·+rect.top)
  let keyed := rows.map fun r => (r, trim m.sheet[r*26+column]! == "", cellValue m.book m.active (r*26+column))
  let ordered := keyed.mergeSort fun a b =>
    if a.2.1 != b.2.1 then !a.2.1
    else let c := compareValue a.2.2 b.2.2
         if descending then c != .lt else c != .gt
  let originalStyles := m.book[m.active]!.styles
  let mut styles := originalStyles.filter (fun st => !rect.contains st.cell)
  let mut next := m.sheet
  for (target,source) in rows.zip ordered do
    for col in [rect.left:rect.right+1] do
      if let some st := originalStyles.find? (·.cell == source.1*26+col) then
        styles := styles.push {st with cell:=target*26+col}
      next := put next (target*26+col) (shiftFormula m.sheet[source.1*26+col]! (Int.ofNat target-Int.ofNat source.1) 0)
  let b := m.book.set! m.active {m.book[m.active]! with cells:=next,styles:=styles}
  validateBook b
  return updateBook m b m.active

def transferStyles (next : Model) (source : Book) (sourceSheet : Nat) (rect : Rect) (dest : Nat) (cut : Bool) (before : Option Model := none) : Model := Id.run do
  let target := next.active
  let targetRect := {top:=dest/26,left:=dest%26,bottom:=dest/26+rect.bottom-rect.top,right:=dest%26+rect.right-rect.left : Rect}
  let mut b := next.book
  if cut then
    b := b.set! sourceSheet {b[sourceSheet]! with styles:=b[sourceSheet]!.styles.filter (fun st => !rect.contains st.cell)}
  let mut styles := b[target]!.styles.filter (fun st => !targetRect.contains st.cell)
  for st in source[sourceSheet]!.styles do
    if rect.contains st.cell then
      let i := (dest/26+st.cell/26-rect.top)*26+dest%26+st.cell%26-rect.left
      styles := styles.push {st with cell:=i}
  b := b.set! target {b[target]! with styles:=styles}
  return match before with | some m => updateBook m b next.active | none => {next with book:=b}

def filterRows (m : Model) (column : Nat) (query : String) : List Nat :=
  (List.range (m.sheet.size/26)).filter fun row => query == "" ||
    (((cellDisplay m.book m.active (row*26+column)).toLower).splitOn query.toLower).length > 1

def htmlEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

def printHTML (m : Model) : String := Id.run do
  let rect := usedRect m.sheet
  let mut html := "<!doctype html><meta charset=\"utf-8\"><title>" ++ htmlEscape m.book[m.active]!.name ++ "</title><style>body{font:12px -apple-system,sans-serif;color:#222}table{border-collapse:collapse}td,th{border:1px solid #ccc;padding:4px 8px;white-space:pre-wrap}th{background:#eee}@page{size:landscape;margin:12mm}@media print{thead{display:table-header-group}tr{break-inside:avoid}}</style><h1>" ++ htmlEscape m.book[m.active]!.name ++ "</h1><table><thead><tr><th></th>"
  for col in [:rect.right+1] do html := html ++ "<th>" ++ String.singleton (Char.ofNat (65+col)) ++ "</th>"
  html := html ++ "</tr></thead><tbody>"
  for row in [:rect.bottom+1] do
    html := html ++ "<tr><th>" ++ toString (row+1) ++ "</th>"
    for col in [:rect.right+1] do
      let st := styleAt m.book[m.active]! (row*26+col)
      let family := if st.fontFamily == "serif" then "serif" else if st.fontFamily == "mono" then "monospace" else "sans-serif"
      html := html ++ "<td style=\"background:" ++ (let c := Features.colorAt m.book m.active (row*26+col); if c == "" then "white" else c) ++ ";font-family:" ++ family ++ ";font-size:" ++ toString st.fontSize ++ "px;font-weight:" ++ (if st.bold then "bold" else "normal") ++ "\">" ++ htmlEscape (formatted m.book[m.active]! (row*26+col) (cellDisplay m.book m.active (row*26+col))) ++ "</td>"
    html := html ++ "</tr>"
  return html ++ "</tbody></table>" ++ Features.objectsHTML m
end Presentation
