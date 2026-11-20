import Incremental
open Lean Phase2
namespace Features

def addObject (m : Model) (o : SheetObject) : Except String Model := do
  let s := m.book[m.active]!
  let b := m.book.set! m.active {s with objects:=s.objects.push o}
  validateBook b
  return updateBook m b m.active

def removeObject (m : Model) (index : Nat) : Except String Model := do
  let s := m.book[m.active]!
  if index >= s.objects.size then throw "Choose an object in this sheet."
  let b := m.book.set! m.active {s with objects:=s.objects.extract 0 index ++ s.objects.extract (index+1) s.objects.size}
  validateBook b
  return updateBook m b m.active

def colorAt (b : Book) (si i : Nat) : String := Id.run do
  let mut color := ""
  for o in b[si]!.objects do
    if o.kind == "condition" && (rectangle o.first o.last).contains i && b[si]!.cells[i]! != "" then
      if let .ok (.number n) := cellValue b si i then
        let criterion := o.options[0]! ++ o.options[1]!
        if matchesCriterion (.number n) (.text criterion) then color := o.options[2]!
  return color

-- Charts use the first selected column for labels and the second for values.
-- A single column uses row numbers as labels. Text and blank values are skipped.
def series (b : Book) (si : Nat) (o : SheetObject) : Except String (Array (String × Rat)) := do
  let r := rectangle o.first o.last
  if r.bottom-r.top+1 > 200 then throw "Charts support up to 200 selected rows."
  let vc := if r.left == r.right then r.left else r.left+1
  let mut out := #[]
  for row in [r.top:r.bottom+1] do
    let i := row*26+vc
    if b[si]!.cells[i]! != "" then
      match cellValue b si i with
      | .error e => throw ("Chart source " ++ address i ++ ": " ++ e)
      | .ok (.number n) =>
        let label := if r.left == r.right then toString (row+1) else cellDisplay b si (row*26+r.left)
        out := out.push (label,n)
      | _ => pure ()
  return out

def escape (s : String) := s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"
def svg (b : Book) (si : Nat) (o : SheetObject) : Except String String := do
  let values ← series b si o
  let lo := values.foldl (fun n p => min n p.2) 0
  let hi := values.foldl (fun n p => max n p.2) 0
  let span := if hi == lo then 1 else hi-lo
  let y := fun n => 30+((hi-n)*260/span).floor.toNat
  let baseline := y 0
  let step := 600 / max 1 values.size
  let mut s := "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 660 340\" role=\"img\" aria-label=\"" ++ escape o.title ++ "\"><rect width=\"660\" height=\"340\" fill=\"white\"/><text x=\"25\" y=\"20\">" ++ escape o.title ++ "</text><path d=\"M25 " ++ toString baseline ++ " H635\" stroke=\"#888\"/>"
  let mut points := ""
  for k in [:values.size] do
    let (label,n) := values[k]!
    let x := 25+k*step
    let yy := y n
    if o.options[0]! == "line" then
      points := points ++ toString (x+step/2) ++ "," ++ toString yy ++ " "
      s := s ++ "<circle cx=\""++toString (x+step/2)++"\" cy=\""++toString yy++"\" r=\"3\" fill=\"#16856b\"><title>"++escape label++": "++escape (MathFunctions.display n)++"</title></circle>"
    else s := s ++ "<rect x=\""++toString x++"\" y=\""++toString (min yy baseline)++"\" width=\""++toString (max 1 (step-2))++"\" height=\""++toString (max yy baseline-min yy baseline)++"\" fill=\"#16856b\"><title>"++escape label++": "++escape (MathFunctions.display n)++"</title></rect>"
    if values.size <= 12 then s := s ++ "<text x=\""++toString (x+step/2)++"\" y=\"315\" text-anchor=\"middle\" font-size=\"10\">"++escape (String.ofList (label.toList.take 12))++"</text>"
  if o.options[0]! == "line" then s := s ++ "<polyline points=\""++points++"\" fill=\"none\" stroke=\"#16856b\" stroke-width=\"2\"/>"
  return s ++ "</svg>"

def objectsHTML (m : Model) : String := Id.run do
  let mut out := ""
  for o in m.book[m.active]!.objects do
    if o.kind == "chart" then
      out := out ++ (match svg m.book m.active o with | .ok s => "<figure>"++s++"</figure>" | .error e => "<p>"++escape e++"</p>")
    if o.kind == "image" then out := out ++ "<figure><img style=\"max-width:100%;max-height:500px\" alt=\""++escape o.title++"\" src=\"data:image/png;base64,"++o.data++"\"><figcaption>"++escape o.title++"</figcaption></figure>"
  return out

-- A pivot is a materialized, refreshable summary on a separate sheet. It keeps
-- a source definition and uses exactly one undo transaction for each refresh.
def pivotCells (b : Book) (o : SheetObject) : Except String Sheet := do
  let some si := sheetIndex b o.options[0]! | throw "Pivot source sheet is missing."
  let r := rectangle o.first o.last
  let some group := o.options[1]!.toNat? | throw "Invalid grouping column."
  let some value := o.options[2]!.toNat? | throw "Invalid value column."
  if group < r.left || group > r.right || value < r.left || value > r.right || r.bottom >= b[si]!.cells.size/26 then throw "Pivot columns must lie inside the source range."
  let mut groups : Array (String × Rat × Nat) := #[]
  for row in [r.top+1:r.bottom+1] do
    let key := cellDisplay b si (row*26+group)
    let vi := row*26+value
    if key != "" then
      let v ← cellValue b si vi
      let existing := groups.findIdx? (fun p => p.1 == key)
      let prior := existing.map (fun j => groups[j]!) |>.getD (key,0,0)
      let mut total := prior.2.1
      let mut count := prior.2.2
      if o.options[3]! == "COUNT" then
        if b[si]!.cells[vi]! != "" then count := count+1
      else if let .number n := v then
        if b[si]!.cells[vi]! != "" then
          total := if o.options[3]! == "MIN" then (if count == 0 then n else min total n) else if o.options[3]! == "MAX" then (if count == 0 then n else max total n) else total+n
          count := count+1
      let entry := (key,total,count)
      groups := match existing with | some j => groups.set! j entry | none => groups.push entry
  if groups.size >= b[si]!.cells.size/26 then throw "Pivot result exceeds the sheet size."
  let mut cells := Sheet.blank b[si]!.cells.size
  cells := cells.set! 0 ("'"++cellDisplay b si (r.top*26+group))
  cells := cells.set! 1 ("'"++o.options[3]!++" "++cellDisplay b si (r.top*26+value))
  for i in [:groups.size] do
    let (key,total,count) := groups[i]!
    let result := if o.options[3]! == "COUNT" then Rat.ofInt count else if o.options[3]! == "AVERAGE" then (if count == 0 then 0 else total/Rat.ofInt count) else total
    cells := cells.set! ((i+1)*26) ("'"++key)
    cells := cells.set! ((i+1)*26+1) (if result.den == 1 then toString result.num else "="++toString result.num++"/"++toString result.den)
  return cells

def createPivot (m : Model) (name : String) (r : Rect) (group value : Nat) (aggregate : String) : Except String Model := do
  if !validName name || (sheetIndex m.book name).isSome || m.book.size >= 32 then throw "Choose a unique pivot sheet name."
  let o : SheetObject := {kind:="pivot",title:=name,first:=r.top*26+r.left,last:=r.bottom*26+r.right,options:=#[m.book[m.active]!.name,toString group,toString value,aggregate.toUpper]}
  if !["SUM","COUNT","AVERAGE","MIN","MAX"].contains aggregate.toUpper then throw "Choose SUM, COUNT, AVERAGE, MIN or MAX."
  let cells ← pivotCells m.book o
  let b := m.book.push {name:=name,cells:=cells,objects:=#[o]}
  validateBook b
  return updateBook m b m.book.size

def refreshPivot (m : Model) : Except String Model := do
  let s := m.book[m.active]!
  let some o := s.objects.find? (·.kind == "pivot") | throw "This sheet is not a pivot table."
  let cells ← pivotCells m.book o
  let b := m.book.set! m.active {s with cells:=cells}
  validateBook b
  return updateBook m b m.active

def importFunctions (m : Model) (text : String) : Except String Model := do
  let j ← Json.parse text
  let version ← j.getObjValAs? String "format"
  if version != "LeanCalc-functions-1" then throw "Unsupported function pack."
  let defs ← j.getObjValAs? (Array SheetObject) "functions"
  if defs.any (·.kind != "function") then throw "Function packs can only contain declarative functions."
  let s := m.book[m.active]!
  let b := m.book.set! m.active {s with objects:=s.objects ++ defs}
  validateBook b
  return updateBook m b m.active

def exportFunctions (m : Model) : String :=
  (Json.mkObj [("format",toJson "LeanCalc-functions-1"),("functions",toJson (m.book.foldl (fun out s => out ++ s.objects.filter (·.kind == "function")) (#[] : Array SheetObject)))]).pretty
end Features
