import Phase2Tests
import AdvancedTests
import Stage3Tests
import InterchangeTests
import FeatureTests
open Lean

abbrev Model := Phase2.Model
def singleModel (s : Sheet) : Model := {book:=Phase2.singleBook s}
def edit := Phase2.editCell
def undoEdit := Phase2.undoModel
def redoEdit := Phase2.redoModel

@[extern "calc_tk_init"] opaque tkInit (gui : Bool) : IO Unit
@[extern "calc_tk_call"] opaque tk (args : @& Array String) : IO String
@[extern "calc_tk_eval"] opaque tkEval (script : @& String) : IO String
@[extern "calc_tk_loop"] opaque tkLoop : IO Unit
@[extern "calc_atomic_write"] opaque atomicWrite (path : @& String) (data : @& ByteArray) : IO Unit
@[extern "calc_is_main_thread"] opaque isMainThread : IO Bool
@[extern "calc_startup_configured"] opaque startupConfigured : IO Bool

def cmd (args : Array String) : IO Unit := do discard <| tk args
def script (s : String) : IO Unit := do discard <| tkEval s

def readOptional (path : String) : IO (Option ByteArray) := do
  try return some (← IO.FS.readBinFile path)
  catch e => match e with | .noFileOrDirectory .. => return none | _ => throw e

def saveChecked (path : String) (expected : Option ByteArray) (sheet : Sheet) : IO ByteArray := do
  if (← readOptional path) != expected then throw <| IO.userError "File changed on disk. Use Save As to keep both versions."
  let bytes := (encode sheet).toUTF8
  atomicWrite path bytes
  return bytes

initialize model : IO.Ref Model ← IO.mkRef {}
initialize selected : IO.Ref Nat ← IO.mkRef 0
initialize saved : IO.Ref Phase2.Book ← IO.mkRef (Phase2.singleBook emptySheet)
initialize filePath : IO.Ref String ← IO.mkRef ""
initialize original : IO.Ref (Option ByteArray) ← IO.mkRef none

initialize selectionAnchor : IO.Ref (Option Nat) ← IO.mkRef none
initialize paintedSelection : IO.Ref (List Nat) ← IO.mkRef []
structure CellClipboard where
  book : Phase2.Book
  sourceSheet : Nat
  rect : Phase2.Rect
  table : Phase2.Table
  text : String
  cut : Bool
initialize cellClipboard : IO.Ref (Option CellClipboard) ← IO.mkRef none

def currentRect : IO Phase2.Rect := do
  let i ← selected.get
  return Phase2.rectangle ((← selectionAnchor.get).getD i) i

def paintSelection : IO Unit := do
  let r ← currentRect
  let cells := if r.top == r.bottom && r.left == r.right then [] else r.indices
  let previous ← paintedSelection.get
  if cells == previous then return
  for (action,items) in [("remove",previous),("add",cells)] do
    if !items.isEmpty then
      let mut pairs : Array String := #[]
      for i in items do
        pairs := pairs.push (← tk #["list",toString (i/26),String.singleton (Char.ofNat (65+i%26))])
      cmd #[".grid","tag","cell",action,"range",← tk (#["list"] ++ pairs)]
  paintedSelection.set cells

def unwrap {α : Type} (v : Except String α) : IO α :=
  match v with | .ok a => pure a | .error e => throw <| IO.userError e


-- Formula range picking edits a draft; it never changes the active cell or
-- workbook until the normal commit path runs.
structure FormulaPick where
  owner : Nat
  sheet : Nat
  widget : String
  beforeText : String
  afterText : String
  anchor : Nat
  endpoint : Nat
  deriving Inhabited
initialize formulaPick : IO.Ref (Option FormulaPick) ← IO.mkRef none
initialize paintedFormulaRange : IO.Ref (List Nat) ← IO.mkRef []

def FormulaPick.reference (p : FormulaPick) : String :=
  let r := Phase2.rectangle p.anchor p.endpoint
  let first := address (r.top*26+r.left)
  if p.anchor == p.endpoint then first else first ++ ":" ++ address (r.bottom*26+r.right)
def FormulaPick.draft (p : FormulaPick) := p.beforeText ++ p.reference ++ p.afterText

def insideFormulaQuotes (text : String) (position : Nat) : Bool := Id.run do
  let chars := text.toList.toArray
  let mut quote : Option Char := none
  let mut i := 0
  while i < min position chars.size do
    let c := chars[i]!
    if let some q := quote then
      if c == q then
        if chars[i+1]? == some q then i := i+1 else quote := none
    else if c == '"' || c == '\'' then quote := some c
    i := i+1
  return quote.isSome

-- Insert at an operand position, or replace explicitly selected text. Refuse
-- clicks inside quoted strings/sheet names so ordinary editing still works.
def formulaPickSlot (text : String) (caret : Nat) (selection : Option (Nat × Nat)) : Option (String × String) := do
  if !(trim text).startsWith "=" || caret > text.length then none else do
    let (first,last) := selection.getD (caret,caret)
    if first > last || last > text.length || first == 0 then none else do
      let beforeText := String.ofList (text.toList.take first)
      let afterText := String.ofList (text.toList.drop last)
      if !(trim beforeText).startsWith "=" || insideFormulaQuotes text first then none else do
        let preceding := (trim beforeText).toList.getLast?
        if first == last && !(preceding.any (fun c => "=(,+-*/^<>".contains c)) then none
        else some (beforeText,afterText)

def paintFormulaRange (cells : List Nat) : IO Unit := do
  let previous ← paintedFormulaRange.get
  if previous == cells then return
  for (action,items) in [("remove",previous),("add",cells)] do
    if !items.isEmpty then
      let mut pairs : Array String := #[]
      for i in items do
        pairs := pairs.push (← tk #["list",toString (i/26),String.singleton (Char.ofNat (65+i%26))])
      cmd #[".grid","tag","cell",action,"formulaRange",← tk (#["list"] ++ pairs)]
  paintedFormulaRange.set cells

def clearFormulaPick : IO Unit := do
  formulaPick.set none
  paintFormulaRange []
  cmd #["set","::calcPicking","0"]
  cmd #["set","::calcDragMode","none"]

def updateFormulaPick (p : FormulaPick) : IO Unit := do
  if !Phase2.validCell p.draft then throw <| IO.userError "The formula draft exceeds the cell limit."
  cmd #["set","::calcDraft",p.draft]
  cmd #[p.widget,"selection","clear"]
  cmd #[p.widget,"icursor",toString (p.beforeText.length+p.reference.length)]
  cmd #[p.widget,"xview","insert"]
  formulaPick.set (some p)
  paintFormulaRange (Phase2.rectangle p.anchor p.endpoint).indices
  cmd #[".status","configure","-text",p.reference ++ "  |  Continue typing; Enter applies; Escape cancels"]

def startFormulaPick (args : Array String) : IO Unit := do
  cmd #["set","::calcPicking","0"]
  let widget := args[3]?.getD ""
  if widget != ".grid.editor" && widget != ".formula" then return
  let text ← tk #["set","::calcDraft"]
  let caret := (args[4]?.getD "0").toNat?.getD 0
  let selection := do
    let first ← (args[5]?.getD "-1").toNat?
    let last ← (args[6]?.getD "-1").toNat?
    if last > first then some (first,last) else none
  let owner ← selected.get
  let sheet := (← model.get).active
  let prior ← formulaPick.get
  let slot := match prior with
    | some p =>
      if p.owner == owner && p.sheet == sheet && p.widget == widget && p.draft == text &&
          caret == p.beforeText.length+p.reference.length && selection.isNone then some (p.beforeText,p.afterText)
      else formulaPickSlot text caret selection
    | none => formulaPickSlot text caret selection
  let some (beforeText,afterText) := slot | return
  -- Mark the gesture handled before validation: a failed insertion must not
  -- fall through to ordinary selection and accidentally commit the draft.
  cmd #["set","::calcPicking","1"]
  let row := (args[1]?.getD "0").toNat?.getD 0
  let col := (args[2]?.getD "1").toNat?.getD 1
  let cell := min ((← model.get).sheet.size-1) (row*26+col-1)
  cmd #["set","::calcEditing","1"]
  cmd #[".grid.editor","configure","-state","normal","-textvariable","::calcDraft"]
  updateFormulaPick {owner:=owner,sheet:=sheet,widget:=widget,beforeText:=beforeText,afterText:=afterText,anchor:=cell,endpoint:=cell}

def extendFormulaPick (row col : Nat) : IO Unit := do
  let some p ← formulaPick.get | return
  if p.owner != (← selected.get) || p.sheet != (← model.get).active then clearFormulaPick; return
  let cell := min ((← model.get).sheet.size-1) (row*26+col-1)
  if cell != p.endpoint then updateFormulaPick {p with endpoint:=cell}

def finishFormulaPick : IO Unit := do
  cmd #["set","::calcPicking","0"]
  if let some p ← formulaPick.get then
    cmd #["focus",p.widget]


-- Keep the raw snapshot beside its displayed values. Comparing snapshots also
-- handles undo/redo, open, new, paste and clear without separate invalidation.
-- Publish only after all widget writes succeed, so a failed refresh is retried.
initialize renderedSheet : IO.Ref (Phase2.Snapshot × Sheet) ← IO.mkRef (({book:=#[]} : Phase2.Snapshot), Sheet.blank 0)

initialize calculationCache : IO.Ref Incremental.Cache ← IO.mkRef {}

def refreshValues : IO Sheet := do
  let m ← model.get
  let (previous, values) ← renderedSheet.get
  if previous == m.toSnapshot then return values
  let mut cache := Incremental.synchronize (← calculationCache.get) m.book
  let mut next := #[]
  for r in [0:m.sheet.size/26] do
    let mut row := #[]
    let mut changed := false
    for c in [0:26] do
      let i := r*26+c
      let (plain,updated) := Incremental.display cache m.active i
      let text := Presentation.formatted m.book[m.active]! i plain
      cache := updated
      row := row.push text
      next := next.push text
      if values[i]? != some text then changed := true
    if changed then
      let list ← tk (#["list"] ++ row)
      cmd #[".grid", "item", toString r, "-values", list]
  calculationCache.set cache
  renderedSheet.set (m.toSnapshot, next)
  return next

initialize paintedStyles : IO.Ref (Option (Array Phase2.CellStyle × Array Phase2.ColumnStyle)) ← IO.mkRef none

def refreshStyles : IO Unit := do
  let m ← model.get
  let s := m.book[m.active]!
  let next := (s.styles,s.columns)
  if (← paintedStyles.get) == some next then return
  let old := (← paintedStyles.get).getD (#[],#[])
  for st in old.1 do
    cmd #[".grid","tag","delete","style"++toString st.cell]
  for st in s.styles do
    let family := if st.fontFamily == "serif" then "Times" else if st.fontFamily == "mono" then "Menlo" else "Helvetica"
    let font ← tk #["list",family,toString st.fontSize,if st.bold then "bold" else "normal"]
    let tag := "style"++toString st.cell
    cmd #[".grid","tag","configure",tag,"-font",font]
    cmd #[".grid","tag","cell","add",tag,← tk #["list",← tk #["list",toString (st.cell/26),String.singleton (Char.ofNat (65+st.cell%26))]]]
  for c in [:26] do
    let style := (s.columns.find? (·.column == c)).getD {column:=c}
    cmd #[".grid","column",String.singleton (Char.ofNat (65+c)),"-width",toString style.width,"-anchor",style.alignment]
  paintedStyles.set (some next)

def objectUIScript : String := "# All data enters these procedures as Tcl arguments, never evaluated as script.\nproc calcObjectsStart {sheet} {\n    catch {destroy .objects}\n    foreach name [image names] {if {[string match calcObjectPhoto* $name]} {image delete $name}}\n    toplevel .objects\n    wm title .objects \"Sheet objects — $sheet\"\n    ttk::notebook .objects.tabs\n    pack .objects.tabs -fill both -expand 1 -padx 12 -pady 12\n    wm geometry .objects 700x440\n}\nproc calcObjectPage {index title} {\n    set frame .objects.tabs.p$index\n    ttk::frame $frame\n    .objects.tabs add $frame -text $title\n    return $frame\n}\nproc calcCheckPNG {bytes} {\n    if {[string length $bytes] < 24 || [string length $bytes] > 1400000 || [string range $bytes 0 7] ne \"\\x89PNG\\r\\n\\x1a\\n\"} {error \"Choose a PNG image smaller than 1.4 MB.\"}\n    binary scan [string range $bytes 16 23] II width height\n    if {$width < 1 || $height < 1 || $width > 4096 || $height > 4096 || $width*$height > 4000000} {error \"PNG dimensions must be at most 4096 per side and 4 million pixels.\"}\n}\nproc calcReadPNG {path} {\n    set file [open $path rb]\n    try {set bytes [read $file 1400001]} finally {close $file}\n    calcCheckPNG $bytes\n    # Decode once to reject malformed PNGs before storing them.\n    set picture [image create photo -data $bytes -format png]\n    image delete $picture\n    return [binary encode base64 -maxlen 0 $bytes]\n}\nproc calcObjectImage {frame data} {\n    set bytes [binary decode base64 -strict $data]\n    calcCheckPNG $bytes\n    set original [image create photo -data $bytes -format png]\n    set scale [expr {max(1,int(ceil([image width $original]/640.0)),int(ceil([image height $original]/340.0)))}]\n    set photo [image create photo calcObjectPhoto[string map {. _} $frame]]\n    $photo copy $original -subsample $scale $scale\n    image delete $original\n    ttk::label $frame.image -image $photo\n    pack $frame.image -expand 1 -padx 12 -pady 12\n}\n"

def promptArg (args : Array String) (index : Nat) (title : String) (initial : String := "") : IO String :=
  match args[index]? with | some s => pure s | none => tk #["calcPrompt",title,initial]

initialize paintedConditions : IO.Ref (List (Nat × String)) ← IO.mkRef []
def refreshConditions : IO Unit := do
  let m ← model.get
  let mut next := []
  if m.book[m.active]!.objects.any (·.kind == "condition") then
    for (i,_) in m.sheet.entries.toList do
      let color := Features.colorAt m.book m.active i
      if color != "" then next := (i,color)::next
  let old ← paintedConditions.get
  if old == next then return
  for (i,_) in old do cmd #[".grid","tag","delete","condition"++toString i]
  for (i,color) in next do
    let tag := "condition"++toString i
    cmd #[".grid","tag","configure",tag,"-background",color]
    cmd #[".grid","tag","cell","add",tag,← tk #["list",← tk #["list",toString (i/26),String.singleton (Char.ofNat (65+i%26))]]]
  paintedConditions.set next

def showObjects : IO Unit := do
  let m ← model.get
  let s := m.book[m.active]!
  cmd #["calcObjectsStart",s.name]
  for index in [:s.objects.size] do
    let o := s.objects[index]!
    let frame ← tk #["calcObjectPage",toString index,o.title]
    if o.kind == "chart" then
      let values ← IO.ofExcept (Features.series m.book m.active o)
      let lo := values.foldl (fun n p => min n p.2) 0
      let hi := values.foldl (fun n p => max n p.2) 0
      let span := if hi == lo then 1 else hi-lo
      let y := fun n => 30+((hi-n)*260/span).floor.toNat
      let base := y 0
      let step := 600 / max 1 values.size
      let canvas := frame++".chart"
      cmd #["canvas",canvas,"-width","660","-height","360","-background","white","-highlightthickness","0"]
      cmd #["pack",canvas,"-fill","both","-expand","1"]
      cmd #[canvas,"create","text","25","15","-anchor","w","-text",o.title]
      cmd #[canvas,"create","line","25",toString base,"635",toString base,"-fill","#888888"]
      let mut points := #[canvas,"create","line"]
      for k in [:values.size] do
        let (label,value) := values[k]!
        let x := 25+k*step
        let yy := y value
        if o.options[0]! == "line" then
          points := points ++ #[toString (x+step/2),toString yy]
          cmd #[canvas,"create","oval",toString (x+step/2-3),toString (yy-3),toString (x+step/2+3),toString (yy+3),"-fill","#16856b","-outline",""]
        else cmd #[canvas,"create","rectangle",toString x,toString (min yy base),toString (x+max 1 (step-2)),toString (max yy base),"-fill","#16856b","-outline",""]
        if values.size <= 12 then
          cmd #[canvas,"create","text",toString (x+step/2),"315","-text",String.ofList (label.toList.take 12),"-width",toString (max 30 step)]
          cmd #[canvas,"create","text",toString (x+step/2),toString (if value < 0 then yy+10 else yy-10),"-text",MathFunctions.display value]
      if o.options[0]! == "line" && values.size >= 2 then cmd (points ++ #["-fill","#16856b","-width","2"])
    else if o.kind == "image" then cmd #["calcObjectImage",frame,o.data]
    else
      let info := o.kind ++ ": " ++ o.title ++ "\nRange: " ++ address o.first ++ ":" ++ address o.last ++ "\n" ++ String.intercalate ", " o.options.toList ++ "\n" ++ o.data
      cmd #["ttk::label",frame++".info","-text",info,"-wraplength","620","-padding","20"]
      cmd #["pack",frame++".info","-anchor","nw"]
  if s.objects.isEmpty then
    cmd #["ttk::label",".objects.empty","-text","No objects in this sheet. Use the Insert and Data menus to add them.","-padding","20"]
    cmd #["pack",".objects.empty"]

initialize findText : IO.Ref String ← IO.mkRef ""
initialize filterText : IO.Ref String ← IO.mkRef ""
initialize filterPainted : IO.Ref Bool ← IO.mkRef false
initialize filterColumn : IO.Ref Nat ← IO.mkRef 0
initialize filteredSheet : IO.Ref Nat ← IO.mkRef 0

def refreshFilter : IO Unit := do
  let m ← model.get
  let text ← filterText.get
  if text == "" then
    if ← filterPainted.get then
      for r in [:m.sheet.size/26] do cmd #[".grid","move",toString r,"","end"]
      filterPainted.set false
    return
  filterPainted.set true
  if m.active != (← filteredSheet.get) then
    filterText.set ""
    for r in [:(← model.get).sheet.size/26] do cmd #[".grid","move",toString r,"","end"]
    return
  let rows := Presentation.filterRows m (← filterColumn.get) text
  for r in [:(← model.get).sheet.size/26] do
    if rows.contains r then cmd #[".grid","move",toString r,"","end"]
    else cmd #[".grid","detach",toString r]

initialize gridRows : IO.Ref Nat ← IO.mkRef 100

def refresh : IO Unit := do
  clearFormulaPick
  let focus ← tk #["focus"]
  if focus == ".grid.editor" then cmd #["focus", ".grid"]
  cmd #["set", "::calcEditing", "0"]
  cmd #[".grid.editor", "configure", "-state", "readonly", "-textvariable", "::calcDisplay"]
  cmd #[".grid.editor", "selection", "clear"]
  cmd #[".grid.editor", "xview", "moveto", "0"]
  let m ← model.get
  let s := m.sheet
  let rows := s.size/26
  let previousRows ← gridRows.get
  if rows > previousRows then
    for r in [previousRows:rows] do cmd #[".grid","insert","","end","-id",toString r,"-text",toString (r+1)]
  else if rows < previousRows then
    for r in [rows:previousRows] do cmd #[".grid","delete",toString r]
  gridRows.set rows
  selected.modify (min (s.size-1))
  let values ← refreshValues
  let names ← tk (#["list"] ++ m.book.map (·.name))
  cmd #["calcSyncSheets",names,toString m.active]
  paintSelection
  refreshStyles
  refreshConditions
  refreshFilter
  let i ← selected.get
  let st := Presentation.styleAt m.book[m.active]! i
  let family := if st.fontFamily == "serif" then "Times" else if st.fontFamily == "mono" then "Menlo" else "Helvetica"
  cmd #[".grid.editor","configure","-font",← tk #["list",family,toString st.fontSize,if st.bold then "bold" else "normal"]]
  let rect ← currentRect
  let label := if rect.top == rect.bottom && rect.left == rect.right then address i else address (rect.top*26+rect.left) ++ ":" ++ address (rect.bottom*26+rect.right)
  cmd #[".addr","configure","-text",label]
  cmd #["set", "::calcDraft", s[i]!]
  cmd #["set", "::calcDisplay", values[i]!]
  cmd #["set", "::calcRow", toString (i/26)]
  cmd #["set", "::calcColumn", String.singleton (Char.ofNat (65+i%26))]
  cmd #[".grid","selection","set", ""]
  cmd #[".grid","focus",toString (i/26)]
  cmd #["calcRevealCell"]
  let path ← filePath.get
  cmd #["wm","title",".",(if (← model.get).book != (← saved.get) then "* " else "") ++ "LeanCalc 0.5.1 - " ++ (if path == "" then "Untitled" else path)]
  cmd #[".status","configure","-text",address i ++ "  |  " ++ values[i]! ++ ""]

def beginCellEdit (replacement : Option String := none) : IO Unit := do
  clearFormulaPick
  selectionAnchor.set none
  paintSelection
  if let some text := replacement then cmd #["set", "::calcDraft", text]
  cmd #["set", "::calcEditing", "1"]
  cmd #[".grid.editor", "configure", "-state", "normal", "-textvariable", "::calcDraft"]
  cmd #["calcRevealCell"]
  cmd #["calcPlaceEditor"]
  cmd #[".grid.editor", "selection", "clear"]
  cmd #[".grid.editor", "icursor", "end"]
  cmd #[".grid.editor", "xview", "end"]
  cmd #["focus", ".grid.editor"]

def moveCell (i : Nat) (direction : String) (size : Nat := 2600) : Nat :=
  match direction with
  | "down" => if i+26 < size then i+26 else i
  | "up" => if i >= 26 then i-26 else i
  | "left" => if i%26 > 0 then i-1 else i
  | "right" => if i%26 < 25 then i+1 else i
  | "next" => min (size-1) (i+1)
  | "previous" => i-1
  | _ => i

def commit : IO Unit := do
  let v ← tk #["set", "::calcDraft"]
  if v.length > 4096 || v.contains '\u0000' then throw <| IO.userError "Cells allow at most 4096 characters and no NUL."
  let i ← selected.get
  let m ← model.get
  let next := edit m i v
  if next.book != m.book then discard <| unwrap (Phase2.validateBook next.book)
  model.set next

def saveFile (saveAs : Bool) : IO Bool := do
  commit
  let old ← filePath.get
  let path ← if saveAs || old == "" then tk #["tk_getSaveFile","-title","Save workbook (.lcalc) or active sheet (.csv)","-defaultextension",".lcalc","-filetypes","{{Workbook or CSV} {.lcalc .csv}} {{All files} {*}}"] else pure old
  if path == "" then return false
  -- A CSV is an export of one sheet, not a saved copy of the full workbook.
  -- Returning false keeps a save-before-close prompt from discarding formulas
  -- or other sheets after a CSV export.
  if path.toLower.endsWith ".csv" then
    atomicWrite path ((Phase2.exportCSV (← model.get) ',').toUTF8)
    refresh
    cmd #[".status","configure","-text","CSV saved: " ++ path ++ " | Active sheet values only; save .lcalc to keep the workbook."]
    return false
  let canonical ← IO.FS.realPath ((System.FilePath.mk path).parent.getD ".")
  let path := (canonical / (System.FilePath.mk path).fileName.getD "Untitled.lcalc").toString
  -- Resolve symlinks before atomic replacement.
  let path ← if ← (System.FilePath.mk path).pathExists then pure (← IO.FS.realPath path).toString else pure path
  let expected ← if path == old then original.get else readOptional path
  if (← readOptional path) != expected then throw <| IO.userError "File changed on disk. Use Save As to keep both versions."
  let m ← model.get
  let bytes := (Phase2.encodeBook m.book m.active).toUTF8
  atomicWrite path bytes
  filePath.set path
  original.set (some bytes)
  saved.set (← model.get).book
  refresh
  return true

def mayDiscard : IO Bool := do
  commit
  if (← model.get).book == (← saved.get) then return true
  let answer ← tk #["tk_messageBox","-type","yesnocancel","-icon","question","-message","Save changes to this workbook?"]
  if answer == "yes" then saveFile false else pure (answer == "no")

structure OpenedDocument where
  book : Phase2.Book
  active : Nat := 0
  path : String := ""
  bytes : Option ByteArray := none

def readDocument (path : String) : IO OpenedDocument := do
  let path := (← IO.FS.realPath path).toString
  if path.toLower.endsWith ".ods" then
    return {book:=← OpenDocument.read path}
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes | throw <| IO.userError "File must be UTF-8."
  if path.toLower.endsWith ".csv" then
    let base : Model := {book:=Phase2.singleBook (Sheet.blank 26000)}
    let imported ← unwrap (Phase2.importCSV base text ',')
    return {book:=imported.book}
  let (b,active) ← unwrap (Phase2.decodeBook text)
  return {book:=b,active:=active,path:=path,bytes:=some bytes}

def installDocument (d : OpenedDocument) : IO Unit := do
  filterText.set ""
  model.set {book:=d.book,active:=d.active}
  saved.set (if d.path == "" then #[] else d.book)
  selected.set 0
  selectionAnchor.set none
  cellClipboard.set none
  formulaPick.set none
  filePath.set d.path
  original.set d.bytes

def loadFile (path : String) : IO Unit := do
  installDocument (← readDocument path)

def openDocuments (paths : Array String) : IO Unit := do
  if paths.size != 1 then throw <| IO.userError "Please open one file at a time. No files were opened."
  let path := paths[0]!
  if ![".lcalc",".csv",".ods"].any (fun ext => path.toLower.endsWith ext) then
    throw <| IO.userError "Open a .lcalc, .csv or .ods file."
  -- Fully validate before changing the current workbook or offering to discard it.
  let document ← readDocument path
  if !(← mayDiscard) then return
  installDocument document
  refresh
  cmd #["wm","deiconify","."]
  cmd #["raise","."]
  cmd #["focus",".grid"]
  if document.path == "" then
    cmd #[".status","configure","-text","Imported as a new workbook. Save as .lcalc; the original file is unchanged."]

def dispatch (args : Array String) : IO Unit := do
  match args[0]?.getD "" with
  | "opendocuments" => openDocuments (args.extract 1 args.size)
  | "pickstart" => startFormulaPick args
  | "pickmove" => extendFormulaPick ((args[1]?.getD "0").toNat?.getD 0) ((args[2]?.getD "1").toNat?.getD 1)
  | "pickend" => finishFormulaPick
  | "select" | "extend" =>
    commit
    let r := (args[1]?.getD "0").toNat?.getD 0
    let c := (args[2]?.getD "1").toNat?.getD 1
    if args[0]! == "extend" then
      if (← selectionAnchor.get).isNone then selectionAnchor.set (some (← selected.get))
    else selectionAnchor.set none
    selected.set (min ((← model.get).sheet.size-1) (r*26 + c-1))
    refresh
    cmd #["focus",".grid"]
  | "begin" => beginCellEdit
  | "type" => beginCellEdit (some (args[1]?.getD ""))
  | "apply" => commit; refresh
  | "down" | "up" | "left" | "right" | "next" | "previous" =>
    commit
    selectionAnchor.set none
    let size := (← model.get).sheet.size
    selected.modify (fun i => moveCell i args[0]! size)
    refresh
    cmd #["focus", ".grid"]
  | "cancel" => refresh; cmd #["focus", ".grid"]
  | "save" => discard <| saveFile false
  | "saveas" => discard <| saveFile true
  | "objects" => commit; showObjects
  | "removeobject" =>
    commit
    let m ← model.get
    let labels := String.intercalate "\n" (m.book[m.active]!.objects.toList.zipIdx.map fun (o,i) => toString (i+1)++": "++o.kind++" "++o.title)
    let answer ← promptArg args 1 ("Remove object number\n"++labels)
    if answer != "" then
      let some n := answer.toNat? | throw <| IO.userError "Enter an object number."
      if n == 0 then throw <| IO.userError "Object numbers start at 1."
      model.set (← unwrap (Features.removeObject m (n-1)))
      refresh
  | "name" | "chart" | "validation" | "condition" =>
    commit
    let r ← currentRect
    let first := r.top*26+r.left
    let last := r.bottom*26+r.right
    let kind := args[0]!
    let title ← promptArg args 1 (if kind == "name" then "Name for selected range (letters and underscores)" else kind++" title") (if kind == "name" then "" else "Selected cells")
    if title == "" then return
    let mut options := #[]
    if kind == "chart" then
      let style ← promptArg args 2 "Chart type: bar or line" "bar"
      if style == "" then return
      options := #[style]
    if kind == "validation" then
      let rule ← promptArg args 2 "Rule: number,min,max | whole,min,max | list,choice,choice" "number,0,100"
      if rule == "" then return
      options := (rule.splitOn "," |>.map trim).toArray
    if kind == "condition" then
      let rule ← promptArg args 2 "Comparison,threshold,color (red/green/yellow/blue)" ">,0,green"
      if rule == "" then return
      options := (rule.splitOn "," |>.map trim).toArray
      if options.size == 3 then
        let color := match options[2]! with | "red" => "#fee2e2" | "green" => "#dcfce7" | "yellow" => "#fef3c7" | "blue" => "#dbeafe" | s => s
        options := options.set! 2 color
    let o : Phase2.SheetObject := {kind:=kind,title:=title,first:=first,last:=last,options:=options}
    if kind == "chart" then discard <| unwrap (Features.series (← model.get).book (← model.get).active o)
    model.set (← unwrap (Features.addObject (← model.get) o))
    refresh
    if kind == "chart" then showObjects
  | "image" =>
    commit
    let path ← match args[1]? with | some p => pure p | none => tk #["tk_getOpenFile","-title","Insert PNG image","-filetypes","{{PNG images} {.png}}"]
    if path != "" then
      let data ← tk #["calcReadPNG",path]
      let o : Phase2.SheetObject := {kind:="image",title:=System.FilePath.fileName path |>.getD "Image",first:=← selected.get,last:=← selected.get,data:=data}
      model.set (← unwrap (Features.addObject (← model.get) o))
      refresh
      showObjects
  | "pivot" =>
    commit
    let name ← promptArg args 1 "Name for new pivot sheet" "Pivot"
    if name == "" then return
    let spec ← promptArg args 2 "Group column, value column, aggregate (selection includes headers)" "A,B,SUM"
    if spec == "" then return
    let parts := (spec.toUpper.splitOn ",").map trim
    if parts.length != 3 then throw <| IO.userError "Example: A,B,SUM"
    let some group := Phase2.parseRef (parts[0]!++"1") | throw <| IO.userError "Invalid group column."
    let some value := Phase2.parseRef (parts[1]!++"1") | throw <| IO.userError "Invalid value column."
    model.set (← unwrap (Features.createPivot (← model.get) name (← currentRect) group.col value.col parts[2]!))
    selected.set 0; selectionAnchor.set none; refresh
  | "refreshpivot" =>
    commit
    model.set (← unwrap (Features.refreshPivot (← model.get)))
    refresh
  | "function" =>
    commit
    let declaration ← promptArg args 1 "Define a pure function, e.g. DOUBLE(X)=X*2"
    if declaration == "" then return
    let pieces := declaration.splitOn "="
    if pieces.length < 2 then throw <| IO.userError "Use NAME(PARAMETER)=expression."
    let head := pieces[0]!.toUpper
    let signature := head.splitOn "("
    if signature.length != 2 || !signature[1]!.endsWith ")" then throw <| IO.userError "Use NAME(PARAMETER)=expression."
    let params := String.ofList (signature[1]!.toList.take (signature[1]!.length-1))
    let o : Phase2.SheetObject := {kind:="function",title:=trim signature[0]!,options:=(params.splitOn "," |>.map trim).toArray,data:=String.intercalate "=" (pieces.drop 1)}
    model.set (← unwrap (Features.addObject (← model.get) o))
    refresh
  | "importfunctions" =>
    commit
    let path ← match args[1]? with | some p => pure p | none => tk #["tk_getOpenFile","-filetypes","{{Function packs} {.json}}"]
    if path != "" then
      if (← (System.FilePath.mk path).metadata).byteSize > 1000000 then throw <| IO.userError "Function packs must be under 1 MB."
      model.set (← unwrap (Features.importFunctions (← model.get) (← IO.FS.readFile path)))
      refresh
  | "exportfunctions" =>
    commit
    let path ← match args[1]? with | some p => pure p | none => tk #["tk_getSaveFile","-defaultextension",".json","-filetypes","{{Function packs} {.json}}"]
    if path != "" then atomicWrite path (Features.exportFunctions (← model.get)).toUTF8
  | "expand" =>
    commit
    let m ← model.get
    if m.sheet.size < 26000 then
      let cells := {m.sheet with size:=26000}
      model.set (Phase2.updateBook m (m.book.set! m.active {m.book[m.active]! with cells:=cells}) m.active)
      refresh
  | "format" =>
    commit
    let name := args[1]?.getD "general"
    model.set (Presentation.formatCells (← model.get) (← currentRect) name)
    refresh
  | "align" | "width" =>
    commit
    let m ← model.get
    let col := (← selected.get)%26
    let old := (m.book[m.active]!.columns.find? (·.column == col)).getD {column:=col}
    let width ← if args[0]! == "width" then
      let value ← tk #["calcPrompt","Column width (35-600 pixels)",toString old.width]
      if value == "" then return
      let some width := value.toNat? | throw <| IO.userError "Enter a width from 35 to 600."
      if width < 35 || width > 600 then throw <| IO.userError "Enter a width from 35 to 600."
      pure width
      else pure old.width
    let alignment := if args[0]! == "align" then args[1]?.getD "w" else old.alignment
    model.set (Presentation.columnStyle m col width alignment)
    refresh
  | "find" | "findnext" =>
    commit
    let query ← if args[0]! == "find" then
      match args[1]? with
      | some q => pure q
      | none => tk #["calcPrompt","Find in this sheet",← findText.get]
      else findText.get
    if query != "" then
      findText.set query
      match Presentation.findCell (← model.get) query (← selected.get) with
      | some i => filterText.set ""; selected.set i; selectionAnchor.set none; refresh
      | none => cmd #[".status","configure","-text","No match for: "++query]
  | "sortup" | "sortdown" =>
    commit
    let rect ← currentRect
    model.set (← unwrap (Presentation.sortRows (← model.get) rect ((← selected.get)%26) (args[0]! == "sortdown")))
    refresh
  | "filter" =>
    commit
    let text ← match args[1]? with
      | some q => pure q
      | none => tk #["calcPrompt","Show rows containing (active column)",""]
    filterText.set text
    filterColumn.set ((← selected.get)%26)
    filteredSheet.set (← model.get).active
    if text == "" then
      for r in [:(← model.get).sheet.size/26] do cmd #[".grid","move",toString r,"","end"]
    refresh
  | "clearfilter" =>
    filterText.set ""
    for r in [:(← model.get).sheet.size/26] do cmd #[".grid","move",toString r,"","end"]
    refresh
  | "print" =>
    commit
    let path ← tk #["tk_getSaveFile","-title","Export printable sheet","-defaultextension",".html","-filetypes","{{Printable HTML} {.html}}"]
    if path != "" then
      atomicWrite path (Presentation.printHTML (← model.get)).toUTF8
      cmd #[".status","configure","-text","Printable sheet saved. Open the HTML in a browser and choose Print or Save as PDF."]
  | "new" =>
    if ← mayDiscard then
      filterText.set ""
      model.set {}; saved.set (Phase2.singleBook emptySheet); selected.set 0; selectionAnchor.set none; cellClipboard.set none; filePath.set ""; original.set none; refresh
  | "open" =>
    let path ← tk #["tk_getOpenFile","-filetypes","{{Spreadsheets} {.lcalc .csv .ods}} {{LeanCalc workbook} {.lcalc}} {{CSV spreadsheet} {.csv}} {{OpenDocument spreadsheet} {.ods}}"]
    if path != "" then openDocuments #[path]
  | "quit" => if ← mayDiscard then cmd #["destroy","."]
  | "undo" => commit; model.modify undoEdit; selectionAnchor.set none; refresh
  | "redo" => commit; model.modify redoEdit; selectionAnchor.set none; refresh
  | "extendmove" =>
    commit
    if (← selectionAnchor.get).isNone then selectionAnchor.set (some (← selected.get))
    let size := (← model.get).sheet.size
    selected.modify (fun i => moveCell i (args[1]?.getD "right") size)
    refresh
    cmd #["focus",".grid"]
  | "sheet" =>
    commit
    let index := (args[1]?.getD "0").toNat?.getD 0
    if index >= (← model.get).book.size then throw <| IO.userError "Unknown sheet."
    model.modify (fun m => {m with active:=index})
    selected.set 0; selectionAnchor.set none; refresh
    cmd #["focus",".grid"]
  | "addsheet" | "renamesheet" =>
    commit
    let m ← model.get
    let initial := if args[0]! == "renamesheet" then m.book[m.active]!.name else "Sheet" ++ toString (m.book.size+1)
    let name ← if let some n := args[1]? then pure n else tk #["calcSheetName",initial]
    if name != "" then
      model.set (← unwrap (if args[0]! == "addsheet" then Phase2.addSheet m name else Phase2.renameSheet m name))
      selected.set 0; selectionAnchor.set none; refresh
      cmd #["focus",".grid"]
  | "deletesheet" =>
    commit
    let answer ← tk #["tk_messageBox","-type","yesno","-icon","question","-message","Delete the active sheet? This can be undone."]
    if answer == "yes" then
      model.set (← unwrap (Phase2.deleteSheet (← model.get)))
      selected.set 0; selectionAnchor.set none; refresh
  | "insertrow" | "deleterow" | "insertcolumn" | "deletecolumn" =>
    commit
    let rect ← currentRect
    let rows := args[0]!.endsWith "row"
    model.set (← unwrap (Phase2.structureEdit (← model.get) rows (args[0]!.startsWith "insert") (if rows then rect.top else rect.left)))
    selectionAnchor.set none; refresh
  | "filldown" | "fillright" =>
    commit
    model.set (← unwrap (Phase2.fillRect (← model.get) (← currentRect) (args[0]! == "filldown")))
    refresh
  | "clear" =>
    let rect ← currentRect
    let next := Phase2.clearRect (← model.get) rect
    discard <| unwrap (Phase2.validateBook next.book)
    model.set next
    refresh
  | "copy" | "cut" =>
    commit
    let m ← model.get
    let rect ← currentRect
    let table := Phase2.extract m.sheet rect
    let text := Phase2.encodeDelimited table '\t'
    cmd #["clipboard","clear"]
    cmd #["clipboard","append","--",text]
    cellClipboard.set (some {book:=m.book,sourceSheet:=m.active,rect:=rect,table:=table,text:=text,cut:=args[0]! == "cut"})
    refresh
    if args[0]! == "cut" then cmd #[".status","configure","-text","Cut ready: select a destination and Paste. The move is one undo step."]
  | "paste" =>
    commit
    let text ← tk #["clipboard","get"]
    let rect ← currentRect
    let dest := rect.top*26+rect.left
    let m ← model.get
    let clip ← cellClipboard.get
    let next ← if let some clip := clip.filter (fun c => c.text == text) then
      if clip.cut then
        if clip.book != m.book then throw <| IO.userError "Workbook changed after Cut. Cut the cells again."
        unwrap (Phase2.moveRect m clip.sourceSheet clip.rect dest)
      else unwrap (Phase2.pasteTable m dest clip.table (some (clip.rect.top,clip.rect.left)))
    else unwrap (Phase2.pasteTable m dest (← unwrap (Phase2.parseDelimited text '\t' (m.sheet.size/26))))
    let next := match clip.filter (fun c => c.text == text) with
      | some c => Presentation.transferStyles next c.book c.sourceSheet c.rect dest c.cut (some m)
      | none => next
    model.set next
    if clip.any (fun c => c.cut && c.text == text) then cellClipboard.set none
    selected.set dest; selectionAnchor.set none; refresh
  | "importods" =>
    if ← mayDiscard then
      let path ← tk #["tk_getOpenFile","-filetypes","{{OpenDocument spreadsheet} {.ods}}"]
      if path != "" then
        let book ← OpenDocument.read path
        filterText.set ""
        model.set {book:=book}
        filePath.set ""; original.set none; saved.set #[]; selected.set 0; selectionAnchor.set none
        refresh
        cmd #[".status","configure","-text","ODS imported as a new workbook; the original is unchanged. Save as .lcalc to retain native precision."]
  | "exportods" =>
    commit
    let path ← tk #["tk_getSaveFile","-defaultextension",".ods","-filetypes","{{OpenDocument spreadsheet} {.ods}}"]
    if path != "" then
      atomicWrite path (← OpenDocument.bytes (← model.get).book)
      cmd #[".status","configure","-text","ODS exported: values, formulas and supported styles; numeric values use 15 significant digits."]
  | "importcsv" | "importsemicolon" =>
    commit
    let path ← tk #["tk_getOpenFile","-filetypes","{{CSV text} {.csv .txt}} {{All files} {*}}"]
    if path != "" then
      let bytes ← IO.FS.readBinFile path
      let some text := String.fromUTF8? bytes | throw <| IO.userError "CSV must be UTF-8."
      let next ← unwrap (Phase2.importCSV (← model.get) text (if args[0]! == "importcsv" then ',' else ';'))
      let answer ← tk #["tk_messageBox","-type","yesno","-icon","question","-message","Replace the active sheet with this CSV? This can be undone."]
      if answer == "yes" then model.set next; selected.set 0; selectionAnchor.set none; refresh
  | "exportcsv" | "exportsemicolon" =>
    commit
    let path ← tk #["tk_getSaveFile","-defaultextension",".csv","-filetypes","{{CSV text} {.csv}}"]
    if path != "" then
      atomicWrite path ((Phase2.exportCSV (← model.get) (if args[0]! == "exportcsv" then ',' else ';')).toUTF8)
    refresh
  | "help" => cmd #["tk_messageBox","-title","LeanCalc help","-message","Click and type; F2 edits. Enter/Tab commit; Escape cancels.\nShift-click, Shift-arrows or drag select a rectangle. Cmd+C/X/V copy, cut and paste cells; Cmd+D/R fill down/right.\nChoose sheets below the grid. Sheet menu adds, renames, deletes sheets and inserts/deletes rows or columns.\nReferences: A1, $A$1, A$1, $A1, Sheet2!A1, 'Annual total'!B2.\nFunctions: SUM, AVERAGE, MIN/MAX, COUNT, IF/IFERROR; SIN/COS/TAN, ABS, SQRT, POWER, LOG, ROUND, MEDIAN, STDEV and more.\nInsert menu: names, charts, images, pivots, pure custom functions. Data menu: validation, conditional formats, function packs, find, sort and filter. Format menu: numbers, fonts and columns. Sheet menu: expand to 1,000 rows.\nFile menu: ODS interchange and printable HTML. Save .lcalc for native precision. Comparisons: = <> < <= > >=.\nFile menu imports/exports UTF-8 CSV with comma or semicolon. CSV import replaces only the active sheet and treats formulas as text.\nNative files save all sheets. Cmd+Z / Shift+Cmd+Z undo/redo across sheets.\nThe bundled LeanCalc.pdf contains reference-adjustment and CSV rules."]
  | _ => pure ()

@[export calc_event] def onEvent (args : Array String) : IO Unit := do
  try dispatch args
  catch e => cmd #["tk_messageBox","-icon","error","-title","LeanCalc","-message",toString e]

-- Draw separators inside the widget's layouts so they follow scrolling,
-- column resizing and selection without overlay widgets intercepting clicks.
-- Tk tiles image elements; it does not scale them. A 1x1 image performs one
-- native image draw per pixel of every line, even on a navigation-only repaint.
-- Long strips preserve one-pixel thickness with only a few image draws per line.
def setupGridStyle : IO Unit := do
  script "image create photo calcGridHorizontal -width 4096 -height 1; calcGridHorizontal put #d9d9d9 -to 0 0 4096 1"
  script "image create photo calcGridVertical -width 1 -height 4096; calcGridVertical put #d9d9d9 -to 0 0 1 4096"
  script "ttk::style element create LeanCalc.gridHorizontal image calcGridHorizontal -sticky ew -width 1 -height 1"
  script "ttk::style element create LeanCalc.gridVertical image calcGridVertical -sticky ns -width 1 -height 1"
  script "ttk::style layout LeanCalc.Treeview.Row {Treeitem.row -sticky nswe -children {LeanCalc.gridHorizontal -side bottom -sticky ew}}"
  script "ttk::style layout LeanCalc.Treeview.Separator {LeanCalc.gridVertical -sticky nswe}"
  script "ttk::style configure LeanCalc.Treeview -background white -fieldbackground white -foreground #202020 -columnseparatorwidth 1 -rowheight [expr {[font metrics TkDefaultFont -linespace] + 6}]"
  script "ttk::style map LeanCalc.Treeview -background {selected #e2f0d9} -foreground {selected #202020}"

def cellUIScript : String :=
  "set ::calcDraft {}\n" ++
  "set ::calcDisplay {}\n" ++
  "set ::calcEditing 0\n" ++
  "set ::calcRow 0\n" ++
  "set ::calcColumn A\n" ++
  "set ::calcPlacePending {}\n" ++
  "set ::calcPicking 0\n" ++
  "set ::calcDragMode none\n" ++
  "proc calcQueuePlace {} {\n" ++
  "    if {$::calcPlacePending eq {}} {\n" ++
  "        set ::calcPlacePending [after idle calcPlaceEditor]\n" ++
  "    }\n" ++
  "}\n" ++
  "proc calcPlaceEditor {} {\n" ++
  "    set ::calcPlacePending {}\n" ++
  "    if {![winfo exists .grid.editor]} {return}\n" ++
  "    set box [.grid bbox $::calcRow $::calcColumn]\n" ++
  "    if {$box eq {}} {place forget .grid.editor; return}\n" ++
  "    lassign $box x y width height\n" ++
  "    if {$x < 1 || $x+$width > [winfo width .grid]-1 || $y+$height > [winfo height .grid]-1} {\n" ++
  "        place forget .grid.editor\n" ++
  "        return\n" ++
  "    }\n" ++
  "    place .grid.editor -x $x -y $y -width $width -height $height\n" ++
  "    raise .grid.editor\n" ++
  "}\n" ++
  "proc calcScrolled {axis first last} {\n" ++
  "    .${axis}s set $first $last\n" ++
  "    calcQueuePlace\n" ++
  "}\n" ++
  "proc calcRevealCell {} {\n" ++
  "    .grid see $::calcRow\n" ++
  "    set box [.grid bbox $::calcRow $::calcColumn]\n" ++
  "    if {$box ne {} && [winfo width .grid] > 1} {\n" ++
  "        lassign $box x y width height\n" ++
  "        set available [expr {[winfo width .grid]-2}]\n" ++
  "        set shift 0\n" ++
  "        if {$x < 1} {set shift [expr {$x-1}]}\n" ++
  "        if {$x+$width > $available} {set shift [expr {$x+$width-$available}]}\n" ++
  "        if {$shift != 0} {\n" ++
  "            set total [.grid column #0 -width]\n" ++
  "            foreach c [.grid cget -columns] {incr total [.grid column $c -width]}\n" ++
  "            .grid xview moveto [expr {[lindex [.grid xview] 0]+double($shift)/$total}]\n" ++
  "        }\n" ++
  "    }\n" ++
  "    calcQueuePlace\n" ++
  "}\n" ++
  "proc calcCellAt {x y} {\n    if {[.grid identify region $x $y] ne {cell}} {return {}}\n    set row [.grid identify row $x $y]\n    set column [.grid identify column $x $y]\n    if {$row eq {} || $column eq {} || $column eq {#0}} {return {}}\n    return [list $row [string range $column 1 end]]\n}\nproc calcTryPick {row column} {\n    set widget [focus]\n    if {$widget ne {.formula} && ($widget ne {.grid.editor} || !$::calcEditing)} {return 0}\n    set first -1\n    set last -1\n    if {[$widget selection present]} {\n        set first [$widget index sel.first]\n        set last [$widget index sel.last]\n    }\n    calc pickstart $row $column $widget [$widget index insert] $first $last\n    return $::calcPicking\n}\nproc calcClick {x y {extend 0}} {\n    set ::calcDragMode none\n    set cell [calcCellAt $x $y]\n    if {$cell eq {}} {return 0}\n    lassign $cell row column\n    if {[calcTryPick $row $column]} {\n        set ::calcDragMode pick\n        return 1\n    }\n    if {$extend} {calc extend $row $column} else {calc select $row $column}\n    set ::calcDragMode select\n    return 1\n}\nproc calcDrag {x y} {\n    if {$::calcDragMode eq {none}} {return 0}\n    set cell [calcCellAt $x $y]\n    if {$cell ne {}} {\n        lassign $cell row column\n        if {$::calcDragMode eq {pick}} {\n            calc pickmove $row $column\n        } else {\n            calc extend $row $column\n            set ::calcDragMode select\n        }\n    }\n    return 1\n}\nproc calcRelease {x y} {\n    set mode $::calcDragMode\n    if {$mode eq {pick}} {\n        calcDrag $x $y\n        calc pickend\n    }\n    set ::calcDragMode none\n    return [expr {$mode ne {none}}]\n}\n" ++
  "proc calcTyped {character state} {\n" ++
  "    if {$character ne {} && ($state & 12) == 0 && [string is print -strict $character]} {\n" ++
  "        calc type $character\n" ++
  "    }\n" ++
  "}\n"

def sheetTabsScript : String :=
  "set ::calcSheetNames {}\nset ::calcSheetActive -1\nproc calcRevealSheet {} {\n    set tab .sheetbar.tabs.items.t$::calcSheetActive\n    if {![winfo exists $tab]} {return}\n    update idletasks\n    set total [winfo reqwidth .sheetbar.tabs.items]\n    set width [winfo width .sheetbar.tabs]\n    .sheetbar.tabs configure -scrollregion [list 0 0 $total 38]\n    if {$total <= $width} {.sheetbar.tabs xview moveto 0; return}\n    set left [winfo x $tab]\n    set right [expr {$left+[winfo width $tab]}]\n    set offset [expr {[lindex [.sheetbar.tabs xview] 0]*$total}]\n    if {$left < $offset} {\n        .sheetbar.tabs xview moveto [expr {double($left)/$total}]\n    } elseif {$right > $offset+$width} {\n        .sheetbar.tabs xview moveto [expr {double($right-$width)/$total}]\n    }\n}\nproc calcSyncSheets {names active} {\n    if {$names eq $::calcSheetNames && $active == $::calcSheetActive} {return}\n    if {$names ne $::calcSheetNames} {\n        foreach child [winfo children .sheetbar.tabs.items] {destroy $child}\n        set i 0\n        foreach name $names {\n            set tab .sheetbar.tabs.items.t$i\n            frame $tab -background #f3f5f4 -borderwidth 0\n            button $tab.label -text $name -command [list calc sheet $i] -relief flat -borderwidth 0 -highlightthickness 0 -padx 16 -pady 7 -background #f3f5f4 -foreground #4b5550 -activebackground #e5eee8 -activeforeground #176b42 -font TkDefaultFont -takefocus 1\n            frame $tab.line -height 3 -background #f3f5f4\n            pack $tab.label -side top -fill both -expand 1\n            pack $tab.line -side bottom -fill x\n            pack $tab -side left -fill y\n            bind $tab.label <Double-Button-1> [list calcRenameTab $i]\n            incr i\n        }\n        set ::calcSheetNames $names\n    }\n    for {set i 0} {$i < [llength $names]} {incr i} {\n        set tab .sheetbar.tabs.items.t$i\n        set bg [expr {$i == $active ? {white} : {#f3f5f4}}]\n        set fg [expr {$i == $active ? {#176b42} : {#4b5550}}]\n        set line [expr {$i == $active ? {#217346} : {#f3f5f4}}]\n        $tab configure -background $bg\n        $tab.label configure -background $bg -foreground $fg\n        $tab.line configure -background $line\n    }\n    set ::calcSheetActive $active\n    calcRevealSheet\n}\nproc calcRenameTab {index} {\n    calc sheet $index\n    calc renamesheet\n}\n"

def setupUI : IO Unit := do
  setupGridStyle
  script cellUIScript
  script sheetTabsScript
  script "proc calcSheetName {initial {title {Sheet name}}} {\n    if {[winfo exists .sheetName]} {destroy .sheetName}\n    set ::sheetNameDraft $initial\n    set ::sheetNameResult {}\n    toplevel .sheetName\n    wm title .sheetName $title\n    wm transient .sheetName .\n    ttk::label .sheetName.label -text $title\n    ttk::entry .sheetName.name -textvariable ::sheetNameDraft -width 32\n    ttk::button .sheetName.ok -text OK -command {set ::sheetNameResult $::sheetNameDraft; destroy .sheetName}\n    ttk::button .sheetName.cancel -text Cancel -command {destroy .sheetName}\n    grid .sheetName.label -row 0 -column 0 -columnspan 2 -padx 12 -pady 8\n    grid .sheetName.name -row 1 -column 0 -columnspan 2 -padx 12 -pady 8\n    grid .sheetName.ok .sheetName.cancel -padx 12 -pady 8\n    bind .sheetName.name <Return> {.sheetName.ok invoke; break}\n    bind .sheetName <Escape> {destroy .sheetName; break}\n    wm protocol .sheetName WM_DELETE_WINDOW {destroy .sheetName}\n    tkwait visibility .sheetName\n    grab .sheetName\n    focus .sheetName.name\n    .sheetName.name selection range 0 end\n    tkwait window .sheetName\n    return $::sheetNameResult\n}\n"
  script "wm geometry . 1080x680; wm minsize . 640 360; wm protocol . WM_DELETE_WINDOW {calc quit}; menu .menu; . configure -menu .menu"
  for (name, title, entries) in [
    ("file", "File", [("New", "new"), ("Open...", "open"), ("Save", "save"), ("Save As...", "saveas"), ("Export printable sheet...", "print"), ("Import ODS...", "importods"),("Export ODS...", "exportods"),("Import CSV (comma)...", "importcsv"), ("Import CSV (semicolon)...", "importsemicolon"), ("Export CSV (comma)...", "exportcsv"), ("Export CSV (semicolon)...", "exportsemicolon"), ("Quit", "quit")]),
    ("edit", "Edit", [("Undo", "undo"), ("Redo", "redo"), ("Cut cells", "cut"), ("Copy cells", "copy"), ("Paste cells", "paste"), ("Clear cells", "clear"), ("Fill Down", "filldown"), ("Fill Right", "fillright")]),
    ("format", "Format", [("General", "format general"),("Number (2 decimals)", "format number"),("Currency ($)", "format currency"),("Date (YYYY-MM-DD)", "format date"),("Percent", "format percent"),("Fraction", "format fraction"),("Bold", "format bold"),("Font: sans serif", "format font:default"),("Font: serif", "format font:serif"),("Font: monospace", "format font:mono"),("Font size: 10", "format size:10"),("Font size: 13", "format size:13"),("Font size: 16", "format size:16"),("Column: align left", "align w"),("Column: align center", "align center"),("Column: align right", "align e"),("Column width...", "width")]),
    ("insert", "Insert", [("Named range...", "name"),("Chart...", "chart"),("PNG image...", "image"),("Pivot table...", "pivot"),("Custom function...", "function"),("Sheet objects...", "objects"),("Remove object...", "removeobject")]),
    ("data", "Data", [("Validation...", "validation"),("Conditional format...", "condition"),("Refresh pivot table", "refreshpivot"),("Import function pack...", "importfunctions"),("Export function pack...", "exportfunctions"),("Find...", "find"),("Find next", "findnext"),("Sort by active column: ascending", "sortup"),("Sort by active column: descending", "sortdown"),("Filter active column...", "filter"),("Clear filter", "clearfilter")]),
    ("sheet", "Sheet", [("Expand to 1,000 rows", "expand"),("Add sheet...", "addsheet"), ("Rename sheet...", "renamesheet"), ("Delete sheet", "deletesheet"), ("Insert row", "insertrow"), ("Delete row", "deleterow"), ("Insert column", "insertcolumn"), ("Delete column", "deletecolumn")]),
    ("help", "Help", [("User guide and shortcuts", "help")])] do
    cmd #["menu",".menu."++name,"-tearoff","0"]
    cmd #[".menu","add","cascade","-label",title,"-menu",".menu."++name]
    for (label, action) in entries do
      cmd #[".menu."++name,"add","command","-label",label,"-command","calc "++action]
  script objectUIScript
  script "proc calcPrompt {title initial} {set answer [calcSheetName $initial $title]; return $answer}"
  let cols := (List.range 26).map (fun c => String.singleton (Char.ofNat (65+c)))
  cmd #["ttk::label",".addr","-width","10","-anchor","center"]
  cmd #["ttk::label",".fx","-text","fx","-foreground","#6b756f","-padding","6"]
  cmd #["ttk::entry",".formula", "-textvariable", "::calcDraft"]
  cmd #["ttk::button",".apply","-text","Apply","-command","calc apply"]
  cmd #["ttk::treeview",".grid","-style","LeanCalc.Treeview","-columns",String.intercalate " " cols,"-show","tree headings","-selectmode","none","-xscrollcommand","calcScrolled x","-yscrollcommand","calcScrolled y"]
  script "font create LeanCalcBold -family [font actual TkDefaultFont -family] -size [font actual TkDefaultFont -size] -weight bold"
  cmd #[".grid","tag","configure","bold","-font","LeanCalcBold"]
  cmd #[".grid","tag","configure","range","-background","#e2f0d9"]
  cmd #[".grid","tag","configure","formulaRange","-background","#dcecff"]
  cmd #["entry", ".grid.editor", "-textvariable", "::calcDisplay", "-state", "readonly",
    "-font", "TkDefaultFont", "-borderwidth", "0", "-highlightthickness", "2",
    "-highlightbackground", "#217346", "-highlightcolor", "#217346", "-background", "white",
    "-readonlybackground", "white", "-foreground", "#202020", "-insertbackground", "#202020",
    "-insertwidth", "2", "-insertontime", "600", "-insertofftime", "300", "-exportselection", "0"]
  cmd #[".grid","heading","#0","-text",""]
  cmd #[".grid","column","#0","-width","55","-stretch","0","-separator","1"]
  for c in cols do
    cmd #[".grid","heading",c,"-text",c]
    cmd #[".grid","column",c,"-width","105","-stretch","0","-separator","1"]
  for r in [0:100] do cmd #[".grid","insert","","end","-id",toString r,"-text",toString (r+1)]
  script "ttk::scrollbar .ys -orient vertical -command {.grid yview}\nttk::scrollbar .xs -orient horizontal -command {.grid xview}\nttk::label .status -padding {8 3} -foreground #68736c\ngrid .addr -row 0 -column 0 -sticky ew -padx 6 -pady 8\ngrid .fx -row 0 -column 1 -sticky ew\ngrid .formula -row 0 -column 2 -sticky ew -pady 8\ngrid .apply -row 0 -column 3 -sticky ew -padx 6 -pady 8\ngrid .grid -row 1 -column 0 -columnspan 4 -sticky nsew\ngrid .ys -row 1 -column 4 -sticky ns\ngrid .xs -row 2 -column 0 -columnspan 4 -sticky ew\nframe .sheetbar -background #f3f5f4 -height 38\nbutton .sheetbar.prev -text {\u2039} -command {.sheetbar.tabs xview scroll -5 units} -relief flat -borderwidth 0 -highlightthickness 0 -background #f3f5f4 -foreground #68736c -width 2\nbutton .sheetbar.next -text {\u203a} -command {.sheetbar.tabs xview scroll 5 units} -relief flat -borderwidth 0 -highlightthickness 0 -background #f3f5f4 -foreground #68736c -width 2\nbutton .sheetbar.add -text {+} -command {calc addsheet} -relief flat -borderwidth 0 -highlightthickness 0 -background #f3f5f4 -foreground #176b42 -width 3 -font TkDefaultFont\ncanvas .sheetbar.tabs -height 38 -width 1 -borderwidth 0 -highlightthickness 0 -background #f3f5f4 -xscrollincrement 20\nframe .sheetbar.tabs.items -background #f3f5f4\n.sheetbar.tabs create window 0 0 -anchor nw -window .sheetbar.tabs.items -tags tabs\npack .sheetbar.prev .sheetbar.next .sheetbar.add -side left -fill y\npack .sheetbar.tabs -side left -fill both -expand 1\nbind .sheetbar.tabs <Configure> {after idle calcRevealSheet}\nbind .sheetbar.tabs <MouseWheel> {.sheetbar.tabs xview scroll [expr {%D > 0 ? -3 : 3}] units}\ngrid .sheetbar -row 3 -column 0 -columnspan 5 -sticky ew\ngrid .status -row 4 -column 0 -columnspan 5 -sticky ew\ngrid columnconfigure . 2 -weight 1\ngrid rowconfigure . 1 -weight 1"
  script "bind .grid <Button-1> {if {[calcClick %x %y]} {break}}; bind .grid <Double-Button-1> {if {[calcClick %x %y]} {if {!$::calcPicking} {calc begin}; break}}; bind .grid <KeyPress> {calcTyped %A %s; break}"
  script "bind .grid <Shift-Button-1> {calcClick %x %y 1; break}; bind .grid <B1-Motion> {if {[calcDrag %x %y]} {break}}; bind .grid <ButtonRelease-1> {if {[calcRelease %x %y]} {break}}"
  script "bind .grid.editor <Button-1> {if {!$::calcEditing} {calc begin}}; bind .grid.editor <Double-Button-1> {if {!$::calcEditing} {calc begin; break}}"
  script "bind .grid <Configure> {calcQueuePlace}; bind .grid <B1-Motion> {+calcQueuePlace}; bind .grid.editor <MouseWheel> {event generate .grid <MouseWheel> -delta %D -state %s; break}"
  for widget in [".grid", ".grid.editor", ".formula"] do
    for (key, action) in [("Return","down"),("Shift-Return","up"),("Tab","next"),("Shift-Tab","previous"),("ISO_Left_Tab","previous"),("Escape","cancel")] do
      cmd #["bind", widget, "<"++key++">", "calc "++action++"; break"]
  for (key, action) in [("Up","up"),("Down","down"),("Left","left"),("Right","right"),("Delete","clear"),("BackSpace","clear"),("F2","begin")] do
    cmd #["bind", ".grid", "<"++key++">", "calc "++action++"; break"]
  for (key, action) in [("Up","up"),("Down","down"),("Left","left"),("Right","right")] do
    cmd #["bind", ".grid", "<Shift-"++key++">", "calc extendmove "++action++"; break"]
  for (key, action) in [("f","find"),("g","findnext"),("d","filldown"),("r","fillright"),("n","new"),("o","open"),("s","save"),("Shift-S","saveas"),("q","quit"),("z","undo"),("Shift-Z","redo"),("c","copy"),("x","cut"),("v","paste")] do
    for modifier in ["Command", "Control"] do
      let binding := "<"++modifier++"-"++key++">"
      for widget in [".", ".grid", ".formula", ".grid.editor"] do
        let virtual := if action == "copy" then "Copy" else if action == "cut" then "Cut" else if action == "paste" then "Paste" else ""
        let handler := if virtual != "" && (widget == ".formula" || widget == ".grid.editor") then
          "event generate "++widget++" <<"++virtual++">>; break"
          else "calc "++action++"; break"
        cmd #["bind", widget, binding, handler]
  refresh
  cmd #["focus",".grid"]

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false
def Except.isError (x : Except ε α) : Bool := match x with | .error _ => true | _ => false

initialize passed : IO.Ref Nat ← IO.mkRef 0
def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw <| IO.userError ("FAIL: " ++ name)
  passed.modify (·+1)
  IO.println ("PASS: " ++ name)
def calculate (formula : String) : Except String Rat := value (put emptySheet 0 ("="++formula)) 0
def sample : Sheet := put (put (put (put emptySheet 0 "1") 1 "2") 26 "3") 27 "4"

def selfTests : IO Unit := do
  check "First cell address" (parseAddress "A1" == some 0)
  check "Last cell address" (parseAddress "Z100" == some 2599)
  check "Lowercase addresses" (parseAddress "b2" == some 27)
  check "Whitespace around addresses" (parseAddress " A1 " == some 0)
  check "Reject row zero" ((parseAddress "A0").isNone)
  check "Reject row beyond sheet" ((parseAddress "A101").isNone)
  check "Reject column beyond sheet" ((parseAddress "AA1").isNone)
  check "Reject missing row" ((parseAddress "A").isNone)
  check "Address round-trip across all 2600 cells" ((List.range 2600).all (fun i => parseAddress (address i) == some i))
  check "Empty sheet dimensions and contents" (emptySheet.size == 2600 && emptySheet.all (· == ""))
  check "Parse positive integer" (decimal "42" == some 42)
  check "Parse negative decimal" (decimal "-1.25" == some (mkRat (-5) 4))
  check "Parse leading decimal point" (decimal ".5" == some (mkRat 1 2))
  check "Parse explicit plus" (decimal "+3" == some 3)
  check "Reject multiple decimal points" ((decimal "1.2.3").isNone)
  check "Reject lone decimal point" ((decimal ".").isNone)
  check "Exact decimal addition" (calculate "0.1+0.2" == .ok (mkRat 3 10))
  check "Display terminating decimal" (showNumber (mkRat (-1) 8) == "-0.125")
  check "Display repeating result as fraction" (showNumber (mkRat 1 3) == "1/3")
  check "Preserve Unicode text" (display (put emptySheet 0 "café λ 日本語") 0 == "café λ 日本語")
  check "Formula addition" (calculate "2+3" == .ok 5)
  check "Formula subtraction" (calculate "2-7" == .ok (-5))
  check "Formula multiplication" (calculate "6*7" == .ok 42)
  check "Formula division" (calculate "3/2" == .ok (mkRat 3 2))
  check "Multiplication precedence" (calculate "2+3*4" == .ok 14)
  check "Parentheses precedence" (calculate "(2+3)*4" == .ok 20)
  check "Left-associative subtraction" (calculate "10-3-2" == .ok 5)
  check "Left-associative division" (calculate "12/3/2" == .ok 2)
  check "Unary minus and plus" (calculate "-(-3)+ +2" == .ok 5)
  check "Formula whitespace" (calculate " 2 + 3 " == .ok 5)
  check "Reference another cell" (value (put (put emptySheet 0 "7") 1 "=A1*2") 1 == .ok 14)
  check "Recalculate changed dependency" (value (put (put (put emptySheet 0 "7") 1 "=A1*2") 0 "9") 1 == .ok 18)
  check "Blank references equal zero" (calculate "B1+2" == .ok 2)
  check "Text reference is an error" (value (put (put emptySheet 0 "hello") 1 "=A1+1") 1 == .error "#VALUE!")
  check "Division by zero error" (calculate "1/0" == .error "#DIV/0!")
  check "Direct circular reference" (calculate "A1" == .error "#CYCLE!")
  check "Indirect circular reference" (value (put (put emptySheet 0 "=B1") 1 "=A1") 0 == .error "#CYCLE!")
  check "Out-of-range reference error" (calculate "A101" == .error "#REF!")
  check "Unknown function error" (calculate "AVG(B1:B2)" == .error "#NAME?")
  check "Reject trailing expression tokens" (calculate "2 3" == .error "#PARSE!")
  check "Reject unmatched parentheses" (calculate "(2+3" == .error "#PARSE!")
  check "Rectangular SUM" (value (put sample 2 "=SUM(A1:B2)") 2 == .ok 10)
  check "Reversed SUM endpoints" (value (put sample 2 "=sum(B2:A1)") 2 == .ok 10)
  check "SUM skips text and blank cells" (value (put (put sample 0 "text") 2 "=SUM(A1:B3)") 2 == .ok 9)
  check "SUM propagates formula errors" (value (put (put sample 0 "=1/0") 2 "=SUM(A1:B2)") 2 == .error "#DIV/0!")
  check "Formula length limit" (calculate (String.ofList (List.replicate 513 '1')) == .error "#LIMIT!")
  check "Apostrophe forces literal text" (display (put emptySheet 0 "'=1+2") 0 == "=1+2")
  check "Editing affects only chosen cell" ((put sample 1 "99")[0]! == "1" && (put sample 1 "99")[1]! == "99" && (put sample 1 "99")[26]! == "3")
  check "Out-of-bounds edit is unchanged" (put sample 2600 "bad" == sample)
  check "Undo restores previous sheet" ((undoEdit (edit (singleModel sample) 0 "99")).sheet == sample)
  check "Redo restores undone edit" ((redoEdit (undoEdit (edit (singleModel sample) 0 "99"))).sheet == put sample 0 "99")
  check "New edit clears redo history" ((edit (undoEdit (edit (singleModel sample) 0 "99")) 1 "88").redo.isEmpty)
  check "Identical edit does not create undo history" ((edit (singleModel sample) 0 "1").undo.isEmpty)
  check "File round-trip preserves formulas and Unicode" (decode (encode (put (put sample 2 "=SUM(A1:B2)") 3 "λ\n\"text\"")) == .ok (put (put sample 2 "=SUM(A1:B2)") 3 "λ\n\"text\""))
  check "Reject malformed file" ((decode "not JSON").isError)
  check "Reject unsupported file version" ((decode ((encode sample).replace "LeanCalc-1" "LeanCalc-2")).isError)
  check "Reject incorrect sheet dimensions" ((decode (encode #["one cell"])).isError)
  check "Reject oversized or NUL-containing cells" ((decode (encode (put emptySheet 0 (String.ofList (List.replicate 4097 'x'))))).isError && (decode (encode (put emptySheet 0 "\u0000"))).isError)
  tkInit false
  check "Native main thread and noninteractive startup" ((← isMainThread) && (← startupConfigured))
  let literal := "λ [error injection] {$name}; \"quotes\""
  check "Tcl bridge preserves text without evaluation" ((← tk #["lindex", ← tk #["list", literal], "0"]) == literal)
  let temp ← tk #["file", "tempfile", "calcTestChannel"]
  let path ← tk #["set", "calcTestChannel"]
  cmd #["close", temp]
  try
    let before ← readOptional path
    let bytes ← saveChecked path before sample
    let roundTrip := (← readOptional path) == some bytes
    let rejected ← try
      discard <| saveChecked path before emptySheet
      pure false
      catch _ => pure true
    check "Atomic save round-trip and conflict protection" (roundTrip && rejected && (← readOptional path) == some bytes)
  finally IO.FS.removeFile path
  if (← passed.get) != 61 then throw <| IO.userError "Expected exactly 61 tests."
  IO.println "61/61 tests passed."

-- Headless interaction checks use the real Lean command handlers and Tcl key
-- translation. Widget calls are replaced by small adapters; painting is tested
-- separately by --gui-self-test on a desktop.
def interactionTests : IO Unit := do
  tkInit false
  script cellUIScript
  script "proc focus {args} {if {[llength $args]} {set ::testFocus [lindex $args 0]}; return $::testFocus}; set ::testFocus .grid"
  script "proc noop {args} {}; foreach name {.grid .grid.editor .addr .status calcSyncSheets wm} {interp alias {} $name {} noop}; proc calcRevealCell {} {}; proc calcPlaceEditor {} {}"
  refresh
  dispatch #["select", "1", "2"]
  check "Cell click selects B2 and keeps grid focus" ((← selected.get) == 27 && (← tk #["focus"]) == ".grid")
  cmd #["calcTyped", "7", "0"]
  check "Typing starts an in-cell draft with editor focus" ((← tk #["set", "::calcDraft"]) == "7" && (← tk #["set", "::calcEditing"]) == "1" && (← tk #["focus"]) == ".grid.editor")
  check "Draft is not committed prematurely" ((← model.get).sheet[27]! == "")
  cmd #["append", "::calcDraft", "2"]
  dispatch #["down"]
  check "Enter commits all typed characters and moves down" ((← model.get).sheet[27]! == "72" && (← selected.get) == 53 && (← tk #["focus"]) == ".grid")
  dispatch #["undo"]
  check "Undo reverses the whole in-cell edit" ((← model.get).sheet[27]! == "")
  dispatch #["redo"]
  check "Redo restores the whole in-cell edit" ((← model.get).sheet[27]! == "72")
  dispatch #["select", "1", "2"]
  dispatch #["begin"]
  check "Edit existing keeps the original contents" ((← tk #["set", "::calcDraft"]) == "72" && (← tk #["set", "::calcEditing"]) == "1")
  cmd #["set", "::calcDraft", "99"]
  dispatch #["cancel"]
  check "Escape restores both draft and committed value" ((← tk #["set", "::calcDraft"]) == "72" && (← model.get).sheet[27]! == "72" && (← tk #["set", "::calcEditing"]) == "0")
  dispatch #["type", "=2+3"]
  dispatch #["select", "0", "1"]
  check "Clicking another cell commits and recalculates the edit" ((← selected.get) == 0 && display (← model.get).sheet 27 == "5")
  cmd #["set", "::calcDraft", "=B2*2"]
  dispatch #["apply"]
  check "Formula-bar draft uses the same commit path" (display (← model.get).sheet 0 == "10")
  dispatch #["begin"]
  check "Editing a formula shows its source rather than result" ((← tk #["set", "::calcDraft"]) == "=B2*2")
  dispatch #["cancel"]
  check "Arrow navigation stays inside sheet boundaries" (moveCell 0 "left" == 0 && moveCell 0 "up" == 0 && moveCell 25 "right" == 25 && moveCell 2599 "down" == 2599 && moveCell 27 "left" == 26 && moveCell 27 "up" == 1)
  check "Tab and Shift-Tab cross row boundaries and stop at ends" (moveCell 25 "next" == 26 && moveCell 26 "previous" == 25 && moveCell 0 "previous" == 0 && moveCell 2599 "next" == 2599)
  let literal := "λ [error injected] {$value}; \"quotes\""
  cmd #["calcTyped", literal, "0"]
  check "Typing Unicode and Tcl punctuation is literal data" ((← tk #["set", "::calcDraft"]) == literal)
  cmd #["calcTyped", "x", "4"]
  cmd #["calcTyped", "x", "8"]
  cmd #["calcTyped", "\n", "0"]
  check "Shortcut modifiers and control characters do not replace cells" ((← tk #["set", "::calcDraft"]) == literal)
  dispatch #["cancel"]
  dispatch #["type", String.ofList (List.replicate 4097 'x')]
  let rejected ← try dispatch #["next"]; pure false catch _ => pure true
  check "Invalid draft blocks navigation without losing original data" (rejected && (← selected.get) == 0 && (← model.get).sheet[0]! == "=B2*2")
  dispatch #["cancel"]
  let channel ← tk #["file", "tempfile", "interactionTestPath"]
  let path ← tk #["set", "interactionTestPath"]
  cmd #["close", channel]
  try
    filePath.set path
    original.set (← readOptional path)
    dispatch #["type", "123"]
    let success ← saveFile false
    let bytes ← IO.FS.readFile path
    check "Save commits and persists a pending in-cell edit" (success && (Phase2.decodeBook bytes).toOption == some ((← model.get).book,(← model.get).active) && (← model.get).sheet[0]! == "123")
  finally IO.FS.removeFile path
  IO.println s!"{← passed.get} interaction checks passed (headless widget adapters)."

def guiTests : IO Unit := do
  tkInit true
  setupUI
  script "set ::testErrors {}; proc bgerror {message} {lappend ::testErrors $message}"
  cmd #["update"]
  script "lassign [.grid bbox 0 A] x y w h; event generate .grid <Button-1> -x [expr {$x+8}] -y [expr {$y+8}]; event generate .grid <ButtonRelease-1> -x [expr {$x+8}] -y [expr {$y+8}]"
  script "focus -force .grid; update"
  cmd #["event", "generate", ".grid", "<KeyPress>", "-keysym", "1"]
  cmd #["event", "generate", ".grid.editor", "<KeyPress>", "-keysym", "2"]
  check "GUI typing in selected cell synchronizes formula bar" ((← tk #[".formula", "get"]) == "12" && (← tk #["focus"]) == ".grid.editor")
  cmd #["event", "generate", ".grid.editor", "<Return>"]
  check "GUI Enter commits and moves to next row" ((← model.get).sheet[0]! == "12" && (← selected.get) == 26)
  cmd #["event", "generate", ".grid", "<F2>"]
  cmd #[".grid.editor", "insert", "end", "=A1*2"]
  check "GUI cell editor and formula bar share formula text" ((← tk #[".formula", "get"]) == "=A1*2")
  cmd #["event", "generate", ".grid.editor", "<Tab>"]
  check "GUI formula recalculation and Tab navigation" ((← tk #[".grid", "set", "1", "A"]) == "24" && (← selected.get) == 27)
  cmd #["event", "generate", ".grid", "<Left>"]
  cmd #["event", "generate", ".grid", "<F2>"]
  check "GUI F2 edits raw formula" ((← tk #[".grid.editor", "get"]) == "=A1*2")
  cmd #[".grid.editor", "insert", "end", "+100"]
  cmd #["event", "generate", ".grid.editor", "<Escape>"]
  check "GUI Escape cancels uncommitted changes" ((← model.get).sheet[26]! == "=A1*2" && (← tk #[".formula", "get"]) == "=A1*2")
  dispatch #["undo"]
  check "GUI undo restores previous cell contents" ((← model.get).sheet[26]! == "")
  dispatch #["redo"]
  check "GUI redo restores in-cell formula" ((← model.get).sheet[26]! == "=A1*2")
  dispatch #["select", "99", "26"]
  cmd #["update"]
  check "GUI navigation reveals far-right bottom cell" ((← tk #["winfo", "ismapped", ".grid.editor"]) == "1")
  script "lassign [.grid bbox 99 Z] x y w h; set ::editorAligned [expr {[winfo x .grid.editor] == $x && [winfo y .grid.editor] == $y && [winfo width .grid.editor] == $w && [winfo height .grid.editor] == $h}]"
  check "GUI active outline matches cell bounds" ((← tk #["set", "::editorAligned"]) == "1")
  script ".grid column Z -width 140; update"
  check "GUI resize keeps an active editor without Tcl errors" ((← tk #["set", "::testErrors"]) == "")
  check "GUI grid strips retain one-pixel thickness and gray color" ((← tk #["image", "height", "calcGridHorizontal"]) == "1" && (← tk #["image", "width", "calcGridVertical"]) == "1" && (← tk #["calcGridHorizontal", "get", "0", "0"]) == "217 217 217" && (← tk #["calcGridVertical", "get", "0", "0"]) == "217 217 217")
  script "wm geometry . 1400x800; .grid column Z -width 220; update"
  check "GUI resizing preserves grid strip dimensions" ((← tk #["image", "width", "calcGridHorizontal"]) == "4096" && (← tk #["image", "height", "calcGridVertical"]) == "4096")
  dispatch #["select","0","1"]
  cmd #["event","generate",".grid","<Shift-Right>"]
  cmd #["event","generate",".grid","<Shift-Down>"]
  cmd #["update"]
  check "GUI Shift-arrows paint a rectangular selection" ((← tk #["llength",← tk #[".grid","tag","cell","has","range"]]) == "4")
  dispatch #["filldown"]
  check "GUI fill updates displayed cells" ((← tk #[".grid","set","1","A"]) == "12")
  dispatch #["addsheet","Totals"]
  dispatch #["type","=Sheet1!A1"]
  dispatch #["apply"]
  check "GUI sheet tabs and cross-sheet results stay synchronized" ((← tk #["set","::calcSheetActive"]) == "1" && (← tk #[".grid","set","0","A"]) == "12")
  cmd #[".sheetbar.tabs.items.t0.label","invoke"]
  check "GUI clicking a sheet tab switches the displayed workbook sheet" ((← model.get).active == 0 && (← tk #[".grid","set","0","A"]) == "12")
  dispatch #["select","4","4"]
  dispatch #["type","=sum("]
  script "focus -force .grid.editor; update; lassign [.grid bbox 0 A] x y w h; event generate .grid <Button-1> -x [expr {$x+8}] -y [expr {$y+8}]; lassign [.grid bbox 1 A] x y w h; event generate .grid <B1-Motion> -x [expr {$x+8}] -y [expr {$y+8}]; event generate .grid <ButtonRelease-1> -x [expr {$x+8}] -y [expr {$y+8}]; update"
  check "GUI formula dragging retains the owner and editor focus" ((← selected.get) == 107 && (← tk #["focus"]) == ".grid.editor" && (← tk #[".formula","get"]) == "=sum(A1:A2" && (← model.get).sheet[107]! == "")
  check "GUI formula dragging highlights the reference rectangle" ((← tk #["llength",← tk #[".grid","tag","cell","has","formulaRange"]]) == "2")
  script "event generate .grid.editor <KeyPress> -keysym parenright; event generate .grid.editor <Return>; update"
  check "GUI closing a picked formula and pressing Return computes the sum" ((← model.get).sheet[107]! == "=sum(A1:A2)" && (← tk #[".grid","set","4","D"]) == "24" && (← selected.get) == 133)
  check "GUI formula picking completes without Tcl errors" ((← tk #["set","::testErrors"]) == "")
  dispatch #["renamesheet","Annual total"]
  check "GUI renamed sheet has a visible tab and active underline" ((← tk #[".sheetbar.tabs.items.t0.label","cget","-text"]) == "Annual total" && (← tk #[".sheetbar.tabs.items.t0.line","cget","-background"]) == "#217346")
  for i in [2:32] do
    model.set (← unwrap (Phase2.addSheet (← model.get) ("Worksheet " ++ toString i)))
  refresh
  script "wm geometry . 640x420; update"
  check "GUI overflow tabs reveal the active sheet in a narrow window" ((← tk #["expr","[lindex [.sheetbar.tabs xview] 0] > 0"]) == "1" && (← tk #["llength",← tk #["winfo","children",".sheetbar.tabs.items"]]) == "32")
  cmd #[".sheetbar.tabs.items.t0.label","invoke"]
  cmd #["update"]
  check "GUI switching to the first tab scrolls it back into view" ((← model.get).active == 0 && (← tk #["expr","[lindex [.sheetbar.tabs xview] 0] == 0"]) == "1")
  check "GUI sheet strip resizes without Tcl errors" ((← tk #["set","::testErrors"]) == "")
  cmd #["destroy", "."]
  IO.println s!"{← passed.get} GUI checks passed."

-- Unlike --navigation-benchmark, this exercises real Tk events and drains
-- redraw/geometry work after EVERY key. It compares both tile sizes in the
-- same window, without opening or changing any user document.
def guiRenderBenchmark : IO Unit := do
  tkInit true
  setupUI
  script "focus -force .grid; update"
  let reportPath ← tk #["file", "normalize", ← tk #["file", "join", ← tk #["file", "dirname", ← tk #["info", "nameofexecutable"]], "..", "..", "..", "LeanCalc-render-benchmark.log"]]
  let mut report := "LeanCalc 0.5.1: real Tk keyboard + repaint benchmark\n"
  IO.FS.writeFile reportPath report
  for (size, label) in [(4096, "strip"), (1, "legacy one-pixel tile"), (4096, "strip repeated")] do
    cmd #["calcGridHorizontal", "configure", "-width", toString size]
    cmd #["calcGridHorizontal", "put", "#d9d9d9", "-to", "0", "0", toString size, "1"]
    cmd #["calcGridVertical", "configure", "-height", toString size]
    cmd #["calcGridVertical", "put", "#d9d9d9", "-to", "0", "0", "1", toString size]
    cmd #["update", "idletasks"]
    let start ← IO.monoNanosNow
    for key in ["Right", "Left", "Down", "Up"] do
      cmd #["event", "generate", ".grid", "<" ++ key ++ ">"]
      cmd #["update", "idletasks"]
    let elapsed := (← IO.monoNanosNow) - start
    if (← selected.get) != 0 then throw <| IO.userError "Benchmark keyboard navigation failed."
    report := report ++ s!"{label}: 4 arrow events + painting, {elapsed / 1000000} ms total; {elapsed / 4000} us/event\n"
    IO.FS.writeFile reportPath report
  cmd #["destroy", "."]
  IO.println report

-- Instrument widget writes while running the real dispatcher without a desktop.
def setupPerformanceTest : IO Unit := do
  tkInit false
  script cellUIScript
  script "proc focus {args} {if {[llength $args]} {set ::testFocus [lindex $args 0]}; return $::testFocus}; set ::testFocus .grid"
  script "proc noop {args} {}; foreach name {.grid.editor .addr .status calcSyncSheets wm} {interp alias {} $name {} noop}; proc calcRevealCell {} {}; proc calcPlaceEditor {} {}; set ::rowWrites 0; array set ::testRows {}; proc .grid {args} {if {[lindex $args 0] eq {item}} {incr ::rowWrites; set ::testRows([lindex $args 1]) [lindex $args 3]}}"

def navigationBenchmark : IO Unit := do
  setupPerformanceTest
  let mut s := put emptySheet 0 "1"
  for i in [2340:2600] do s := put s i "=SUM(A1:Z90)"
  model.set (singleModel s)
  selected.set 2340
  refresh
  cmd #["set", "::rowWrites", "0"]
  let start ← IO.monoNanosNow
  for _ in [0:10] do
    dispatch #["right"]
    dispatch #["left"]
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"20 navigation actions: {elapsed / 1000000} ms total, {elapsed / 20000} us/action; grid row writes: {← tk #["set", "::rowWrites"]} (headless, 260 SUM formulas)."

def performanceTests : IO Unit := do
  setupPerformanceTest
  refresh
  check "Initial refresh populates all grid rows" ((← tk #["set", "::rowWrites"]) == "100")
  cmd #["set", "::rowWrites", "0"]
  dispatch #["right"]
  dispatch #["left"]
  dispatch #["select", "99", "26"]
  dispatch #["cancel"]
  check "Navigation and cancel never rewrite unchanged grid rows" ((← tk #["set", "::rowWrites"]) == "0" && (← model.get).undo.isEmpty)
  model.set (singleModel (put (put emptySheet 0 "2") 26 "=A1*3"))
  selected.set 0
  refresh
  check "Changed sheet updates only rows with different values" ((← tk #["set", "::rowWrites"]) == "2")
  cmd #["set", "::rowWrites", "0"]
  dispatch #["type", "4"]
  dispatch #["down"]
  check "Committing recalculates dependent rows and the active formula" ((← tk #["lindex", ← tk #["set", "::testRows(1)"], "0"]) == "12" && (← tk #["set", "::calcDisplay"]) == "12" && (← tk #["set", "::calcDraft"]) == "=A1*3" && (← tk #["set", "::rowWrites"]) == "2")
  cmd #["set", "::rowWrites", "0"]
  dispatch #["right"]
  dispatch #["left"]
  check "Returning to a formula reuses its cached result" ((← tk #["set", "::calcDisplay"]) == "12" && (← tk #["set", "::rowWrites"]) == "0")
  dispatch #["undo"]
  check "Undo refreshes dependent formula results" ((← tk #["set", "::calcDisplay"]) == "6")
  dispatch #["redo"]
  check "Redo refreshes dependent formula results" ((← tk #["set", "::calcDisplay"]) == "12")
  cmd #["set", "::rowWrites", "0"]
  dispatch #["type", "=A1+A1+A1"]
  dispatch #["apply"]
  check "Equivalent formula updates its source without rewriting rows" ((← tk #["set", "::calcDraft"]) == "=A1+A1+A1" && (← tk #["set", "::rowWrites"]) == "0")
  dispatch #["clear"]
  check "Clear removes a cached result" ((← tk #["lindex", ← tk #["set", "::testRows(1)"], "0"]) == "" && (← tk #["set", "::calcDisplay"]) == "")
  dispatch #["type", "=1/0"]
  dispatch #["apply"]
  check "Formula errors replace previous cached values" ((← tk #["set", "::calcDisplay"]) == "#DIV/0!")
  let channel ← tk #["file", "tempfile", "performanceTestPath"]
  let path ← tk #["set", "performanceTestPath"]
  cmd #["close", channel]
  try
    IO.FS.writeFile path (encode (put emptySheet 0 "=7+8"))
    loadFile path
    refresh
    check "Loading another file replaces stale results" ((← tk #["set", "::calcDisplay"]) == "15" && (← tk #["lindex", ← tk #["set", "::testRows(1)"], "0"]) == "")
    dispatch #["new"]
    check "New sheet clears cached values" ((← tk #["set", "::calcDisplay"]) == "" && (← tk #["lindex", ← tk #["set", "::testRows(0)"], "0"]) == "")
  finally IO.FS.removeFile path
  IO.println s!"{← passed.get} performance regression checks passed (headless widget adapters)."

def phase2InteractionTests : IO Unit := do
  setupPerformanceTest
  script "set ::testClipboard {}; proc clipboard {op args} {switch -- $op {clear {set ::testClipboard {}} append {append ::testClipboard [lindex $args end]} get {return $::testClipboard}}}; proc tk_messageBox {args} {return yes}; proc tk_getOpenFile {args} {return $::testOpenPath}; proc tk_getSaveFile {args} {return $::testSavePath}"
  model.set (singleModel (put (put (put (put emptySheet 0 "2") 1 "=A1*3") 26 "4") 27 "=A2*3"))
  saved.set (← model.get).book
  refresh
  dispatch #["extendmove","right"]
  dispatch #["extendmove","down"]
  check "Shift navigation selects a rectangle" ((← currentRect) == Phase2.rectangle 0 27 && (← paintedSelection.get).length == 4)
  dispatch #["copy"]
  check "Copy does not alter workbook or undo history" ((← model.get).undo.isEmpty && (← cellClipboard.get).isSome)
  dispatch #["select","0","3"]
  dispatch #["paste"]
  check "Clipboard paste shifts relative formulas in the real handler" ((← model.get).sheet[3]! == "=C1*3" && (← tk #["lindex",← tk #["set","::testRows(0)"],"3"]) == "6")
  dispatch #["undo"]
  check "UI undo reverses rectangular paste as one action" ((← model.get).sheet[2]! == "")
  dispatch #["redo"]
  check "UI redo restores the pasted rectangle" ((← model.get).sheet[29]! == "=C2*3")
  dispatch #["select","0","3"]
  dispatch #["extend","2","4"]
  dispatch #["filldown"]
  check "Fill Down handler updates the whole selected rectangle" ((← model.get).sheet[54]! == "2" && (← model.get).sheet[55]! == "=C3*3")
  dispatch #["addsheet","Totals"]
  dispatch #["type","=Sheet1!D1"]
  dispatch #["apply"]
  check "New sheet and cross-sheet formula are connected to the UI" ((← model.get).active == 1 && (← tk #["set","::calcDisplay"]) == "6" && (← tk #["focus"]) == ".grid")
  dispatch #["sheet","0"]
  dispatch #["renamesheet","Inputs"]
  dispatch #["sheet","1"]
  check "Sheet rename updates live cross-sheet formulas" ((← model.get).sheet[0]! == "='Inputs'!D1" && (← tk #["set","::calcDisplay"]) == "6")
  dispatch #["sheet","0"]
  dispatch #["select","0","1"]
  dispatch #["cut"]
  check "Cut leaves source cells intact until Paste" ((← model.get).sheet[0]! == "2")
  dispatch #["sheet","1"]
  dispatch #["select","1","2"]
  dispatch #["paste"]
  check "Cut across sheets moves data and follows incoming references" ((← model.get).sheet[27]! == "2" && (← model.get).book[0]!.cells[0]! == "" && Phase2.cellDisplay (← model.get).book 0 1 == "6")
  dispatch #["undo"]
  check "UI undo restores a cut across sheets" ((← model.get).book[0]!.cells[0]! == "2" && (← model.get).sheet[27]! == "")
  dispatch #["sheet","0"]
  dispatch #["select","0","1"]
  dispatch #["cut"]
  dispatch #["type","9"]
  dispatch #["apply"]
  dispatch #["select","5","1"]
  let rejected ← try dispatch #["paste"]; pure false catch _ => pure true
  check "Stale Cut is rejected without losing data" (rejected && (← model.get).sheet[0]! == "9" && (← model.get).sheet[130]! == "")
  cmd #["set","::testClipboard","5\t6\r\n7\t8\r\n"]
  dispatch #["paste"]
  check "External TSV clipboard pastes as a rectangle" ((← model.get).sheet[130]! == "5" && (← model.get).sheet[157]! == "8")
  dispatch #["select","5","1"]
  dispatch #["insertrow"]
  check "Row insertion handler shifts pasted data" ((← model.get).sheet[130]! == "" && (← model.get).sheet[156]! == "5")
  dispatch #["deleterow"]
  check "Row deletion handler removes the inserted row" ((← model.get).sheet[130]! == "5")
  dispatch #["sheet","1"]
  dispatch #["deletesheet"]
  check "Delete sheet command remains undoable" ((← model.get).book.size == 1)
  dispatch #["undo"]
  check "Undo restores a deleted sheet and activates it" ((← model.get).book.size == 2 && (← model.get).active == 1)
  let channel ← tk #["file","tempfile","phase2Path"]
  let path ← tk #["set","phase2Path"]
  cmd #["close",channel]
  let csvChannel ← tk #["file","tempfile","phase2CSVPath"]
  let csvPath ← tk #["set","phase2CSVPath"]
  cmd #["close",csvChannel]
  try
    filePath.set path; original.set (← readOptional path)
    discard <| saveFile false
    let expected := (← model.get).book
    model.set {}
    loadFile path
    refresh
    check "Native save and load preserve every sheet and the active tab" ((← model.get).book == expected && (← model.get).active == 1)
    IO.FS.writeFile path "external edit"
    let rejected ← try discard <| saveFile false; pure false catch _ => pure true
    check "Workbook save still detects external file changes" (rejected && (← IO.FS.readFile path) == "external edit")
    IO.FS.writeFile csvPath "1,\"=2+3\"\r\n4,5\r\n"
    cmd #["set","::testOpenPath",csvPath]
    dispatch #["importcsv"]
    check "CSV import handler replaces only the active sheet" ((← model.get).sheet[0]! == "1" && (← model.get).book[0]! == expected[0]! && (← tk #["lindex",← tk #["set","::testRows(0)"],"1"]) == "=2+3")
    cmd #["set","::testSavePath",csvPath]
    let nativePath ← filePath.get
    dispatch #["exportcsv"]
    check "CSV export writes display text without changing the native path" ((← IO.FS.readFile csvPath) == "1,=2+3\r\n4,5\r\n" && (← filePath.get) == nativePath)
    dispatch #["undo"]
    check "Undo reverses CSV import in one step" ((← model.get).book == expected)
    dispatch #["sheet","0"]
    dispatch #["select","0","3"]
    dispatch #["type","7"]
    dispatch #["apply"]
    dispatch #["sheet","1"]
    check "Cached results refresh after editing a referenced sheet" ((← tk #["set","::calcDisplay"]) == "21")
  finally
    IO.FS.removeFile path
    IO.FS.removeFile csvPath
  IO.println s!"{← passed.get} Phase 2 interaction checks passed (headless widget adapters)."

def formulaPickingTestAdapters : String :=
  "array set ::testCaret {.grid.editor 0 .formula 0}\narray set ::testFirst {.grid.editor -1 .formula -1}\narray set ::testLast {.grid.editor -1 .formula -1}\narray set ::testVar {.grid.editor ::calcDisplay .formula ::calcDraft}\nrename .grid.editor {}\nproc testEntryIndex {widget index} {\n    switch -- $index {\n        insert {return $::testCaret($widget)}\n        end {return [string length [set $::testVar($widget)]]}\n        sel.first {return $::testFirst($widget)}\n        sel.last {return $::testLast($widget)}\n        default {return $index}\n    }\n}\nproc testEntry {widget op args} {\n    switch -- $op {\n        get {return [set $::testVar($widget)]}\n        configure {\n            foreach {name value} $args {\n                if {$name eq {-textvariable}} {set ::testVar($widget) $value}\n            }\n        }\n        index {return [testEntryIndex $widget [lindex $args 0]]}\n        icursor {set ::testCaret($widget) [testEntryIndex $widget [lindex $args 0]]}\n        selection {\n            switch -- [lindex $args 0] {\n                present {return [expr {$::testFirst($widget) >= 0 && $::testLast($widget) > $::testFirst($widget)}]}\n                clear {set ::testFirst($widget) -1; set ::testLast($widget) -1}\n                range {\n                    set ::testFirst($widget) [testEntryIndex $widget [lindex $args 1]]\n                    set ::testLast($widget) [testEntryIndex $widget [lindex $args 2]]\n                }\n            }\n        }\n        insert {\n            set at [testEntryIndex $widget [lindex $args 0]]\n            set text [lindex $args 1]\n            set old [set $::testVar($widget)]\n            set $::testVar($widget) [string cat [string range $old 0 [expr {$at-1}]] $text [string range $old $at end]]\n            set ::testCaret($widget) [expr {$at+[string length $text]}]\n        }\n        delete {\n            set first [testEntryIndex $widget [lindex $args 0]]\n            set last [testEntryIndex $widget [lindex $args 1]]\n            set $::testVar($widget) [string replace [set $::testVar($widget)] $first [expr {$last-1}] {}]\n            set ::testCaret($widget) $first\n        }\n    }\n}\ninterp alias {} .grid.editor {} testEntry .grid.editor\ninterp alias {} .formula {} testEntry .formula\nrename .grid testGridRows\nproc .grid {args} {\n    if {[lindex $args 0] eq {identify}} {\n        lassign $args unused kind x y\n        switch -- $kind {\n            region {return [expr {$x >= 1 && $x <= 26 && $y >= 0 && $y < 100 ? \"cell\" : \"heading\"}]}\n            row {return $y}\n            column {return #$x}\n        }\n    }\n    return [testGridRows {*}$args]\n}\n"

def formulaPickingTests : IO Unit := do
  setupPerformanceTest
  script formulaPickingTestAdapters
  model.set (singleModel (put (put (put (put (put (put emptySheet 0 "1") 1 "2") 26 "3") 27 "4") 52 "5") 53 "6"))
  selected.set 107
  refresh
  dispatch #["type","=sum("]
  cmd #["set","::rowWrites","0"]
  cmd #["calcClick","1","0"]
  check "Picking starts without committing or moving the formula cell" ((← selected.get) == 107 && (← model.get).sheet[107]! == "" && (← model.get).undo.isEmpty && (← tk #["set","::calcDraft"]) == "=sum(A1")
  cmd #["calcDrag","2","2"]
  check "Dragging replaces the temporary reference with a rectangle" ((← tk #["set","::calcDraft"]) == "=sum(A1:B3" && (← paintedFormulaRange.get).length == 6)
  cmd #["calcDrag","2","2"]
  check "Repeated drag motion never duplicates reference text" ((← tk #["set","::calcDraft"]) == "=sum(A1:B3")
  cmd #["calcRelease","2","2"]
  check "Mouse release leaves the draft in its original editor" ((← tk #["focus"]) == ".grid.editor" && (← tk #["set","::calcEditing"]) == "1" && (← tk #["set","::calcPicking"]) == "0" && (← selected.get) == 107)
  check "Formula picking does not rewrite grid values" ((← tk #["set","::rowWrites"]) == "0")
  cmd #[".grid.editor","insert","insert",")"]
  dispatch #["down"]
  check "Closing parenthesis and Return calculate the picked SUM" ((← model.get).sheet[107]! == "=sum(A1:B3)" && Phase2.cellDisplay (← model.get).book 0 107 == "21" && (← selected.get) == 133)
  check "Committing clears reference highlights and picking state" ((← formulaPick.get).isNone && (← paintedFormulaRange.get).isEmpty)
  dispatch #["undo"]
  check "Undo reverses the complete picked formula in one step" ((← model.get).sheet[107]! == "" && (← model.get).sheet[0]! == "1")
  dispatch #["redo"]
  check "Redo restores the picked formula" (Phase2.cellDisplay (← model.get).book 0 107 == "21")
  dispatch #["select","4","4"]
  dispatch #["type","=SUM("]
  cmd #["calcClick","2","2"]
  cmd #["calcDrag","1","0"]
  cmd #["calcRelease","1","0"]
  check "Reverse-direction dragging produces a normalized range" ((← tk #["set","::calcDraft"]) == "=SUM(A1:B3")
  cmd #["calcClick","3","0"]
  cmd #["calcDrag","4","1"]
  cmd #["calcRelease","4","1"]
  check "Picking again replaces the previous range until typing resumes" ((← tk #["set","::calcDraft"]) == "=SUM(C1:D2")
  dispatch #["cancel"]
  check "Escape cancels picking without changing committed content" ((← model.get).sheet[107]! == "=sum(A1:B3)" && (← tk #["set","::calcDraft"]) == "=sum(A1:B3)" && (← paintedFormulaRange.get).isEmpty)
  dispatch #["type","=SUM()"]
  cmd #[".grid.editor","icursor","5"]
  cmd #["calcClick","1","0"]
  cmd #["calcDrag","2","1"]
  cmd #["calcRelease","2","1"]
  check "Picking at the caret preserves the existing formula suffix" ((← tk #["set","::calcDraft"]) == "=SUM(A1:B2)" && (← tk #[".grid.editor","index","insert"]) == "10")
  cmd #[".grid.editor","icursor","end"]
  cmd #["calcClick","3","0"]
  cmd #["calcRelease","3","0"]
  check "Ordinary clicking after a completed formula still commits and navigates" ((← selected.get) == 2 && (← model.get).sheet[107]! == "=SUM(A1:B2)")
  dispatch #["select","4","4"]
  dispatch #["begin"]
  cmd #[".grid.editor","selection","range","5","10"]
  cmd #["calcClick","3","0"]
  cmd #["calcDrag","4","1"]
  cmd #["calcRelease","4","1"]
  check "Picking replaces a selected reference inside an existing formula" ((← tk #["set","::calcDraft"]) == "=SUM(C1:D2)")
  dispatch #["cancel"]
  dispatch #["type","=SUM("]
  cmd #["calcClick","1","0"]
  cmd #["calcDrag","2","1"]
  cmd #["calcRelease","2","1"]
  cmd #[".grid.editor","insert","insert",","]
  cmd #["calcClick","3","0"]
  cmd #["calcDrag","4","1"]
  cmd #["calcRelease","4","1"]
  cmd #[".grid.editor","insert","insert",")"]
  check "Typing a comma permits picking another function argument" ((← tk #["set","::calcDraft"]) == "=SUM(A1:B2,C1:D2)")
  dispatch #["cancel"]
  cmd #[".formula","delete","0","end"]
  cmd #[".formula","insert","0","=SUM("]
  cmd #["focus",".formula"]
  cmd #["calcClick","1","0"]
  cmd #["calcDrag","2","2"]
  cmd #["calcRelease","2","2"]
  check "Formula-bar picking keeps focus and synchronizes both editors" ((← tk #["focus"]) == ".formula" && (← tk #[".formula","get"]) == "=SUM(A1:B3" && (← tk #[".grid.editor","get"]) == "=SUM(A1:B3")
  cmd #[".formula","insert","insert",")"]
  dispatch #["apply"]
  check "Formula-bar picked ranges use the normal commit path" (Phase2.cellDisplay (← model.get).book 0 107 == "21")
  dispatch #["type","="]
  cmd #["calcClick","2","1"]
  cmd #["calcRelease","2","1"]
  check "A single picked cell inserts one address without a colon" ((← tk #["set","::calcDraft"]) == "=B2")
  cmd #[".grid.editor","insert","insert","+"]
  cmd #["calcClick","1","0"]
  cmd #["calcRelease","1","0"]
  check "Picking after an arithmetic operator appends a new reference" ((← tk #["set","::calcDraft"]) == "=B2+A1")
  dispatch #["cancel"]
  dispatch #["type","=SUM("]
  cmd #["calcClick","1","0"]
  cmd #["calcDrag","30","101"]
  cmd #["calcRelease","30","101"]
  check "Dragging outside the grid retains the last valid reference" ((← tk #["set","::calcDraft"]) == "=SUM(A1" && (← selected.get) == 107)
  dispatch #["cancel"]
  check "Quoted strings and quoted sheet names are not insertion slots" ((formulaPickSlot "=IF(1,\"hello\",0)" 10 none).isNone && (formulaPickSlot "='My sheet'!A1" 5 none).isNone)
  check "Unicode and escaped quotes preserve caret insertion boundaries" (formulaPickSlot "=IF(\"λ\"=\"λ\",SUM(),0)" 16 none == some ("=IF(\"λ\"=\"λ\",SUM(","),0)") && insideFormulaQuotes "=\"a\"\"b\"" 4)
  dispatch #["type","ordinary text"]
  cmd #["calcClick","1","0"]
  cmd #["calcRelease","1","0"]
  check "Non-formula editing still commits normally on a cell click" ((← model.get).sheet[107]! == "ordinary text" && (← selected.get) == 0)
  dispatch #["select","4","4"]
  let long := "=SUM(" ++ String.ofList (List.replicate 4089 ' ')
  dispatch #["type",long]
  let rejected ← try
    dispatch #["pickstart","99","26",".grid.editor",toString long.length,"-1","-1"]
    pure false
    catch _ => pure true
  check "Oversized range insertion preserves the draft and original cell" (rejected && (← tk #["set","::calcDraft"]) == long && (← selected.get) == 107 && (← model.get).sheet[107]! == "ordinary text")
  dispatch #["cancel"]
  IO.println s!"{← passed.get} formula-picking checks passed (headless widget adapters)."

def sheetTabsTestAdapters : String :=
  "array set ::tabOptions {}\nset ::tabWrites 0\nproc calcRevealSheet {} {}\nproc tabWidget {name op args} {\n    switch -- $op {\n        configure {incr ::tabWrites; foreach {k v} $args {dict set ::tabOptions($name) $k $v}}\n        cget {return [dict get $::tabOptions($name) [lindex $args 0]]}\n        invoke {uplevel #0 [dict get $::tabOptions($name) -command]}\n    }\n}\nproc frame {name args} {incr ::tabWrites; set ::tabOptions($name) $args; interp alias {} $name {} tabWidget $name}\nproc button {name args} {frame $name {*}$args}\nproc pack {args} {}\nproc bind {args} {}\nproc winfo {op name} {\n    switch -- $op {\n        exists {return [info exists ::tabOptions($name)]}\n        children {\n            set result {}\n            foreach key [array names ::tabOptions $name.*] {\n                if {[string first . [string range $key [expr {[string length $name]+1}] end]] < 0} {lappend result $key}\n            }\n            return $result\n        }\n    }\n}\nproc destroy {name} {\n    foreach key [array names ::tabOptions $name*] {rename $key {}; unset ::tabOptions($key)}\n}\n"

def saveTabsTests : IO Unit := do
  setupPerformanceTest
  script "proc tk_getSaveFile {args} {set ::saveOptions $args; return $::saveTestPath}; proc tk_messageBox {args} {return yes}"
  let channel ← tk #["file","tempfile","saveTestBase"]
  let base := (← IO.FS.realPath (← tk #["set","saveTestBase"])).toString
  cmd #["close",channel]
  let csv := base ++ ".csv"
  let upper := base ++ ".CSV"
  let native := base ++ ".lcalc"
  try
    model.set (singleModel (put (put emptySheet 0 "=2+3") 1 "a,\"λ\""))
    model.set (← unwrap (Phase2.addSheet (← model.get) "Other"))
    model.modify (fun m => {m with active:=0})
    selected.set 0
    refresh
    cmd #["set","::saveTestPath",csv]
    let persisted ← saveFile true
    check "Save As with a CSV suffix writes quoted UTF-8 CSV values" ((← IO.FS.readFile csv) == "5,\"a,\"\"λ\"\"\"\r\n")
    check "CSV Save As is not mistaken for saving the entire workbook" (!persisted && (← filePath.get) == "" && (← model.get).book != (← saved.get))
    check "Save dialog permits both native and CSV filename extensions" ((← tk #["dict","get",← tk #["set","::saveOptions"],"-filetypes"]) == "{{Workbook or CSV} {.lcalc .csv}} {{All files} {*}}")
    cmd #["set","::saveTestPath",native]
    let persisted ← saveFile true
    let bytes ← IO.FS.readBinFile native
    check "Native Save As still persists all sheets and marks the workbook saved" (persisted && (Phase2.decodeBook (← IO.FS.readFile native)).toOption == some ((← model.get).book,0) && (← saved.get) == (← model.get).book)
    dispatch #["type","=3+4"]
    cmd #["set","::saveTestPath",upper]
    discard <| saveFile true
    check "Uppercase CSV extension also exports and commits the pending draft" ((← IO.FS.readFile upper) == "7,\"a,\"\"λ\"\"\"\r\n" && (← model.get).sheet[0]! == "=3+4")
    check "CSV export preserves the native path and conflict baseline" ((← filePath.get) == native && (← original.get) == some bytes && (← IO.FS.readBinFile native) == bytes)
    check "CSV export preserves formulas, other sheets, and unsaved changes" ((← model.get).book.size == 2 && (← model.get).sheet[0]! == "=3+4" && (← saved.get) != (← model.get).book)
    let persisted ← saveFile false
    check "Save after CSV export still updates the native workbook" (persisted && (Phase2.decodeBook (← IO.FS.readFile native)).toOption == some ((← model.get).book,0))
    cmd #["set","::saveTestPath",""]
    let cancelled ← saveFile true
    check "Cancelling Save As leaves existing files unchanged" (!cancelled && (← filePath.get) == native && (← IO.FS.readFile upper).startsWith "7,")
    filePath.set ""
    dispatch #["type","9"]
    cmd #["set","::saveTestPath",csv]
    let discarded ← mayDiscard
    check "CSV during save-before-close keeps the unsaved workbook open" (!discarded && (← model.get).sheet[0]! == "9" && (← model.get).book.size == 2)
    model.modify (fun m => {m with active:=1})
    refresh
    dispatch #["type","42"]
    discard <| saveFile true
    check "CSV Save As exports the active sheet rather than the first sheet" ((← IO.FS.readFile csv) == "42\r\n")
  finally
    for path in [base,csv,upper,native] do
      if ← (System.FilePath.mk path).pathExists then IO.FS.removeFile path
  script sheetTabsScript
  script sheetTabsTestAdapters
  model.set (singleModel emptySheet)
  selected.set 0
  refresh
  check "A workbook renders one visible named sheet tab" ((← tk #["set","::calcSheetNames"]) == "Sheet1" && (← tk #[".sheetbar.tabs.items.t0.label","cget","-text"]) == "Sheet1")
  dispatch #["addsheet","Annual total"]
  check "Adding a sheet creates its named tab and marks it active" ((← tk #["set","::calcSheetActive"]) == "1" && (← tk #[".sheetbar.tabs.items.t1.label","cget","-text"]) == "Annual total" && (← tk #[".sheetbar.tabs.items.t1.line","cget","-background"]) == "#217346")
  dispatch #["type","123"]
  cmd #[".sheetbar.tabs.items.t0.label","invoke"]
  check "Clicking a tab commits a pending draft and switches sheets" ((← model.get).active == 0 && (← model.get).book[1]!.cells[0]! == "123" && (← tk #["set","::calcSheetActive"]) == "0")
  check "Switching tabs removes the old active underline" ((← tk #[".sheetbar.tabs.items.t1.line","cget","-background"]) == "#f3f5f4")
  cmd #["set","::tabWrites","0"]
  dispatch #["right"]
  dispatch #["left"]
  check "Cell navigation leaves unchanged sheet tabs untouched" ((← tk #["set","::tabWrites"]) == "0")
  let name := "λ; $data {ok}"
  dispatch #["renamesheet",name]
  check "Renaming a sheet updates its tab with literal Unicode and punctuation" ((← tk #[".sheetbar.tabs.items.t0.label","cget","-text"]) == name)
  dispatch #["deletesheet"]
  check "Deleting a sheet removes its tab and selects the remaining sheet" ((← tk #["set","::calcSheetNames"]) == "{Annual total}" && (← tk #["winfo","exists",".sheetbar.tabs.items.t1"]) == "0")
  dispatch #["undo"]
  check "Undo restores deleted sheet tabs and the active indicator" ((← tk #["llength",← tk #["set","::calcSheetNames"]]) == "2" && (← tk #["set","::calcSheetActive"]) == toString (← model.get).active)
  IO.println s!"{← passed.get} save-and-tabs checks passed (headless widget adapters)."

def stage3InteractionTests : IO Unit := do
  setupPerformanceTest
  model.set (singleModel (put (put (put (put emptySheet 0 "2") 1 "second") 26 "1") 27 "first"))
  selected.set 0
  refresh
  dispatch #["format","currency"]
  check "Format command updates display without changing the formula source" ((← tk #["set","::calcDisplay"]) == "$2.00" && (← model.get).sheet[0]! == "2")
  dispatch #["format","font:mono"]
  check "Font command persists a cell font choice" ((Presentation.styleAt (← model.get).book[0]! 0).fontFamily == "mono")
  selectionAnchor.set (some 1)
  selected.set 26
  refresh
  dispatch #["sortup"]
  check "Sort command moves selected rows and their formats" ((← model.get).sheet[1]! == "first" && (Presentation.styleAt (← model.get).book[0]! 26).numberFormat == "currency")
  dispatch #["undo"]
  check "Undo command restores the original row order" ((← model.get).sheet[1]! == "second")
  dispatch #["find","FIRST"]
  check "Find command selects matching cell text" ((← selected.get) == 27)
  dispatch #["filter","first"]
  check "Filter command records a temporary view without changing contents" ((← filterText.get) == "first" && (← model.get).sheet[1]! == "second")
  dispatch #["clearfilter"]
  dispatch #["expand"]
  dispatch #["select","999","26"]
  dispatch #["type","=SUM(A1:A2)"]
  dispatch #["apply"]
  check "Expanded-grid commands edit and calculate cell Z1000" ((← model.get).sheet.size == 26000 && (← tk #["set","::calcDisplay"]) == "3" && (← selected.get) == 25999)
  dispatch #["down"]
  check "Expanded-grid navigation stops at the actual sheet boundary" ((← selected.get) == 25999 && (← filterText.get) == "")
  IO.println s!"{← passed.get} Phase 3 interaction checks passed."

def featureInteractionTests : IO Unit := do
  setupPerformanceTest
  script objectUIScript
  script "proc calcObjectsStart {name} {}; proc calcObjectPage {index title} {return .objects.p$index}; proc canvas {name args} {interp alias {} $name {} noop}; proc pack {args} {}; namespace eval ttk {}; proc ttk::label {args} {}; proc calcObjectImage {frame data} {set ::imageData $data}"
  let cells := put (put emptySheet 0 "2") 26 "4"
  model.set (singleModel cells); selected.set 26; selectionAnchor.set (some 0); refresh
  dispatch #["name","Revenue"]
  check "Named-range menu saves the selected rectangle" ((← model.get).book[0]!.objects[0]!.last == 26)
  dispatch #["function","DOUBLE(X)=X*2"]
  check "Custom-function menu defines a callable function" (Phase2.cellDisplay (Phase2.editCell (← model.get) 1 "=DOUBLE(SUM(Revenue))").book 0 1 == "12")
  dispatch #["validation","Bounded","number,0,10"]
  cmd #["set","::calcDraft","11"]
  let failed ← try commit; pure false catch _ => pure true
  check "Rejected cell validation preserves the workbook and draft" (failed && (← model.get).sheet[26]! == "4" && (← tk #["set","::calcDraft"]) == "11")
  dispatch #["cancel"]
  dispatch #["condition","Positive",">,0,green"]
  check "Conditional-format menu paints matching cells" ((← paintedConditions.get).length == 2)
  dispatch #["chart","Revenue chart","bar"]
  check "Chart menu stores a source range and renders through canvas commands" ((← model.get).book[0]!.objects[4]!.kind == "chart")
  dispatch #["undo"]
  check "Undo removes a newly inserted chart" ((← model.get).book[0]!.objects.size == 4)
  dispatch #["redo"]
  dispatch #["removeobject","5"]
  check "Object removal uses one reversible workbook edit" ((← model.get).book[0]!.objects.size == 4)
  IO.FS.withTempDir fun dir => do
    let path := (dir / "functions.json").toString
    dispatch #["exportfunctions",path]
    model.set (singleModel emptySheet); selected.set 0; selectionAnchor.set none; refresh
    dispatch #["importfunctions",path]
    check "Function-pack menus round-trip declarative definitions" (Phase2.cellDisplay (Phase2.editCell (← model.get) 0 "=DOUBLE(7)").book 0 0 == "14")
  script "set bytes [binary decode base64 iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGMQa83+DwADwQIGhkJ1vwAAAABJRU5ErkJggg==]; calcCheckPNG $bytes"
  check "PNG preflight accepts a small valid header" true
  let bad ← tk #["catch","calcCheckPNG not-a-png"]
  check "PNG preflight rejects non-image input" (bad == "1")
  let tooBig ← tk #["catch","calcCheckPNG [string replace $bytes 16 23 [binary format II 100000 100000]]"]
  check "PNG preflight rejects excessive decoded dimensions" (tooBig == "1")
  let s := put (put (put (put emptySheet 0 "Group") 1 "Value") 26 "A") 27 "3"
  model.set (singleModel s); selected.set 27; selectionAnchor.set (some 0); refresh
  dispatch #["pivot","Summary","A,B,SUM"]
  check "Pivot menu creates and activates a summary sheet" ((← model.get).active == 1 && Phase2.cellDisplay (← model.get).book 1 27 == "3")
  dispatch #["refreshpivot"]
  check "An unchanged pivot refresh does not add undo history" ((← model.get).undo.length == 1)
  IO.println s!"{← passed.get} Phase 5 interaction checks passed."

def documentOpenTests : IO Unit := do
  setupPerformanceTest
  script "proc raise {args} {}; set ::openAnswer cancel; set ::openMessages {}; proc tk_messageBox {args} {lappend ::openMessages $args; return $::openAnswer}; proc tk_getSaveFile {args} {return {}}"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    let a := (dir / "Annual λ $[set injected 1] {draft};.lcalc").toString
    let b := (dir / "second.lcalc").toString
    let bad := (dir / "broken.lcalc").toString
    let csv := (dir / "values.CSV").toString
    let ods := (dir / "sheet.ods").toString
    let ba := Phase2.singleBook (put emptySheet 0 "12")
    let bb := Phase2.singleBook (put emptySheet 0 "34")
    IO.FS.writeFile a (Phase2.encodeBook ba 0)
    IO.FS.writeFile b (Phase2.encodeBook bb 0)
    IO.FS.writeFile bad "not a workbook"
    IO.FS.writeFile csv "Value,Formula\r\n5,=2+2\r\n"
    IO.FS.writeBinFile ods (← OpenDocument.bytes bb)
    model.set {}; saved.set (Phase2.singleBook emptySheet); selected.set 0; refresh
    cmd #["::tk::mac::OpenDocument",a]
    cmd #["update","idletasks"]
    check "Finder open requests wait until the interface is ready" ((← model.get).sheet[0]! == "" && (← tk #["llength",← tk #["set","::calcDocumentBatches"]]) == "1")
    cmd #["calcDocumentsReady"]
    cmd #["update","idletasks"]
    check "Queued Finder requests open a native workbook after startup" ((← model.get).book == ba && (← filePath.get) == a)
    check "Dropped paths preserve Unicode spaces and Tcl metacharacters" ((← tk #["info","exists","injected"]) == "0")
    cmd #["set","::calcDraft","99"]
    cmd #["::tk::mac::OpenDocument",b]
    cmd #["update","idletasks"]
    check "Cancel keeps pending edits when another file is dropped" ((← model.get).sheet[0]! == "99" && (← filePath.get) == a)
    check "Cancelled drops do not overwrite the original file" ((← IO.FS.readFile a) == Phase2.encodeBook ba 0)
    cmd #["set","::openAnswer","no"]
    cmd #["::tk::mac::OpenDocument",b]
    cmd #["update","idletasks"]
    check "Discard opens a file dropped onto a running app" ((← model.get).book == bb && (← model.get).undo.isEmpty)
    let before ← model.get
    let failed ← try dispatch #["opendocuments",bad]; pure false catch _ => pure true
    check "Invalid dropped workbooks leave the current workbook intact" (failed && (← model.get).book == before.book && (← filePath.get) == b)
    let failed ← try dispatch #["opendocuments",(dir / "missing.lcalc").toString]; pure false catch _ => pure true
    check "Missing dropped files leave the current workbook intact" (failed && (← model.get).book == before.book)
    let failed ← try dispatch #["opendocuments",a,b]; pure false catch _ => pure true
    check "Multiple-file drops are rejected without silently replacing workbooks" (failed && (← model.get).book == before.book)
    let failed ← try dispatch #["opendocuments","unsupported.xlsx"]; pure false catch _ => pure true
    check "Unsupported file types receive a clear rejection" failed
    dispatch #["opendocuments",csv]
    check "Dropped CSV files import as new unsaved workbooks" ((← filePath.get) == "" && (← original.get).isNone && (← saved.get).isEmpty && (← model.get).sheet[26]! == "5")
    check "Dropped CSV formula-looking fields remain literal text" ((← model.get).sheet[27]! == "'=2+2")
    cmd #["set","::openAnswer","yes"]
    dispatch #["opendocuments",a]
    check "Cancelling Save As cancels the document switch" ((← filePath.get) == "" && (← model.get).sheet[26]! == "5")
    cmd #["set","::openAnswer","no"]
    dispatch #["opendocuments",ods]
    check "Dropped ODS files import without becoming the native Save target" ((← model.get).sheet[0]! == "34" && (← filePath.get) == "" && (← saved.get).isEmpty)
    cmd #["set","::calcDocumentsBusy","1"]
    cmd #["::tk::mac::OpenDocument",a]
    cmd #["update","idletasks"]
    check "Document events cannot reenter an in-progress open dialog" ((← model.get).sheet[0]! == "34" && (← tk #["set","::calcDocumentsScheduled"]) == "0")
    cmd #["set","::calcDocumentsBusy","0"]
    cmd #["calcScheduleDocuments"]
    cmd #["update","idletasks"]
    check "Deferred document events resume after the current operation" ((← model.get).book == ba)
    cmd #["set","::calcDraft","88"]
    cmd #["set","::openAnswer","yes"]
    dispatch #["opendocuments",b]
    let (savedA,_) ← unwrap (Phase2.decodeBook (← IO.FS.readFile a))
    check "Save-before-open persists edits before installing the dropped workbook" (savedA[0]!.cells[0]! == "88" && (← model.get).book == bb)
  IO.println s!"{← passed.get} document-open checks passed."

def main (args : List String) : IO UInt32 := do
  try
    if args.contains "--version" || args.contains "--help" then
      IO.println "LeanCalc 0.5.1 | Lean -> C -> native macOS\nUsage: LeanCalc [sheet.lcalc] | --math-test | --stage3-test | --ods-test | --stage3-benchmark | --save-tabs-test | --self-test | --formula-picking-test | --phase2-self-test | --phase2-interaction-test | --interaction-self-test | --performance-self-test | --navigation-benchmark | --gui-self-test | --gui-render-benchmark"
      return 0
    if args.contains "--document-open-test" then documentOpenTests; return 0
    if args.contains "--phase2-interaction-test" then phase2InteractionTests; return 0
    if args.contains "--stage3-interaction-test" then stage3InteractionTests; return 0
    if args.contains "--ods-test" then InterchangeTests.run; return 0
    if args.contains "--stage3-benchmark" then InterchangeTests.benchmark; return 0
    if args.contains "--stage3-test" then Stage3Tests.run; return 0
    if args.head? == some "--ods-inspect" && args.length == 2 then
      let book ← OpenDocument.read args[1]!
      let sheets := book.mapIdx fun si s => Json.mkObj [("name",toJson s.name),("cells",toJson (s.cells.entries.toList.map fun (i,_) => (address i,Phase2.cellDisplay book si i)))]
      IO.println (toJson sheets).pretty
      return 0
    if args.contains "--features-interaction-test" then featureInteractionTests; return 0
    if args.contains "--features-test" then FeatureTests.run; return 0
    if args.contains "--math-test" then AdvancedTests.run; return 0
    if args.contains "--save-tabs-test" then saveTabsTests; return 0
    if args.contains "--formula-picking-test" then formulaPickingTests; return 0
    if args.contains "--phase2-self-test" then Phase2Tests.run; return 0
    if args.contains "--self-test" then selfTests; return 0
    if args.contains "--navigation-benchmark" then navigationBenchmark; return 0
    if args.contains "--performance-self-test" then performanceTests; return 0
    if args.contains "--interaction-self-test" then interactionTests; return 0
    if args.contains "--gui-self-test" then guiTests; return 0
    if args.contains "--gui-render-benchmark" then guiRenderBenchmark; return 0
    if args.length > 1 then throw <| IO.userError "Open one .lcalc file at a time."
    if let some path := args.head? then loadFile path
    tkInit true
    setupUI
    cmd #["calcDocumentsReady"]
    tkLoop
    return 0
  catch e => IO.eprintln (toString e); return 1
