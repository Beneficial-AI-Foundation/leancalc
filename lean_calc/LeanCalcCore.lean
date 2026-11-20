import SparseGrid
import Init.Data.Rat
open Lean

/- Phase 1: all spreadsheet semantics, persistence and UI commands live in Lean.
   The C bridge supplies Tcl/Tk widgets and atomic file replacement only. -/
def rowCount : Nat := 100
def colCount : Nat := 26
def emptySheet : Sheet := Sheet.blank (rowCount * colCount)
def trim (s : String) := s.trimAscii.toString
def address (i : Nat) : String := String.singleton (Char.ofNat (65 + i % 26)) ++ toString (i / 26 + 1)
def parseAddress (s : String) : Option Nat := do
  let cs := (trim s).toUpper.toList
  let c ← cs.head?
  let r ← (String.ofList cs.tail).toNat?
  if c < 'A' || c > 'Z' || r == 0 || r > rowCount then none
  else some ((r-1)*26 + c.toNat-65)
def put (s : Sheet) (i : Nat) (v : String) : Sheet := s.setIfInBounds i v

def decimal (s : String) : Option Rat := do
  let cs := (trim s).toList
  let neg := cs.head? == some '-'
  let cs := if neg || cs.head? == some '+' then cs.tail else cs
  let s := String.ofList cs
  let parts := s.splitOn "."
  if parts.length > 2 || !cs.any Char.isDigit || !cs.all (fun c => c.isDigit || c == '.') then none
  else
    let digits := String.ofList (cs.filter Char.isDigit)
    let n ← digits.toNat?
    let scale := if parts.length == 2 then parts[1]!.length else 0
    pure (mkRat (if neg then -(Int.ofNat n) else Int.ofNat n) (10^scale))

def showNumber (q : Rat) : String := Id.run do
  if q.den == 1 then return toString q.num
  let mut scale := 1
  for k in [1:11] do
    scale := scale * 10
    if scale % q.den == 0 then
      let digits := toString (q.num.natAbs * (scale / q.den))
      let padded := String.ofList (List.replicate (k+1-digits.length) '0') ++ digits
      let cs := padded.toList
      return (if q.num < 0 then "-" else "") ++ String.ofList (cs.take (cs.length-k)) ++ "." ++ String.ofList (cs.drop (cs.length-k))
  return toString q

inductive CalcExpr where
  | num : Rat → CalcExpr
  | ref : Nat → CalcExpr
  | neg : CalcExpr → CalcExpr
  | bin : Char → CalcExpr → CalcExpr → CalcExpr
  | sum : Nat → Nat → CalcExpr
  deriving Inhabited

-- Tokens never enter Tcl evaluation; formulas are parsed as data in Lean.
def tokenize (s : String) : Except String (List String) := do
  let mut out := []
  let mut word := ""
  for c in s.toList do
    if c.isAlphanum || c == '.' then word := word.push c
    else
      if word != "" then out := out ++ [word]; word := ""
      if !c.isWhitespace then
        if ['+','-','*','/','(',')',':'].contains c then out := out ++ [String.singleton c]
        else throw "#PARSE!"
  if word != "" then out := out ++ [word]
  return out

def priority (s : String) : Nat := if s == "+" || s == "-" then 1 else if s == "*" || s == "/" then 2 else 0
mutual
  def parseCalcExpr : Nat → Nat → List String → Except String (CalcExpr × List String)
    | 0, _, _ => .error "#LIMIT!"
    | fuel+1, p, ts => do
      let (a, rest) ← parseAtom fuel ts
      parseTail fuel p a rest
  def parseAtom : Nat → List String → Except String (CalcExpr × List String)
    | 0, _ => .error "#LIMIT!"
    | fuel+1, ts => do
      match ts with
      | "-" :: rest => let (a, rest) ← parseAtom fuel rest; return (.neg a, rest)
      | "+" :: rest => parseAtom fuel rest
      | "(" :: rest =>
        let (a, rest) ← parseCalcExpr fuel 1 rest
        match rest with
        | ")" :: rest => return (a, rest)
        | _ => throw "#PARSE!"
      | name :: "(" :: a :: ":" :: b :: ")" :: rest =>
        if name.toUpper != "SUM" then throw "#NAME?"
        let some a := parseAddress a | throw "#REF!"
        let some b := parseAddress b | throw "#REF!"
        return (.sum a b, rest)
      | t :: rest =>
        if let some n := decimal t then return (.num n, rest)
        if let some i := parseAddress t then return (.ref i, rest)
        throw (if t.toList.any Char.isDigit then "#REF!" else "#NAME?")
      | [] => throw "#PARSE!"
  def parseTail : Nat → Nat → CalcExpr → List String → Except String (CalcExpr × List String)
    | 0, _, _, _ => .error "#LIMIT!"
    | fuel+1, p, a, ts => do
      match ts with
      | op :: rest =>
        if priority op < p || priority op == 0 then return (a, ts)
        let (b, rest) ← parseCalcExpr fuel (priority op + 1) rest
        parseTail fuel p (.bin (op.toList.head!) a b) rest
      | [] => return (a, [])
end

def parseFormula (s : String) : Except String CalcExpr := do
  if s.length > 512 then throw "#LIMIT!"
  let tokens ← tokenize s
  let (a, rest) ← parseCalcExpr 128 1 tokens
  if !rest.isEmpty then throw "#PARSE!"
  return a

def rangeCells (a b : Nat) : List Nat :=
  (List.range (max (a/26) (b/26) - min (a/26) (b/26) + 1)).flatMap fun r =>
    (List.range (max (a%26) (b%26) - min (a%26) (b%26) + 1)).map fun c =>
      (min (a/26) (b/26)+r)*26 + min (a%26) (b%26)+c

-- Shared work budget bounds branching dependencies as well as recursion depth.
abbrev Eval := StateT Nat (Except String)
def tick : Eval Unit := do
  let n ← get
  if n == 0 then throw "#LIMIT!"
  set (n-1)
mutual
  def evalCell : Nat → Sheet → List Nat → Nat → Eval Rat
    | 0, _, _, _ => throw "#LIMIT!"
    | fuel+1, s, seen, i => do
      tick
      if i >= s.size then throw "#REF!"
      if seen.contains i then throw "#CYCLE!"
      let raw := trim s[i]!
      if raw == "" then return 0
      if raw.startsWith "=" then
        let e ← match parseFormula (String.ofList raw.toList.tail) with
          | .ok e => pure e
          | .error e => throw e
        evalCalcExpr fuel s (i::seen) e
      else
        let some n := decimal raw | throw "#VALUE!"
        return n
  def evalCalcExpr : Nat → Sheet → List Nat → CalcExpr → Eval Rat
    | 0, _, _, _ => throw "#LIMIT!"
    | fuel+1, s, seen, e => do
      tick
      match e with
      | .num n => return n
      | .ref i => evalCell fuel s seen i
      | .neg e => return -(← evalCalcExpr fuel s seen e)
      | .bin op a b =>
        let x ← evalCalcExpr fuel s seen a
        let y ← evalCalcExpr fuel s seen b
        match op with
        | '+' => return x+y
        | '-' => return x-y
        | '*' => return x*y
        | _ => if y == 0 then throw "#DIV/0!" else return x/y
      | .sum a b =>
        let mut total : Rat := 0
        for i in rangeCells a b do
          let raw := trim s[i]!
          -- SUM skips literal text, but propagates formula errors.
          if raw == "" || raw.startsWith "=" || (decimal raw).isSome then
            total := total + (← evalCell fuel s seen i)
        return total
end

def value (s : Sheet) (i : Nat) : Except String Rat := (evalCell 128 s [] i).run' 20000
def display (s : Sheet) (i : Nat) : String :=
  let raw := s[i]?.getD ""
  if (trim raw).startsWith "=" then
    match value s i with | .ok n => showNumber n | .error e => e
  else if raw.startsWith "'" then String.ofList raw.toList.tail else raw

structure FileData where
  format : String := "LeanCalc-1"
  cells : Array String
  deriving ToJson, FromJson

def encode (s : Sheet) : String := (toJson ({cells := s} : FileData)).compress
def decode (s : String) : Except String Sheet := do
  let json ← Json.parse s
  let doc : FileData ← fromJson? json
  if doc.format != "LeanCalc-1" then throw "Unsupported LeanCalc file version."
  if doc.cells.size != 2600 then throw "Expected 100 rows by 26 columns."
  if doc.cells.any (fun s => s.length > 4096 || s.contains '\u0000') then throw "Cell exceeds 4096 characters or contains NUL."
  return doc.cells

