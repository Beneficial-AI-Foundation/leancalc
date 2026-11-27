import MathFunctions
open Lean
namespace Phase2

structure CellStyle where
  cell : Nat
  numberFormat : String := "general"
  bold : Bool := false
  fontFamily : String := "default"
  fontSize : Nat := 13
  deriving Inhabited, BEq, ToJson, FromJson
structure ColumnStyle where
  column : Nat
  width : Nat := 105
  alignment : String := "w"
  deriving Inhabited, BEq, ToJson, FromJson
-- Versioned, declarative workbook objects. No object executes external code.
structure SheetObject where
  kind : String
  title : String
  first : Nat := 0
  last : Nat := 0
  options : Array String := #[]
  data : String := ""
  deriving Inhabited, BEq, ToJson, FromJson
structure NamedSheet where
  name : String := "Sheet1"
  cells : Sheet := emptySheet
  styles : Array CellStyle := #[]
  columns : Array ColumnStyle := #[]
  objects : Array SheetObject := #[]
  deriving Inhabited, BEq, ToJson, FromJson
abbrev Book := Array NamedSheet
def singleBook (s : Sheet := emptySheet) : Book := #[{cells:=s}]
def sheetIndex (b : Book) (name : String) : Option Nat :=
  (List.range b.size).find? (fun i => b[i]!.name.toLower == name.toLower)
def validName (s : String) : Bool :=
  s == trim s && s.length > 0 && s.length <= 31 &&
  !s.toList.any (fun c => c.toNat < 32 || "[]:*?/\\".contains c)
def validCell (s : String) := s.length <= 4096 && !s.contains '\u0000'

structure Ref where
  sheet : Option String := none
  row : Nat
  col : Nat
  absRow : Bool := false
  absCol : Bool := false
  deriving Inhabited, BEq

def quoteName (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"
def refText (r : Ref) : String :=
  (r.sheet.map (fun n => quoteName n ++ "!")).getD "" ++
  (if r.absCol then "$" else "") ++ String.singleton (Char.ofNat (65+r.col)) ++
  (if r.absRow then "$" else "") ++ toString (r.row+1)

-- The lexer keeps quoted strings and sheet qualifiers intact. Rewriters only
-- touch reference tokens, never text inside a quoted string.
def tokens (s : String) : Except String (List String) := do
  let mut out : Array String := #[]
  let mut word := ""
  let mut quote : Option Char := none
  let mut cs := s.toList
  while !cs.isEmpty do
    let c := cs.head!
    cs := cs.tail
    if let some q := quote then
      word := word.push c
      if c == q then
        if cs.head? == some q then word := word.push q; cs := cs.tail
        else quote := none
    else if c == '\'' || c == '"' then
      word := word.push c
      quote := some c
    else if c.isWhitespace then
      if word != "" then out := out.push word; word := ""
    else if (c == '+' || c == '-') && (word.endsWith "e" || word.endsWith "E") &&
        (decimal (String.ofList (word.toList.take (word.length-1)))).isSome then
      word := word.push c
    else if "+-*/^%(),:<>=".contains c then
      if word != "" then out := out.push word; word := ""
      let mut op := String.singleton c
      if (c == '<' || c == '>') && cs.head? == some '=' then
        op := op ++ "="; cs := cs.tail
      else if c == '<' && cs.head? == some '>' then op := "<>"; cs := cs.tail
      out := out.push op
    else word := word.push c
  if quote.isSome then throw "#PARSE!"
  if word != "" then out := out.push word
  return out.toList

def parseRef (s : String) : Option Ref := do
  let parts := s.splitOn "!"
  let (name, cell) ← match parts with
    | [c] => some (none, c)
    | _::_::_ =>
      let n := String.intercalate "!" (parts.take (parts.length-1))
      let c := parts.getLast!
      let n := if n.startsWith "'" && n.endsWith "'" then
        String.ofList (n.toList.drop 1 |>.take (n.length-2)) |>.replace "''" "'" else n
      if validName n then some (some n,c) else none
    | _ => none
  let mut cs := cell.toUpper.toList
  let ac := cs.head? == some '$'
  if ac then cs := cs.tail
  let col ← cs.head?
  if col < 'A' || col > 'Z' then none else do
    cs := cs.tail
    let ar := cs.head? == some '$'
    if ar then cs := cs.tail
    let row ← (String.ofList cs).toNat?
    if row == 0 || row > 1000 then none
    else some {sheet:=name, row:=row-1, col:=col.toNat-65, absCol:=ac, absRow:=ar}

inductive Expr where
  | named : String → Expr
  | num : Rat → Expr
  | text : String → Expr
  | ref : Ref → Expr
  | range : Ref → Ref → Expr
  | neg : Expr → Expr
  | bin : String → Expr → Expr → Expr
  | call : String → List Expr → Expr
  | err : String → Expr
  deriving Inhabited

def prec (s : String) := if ["=","<>","<",">","<=",">="].contains s then 1
  else if s == "+" || s == "-" then 2 else if s == "*" || s == "/" then 3 else if s == "^" then 4 else 0
mutual
 def parseExpr : Nat → Nat → List String → Except String (Expr × List String)
  | 0,_,_ => .error "#LIMIT!"
  | fuel+1,p,ts => do
    let (a,rest) ← atom fuel ts
    tailExpr fuel p a rest
 def atom : Nat → List String → Except String (Expr × List String)
  | 0,_ => .error "#LIMIT!"
  | fuel+1,ts => do
    match ts with
    | "-"::rest => let (e,rest) ← atom fuel rest; return (.neg e,rest)
    | "+"::rest => atom fuel rest
    | "("::rest =>
      let (e,rest) ← parseExpr fuel 1 rest
      match rest with | ")"::rest => return (e,rest) | _ => throw "#PARSE!"
    | name::"("::rest =>
      let (args,rest) ← arguments fuel rest
      if name.toUpper == "IF" && args.length != 3 then throw "#PARSE!"
      return (.call name.toUpper args,rest)
    | a::":"::b::rest =>
      let some a := parseRef a | throw "#REF!"
      let some b := parseRef b | throw "#REF!"
      let b := if b.sheet.isNone then {b with sheet:=a.sheet} else b
      return (.range a b,rest)
    | t::rest =>
      if t.startsWith "#" then return (.err t,rest)
      if t.startsWith "\"" && t.endsWith "\"" then
        return (.text ((String.ofList (t.toList.drop 1 |>.take (t.length-2))).replace "\"\"" "\""),rest)
      if t.toUpper == "TRUE" then return (.num 1,rest)
      if t.toUpper == "FALSE" then return (.num 0,rest)
      if let some n := MathFunctions.literal t then return (.num n,rest)
      if let some r := parseRef t then return (.ref r,rest)
      if t.toList.all (fun c => c.isAlpha || c == '_') && !t.isEmpty then
        return (.named t.toUpper,rest)
      throw (if t.toList.any Char.isDigit then "#REF!" else "#NAME?")
    | [] => throw "#PARSE!"
 def tailExpr : Nat → Nat → Expr → List String → Except String (Expr × List String)
  | 0,_,_,_ => .error "#LIMIT!"
  | fuel+1,p,a,ts => do
    match ts with
    | "%"::rest => tailExpr fuel p (.bin "/" a (.num 100)) rest
    | op::rest =>
      if prec op < p || prec op == 0 then return (a,ts)
      let (b,rest) ← parseExpr fuel (prec op+1) rest
      tailExpr fuel p (.bin op a b) rest
    | [] => return (a,[])
 def arguments : Nat → List String → Except String (List Expr × List String)
  | 0,_ => .error "#LIMIT!"
  | fuel+1,ts => do
    if ts.head? == some ")" then return ([],ts.tail)
    let (e,rest) ← parseExpr fuel 1 ts
    match rest with
    | ")"::rest => return ([e],rest)
    | ","::rest =>
      if rest.head? == some ")" then throw "#PARSE!"
      let (es,rest) ← arguments fuel rest
      return (e::es,rest)
    | _ => throw "#PARSE!"
end

def parse (s : String) : Except String Expr := do
  if s.length > 512 then throw "#LIMIT!"
  let (e,rest) ← parseExpr 128 1 (← tokens s)
  if !rest.isEmpty then throw "#PARSE!"
  return e
inductive Value where
  | number : Rat → Value
  | text : String → Value
  deriving Inhabited, BEq

def number : Value → Except String Rat
  | .number n => .ok n
  | .text _ => .error "#VALUE!"
def resolve (b : Book) (context : Nat) (r : Ref) : Except String (Nat × Nat) := do
  let si ← match r.sheet with
    | none => pure context
    | some name => match sheetIndex b name with | some i => pure i | none => throw "#REF!"
  if si >= b.size || r.row >= b[si]!.cells.size/26 || r.col >= 26 then throw "#REF!"
  return (si,r.row*26+r.col)

def objectNamed (b : Book) (kind name : String) : Option (Nat × SheetObject) :=
  (b.toList.zipIdx).findSome? fun (s,si) =>
    (s.objects.find? fun o => o.kind == kind && o.title.toUpper == name.toUpper).map (si,·)
def namedExpr (b : Book) (name : String) : Except String Expr := do
  let some (si,o) := objectNamed b "name" name | throw "#NAME?"
  let a : Ref := {sheet:=some b[si]!.name,row:=o.first/26,col:=o.first%26}
  let z : Ref := {sheet:=some b[si]!.name,row:=o.last/26,col:=o.last%26}
  return if o.first == o.last then .ref a else .range a z

def substitute (e : Expr) (parameters : Array String) (args : List Expr) : Expr :=
  match e with
  | .named n => match parameters.toList.idxOf? n with | some i => args[i]! | none => e
  | .neg a => .neg (substitute a parameters args)
  | .bin op a b => .bin op (substitute a parameters args) (substitute b parameters args)
  | .call n xs => .call n (xs.map fun x => substitute x parameters args)
  | _ => e

def functionExpr (b : Book) (name : String) (args : List Expr) : Except String Expr := do
  let some (_,o) := objectNamed b "function" name | throw "#NAME?"
  if args.length != o.options.size then throw "#VALUE!"
  return substitute (← parse o.data) o.options args

def equalValue (a b : Value) : Bool := match a,b with
  | .text x,.text y => x.toLower == y.toLower
  | _,_ => a == b
def matchesCriterion (v criterion : Value) : Bool := Id.run do
  if let .text s := criterion then
    let op := (["<=",">=","<>","<",">","="].find? (fun op => s.startsWith op)).getD "="
    let t := if s.startsWith op then s.drop op.length |>.toString else s
    if let some n := MathFunctions.literal t then
      if let .number x := v then
        return if op == "<" then x < n else if op == ">" then x > n else if op == "<=" then x <= n else if op == ">=" then x >= n else if op == "<>" then x != n else x == n
    return if op == "<>" then !equalValue v (.text t) else op == "=" && equalValue v (.text t)
  return equalValue v criterion

def rangeArgument (b : Book) (si : Nat) (e : Expr) : Except String (Nat × List Nat × Nat) := do
  let e ← match e with | .named n => namedExpr b n | _ => pure e
  match e with
  | .ref r => let (sh,i) ← resolve b si r; return (sh,[i],1)
  | .range a z =>
    let (sh,i) ← resolve b si a
    let (zh,j) ← resolve b si z
    if sh != zh then throw "#REF!"
    return (sh,rangeCells i j,max a.col z.col-min a.col z.col+1)
  | _ => throw "#VALUE!"
def leapYear (y : Nat) := y%4 == 0 && (y%100 != 0 || y%400 == 0)
def monthDays (y m : Nat) := if m == 2 then (if leapYear y then 29 else 28) else if [4,6,9,11].contains m then 30 else 31
def dateSerial (y m d : Nat) : Nat :=
  let years := (List.range (y-1900)).foldl (fun n i => n+(if leapYear (1900+i) then 366 else 365)) 0
  2+years+(List.range (m-1)).foldl (fun n i => n+monthDays y (i+1)) 0+d-1
def serialDate (serial : Nat) : Nat × Nat × Nat := Id.run do
  let mut days := serial-2
  let mut year := 1900
  for _ in [:8100] do
    let count := if leapYear year then 366 else 365
    if days < count then break
    days := days-count; year := year+1
  let mut month := 1
  for _ in [:12] do
    let count := monthDays year month
    if days < count then break
    days := days-count; month := month+1
  return (year,month,days+1)

def numericLiteral (s : String) := (MathFunctions.literal (trim s)).isSome
mutual
 def eval : Nat → Book → List (Nat × Nat) → Nat → Nat → Eval Value
  | 0,_,_,_,_ => throw "#LIMIT!"
  | fuel+1,b,seen,si,i => do
    tick
    if si >= b.size || i >= b[si]!.cells.size then throw "#REF!"
    if seen.contains (si,i) then throw "#CYCLE!"
    let raw := b[si]!.cells[i]!
    let t := trim raw
    if t == "" then return .number 0
    if t.startsWith "=" then
      let e ← parse (String.ofList t.toList.tail)
      evalExpr fuel b ((si,i)::seen) si e
    else if raw.startsWith "'" then return .text (String.ofList raw.toList.tail)
    else if let some n := MathFunctions.literal t then return .number n
    else return .text raw
 def evalExpr : Nat → Book → List (Nat × Nat) → Nat → Expr → Eval Value
  | 0,_,_,_,_ => throw "#LIMIT!"
  | fuel+1,b,seen,si,e => do
    tick
    match e with
    | .named n => evalExpr fuel b seen si (← namedExpr b n)
    | .num n => return .number n
    | .text s => return .text s
    | .err s => throw s
    | .ref r => let (sh,i) ← resolve b si r; eval fuel b seen sh i
    | .range .. => throw "#VALUE!"
    | .neg e => return .number (-(← number (← evalExpr fuel b seen si e)))
    | .bin op a c =>
      let x ← evalExpr fuel b seen si a
      let y ← evalExpr fuel b seen si c
      if ["=","<>"].contains op then
        return .number (if (x == y) == (op == "=") then 1 else 0)
      let x ← number x
      let y ← number y
      if ["<",">","<=",">="].contains op then
        return .number (if (if op == "<" then x < y else if op == ">" then x > y else if op == "<=" then x <= y else x >= y) then 1 else 0)
      match op with
      | "^" => return .number (← MathFunctions.power x y)
      | "+" => return .number (x+y)
      | "-" => return .number (x-y)
      | "*" => return .number (x*y)
      | _ => if y == 0 then throw "#DIV/0!" else return .number (x/y)
    | .call "IF" args =>
      let n ← number (← evalExpr fuel b seen si args[0]!)
      evalExpr fuel b seen si (if n == 0 then args[2]! else args[1]!)
    | .call "IFERROR" args =>
      if args.length != 2 then throw "#VALUE!"
      try evalExpr fuel b seen si args[0]!
      catch _ => evalExpr fuel b seen si args[1]!
    | .call name args =>
      if ["LEN","LEFT","RIGHT","MID","UPPER","LOWER","TRIM","CONCATENATE","SUBSTITUTE"].contains name then
        let mut vs : List Value := []
        for a in args do vs := vs ++ [← evalExpr fuel b seen si a]
        let str := fun v => match v with | Value.text s => s | .number n => MathFunctions.display n
        let ss := vs.map str
        if name == "CONCATENATE" then return .text (String.join ss)
        if args.isEmpty then throw "#VALUE!"
        let t := ss[0]!
        if ["LEN","UPPER","LOWER","TRIM"].contains name then
          if args.length != 1 then throw "#VALUE!"
          return if name == "LEN" then .number (Rat.ofInt t.length) else .text (if name == "UPPER" then t.toUpper else if name == "LOWER" then t.toLower else String.intercalate " " ((t.splitOn " ").filter (· != "")))
        if name == "SUBSTITUTE" then
          if args.length != 3 || ss[1]! == "" then throw "#VALUE!"
          return .text (t.replace ss[1]! ss[2]!)
        let n : Rat ← if args.length < 2 then pure 1 else number vs[1]!
        if n < 0 || n.den != 1 || n > 1000000 then throw "#VALUE!"
        if name == "MID" then
          if args.length != 3 || n < 1 then throw "#VALUE!"
          let count ← number vs[2]!
          if count < 0 || count.den != 1 || count > 1000000 then throw "#VALUE!"
          return .text (String.ofList (t.toList.drop (n.num.toNat-1) |>.take count.num.toNat))
        if args.length > 2 then throw "#VALUE!"
        return .text (String.ofList (if name == "LEFT" then t.toList.take n.num.toNat else t.toList.drop (t.length-n.num.toNat)))
      if ["COUNTIF","SUMIF","AVERAGEIF","SUMPRODUCT","INDEX","MATCH","VLOOKUP"].contains name then
        if args.isEmpty then throw "#VALUE!"
        if name == "INDEX" then
          if args.length < 2 || args.length > 3 then throw "#VALUE!"
          let (sh,ids,width) ← rangeArgument b si args[0]!
          let row ← number (← evalExpr fuel b seen si args[1]!)
          let col ← if args.length == 3 then number (← evalExpr fuel b seen si args[2]!) else pure 1
          if row < 1 || col < 1 || row.den != 1 || col.den != 1 || col > Rat.ofInt width then throw "#REF!"
          let pos := (row.num.toNat-1)*width+col.num.toNat-1
          if pos >= ids.length then throw "#REF!"
          return ← eval fuel b seen sh ids[pos]!
        if name == "MATCH" || name == "VLOOKUP" then
          if (name == "MATCH" && args.length != 3) || (name == "VLOOKUP" && args.length != 4) then throw "#VALUE!"
          let needle ← evalExpr fuel b seen si args[0]!
          let (sh,ids,width) ← rangeArgument b si args[1]!
          let mode ← number (← evalExpr fuel b seen si args[args.length-1]!)
          if mode != 0 then throw "#N/A" -- exact matches are the declared subset
          if name == "MATCH" && width != 1 && ids.length != width then throw "#N/A"
          let column ← if name == "VLOOKUP" then number (← evalExpr fuel b seen si args[2]!) else pure 1
          if column < 1 || column.den != 1 || column > Rat.ofInt width then throw "#REF!"
          for pos in [:ids.length] do
            if name == "MATCH" || pos%width == 0 then
              let value ← eval fuel b seen sh ids[pos]!
              if equalValue value needle then
                if name == "MATCH" then return .number (Rat.ofInt (pos+1))
                return ← eval fuel b seen sh ids[pos+column.num.toNat-1]!
          throw "#N/A"
        let (sh,ids,width) ← rangeArgument b si args[0]!
        if args.length < 2 || args.length > (if name == "SUMPRODUCT" || name == "COUNTIF" then 2 else 3) then throw "#VALUE!"
        let criterion ← if name == "SUMPRODUCT" then pure (.number 0) else evalExpr fuel b seen si args[1]!
        let (vh,values,vwidth) ← if name == "SUMPRODUCT" then rangeArgument b si args[1]! else if args.length == 3 then rangeArgument b si args[2]! else pure (sh,ids,width)
        if values.length != ids.length || width != vwidth then throw "#VALUE!"
        let mut total : Rat := 0
        let mut count := 0
        for pos in [:ids.length] do
          let x ← eval fuel b seen sh ids[pos]!
          if name == "SUMPRODUCT" then
            let y ← eval fuel b seen vh values[pos]!
            if let .number a := x then
              if let .number c := y then total := total+a*c
          else if matchesCriterion x criterion then
            if name == "COUNTIF" then count := count+1
            else
              if b[vh]!.cells[values[pos]!]! != "" then
                let y ← eval fuel b seen vh values[pos]!
                if let .number n := y then total := total+n; count := count+1
        if name == "COUNTIF" then return .number (Rat.ofInt count)
        if name == "AVERAGEIF" && count == 0 then throw "#DIV/0!"
        return .number (if name == "AVERAGEIF" then total/Rat.ofInt count else total)
      if ["DATE","YEAR","MONTH","DAY"].contains name then
        let mut ns : List Rat := []
        for a in args do ns := ns ++ [← number (← evalExpr fuel b seen si a)]
        if ns.any (fun n => n.den != 1) then throw "#VALUE!"
        if name == "DATE" then
          if ns.length != 3 then throw "#VALUE!"
          let y := ns[0]!.num; let m := ns[1]!.num; let d := ns[2]!.num
          if y < 1900 || y > 9999 || m < 1 || m > 12 || d < 1 || d > Int.ofNat (monthDays y.toNat m.toNat) then throw "#NUM!"
          return .number (Rat.ofInt (dateSerial y.toNat m.toNat d.toNat))
        if ns.length != 1 || ns[0]! < 2 || ns[0]! > Rat.ofInt (dateSerial 9999 12 31) then throw "#NUM!"
        let (y,m,d) := serialDate ns[0]!.num.toNat
        return .number (Rat.ofInt (if name == "YEAR" then y else if name == "MONTH" then m else d))
      if !MathFunctions.supported name then
        return ← evalExpr fuel b seen si (← functionExpr b name args)
      if !MathFunctions.aggregateNames.contains name then
        let mut values := []
        for arg in args do
          values := values ++ [← number (← evalExpr fuel b seen si arg)]
        return .number (← MathFunctions.apply name values)
      let mut nums : List Rat := []
      for arg in args do
        let arg ← match arg with | .named n => namedExpr b n | _ => pure arg
        match arg with
        | .range a c =>
          let (sa,ia) ← resolve b si a
          let (sc,ic) ← resolve b si c
          if sa != sc then throw "#REF!"
          for i in rangeCells ia ic do
            let raw := trim b[sa]!.cells[i]!
            if raw != "" && (raw.startsWith "=" || numericLiteral raw) then
              let v ← eval fuel b seen sa i
              if let .number n := v then nums := n::nums
        | .ref r =>
          let (sh,i) ← resolve b si r
          let raw := trim b[sh]!.cells[i]!
          if raw != "" && (raw.startsWith "=" || numericLiteral raw) then
            let v ← eval fuel b seen sh i
            if let .number n := v then nums := n::nums
        | _ =>
          let v ← evalExpr fuel b seen si arg
          if let .number n := v then nums := n::nums
      let total := nums.foldl (·+·) 0
      let result ← match name with
        | "SUM" => pure total
        | "COUNT" => pure (Rat.ofInt (Int.ofNat nums.length))
        | "AVERAGE" => if nums.isEmpty then throw "#DIV/0!" else pure (total / Rat.ofInt (Int.ofNat nums.length))
        | "MIN" => pure (nums.foldl min (nums.headD 0))
        | "MAX" => pure (nums.foldl max (nums.headD 0))
        | _ => MathFunctions.apply name nums.reverse
      return .number result
end

def cellValue (b : Book) (si i : Nat) : Except String Value := (eval 128 b [] si i).run' 20000
def cellDisplay (b : Book) (si i : Nat) : String :=
  let raw := b[si]!.cells[i]!
  if !(trim raw).startsWith "=" then
    if raw.startsWith "'" then String.ofList raw.toList.tail else raw
  else match cellValue b si i with
    | .ok (.number n) => MathFunctions.display n
    | .ok (.text s) => s
    | .error e => e

-- Reference rewriting retains malformed formula text for user correction.
def rewrite (raw : String) (f : Ref → Option Ref) (rangeF : Ref → Ref → Option (Ref × Ref) := fun a b => do return (← f a, ← f b)) : String := Id.run do
  if !(trim raw).startsWith "=" then return raw
  let .ok ts := tokens (String.ofList (trim raw).toList.tail) | return raw
  let mut rest := ts
  let mut out := []
  while !rest.isEmpty do
    match rest with
    | a::":"::b::tail =>
      match parseRef a, parseRef b with
      | some ra, some rb =>
        let inherited := rb.sheet.isNone && ra.sheet.isSome
        let rb := if inherited then {rb with sheet:=ra.sheet} else rb
        let text := match rangeF ra rb with
          | none => "#REF!"
          | some (a,b) => refText a ++ ":" ++ refText (if inherited && a.sheet == b.sheet then {b with sheet:=none} else b)
        out := text::out
        rest := tail
      | _,_ => out := a::out; rest := rest.tail
    | t::tail =>
      out := (match parseRef t with | none => t | some r => (f r).map refText |>.getD "#REF!")::out
      rest := tail
    | [] => pure ()
  return "=" ++ String.join out.reverse

def shifted (r : Ref) (dr dc : Int) : Option Ref := do
  let row := Int.ofNat r.row + (if r.absRow then 0 else dr)
  let col := Int.ofNat r.col + (if r.absCol then 0 else dc)
  if row < 0 || row >= 1000 || col < 0 || col >= 26 then none
  else some {r with row:=row.toNat, col:=col.toNat}
def shiftFormula (raw : String) (dr dc : Int) := rewrite raw (fun r => shifted r dr dc)

structure Document where
  format : String := "LeanCalc-2"
  sheets : Book
  active : Nat := 0
  deriving Inhabited, ToJson, FromJson

/-- Strict base64 decoder (line breaks ignored); `none` on any malformed input. -/
def base64Decode (s : String) : Option ByteArray := Id.run do
  let digit (c : Char) : Option Nat :=
    if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
    else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
    else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
    else if c == '+' then some 62 else if c == '/' then some 63 else none
  let chars := (s.toList.filter (fun c => c != '\n' && c != '\r')).toArray
  if chars.size % 4 != 0 then return none
  let mut out := ByteArray.empty
  let mut i := 0
  while i < chars.size do
    let last := i + 4 == chars.size
    let pad := if last && chars[i+3]! == '=' then (if chars[i+2]! == '=' then 2 else 1) else 0
    let mut acc := 0
    for k in [:4] do
      let c := chars[i+k]!
      if k ≥ 4 - pad then
        if c != '=' then return none
        acc := acc * 64
      else
        match digit c with
        | some d => acc := acc * 64 + d
        | none => return none
    out := out.push (acc / 65536 % 256).toUInt8
    if pad < 2 then out := out.push (acc / 256 % 256).toUInt8
    if pad < 1 then out := out.push (acc % 256).toUInt8
    i := i + 4
  return some out

def crc32 (bytes : ByteArray) (start stop : Nat) : UInt32 := Id.run do
  let mut crc : UInt32 := 0xFFFFFFFF
  for i in [start:stop] do
    crc := crc ^^^ bytes[i]!.toUInt32
    for _ in [:8] do
      crc := if crc &&& 1 == 1 then (crc >>> 1) ^^^ 0xEDB88320 else crc >>> 1
  return crc ^^^ 0xFFFFFFFF

/-- Structural PNG check matching the GUI's `calcCheckPNG` limits: signature, IHDR first
with 1..4096 per side and ≤ 4 million pixels, every chunk in bounds with a valid CRC,
at least one IDAT, and IEND as the final chunk. Catches truncated or corrupted data. -/
def validPNG (data : String) : Bool := Id.run do
  let some bytes := base64Decode data | return false
  if bytes.size < 8 || bytes.size > 1400000 then return false
  let sig : List UInt8 := [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
  if (List.range 8).any (fun i => bytes[i]! != sig[i]!) then return false
  let be32 (p : Nat) : Nat := ((bytes[p]!.toNat * 256 + bytes[p+1]!.toNat) * 256 + bytes[p+2]!.toNat) * 256 + bytes[p+3]!.toNat
  let mut pos := 8
  let mut first := true
  let mut sawData := false
  while pos + 12 ≤ bytes.size do
    let len := be32 pos
    if pos + 12 + len > bytes.size then return false
    let kind := String.ofList ((List.range 4).map (fun k => Char.ofNat bytes[pos+4+k]!.toNat))
    if crc32 bytes (pos+4) (pos+8+len) != (be32 (pos+8+len)).toUInt32 then return false
    if first then
      if kind != "IHDR" || len != 13 then return false
      let w := be32 (pos+8)
      let h := be32 (pos+12)
      if w < 1 || h < 1 || w > 4096 || h > 4096 || w*h > 4000000 then return false
      first := false
    if kind == "IDAT" then sawData := true
    pos := pos + 12 + len
    if kind == "IEND" then return sawData && pos == bytes.size
  return false

def validateBook (b : Book) : Except String Unit := do
  if b.isEmpty || b.size > 32 then throw "A workbook needs 1 to 32 sheets."
  let mut names : List String := []
  let mut symbols : List String := []
  for s in b do
    if !validName s.name || names.contains s.name.toLower then throw "Invalid or duplicate sheet name."
    names := s.name.toLower::names
    if s.objects.size > 128 then throw "At most 128 objects per sheet."
    for o in s.objects do
      if !["name","validation","condition","chart","image","pivot","function"].contains o.kind || o.title.length == 0 || o.title.length > 80 || o.first >= s.cells.size || o.last >= s.cells.size || o.options.size > 32 || o.data.length > 2000000 then throw "Invalid workbook object."
      if o.kind == "name" || o.kind == "function" then
        let n := o.title.toUpper
        if !(n.toList.all fun c => c.isAlpha || c == '_') || ["TRUE","FALSE"].contains n || MathFunctions.supported n || symbols.contains n then throw "Names must be unique letters/underscores and cannot shadow built-in functions."
        symbols := n::symbols
        if o.kind == "function" then
          if o.options.isEmpty || o.options.size > 16 || o.options.toList.eraseDups.length != o.options.size || o.options.any (fun p => p.isEmpty || p != p.toUpper || !p.toList.all (fun c => c.isAlpha || c == '_')) then throw "Invalid function parameters."
          let _ ← parse o.data

    if s.styles.size > s.cells.size || s.columns.size > 26 then throw "Too many style records."
    for style in s.styles do
      if style.fontSize < 8 || style.fontSize > 32 || !["default","serif","mono"].contains style.fontFamily || style.cell >= s.cells.size || !["general","number","currency","percent","scientific","fraction","date"].contains style.numberFormat then throw "Invalid cell style."
    for col in s.columns do
      if col.column >= 26 || col.width < 35 || col.width > 600 || !["w","center","e"].contains col.alignment then throw "Invalid column style."
    for o in s.objects do
      if o.kind == "validation" then
        if o.options.isEmpty || !["number","whole","list"].contains o.options[0]! then throw "Unknown validation rule."
        if o.options[0]! == "list" then
          if o.options.size < 2 then throw "A list validation needs choices."
        else
          if o.options.size != 3 || (MathFunctions.literal o.options[1]!).isNone || (MathFunctions.literal o.options[2]!).isNone then throw "Validation needs numeric minimum and maximum."
          if (MathFunctions.literal o.options[1]!).getD 0 > (MathFunctions.literal o.options[2]!).getD 0 then throw "Minimum exceeds maximum."
        for i in rangeCells o.first o.last do
          if s.cells[i]! != "" then
            let si := (sheetIndex b s.name).getD 0
            let value ← cellValue b si i
            let valid := if o.options[0]! == "list" then (o.options.toList.drop 1).contains (cellDisplay b si i) else
              match value with
              | .number n => n >= (MathFunctions.literal o.options[1]!).getD 0 && n <= (MathFunctions.literal o.options[2]!).getD 0 && (o.options[0]! != "whole" || n.den == 1)
              | _ => false
            if !valid then throw ("Validation failed at " ++ s.name ++ "!" ++ address i ++ ": " ++ o.title)
      if o.kind == "condition" then
        if o.options.size != 3 || !["<",">","=","<=",">=","<>"].contains o.options[0]! || (MathFunctions.literal o.options[1]!).isNone || !["#fee2e2","#dcfce7","#fef3c7","#dbeafe"].contains o.options[2]! then throw "Invalid conditional format."
      if o.kind == "chart" && (o.options.size != 1 || !["bar","line"].contains o.options[0]!) then throw "Invalid chart type."
      if o.kind == "image" && !validPNG o.data then throw "Images must contain bounded PNG data."
      if o.kind == "pivot" && (o.options.size != 4 || !["SUM","COUNT","AVERAGE","MIN","MAX"].contains o.options[3]! || o.options[1]!.toNat?.isNone || o.options[2]!.toNat?.isNone) then throw "Invalid pivot definition."
    if (s.cells.size < 2600 || s.cells.size > 26000 || s.cells.size%26 != 0) || !s.cells.all validCell then throw "Invalid sheet dimensions or cell content."
structure SparseSheet where
  name : String
  rows : Nat
  entries : Array (Nat × String)
  styles : Array CellStyle := #[]
  columns : Array ColumnStyle := #[]
  deriving Inhabited, ToJson, FromJson
structure SparseDocument where
  format : String := "LeanCalc-3"
  sheets : Array SparseSheet
  active : Nat := 0
  deriving Inhabited, ToJson, FromJson

structure ExtendedSheet extends SparseSheet where
  objects : Array SheetObject := #[]
  deriving Inhabited, ToJson, FromJson
structure ExtendedDocument where
  format : String := "LeanCalc-4"
  sheets : Array ExtendedSheet
  active : Nat := 0
  deriving Inhabited, ToJson, FromJson

def encodeBook (b : Book) (active : Nat) : String :=
  if b.any (fun s => !s.objects.isEmpty) then
    let sheets := b.map fun s => ({name:=s.name,rows:=s.cells.size/26,entries:=s.cells.entries.toList.toArray,styles:=s.styles,columns:=s.columns,objects:=s.objects} : ExtendedSheet)
    (toJson ({sheets:=sheets,active:=active} : ExtendedDocument)).compress
  else if b.all (fun s => s.cells.size == 2600 && s.styles.isEmpty && s.columns.isEmpty) then
    (toJson ({sheets:=b,active:=active} : Document)).compress
  else
    let sheets := b.map fun s => ({name:=s.name, rows:=(s.cells.size/26), entries:=s.cells.entries.toList.toArray, styles:=s.styles,columns:=s.columns} : SparseSheet)
    (toJson ({sheets:=sheets,active:=active} : SparseDocument)).compress

structure LegacyNamedSheet where
  name : String
  cells : Sheet
  deriving FromJson
structure LegacyDocument where
  format : String
  sheets : Array LegacyNamedSheet
  active : Nat
  deriving FromJson

def decodeBook (text : String) : Except String (Book × Nat) := do
  let json ← Json.parse text
  let format : String ← (json.getObjValAs? String "format")
  if format == "LeanCalc-1" then return (singleBook (← decode text),0)
  if format == "LeanCalc-3" || format == "LeanCalc-4" then
    let extended : Option ExtendedDocument ← if format == "LeanCalc-4" then some <$> fromJson? json else pure none
    let d : SparseDocument ← match extended with
      | some d => pure {sheets:=d.sheets.map (·.toSparseSheet),active:=d.active}
      | none => fromJson? json
    if d.sheets.isEmpty || d.sheets.size > 32 || d.active >= d.sheets.size then throw "Invalid sheets or active sheet."
    let mut b := #[]
    for si in [:d.sheets.size] do
      let s := d.sheets[si]!
      if s.rows < 100 || s.rows > 1000 || s.entries.size > s.rows*26 then throw "Invalid sparse sheet dimensions."
      let mut cells := Sheet.blank (s.rows*26)
      let mut seen := Std.HashSet.emptyWithCapacity
      for (i,v) in s.entries do
        if i >= cells.size || seen.contains i || !validCell v then throw "Invalid or duplicate sparse cell."
        seen := seen.insert i
        cells := cells.set! i v
      b := b.push {name:=s.name,cells:=cells,styles:=s.styles,columns:=s.columns,objects:=(extended.map fun d => d.sheets[si]!.objects).getD #[]}
    validateBook b
    return (b,d.active)
  if format != "LeanCalc-2" then throw "Unsupported LeanCalc file version."
  let d : LegacyDocument ← fromJson? json
  let book : Book := d.sheets.map fun s => {name:=s.name,cells:=s.cells}
  validateBook book
  if d.active >= book.size then throw "Invalid active sheet."
  return (book,d.active)

structure Snapshot where
  book : Book := singleBook emptySheet
  active : Nat := 0
  deriving Inhabited, BEq
structure Model extends Snapshot where
  undo : List Snapshot := []
  redo : List Snapshot := []
  deriving Inhabited

def Model.sheet (m : Model) : Sheet := m.book[m.active]!.cells
def updateBook (m : Model) (b : Book) (active : Nat) : Model :=
  if b == m.book then {m with active:=active}
  else {book:=b,active:=active,undo:=(m.toSnapshot::m.undo).take 100,redo:=[]}
def editCell (m : Model) (i : Nat) (v : String) : Model :=
  if m.sheet[i]? == some v then m else
  updateBook m (m.book.setIfInBounds m.active {m.book[m.active]! with cells:=put m.sheet i v}) m.active
def undoModel (m : Model) : Model := match m.undo with
  | [] => m
  | s::rest => {toSnapshot:=s,undo:=rest,redo:=m.toSnapshot::m.redo}
def redoModel (m : Model) : Model := match m.redo with
  | [] => m
  | s::rest => {toSnapshot:=s,undo:=(m.toSnapshot::m.undo).take 100,redo:=rest}

def addSheet (m : Model) (name : String) : Except String Model := do
  if !validName name || (sheetIndex m.book name).isSome || m.book.size >= 32 then throw "Choose a unique sheet name (1-31 characters); at most 32 sheets."
  return updateBook m (m.book.push {name:=name}) m.book.size

def renameSheet (m : Model) (name : String) : Except String Model := do
  if !validName name then throw "Invalid sheet name."
  if let some i := sheetIndex m.book name then
    if i != m.active then throw "A sheet already has that name."
  let old := m.book[m.active]!.name
  let renameRef := fun (r : Ref) => some (if r.sheet.map String.toLower == some old.toLower then {r with sheet:=some name} else r)
  let b := m.book.map fun s => {s with
    objects:=s.objects.map fun o =>
      if o.kind == "pivot" && o.options[0]!.toLower == old.toLower then {o with options:=o.options.set! 0 name}
      else if o.kind == "function" then {o with data:=(rewrite ("="++o.data) renameRef).drop 1 |>.toString}
      else o
    name:=if s.name == old then name else s.name
    cells:=s.cells.map fun raw => rewrite raw (fun r => some (if r.sheet.map String.toLower == some old.toLower then {r with sheet:=some name} else r))}
  validateBook b
  return updateBook m b m.active

def deleteSheet (m : Model) : Except String Model := do
  if m.book.size == 1 then throw "Keep at least one sheet."
  let old := m.book[m.active]!.name
  let b := (m.book.filter (fun s => s.name != old)).map fun s => {s with cells:=s.cells.map fun raw => rewrite raw (fun r => if r.sheet.map String.toLower == some old.toLower then none else some r)}
  validateBook b
  return updateBook m b (min m.active (b.size-1))

structure Rect where
  top : Nat
  left : Nat
  bottom : Nat
  right : Nat
  deriving Inhabited, BEq

def rectangle (a b : Nat) : Rect := {top:=min (a/26) (b/26),left:=min (a%26) (b%26),bottom:=max (a/26) (b/26),right:=max (a%26) (b%26)}
def Rect.indices (r : Rect) := rangeCells (r.top*26+r.left) (r.bottom*26+r.right)
def Rect.contains (r : Rect) (i : Nat) := i/26 >= r.top && i/26 <= r.bottom && i%26 >= r.left && i%26 <= r.right

def clearRect (m : Model) (r : Rect) : Model := Id.run do
  let mut s := m.sheet
  for i in r.indices do s := put s i ""
  return updateBook m (m.book.set! m.active {m.book[m.active]! with cells:=s}) m.active

abbrev Table := Array (Array String)
def extract (s : Sheet) (r : Rect) : Table :=
  (List.range (r.bottom-r.top+1)).toArray.map fun row =>
    (List.range (r.right-r.left+1)).toArray.map fun col => s[(row+r.top)*26+col+r.left]!

def pasteTable (m : Model) (dest : Nat) (table : Table) (origin : Option (Nat × Nat) := none) : Except String Model := do
  if table.isEmpty || table[0]!.isEmpty then throw "Empty clipboard."
  let width := table[0]!.size
  if table.any (fun r => r.size != width || !r.all validCell) then throw "Invalid or uneven clipboard rows."
  if dest/26+table.size > m.sheet.size/26 || dest%26+width > 26 then throw "Paste would extend beyond the sheet."
  let mut s := m.sheet
  for row in [0:table.size] do
    for col in [0:width] do
      let raw := table[row]![col]!
      let v := match origin with
        | none => raw
        | some (r,c) => shiftFormula raw (Int.ofNat (dest/26)-r) (Int.ofNat (dest%26)-c)
      if !validCell v then throw "Adjusted formula exceeds the cell limit."
      s := put s ((dest/26+row)*26+dest%26+col) v
  let b := m.book.set! m.active {m.book[m.active]! with cells:=s}
  validateBook b
  return updateBook m b m.active

def fillRect (m : Model) (rect : Rect) (down : Bool) : Except String Model := do
  let mut table := extract m.sheet rect
  for row in [0:table.size] do
    for col in [0:table[0]!.size] do
      let raw := if down then table[0]![col]! else table[row]![0]!
      let raw := shiftFormula raw (if down then Int.ofNat row else 0) (if down then 0 else Int.ofNat col)
      table := table.set! row (table[row]!.set! col raw)
  let next ← pasteTable m (rect.top*26+rect.left) table
  let original := m.book[m.active]!.styles
  let mut styles := original.filter (fun st => !rect.contains st.cell)
  for i in rect.indices do
    let source := if down then rect.top*26+i%26 else i/26*26+rect.left
    if let some st := original.find? (·.cell == source) then styles := styles.push {st with cell:=i}
  return updateBook m (next.book.set! m.active {next.book[m.active]! with styles:=styles}) m.active

-- Deferred Cut: resolve every reference in its original context; references
-- into the moved block follow it, and outgoing references keep their targets.
def moveRect (m : Model) (sourceSheet : Nat) (rect : Rect) (dest : Nat) : Except String Model := do
  let table := extract m.book[sourceSheet]!.cells rect
  if dest/26+table.size > m.sheet.size/26 || dest%26+table[0]!.size > 26 then throw "Move would extend beyond the sheet."
  let target := m.active
  for context in [0:m.book.size] do
    for (_,raw) in m.book[context]!.cells.entries.toList do
      if (trim raw).startsWith "=" then
        if let .ok ts := tokens (String.ofList (trim raw).toList.tail) then
          let mut rest := ts
          while !rest.isEmpty do
            if let a::":"::c::_ := rest then
              if let some a := parseRef a then
                if let some c := parseRef c then
                  let c := if c.sheet.isNone then {c with sheet:=a.sheet} else c
                  if let .ok (sa,ia) := resolve m.book context a then
                    if let .ok (sc,ic) := resolve m.book context c then
                      if sa == sourceSheet && sc == sourceSheet then
                        let cells := rangeCells ia ic
                        if cells.any rect.contains && !cells.all rect.contains then
                          throw "Move would split a referenced range. Copy instead, or move its entire range."
            rest := rest.tail
  let transform := fun (oldContext newContext : Nat) (r : Ref) => do
    let (si,i) ← (resolve m.book oldContext r).toOption
    let moved := si == sourceSheet && rect.contains i
    let newSheet := if moved then target else si
    let row := if moved then dest/26+i/26-rect.top else r.row
    let col := if moved then dest%26+i%26-rect.left else r.col
    let qualifier := if r.sheet.isNone && newSheet == newContext then none else some m.book[newSheet]!.name
    some {r with sheet:=qualifier,row:=row,col:=col}
  let mut b := m.book.mapIdx fun si s => {s with cells:=s.cells.map fun raw => rewrite raw (transform si si)}
  let mut src := b[sourceSheet]!.cells
  for i in rect.indices do src := put src i ""
  b := b.set! sourceSheet {b[sourceSheet]! with cells:=src}
  let mut dst := b[target]!.cells
  for r in [0:table.size] do
    for c in [0:table[0]!.size] do
      dst := put dst ((dest/26+r)*26+dest%26+c) (rewrite table[r]![c]! (transform sourceSheet target))
  b := b.set! target {b[target]! with cells:=dst}
  let mut movedObjects := #[]
  let mut keptObjects := #[]
  let relocate := fun (i : Nat) => (dest/26+i/26-rect.top)*26+dest%26+i%26-rect.left
  for o in b[sourceSheet]!.objects do
    if o.kind != "function" && o.kind != "pivot" then
      let indices := rangeCells o.first o.last
      if indices.any rect.contains && !indices.all rect.contains then
        throw "Move would split a named range or sheet object. Move its whole range or copy the cells."
      if indices.all rect.contains then movedObjects := movedObjects.push {o with first:=relocate o.first,last:=relocate o.last}
      else keptObjects := keptObjects.push o
    else keptObjects := keptObjects.push o
  b := b.set! sourceSheet {b[sourceSheet]! with objects:=keptObjects}
  b := b.set! target {b[target]! with objects:=b[target]!.objects ++ movedObjects}
  for sh in [:b.size] do
    let mut objects := #[]
    for o in b[sh]!.objects do
      let mut o := o
      if o.kind == "pivot" && o.options[0]!.toLower == m.book[sourceSheet]!.name.toLower then
        let indices := rangeCells o.first o.last
        if indices.any rect.contains && !indices.all rect.contains then throw "Move would split a pivot source."
        if indices.all rect.contains then
          let gc := dest%26+(o.options[1]!.toNat?.getD 0)-rect.left
          let vc := dest%26+(o.options[2]!.toNat?.getD 0)-rect.left
          o := {o with first:=relocate o.first,last:=relocate o.last,options:=#[m.book[target]!.name,toString gc,toString vc,o.options[3]!]}
      objects := objects.push o
    b := b.set! sh {b[sh]! with objects:=objects}
  validateBook b
  return updateBook m b target

-- All references track structural changes, including absolute references.
def structureEdit (m : Model) (rows insert : Bool) (pos : Nat) : Except String Model := do
  let limit := if rows then m.sheet.size/26 else 26
  if pos >= limit then throw "Invalid row or column."
  let coord := fun (i : Nat) => if rows then i/26 else i%26
  if insert && (List.range m.sheet.size).any (fun i => coord i == limit-1 && m.sheet[i]! != "") then
    throw "Insertion would discard nonempty cells at the sheet edge."
  let belongs := fun (context : Nat) (r : Ref) => match resolve m.book context r with
    | .ok (s,_) => s == m.active | _ => false
  let setCoord := fun (r : Ref) (n : Nat) => if rows then {r with row:=n} else {r with col:=n}
  let getCoord := fun (r : Ref) => if rows then r.row else r.col
  let adjust := fun (context : Nat) (r : Ref) =>
    if !belongs context r then some r else
    let n := getCoord r
    if !insert && n == pos then none else
    let n := if insert && n >= pos then n+1 else if !insert && n > pos then n-1 else n
    if n >= limit then none else some (setCoord r n)
  let rangeAdjust := fun (context : Nat) (a b : Ref) => do
    if insert || !belongs context a || !belongs context b then return (← adjust context a, ← adjust context b)
    let lo := min (getCoord a) (getCoord b)
    let hi := max (getCoord a) (getCoord b)
    if lo == pos && hi == pos then none else do
      let nlo := if lo > pos then lo-1 else lo
      let nhi := if hi >= pos then hi-1 else hi
      let forward := getCoord a <= getCoord b
      some (setCoord a (if forward then nlo else nhi),setCoord b (if forward then nhi else nlo))
  let mut b := m.book.mapIdx fun context s => {s with cells:=s.cells.map fun raw => rewrite raw (adjust context) (rangeAdjust context)}
  let old := b[m.active]!.cells
  let mut next := Sheet.blank m.sheet.size
  for i in [0:m.sheet.size] do
    let n := coord i
    if !(insert && n == pos) && !(!insert && n == limit-1) then
      let srcCoord := if insert && n > pos then n-1 else if !insert && n >= pos then n+1 else n
      let j := if rows then srcCoord*26+i%26 else i/26*26+srcCoord
      next := put next i old[j]!
  let styles := b[m.active]!.styles.filterMap fun st => do
    let n := coord st.cell
    if (!insert && n == pos) || (insert && n == limit-1) then none else
      let dest := if insert && n >= pos then n+1 else if !insert && n > pos then n-1 else n
      some {st with cell:=if rows then dest*26+st.cell%26 else st.cell/26*26+dest}
  let columns := if rows then b[m.active]!.columns else b[m.active]!.columns.filterMap fun col =>
    if (!insert && col.column == pos) || (insert && col.column == 25) then none
    else some {col with column:=if insert && col.column >= pos then col.column+1 else if !insert && col.column > pos then col.column-1 else col.column}
  let objects := b[m.active]!.objects.filterMap fun o => do
    if o.kind == "function" || o.kind == "pivot" then return o
    let a : Ref := {row:=o.first/26,col:=o.first%26}
    let z : Ref := {row:=o.last/26,col:=o.last%26}
    let (a,z) ← rangeAdjust m.active a z
    return {o with first:=a.row*26+a.col,last:=z.row*26+z.col}
  b := b.set! m.active {b[m.active]! with cells:=next,styles:=styles,columns:=columns,objects:=objects}
  for sh in [:b.size] do
    let mut objects := #[]
    for o in b[sh]!.objects do
      let mut o := o
      if o.kind == "function" then
        o := {o with data:=(rewrite ("="++o.data) (adjust sh) (rangeAdjust sh)).drop 1 |>.toString}
      if o.kind == "pivot" && o.options[0]!.toLower == m.book[m.active]!.name.toLower then
        let gc := o.options[1]!.toNat?.getD 0
        let vc := o.options[2]!.toNat?.getD 0
        if !insert && ((rows && pos == o.first/26) || (!rows && (pos == gc || pos == vc))) then throw "Remove the pivot definition before deleting its header or key/value columns."
        let a : Ref := {row:=o.first/26,col:=o.first%26}
        let z : Ref := {row:=o.last/26,col:=o.last%26}
        let some (a,z) := rangeAdjust m.active a z | throw "Structural edit would discard a pivot source."
        let shift := fun n => if rows then n else if insert && n >= pos then n+1 else if !insert && n > pos then n-1 else n
        o := {o with first:=a.row*26+a.col,last:=z.row*26+z.col,options:=#[o.options[0]!,toString (shift gc),toString (shift vc),o.options[3]!]}
      objects := objects.push o
    b := b.set! sh {b[sh]! with objects:=objects}
  validateBook b
  return updateBook m b m.active

-- Strict CSV/TSV state machine, with quoted delimiters and embedded newlines.
def parseDelimited (text : String) (delimiter : Char) (maxRows : Nat := 100) : Except String Table := do
  let mut rows : Table := #[]
  let mut row : Array String := #[]
  let mut field := ""
  let mut quoted := false
  let mut closed := false
  let mut ended := false
  let mut cs := text.toList
  if cs.head? == some '\uFEFF' then cs := cs.tail
  while !cs.isEmpty do
    let c := cs.head!
    cs := cs.tail
    ended := false
    if quoted then
      if c == '"' then
        if cs.head? == some '"' then field := field.push c; cs := cs.tail
        else quoted := false; closed := true
      else field := field.push c
    else if c == delimiter || c == '\n' || c == '\r' then
      if !validCell field then throw "Cell exceeds limits."
      row := row.push field; field := ""; closed := false
      if c != delimiter then
        rows := rows.push row; row := #[]; ended := true
        if c == '\r' && cs.head? == some '\n' then cs := cs.tail
    else if closed then throw "Unexpected character after closing quote."
    else if c == '"' then
      if field != "" then throw "Quote must begin a field."
      quoted := true
    else field := field.push c
    if field.length > 4096 || rows.size > maxRows || row.size > 26 then throw "Table exceeds sheet limits."
  if quoted then throw "Unclosed quoted field."
  if !ended then
    if !validCell field then throw "Cell exceeds limits."
    rows := rows.push (row.push field)
  if rows.size > maxRows || rows.any (fun r => r.size > 26) then throw "Table exceeds sheet limits."
  return rows

def encodeDelimited (table : Table) (delimiter : Char) : String :=
  String.intercalate "\r\n" (table.toList.map fun row =>
    String.intercalate (String.singleton delimiter) (row.toList.map fun s =>
      if s.contains delimiter || s.contains '"' || s.contains '\r' || s.contains '\n' then
        "\"" ++ s.replace "\"" "\"\"" ++ "\"" else s)) ++ "\r\n"

def importCSV (m : Model) (text : String) (delimiter : Char) : Except String Model := do
  let table ← parseDelimited text delimiter (m.sheet.size/26)
  let mut s := Sheet.blank m.sheet.size
  for row in [0:table.size] do
    for col in [0:table[row]!.size] do
      let raw := table[row]![col]!
      let raw := if (trim raw).startsWith "=" || raw.startsWith "'" then "'" ++ raw else raw
      if !validCell raw then throw "Imported cell exceeds limits."
      s := put s (row*26+col) raw
  let b := m.book.set! m.active {m.book[m.active]! with cells:=s}
  validateBook b
  return updateBook m b m.active

def exportCSV (m : Model) (delimiter : Char) : String := Id.run do
  let mut bottom := 0
  let mut right := 0
  for i in [0:m.sheet.size] do
    if m.sheet[i]! != "" then bottom := max bottom (i/26); right := max right (i%26)
  let table := (List.range (bottom+1)).toArray.map fun r =>
    (List.range (right+1)).toArray.map fun c => cellDisplay m.book m.active (r*26+c)
  return encodeDelimited table delimiter
end Phase2
