import LeanCalcCore
namespace MathFunctions
@[extern "calc_float_text"] opaque floatText (x : Float) : String

def literal (s : String) : Option Rat := do
  let parts := (trim s).toLower.splitOn "e"
  match parts with
  | [a] => decimal a
  | [a,e] =>
    let n ← decimal a
    let e ← (if e.startsWith "+" then String.ofList e.toList.tail else e).toInt?
    if e.natAbs > 308 then none else
      let scale := Rat.ofInt (Int.ofNat (10^e.natAbs))
      some (if e < 0 then n/scale else n*scale)
  | _ => none

def asFloat (q : Rat) : Float := q.num.toFloat / (Int.ofNat q.den).toFloat
def approximate (x : Float) : Except String Rat := do
  if x.isNaN || x.isInf then throw "#NUM!"
  let some q := literal (floatText x) | throw "#NUM!"
  return q

def display (q : Rat) : String := Id.run do
  let ordinary := showNumber q
  if !ordinary.contains '/' then return ordinary
  let mut den := q.den
  while den%2 == 0 do den := den/2
  while den%5 == 0 do den := den/5
  return if den == 1 then floatText (asFloat q) else ordinary

def absQ (q : Rat) := if q < 0 then -q else q
def truncQ (q : Rat) : Int := if q < 0 then q.ceil else q.floor

def names : List String := ["ABS","SIGN","INT","TRUNC","ROUND","ROUNDUP","ROUNDDOWN",
  "MOD","QUOTIENT","POWER","SQRT","SQRTPI","EXP","LN","LOG","LOG10","LOG2","PI",
  "SIN","COS","TAN","ASIN","ACOS","ATAN","ATAN2","SINH","COSH","TANH",
  "ASINH","ACOSH","ATANH","RADIANS","DEGREES","FACT","COMBIN","GCD","LCM",
  "FLOOR","CEILING","EVEN","ODD","PRODUCT","SUMSQ","MEDIAN","VAR","VAR.S","VAR.P",
  "STDEV","STDEV.S","STDEV.P","SAVERAGE","AND","OR","NOT"]
def aggregateNames : List String := ["SUM","MIN","MAX","AVERAGE","SAVERAGE","COUNT","PRODUCT","SUMSQ","MEDIAN","VAR","VAR.S","VAR.P","STDEV","STDEV.S","STDEV.P","GCD","LCM","AND","OR"]
def extraNames : List String := ["COUNTIF","SUMIF","AVERAGEIF","SUMPRODUCT","INDEX","MATCH","VLOOKUP","LEN","LEFT","RIGHT","MID","UPPER","LOWER","TRIM","CONCATENATE","SUBSTITUTE","DATE","YEAR","MONTH","DAY"]
def supported (s : String) := (extraNames ++ names ++ ["SUM","MIN","MAX","AVERAGE","COUNT","IF","IFERROR"]).contains s

def power (x y : Rat) : Except String Rat := do
  if x == 0 && y < 0 then throw "#DIV/0!"
  if y.den == 1 then
    if y.num.natAbs > 1024 || (toString x.num).length * y.num.natAbs > 20000 then throw "#LIMIT!"
    let z := (List.range y.num.natAbs).foldl (fun a _ => a*x) 1
    return if y < 0 then 1/z else z
  if x < 0 then throw "#NUM!"
  approximate ((asFloat x).pow (asFloat y))

def factorial (n : Nat) : Rat := Rat.ofInt (Int.ofNat ((List.range n).foldl (fun a i => a*(i+1)) 1))
def apply (name : String) (xs : List Rat) : Except String Rat := do
  let x := xs[0]?.getD 0
  let y := xs[1]?.getD 0
  let unary := ["ABS","SIGN","INT","SQRT","SQRTPI","EXP","LN","LOG10","LOG2","SIN","COS","TAN","ASIN","ACOS","ATAN","SINH","COSH","TANH","ASINH","ACOSH","ATANH","RADIANS","DEGREES","FACT","EVEN","ODD","NOT"]
  let binary := ["MOD","QUOTIENT","POWER","ATAN2","COMBIN","FLOOR","CEILING"]
  if unary.contains name && xs.length != 1 then throw "#VALUE!"
  if binary.contains name && xs.length != 2 then throw "#VALUE!"
  if ["ROUND","ROUNDUP","ROUNDDOWN"].contains name && xs.length != 2 then throw "#VALUE!"
  if ["TRUNC","LOG"].contains name && (xs.isEmpty || xs.length > 2) then throw "#VALUE!"
  match name with
  | "PI" => if xs.isEmpty then approximate 3.141592653589793 else throw "#VALUE!"
  | "ABS" => return absQ x
  | "SIGN" => return if x < 0 then -1 else if x == 0 then 0 else 1
  | "INT" => return Rat.ofInt x.floor
  | "NOT" => return if x == 0 then 1 else 0
  | "ROUND" | "ROUNDUP" | "ROUNDDOWN" | "TRUNC" =>
    let digits := truncQ y
    if digits.natAbs > 100 then throw "#NUM!"
    let scale := Rat.ofInt (Int.ofNat (10^digits.natAbs))
    let factor := if digits < 0 then 1/scale else scale
    let z := absQ (x*factor)
    let n := if name == "ROUND" then (z+mkRat 1 2).floor else if name == "ROUNDUP" then z.ceil else z.floor
    return (if x < 0 then -Rat.ofInt n else Rat.ofInt n)/factor
  | "MOD" => if y == 0 then throw "#DIV/0!" else return x-y*Rat.ofInt (x/y).floor
  | "QUOTIENT" => if y == 0 then throw "#DIV/0!" else return Rat.ofInt (truncQ (x/y))
  | "POWER" => power x y
  | "FLOOR" | "CEILING" =>
    if y == 0 then return 0
    if x*y < 0 then throw "#NUM!"
    let z := x/y
    return y * Rat.ofInt (if name == "FLOOR" then z.floor else z.ceil)
  | "EVEN" | "ODD" =>
    let n := (absQ x).ceil.toNat
    let n := if n%2 == (if name == "EVEN" then 0 else 1) then n else n+1
    return Rat.ofInt (if x < 0 then -Int.ofNat n else Int.ofNat n)
  | "FACT" | "COMBIN" =>
    if x < 0 || x > 170 || (name == "COMBIN" && (y < 0 || y > x)) then throw "#NUM!"
    let n := (truncQ x).toNat
    let k := (truncQ y).toNat
    return if name == "FACT" then factorial n else factorial n / (factorial k * factorial (n-k))
  | "GCD" | "LCM" =>
    if xs.any (· < 0) then throw "#NUM!"
    let ns := xs.map (fun q => (truncQ q).toNat)
    return Rat.ofInt (Int.ofNat (ns.foldl (if name == "GCD" then Nat.gcd else Nat.lcm) (if name == "GCD" then 0 else 1)))
  | "AND" | "OR" =>
    if xs.isEmpty then throw "#VALUE!"
    return if (if name == "AND" then xs.all (· != 0) else xs.any (· != 0)) then 1 else 0
  | "PRODUCT" => return if xs.isEmpty then 0 else xs.foldl (·*·) 1
  | "SUMSQ" => return xs.foldl (fun a q => a+q*q) 0
  | "SAVERAGE" => if xs.isEmpty then throw "#DIV/0!" else return xs.foldl (·+·) 0 / Rat.ofInt (Int.ofNat xs.length)
  | "MEDIAN" =>
    if xs.isEmpty then throw "#NUM!"
    let sorted := xs.mergeSort (· <= ·)
    return if xs.length%2 == 1 then sorted[xs.length/2]! else (sorted[xs.length/2-1]!+sorted[xs.length/2]!)/2
  | "VAR" | "VAR.S" | "VAR.P" | "STDEV" | "STDEV.S" | "STDEV.P" =>
    let sample := !name.endsWith ".P"
    if xs.length <= (if sample then 1 else 0) then throw "#DIV/0!"
    let avg := xs.foldl (·+·) 0 / Rat.ofInt (Int.ofNat xs.length)
    let v := xs.foldl (fun a q => a+(q-avg)*(q-avg)) 0 / Rat.ofInt (Int.ofNat (xs.length-(if sample then 1 else 0)))
    if name.startsWith "STDEV" then approximate ((asFloat v).sqrt) else return v
  | _ =>
    let f := asFloat x
    let pi : Float := 3.141592653589793
    let result ← match name with
      | "SIN" => pure f.sin | "COS" => pure f.cos | "TAN" => pure f.tan
      | "ASIN" => pure f.asin | "ACOS" => pure f.acos | "ATAN" => pure f.atan
      | "SINH" => pure f.sinh | "COSH" => pure f.cosh | "TANH" => pure f.tanh
      | "ASINH" => pure f.asinh | "ACOSH" => pure f.acosh | "ATANH" => pure f.atanh
      | "ATAN2" => if x == 0 && y == 0 then throw "#DIV/0!" else pure ((asFloat y).atan2 f)
      | "SQRT" => pure f.sqrt | "SQRTPI" => pure (f*pi).sqrt
      | "EXP" => pure f.exp | "LN" => pure f.log | "LOG10" => pure f.log10 | "LOG2" => pure f.log2
      | "LOG" =>
        let base := if xs.length == 1 then 10 else y
        if x <= 0 || base <= 0 || base == 1 then throw "#NUM!"
        pure (f.log / (asFloat base).log)
      | "RADIANS" => pure (f*pi/180) | "DEGREES" => pure (f*180/pi)
      | _ => throw "#NAME?"
    approximate result
end MathFunctions
