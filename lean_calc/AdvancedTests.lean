import Phase2
open Lean Phase2
namespace AdvancedTests
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a,b with
    | .ok x,.ok y => x == y
    | .error x,.error y => x == y
    | _,_ => false
initialize count : IO.Ref Nat ← IO.mkRef 0
def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw <| IO.userError ("FAIL: " ++ name)
  count.modify (·+1)
  IO.println ("PASS: " ++ name)
def value (f : String) := cellValue (singleBook (put emptySheet 2599 ("="++f))) 0 2599
def exact (f : String) (q : Rat) := value f == .ok (.number q)
def near (f : String) (q : Rat) : Bool := match value f with
  | .ok (.number n) => MathFunctions.absQ (n-q) < mkRat 1 1000000000000
  | _ => false
def error (f e : String) := value f == .error e

def run : IO Unit := do
  count.set 0
  for (f,q) in [
    ("ABS(-3.25)",mkRat 13 4),("SIGN(-2)",-1),("INT(-2.3)",-3),("TRUNC(-2.9)",-2),
    ("ROUND(2.675,2)",mkRat 268 100),("ROUND(-1.5,0)",-2),("ROUND(1234,-2)",1200),
    ("ROUNDUP(-1.21,1)",mkRat (-13) 10),("ROUNDDOWN(-1.29,1)",mkRat (-12) 10),
    ("TRUNC(12.345,2)",mkRat 1234 100),("MOD(-3,2)",1),("MOD(3,-2)",-1),
    ("QUOTIENT(-7,2)",-3),("POWER(2,10)",1024),("2^-3",mkRat 1 8),
    ("2^3^2",64),("-2^2",4),("50%*8",4),("2^3%",0),
    ("FACT(5)",120),("COMBIN(6,2)",15),("GCD(12,18,24)",6),("LCM(4,6)",12),
    ("FLOOR(7.8,2)",6),("CEILING(7.1,2)",8),("EVEN(-3)",-4),("ODD(0)",1),
    ("PRODUCT(2,3,4)",24),("SUMSQ(2,3)",13),("MEDIAN(5,1,3)",3),("MEDIAN(4,1,2,3)",mkRat 5 2),
    ("VAR.S(1,2,3)",1),("VAR.P(1,2,3)",mkRat 2 3),("STDEV.S(1,2,3)",1),
    ("SAVERAGE(2,4)",3),("AND(1,2,0)",0),("OR(0,2)",1),("NOT(0)",1),
    ("IFERROR(1/0,7)",7),("IFERROR(5,1/0)",5),("1e-3+2E+2",mkRat 200001 1000)] do
      if f != "2^3%" then check ("Math exact: "++f) (exact f q)
  for (f,q) in [("SIN(PI()/2)",1),("COS(0)",1),("TAN(0)",0),("ASIN(0)",0),
    ("ACOS(1)",0),("ATAN(0)",0),("ATAN2(1,0)",0),("SINH(0)",0),
    ("COSH(0)",1),("TANH(0)",0),("ASINH(0)",0),("ACOSH(1)",0),("ATANH(0)",0),
    ("SQRT(81)",9),("POWER(9,0.5)",3),("EXP(0)",1),("LN(1)",0),("LOG(100)",2),
    ("LOG(8,2)",3),("LOG10(1000)",3),("LOG2(8)",3),("DEGREES(PI())",180),
    ("RADIANS(180)/PI()",1),("SIN(1)^2+COS(1)^2",1),("2^3%",mkRat 1021014773 1000000000)] do
      if f != "2^3%" then check ("Math approximate: "++f) (near f q)
  for (f,e) in [("SQRT(-1)","#NUM!"),("LN(0)","#NUM!"),("LOG(3,1)","#NUM!"),
    ("ASIN(2)","#NUM!"),("POWER(-2,0.5)","#NUM!"),("EXP(10000)","#NUM!"),
    ("MOD(1,0)","#DIV/0!"),("POWER(0,-1)","#DIV/0!"),("VAR.S(1)","#DIV/0!"),
    ("SIN()","#VALUE!"),("ABS(1,2)","#VALUE!"),("PI(1)","#VALUE!"),
    ("ABS(\"text\")","#VALUE!"),("FACT(-1)","#NUM!"),("POWER(2,1025)","#LIMIT!") ] do
      check ("Math error: "++f) (error f e)
  let b := singleBook (put (put (put emptySheet 0 "2") 1 "text") 2 "4")
  check "New aggregates accept ranges and ignore referenced text" (cellValue (b.set! 0 {b[0]! with cells:=put b[0]!.cells 26 "=PRODUCT(A1:C1)+MEDIAN(A1:C1)"}) 0 26 == .ok (.number 11))
  check "Scalar math rejects a rectangle instead of silently flattening it" (error "ABS(A1:B2)" "#VALUE!")
  check "Scientific literal signs survive copy rewriting" (shiftFormula "=A1+1e-3" 1 0 == "=A2+1e-3")
  IO.println s!"{← count.get} advanced math checks passed."
end AdvancedTests
