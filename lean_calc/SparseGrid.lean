import Lean
open Lean
structure Sheet where
  size : Nat
  entries : Std.TreeMap Nat String := {}
  deriving Inhabited
namespace Sheet
def blank (size : Nat) : Sheet := {size:=size}
def ofArray (a : Array String) : Sheet :=
  {size:=a.size,entries:=Std.TreeMap.ofList (a.toList.zipIdx.filterMap fun (v,i) => if v == "" then none else some (i,v))}
def get (s : Sheet) (i : Nat) := s.entries[i]?.getD ""
instance : GetElem Sheet Nat String (fun s i => i < s.size) where getElem s i _ := s.get i
def setIfInBounds (s : Sheet) (i : Nat) (v : String) : Sheet :=
  if i >= s.size then s else {s with entries:=if v == "" then s.entries.erase i else s.entries.insert i v}
def set! := setIfInBounds
def toList (s : Sheet) := (List.range s.size).map s.get
def toArray (s : Sheet) := s.toList.toArray
def all (s : Sheet) (f : String → Bool) :=
  (f "" || s.entries.size == s.size) && s.entries.toList.all (fun (_,v) => f v)
def any (s : Sheet) (f : String → Bool) := !s.all (fun v => !f v)
def map (s : Sheet) (f : String → String) : Sheet :=
  if f "" != "" then ofArray (s.toArray.map f)
  else {s with entries:=Std.TreeMap.ofList (s.entries.toList.filterMap fun (i,v) => let v := f v; if v == "" then none else some (i,v))}
def extract (s : Sheet) (start stop : Nat) : Sheet :=
  {size:=min stop s.size-start,entries:=Std.TreeMap.ofList (s.entries.toList.filterMap fun (i,v) => if i >= start && i < stop then some (i-start,v) else none)}
def append (a b : Sheet) : Sheet :=
  {size:=a.size+b.size,entries:=(b.entries.toList.foldl (fun out (i,v) => out.insert (a.size+i) v) a.entries)}
instance : Append Sheet := ⟨append⟩
instance : Coe (Array String) Sheet := ⟨ofArray⟩
instance : Coe Sheet (Array String) := ⟨toArray⟩
instance : BEq Sheet := ⟨fun a b => a.size == b.size && a.entries.toList == b.entries.toList⟩
instance : ToJson Sheet := ⟨fun s => toJson s.toArray⟩
instance : FromJson Sheet := ⟨fun j => ofArray <$> (fromJson? j : Except String (Array String))⟩
end Sheet
