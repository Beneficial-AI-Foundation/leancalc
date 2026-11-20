import Phase2
open Lean Phase2
namespace Incremental
abbrev Key := Nat
-- Formula dependencies include unchosen IF branches, making invalidation safe
-- when the branch condition changes. Evaluation still remains lazy.
def referencesWithFuel : Nat → Book → Nat → Phase2.Expr → List Key
  | 0,_,_,_ => []
  | fuel+1,b,si,e => Id.run do
    match e with
    | .named n => return match namedExpr b n with | .ok e => referencesWithFuel fuel b si e | _ => []
    | .call _ args =>
      let direct := args.flatMap (referencesWithFuel fuel b si)
      return direct
    | .ref r => return match resolve b si r with | .ok (s,i) => [s*26000+i] | _ => []
    | .range a c =>
      match resolve b si a, resolve b si c with
      | .ok (sa,ia),.ok (sc,ic) => return if sa == sc then (rangeCells ia ic).map (sa*26000+·) else []
      | _,_ => return []
    | .neg e => return referencesWithFuel fuel b si e
    | .bin _ a c => return referencesWithFuel fuel b si a ++ referencesWithFuel fuel b si c
    | _ => return []
def references (b : Book) (si : Nat) (e : Phase2.Expr) : List Key := referencesWithFuel 32 b si e
def dependencies (b : Book) (si i : Nat) : List Key :=
  let raw := trim b[si]!.cells[i]!
  if raw.startsWith "=" then
    match parse (String.ofList raw.toList.tail) with | .ok e => references b si e | _ => []
  else []
structure Cache where
  book : Book := #[]
  values : Std.HashMap Key (Option String) := {}
  reverse : Std.HashMap Key (List Key) := {}
  calculations : Nat := 0
  deriving Inhabited

def graph (b : Book) : Std.HashMap Key (List Key) := Id.run do
  let mut reverse := {}
  for si in [:b.size] do
    for (i,_) in b[si]!.cells.entries.toList do
      for dep in dependencies b si i do
        reverse := reverse.insert dep ((si*26000+i)::(reverse[dep]?.getD []))
  return reverse

def synchronize (old : Cache) (b : Book) : Cache := Id.run do
  if old.book == b then return old
  if b.any (fun s => s.objects.any (·.kind == "function")) then
    return {book:=b,values:={},reverse:=graph b}
  if old.book.map (fun s => (s.name,s.cells.size,s.objects)) != b.map (fun s => (s.name,s.cells.size,s.objects)) then
    return {book:=b,values:={},reverse:=graph b}
  let mut dirty := Std.HashSet.emptyWithCapacity
  let mut queue : Array Key := #[]
  for si in [:b.size] do
    for (i,_) in old.book[si]!.cells.entries.toList ++ b[si]!.cells.entries.toList do
      if old.book[si]!.cells[i]! != b[si]!.cells[i]! && !dirty.contains (si*26000+i) then
        let k := si*26000+i
        dirty := dirty.insert k
        queue := queue.push k
  let mut position := 0
  while position < queue.size do
    let k := queue[position]!
    position := position+1
    for dependent in old.reverse[k]?.getD [] do
      if !dirty.contains dependent then
        dirty := dirty.insert dependent
        queue := queue.push dependent
  let mut values := old.values
  for k in queue do values := values.erase k
  return {old with book:=b,values:=values,reverse:=if queue.isEmpty then old.reverse else graph b,calculations:=0}

def display (cache : Cache) (si i : Nat) : String × Cache :=
  let key := si*26000+i
  if cache.book[si]!.cells[i]! == "" then ("",cache) else
  match (cache.values[key]?.getD none) with
  | some value => (value,cache)
  | none =>
    let value := cellDisplay cache.book si i
    (value,{cache with values:=cache.values.insert key (some value), calculations:=cache.calculations+1})
end Incremental
