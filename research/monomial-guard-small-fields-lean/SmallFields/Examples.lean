import SmallFields.Direct
import CountDP.Score

namespace SmallFields.Examples

/-- Independent cross-check using the previously verified general recurrence. -/
def reference {V : Type*} [AddCommGroup V] [DecidableEq V] (rows : List V) : ℕ :=
  let active := rows.filter (· != 0)
  let m : Multiset V := active
  CountDP.D active.dedup m.count m

def cases3 : List (List (ZMod 3)) := do
  let a ← List.range 13
  let b ← List.range (13-a)
  let rows : List (ZMod 3) := List.replicate a 1 ++ List.replicate b 2
  guard (rows.sum == 0)
  return rows

def cases5 : List (List (ZMod 5)) := do
  let a ← List.range 9
  let b ← List.range (9-a)
  let c ← List.range (9-a-b)
  let d ← List.range (9-a-b-c)
  let rows : List (ZMod 5) := List.replicate a 1 ++ List.replicate b 2 ++ List.replicate c 3 ++ List.replicate d 4
  guard (rows.sum == 0)
  return rows

def inverseExamples : Bool :=
  let r : List (ZMod 5) := [1,2,2,0]
  let op (x : ZMod 5) := reference (x :: -x :: r) == reference r+1
  ([1,2,3,4] : List (ZMod 5)).all op &&
    reference ([1,1,1,1] : List (ZMod 2)) == reference ([1,1] : List (ZMod 2))+1

def checks : List (String × Bool) :=
  [("all 31 zero-total F3 histograms through 12 active rows agree with the general DP",
      cases3.length == 31 && cases3.all (fun s => direct3 s == reference s)),
   ("all 99 zero-total F5 histograms through 8 active rows agree with the general DP",
      cases5.length == 99 && cases5.all (fun s => direct5 s == reference s)),
   ("opposite labels, repeated values, and a self-inverse value in characteristic two", inverseExamples),
   ("empty and all-zero physical rows", direct3 [] == 0 && direct5 [] == 0 &&
      direct3 [0,0] == 0 && direct5 [0,0,0] == 0),
   ("F3 leftovers of both signs give triples", formula3 7 1 == 3 && formula3 1 7 == 3),
   ("F5 opposite signs require exchanging the types", direct5 [0,1,3,1] == 1 && direct5 [4,2,4,0] == 1),
   ("F5 either weight can be the strict upper bound", formula5 8 1 0 0 == 2 && formula5 1 7 0 0 == 2),
   ("F5 four inverse pairs, one-type groups of five and counts without a table",
      direct5 [1,1,1,2,4,4,4,3] == 4 && direct5 [3,3,3,3,3] == 1 &&
      formula5 1000000 0 0 1000000 == 1000000)]

#guard checks.all Prod.snd

end SmallFields.Examples
