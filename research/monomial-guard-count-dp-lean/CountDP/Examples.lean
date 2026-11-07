import CountDP.FixedOrder
import GuardDP.Examples
import Mathlib.Data.List.Sublists

namespace CountDP.Examples
open GuardDP.Examples (five targeted binary emptyState singleton)

def cells {I V : Type*} [DecidableEq I] [DecidableEq V] [AddCommGroup V] (y : I → V) (keys : List I) :=
  (table (alphabet y keys) (capacity y keys)).size

def zeroExample :=
  let y := five.charge
  let keys := GuardDP.labels y
  let a := compressed y keys keys.toFinset
  let gs := zeroGroups y
  let w := wordFromGroups five gs
  (cells y keys, a, gs.map (fun b => (b.sort (· ≤ ·)).map Fin.val), w,
   (List.finRange 8).all (fun i => (GuardDP.execute five w).charge i == 0))

/-- Compare every subset, including the nonzero-sum ones, using two materialized tables. -/
def compareSubsets :=
  let y := five.charge
  let keys := GuardDP.labels y
  let types := alphabet y keys
  let n := capacity y keys
  let old := GuardDP.layers y keys keys.toFinset.card
  let small := table types n
  let sets := keys.sublists.map List.toFinset
  (sets.length, sets.all (fun s => (old.read s).length == (lookup types n small (histogram y s)).score))

def collision :=
  let y := targeted.charge
  let keys := GuardDP.augmentedKeys y
  let z := Dummy.augment y 1
  let a := compressed z keys keys.toFinset
  let augmented := augmentedGroups y 1
  let real := realGroups y 1
  let w := wordFromGroups targeted real
  let endCharges := (List.finRange 5).map (fun i => (GuardDP.execute targeted w).charge i)
  (cells z keys, a, (histogram z keys.toFinset).count (-1),
   augmented.any (fun b => decide (none ∈ b ∧ some 1 ∈ b)),
   real.map (fun b => (b.sort (· ≤ ·)).map Fin.val), w, endCharges)

def repeated : HZ.State (Fin 40) (ZMod 5) (ZMod 5) where
  u := fun _ => 1
  w := fun i => if i.val < 20 then 1 else -1
  b := fun _ => 0

def repeatedExample :=
  let y := repeated.charge
  let keys := GuardDP.labels y
  let gs := zeroGroups y
  let w := wordFromGroups repeated gs
  (cells y keys, gs.length, w.length,
   (List.finRange 40).all (fun i => (GuardDP.execute repeated w).charge i == 0))

def checks : List (String × Bool) :=
  let (n, a, gs, w, cleared) := zeroExample
  let (ng, ag, multiplicity, both, real, paid, charges) := collision
  let fixed := binaryWord binary
  [("eight labels / zero total", n == 64 && a.score == 4 && gs.length == 4 && w.length == 4 && cleared),
   ("all labeled subset scores", compareSubsets == (256, true)),
   ("virtual and real charges coincide", ng == 18 && multiplicity == 2 && both &&
     ag.score == 2 && real.length == 2 && paid.length == 2 && charges.filter (· != 0) == [1]),
   ("fixed-order binary guards", fixed.additions.length == 2 && fixed.swap.any (fun p => p.1 != p.2) &&
     (List.finRange 5).all (fun i => (List.finRange 2).all (fun r =>
       (fixed.result binary).charge i r == (if i.val = 4 then 1 else 0)))),
   ("forty repeated labels", repeatedExample == (441, 20, 20, true)),
   ("empty real input", cells emptyState.charge (GuardDP.labels emptyState.charge) == 1 &&
     (separationWord emptyState).isEmpty),
   ("single real carrier", (augmentedGroups singleton.charge 1).length == 1 &&
     (concentrationWord singleton 1).isEmpty)]

#guard checks.all Prod.snd

end CountDP.Examples
