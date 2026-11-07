import GuardDP.Guards

namespace GuardDP.Examples
open GuardDP

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The first four charges sum to zero, but using that group would sacrifice two inverse pairs. -/
def five : HZ.State (Fin 8) (ZMod 5) (ZMod 5) where
  u := fun _ => 1
  w := ![1, 1, 1, 2, 4, 4, 4, 3]
  b := fun _ => 0

def groups5 := (zeroGroups five.charge).map (fun B => (B.sort (· ≤ ·)).map Fin.val)
def word5 := separationWord five

/-- Unequal primal coordinates exercise reconstruction with nontrivial field coefficients. -/
def targeted : HZ.State (Fin 5) (ZMod 5) (ZMod 5) where
  u := ![2, 1, 3, 4, 1]
  w := ![1, 4, 4, 2, 0]
  b := fun _ => 0

def real5 := (realGroups targeted.charge 1).map (fun B => (B.sort (· ≤ ·)).map Fin.val)
def targetWord := concentrationWord targeted 1

/-- Joint binary charges (10,01,10,10,00), with an inactive last row. -/
def binary : HZ.State (Fin 5) Binary.F (Fin 2 → Binary.F) where
  u := fun _ => 1
  w := ![![1, 0], ![0, 1], ![1, 0], ![1, 0], ![0, 0]]
  b := fun _ => 0

def fixed := binaryWord binary

def emptyState : HZ.State (Fin 0) (ZMod 5) (ZMod 5) := ⟨Fin.elim0, Fin.elim0, Fin.elim0⟩
def singleton : HZ.State (Fin 1) (ZMod 5) (ZMod 5) := ⟨fun _ => 2, fun _ => 3, fun _ => 0⟩

/-- Each check runs the actual DP, instruction emitter and, where applicable, interpreter. -/
def checks : List (String × Bool) :=
  [("five / four inverse pairs",
      groups5.length == 4 && word5.length == 4 &&
      (List.finRange 8).all (fun i => (execute five word5).charge i == 0)),
   ("nonzero target / two real groups",
      real5.length == 2 && targetWord.length == 2 &&
      ((List.finRange 5).map (fun i => (execute targeted targetWord).charge i)).filter (· != 0) == [1]),
   ("two binary guards / final swap",
      (augmentedGroups binary.charge 1).length == 2 && fixed.additions.length == 2 &&
      (fixed.swap.any (fun p => p.1 != p.2)) &&
      (List.finRange 5).all (fun i => (List.finRange 2).all (fun r =>
        (fixed.result binary).charge i r == (if i.val = 4 then 1 else 0)))),
   ("empty real input", (zeroGroups emptyState.charge).isEmpty && (separationWord emptyState).isEmpty),
   ("single real carrier",
      (augmentedGroups singleton.charge 1).length == 1 && (concentrationWord singleton 1).isEmpty)]

#guard checks.all Prod.snd

end GuardDP.Examples
