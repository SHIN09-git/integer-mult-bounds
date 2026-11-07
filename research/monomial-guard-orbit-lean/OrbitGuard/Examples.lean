import OrbitGuard.Fixed

namespace OrbitGuard.Examples
open Ternary Finset

def normalized (s : State (Fin m) (Fin d)) : Bool :=
  decide ((∑ i, s.charge i) = 0 ∧ (∑ i, scalar s i) = 1)

/-- Independent executable prefix check over every parameter, using the rank-one determinant identity. -/
def directPass (s : State (Fin m) (Fin d)) : Bool :=
  decide (∀ (k : Fin m) (a : Fin d → F),
    (∑ i ∈ HZ.prefixSet m k.val, s.u i * HZ.familyRow s a i) ≠ 1)

theorem directPass_iff (s : State (Fin m) (Fin d)) : directPass s = true ↔ HZ.Passes s := by
  simp only [directPass,decide_eq_true_eq]
  constructor
  · intro h k hk a
    rw [HZ.principalMinor_eq]
    exact sub_ne_zero.mpr (Ne.symm (h ⟨k,hk⟩ a))
  · intro h k a
    have hp := h k k.isLt a
    rw [HZ.principalMinor_eq] at hp
    exact Ne.symm (sub_ne_zero.mp hp)

def checkSolution (s : State (Fin m) (Fin d)) (expected : ℕ) : Bool :=
  normalized s && match solveFixed s with
    | none => false
    | some (w,e) => w.length == expected && directPass ((replay s w).permute e)

def oneSlope (u v b : Fin m → F) : State (Fin m) (Fin 1) := ⟨u,fun i _ => v i,b⟩

def hidden (w : F) := oneSlope (m := 2) ![1,0] ![0,w] ![1,0]
def reordered := oneSlope (m := 2) ![1,1] ![0,0] ![1,0]
def pair := oneSlope (m := 2) ![1,1] ![1,-1] ![1,0]
def triple := oneSlope (m := 3) ![1,1,1] ![1,1,1] ![1,0,0]
def five := oneSlope (m := 5) ![1,1,1,1,1] ![1,1,1,1,-1] ![1,1,1,1,0]
def twoSlopes : State (Fin 3) (Fin 2) := ⟨![1,1,1],![![1,0],![0,1],![-1,-1]],![1,0,0]⟩
def noSlopes : State (Fin 4) (Fin 0) := ⟨fun _ => 1,fun _ _ => 0,fun _ => 1⟩

def freeCheck : Bool :=
  let s := oneSlope (m := 4) ![1,1,0,0] ![1,1,0,1] ![1,1,0,0]
  let q : Frame (Fin 4) := ⟨Equiv.swap 0 2,fun i => if i = 1 then -1 else 1,by decide⟩
  vertex (q.act s) == vertex s

def hiddenCheck : Bool :=
  normalized (hidden 0) && normalized (hidden 1) &&
    decide (∀ i, (hidden 0).charge i = (hidden 1).charge i ∧ scalar (hidden 0) i = scalar (hidden 1) i) &&
    vertex (hidden 0) != vertex (hidden 1)

/-- Enumerate the six ternary entries of a two-row one-slope state in base three. -/
def fromCode (n : ℕ) : State (Fin 2) (Fin 1) :=
  let digit (k : ℕ) : F := (n / 3^k % 3 : ℕ)
  oneSlope (fun i => digit (3*i.val)) (fun i => digit (3*i.val+1)) (fun i => digit (3*i.val+2))

def tinyCases := ((List.range (3^6)).map fromCode).filter normalized

def tinyGoal (s : State (Fin 2) (Fin 1)) : Bool :=
  directPass s || directPass (s.permute (Equiv.swap 0 1))

/-- Exhaustive ordered-state search with both final row orders and no orbit pruning. -/
def rawWithin (s : State (Fin 2) (Fin 1)) : ℕ → Bool
  | 0 => tinyGoal s
  | k+1 => tinyGoal s || (gates (Fin 2)).any (fun g => rawWithin (g.act s) k)

def crossCheck (s : State (Fin 2) (Fin 1)) : Bool :=
  match solve s with
  | none => false
  | some w => rawWithin s w.length && (List.range w.length).all (fun j => !rawWithin s j)

def checks : List (String × Bool) := [
  ("free row permutation and independent signs, with repeated and zero rows",freeCheck),
  ("hidden slope distinguishes normalized full states with identical charge and scalar products",hiddenCheck),
  ("zero additions and a necessary final free swap",!directPass reordered && checkSolution reordered 0),
  ("one paid addition, with active charges and with zero slope dimensions",checkSolution pair 1 && checkSolution noSlopes 1),
  ("two paid additions for a three-row circuit",checkSolution triple 2),
  ("three paid additions for five active real rows",checkSolution five 3),
  ("two independent slope coordinates and every one of the nine parameters",checkSolution twoSlopes 2),
  ("all normalized two-row one-slope inputs versus direct ordered search",tinyCases.length == 72 && tinyCases.all crossCheck)]

def describe {m : ℕ} (w : List (Gate (Fin m))) := w.map fun g => (g.dst.val,g.src.val,g.coeff.val)

end OrbitGuard.Examples
