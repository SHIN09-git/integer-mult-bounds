import HZ.Partitions
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

open Finset
namespace HZ

variable {I K V : Type*} [DecidableEq I] [Field K] [AddCommGroup V] [Module K V]

/-- Primal column, dual vector-valued row, and a scalar carrier row. -/
@[ext] structure State (I K V : Type*) where
  u : I → K
  w : I → V
  b : I → K

def State.charge (s : State I K V) (i : I) : V := s.u i • s.w i

/-- R_i <- R_i + a R_j, with the inverse action on both dual rows. -/
def State.addRow (s : State I K V) (i j : I) (a : K) : State I K V where
  u := Function.update s.u i (s.u i + a * s.u j)
  w := Function.update s.w j (s.w j - a • s.w i)
  b := Function.update s.b j (s.b j - a * s.b i)

def State.permute (s : State I K V) (e : Equiv.Perm I) : State I K V where
  u := s.u ∘ e
  w := s.w ∘ e
  b := s.b ∘ e

def State.scale (s : State I K V) (c : I → K) : State I K V where
  u := fun i => c i * s.u i
  w := fun i => (c i)⁻¹ • s.w i
  b := fun i => (c i)⁻¹ * s.b i

inductive Operation (I K : Type*) [Field K] where
  | add (i j : I) (a : K) (distinct : i ≠ j) (nonzero : a ≠ 0)
  | permute (e : Equiv.Perm I)
  | scale (c : I → K) (nonzero : ∀ i, c i ≠ 0)

def Operation.apply (g : Operation I K) (s : State I K V) : State I K V :=
  match g with
  | .add i j a _ _ => s.addRow i j a
  | .permute e => s.permute e
  | .scale c _ => s.scale c

def Operation.cost (g : Operation I K) : ℕ :=
  match g with
  | .add .. => 1
  | .permute _ | .scale .. => 0

/-- A finite legal execution. Free operations may occur anywhere. -/
inductive Run : State I K V → ℕ → State I K V → Prop where
  | nil (s) : Run s 0 s
  | cons (s) (g : Operation I K) {n t} (tail : Run (g.apply s) n t) :
      Run s (g.cost + n) t

theorem Run.trans {s t r : State I K V} {n m : ℕ}
    (h : Run s n t) (h' : Run t m r) : Run s (n + m) r := by
  induction h with
  | nil => simpa using h'
  | cons s g tail ih => simpa [Nat.add_assoc] using Run.cons s g (ih h')

omit [DecidableEq I] in
@[simp] theorem charge_permute (s : State I K V) (e : Equiv.Perm I) (i : I) :
    (s.permute e).charge i = s.charge (e i) := rfl

omit [DecidableEq I] in
@[simp] theorem charge_scale (s : State I K V) (c : I → K)
    (hc : ∀ i, c i ≠ 0) (i : I) : (s.scale c).charge i = s.charge i := by
  simp only [State.charge, State.scale, smul_smul]
  congr 1
  field_simp [hc i]

theorem charge_add_outside (s : State I K V) {i j k : I} (a : K)
    (hki : k ≠ i) (hkj : k ≠ j) : (s.addRow i j a).charge k = s.charge k := by
  simp [State.charge, State.addRow, hki, hkj]

theorem charge_add_pair (s : State I K V) {i j : I} (a : K) (hij : i ≠ j) :
    (s.addRow i j a).charge i + (s.addRow i j a).charge j = s.charge i + s.charge j := by
  simp only [State.charge, State.addRow, Function.update_self,
    Function.update_of_ne hij, Function.update_of_ne hij.symm]
  module

theorem addRow_inverse (s : State I K V) {i j : I} (a : K) (hij : i ≠ j) :
    (s.addRow i j a).addRow i j (-a) = s := by
  ext k <;> by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp_all [State.addRow, Ne.symm hij]

/-- Legal accumulation kills the target and transfers its whole charge to the donor. -/
theorem elimination (s : State I K V) {i j : I} (hij : i ≠ j)
    (hi : s.u i ≠ 0) (hj : s.u j ≠ 0) :
    let a := -s.u i / s.u j
    a ≠ 0 ∧ (s.addRow i j a).u i = 0 ∧
    (s.addRow i j a).u j = s.u j ∧
    (s.addRow i j a).charge i = 0 ∧
    (s.addRow i j a).charge j = s.charge i + s.charge j := by
  dsimp
  have hz : (s.addRow i j (-s.u i / s.u j)).u i = 0 := by
    simp [State.addRow, hj]
  have hc : (s.addRow i j (-s.u i / s.u j)).charge i = 0 := by
    simp [State.charge, hz]
  refine ⟨div_ne_zero (neg_ne_zero.mpr hi) hj, hz, ?_, hc, ?_⟩
  · simp [State.addRow, hij.symm]
  · have hp := charge_add_pair s (-s.u i / s.u j) hij
    simpa [hc] using hp

end HZ
