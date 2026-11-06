import Ternary.Scalar
import HZ.Examples
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

open Finset
namespace Ternary

abbrev Coord (J : Type*) (p : ℕ) := (J × Bool) ⊕ (Fin p ⊕ Unit)
abbrev Pencil (I : Type*) := HZ.State I F (Unit → F)

variable {J : Type*} [DecidableEq J] [Fintype J]

/-- The extra zero-image coordinate keeps the pencil nonconstant even when there are no pairs. -/
def phase (p : ℕ) (b : J → F) (T : Finset J) : Pencil (Coord J p) where
  u
    | .inl (j, false) => if j ∈ T then 0 else 1
    | .inl (_, true) => 1
    | .inr (.inl _) => 1
    | .inr (.inr _) => 0
  w
    | .inl (_, false) => fun _ => 1
    | .inl (j, true) => fun _ => if j ∈ T then 0 else -1
    | .inr (.inl _) => 0
    | .inr (.inr _) => fun _ => 1
  b
    | .inl (j, false) => b j
    | .inl (j, true) => if j ∈ T then b j + b j else b j
    | .inr (.inl _) => 1
    | .inr (.inr _) => 0

omit [Fintype J] in
theorem phase_add (p : ℕ) (b : J → F) (T : Finset J) (j : J) (hj : j ∉ T) :
    (phase p b T).addRow (.inl (j, false)) (.inl (j, true)) (-1) = phase p b (insert j T) := by
  apply HZ.State.ext
  · funext i
    rcases i with ⟨k, v⟩ | (k | k)
    · cases v <;> by_cases he : k = j <;> simp_all [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]
  · funext i d
    rcases i with ⟨k, v⟩ | (k | k)
    · cases v <;> by_cases he : k = j <;> simp_all [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]
  · funext i
    rcases i with ⟨k, v⟩ | (k | k)
    · cases v <;> by_cases he : k = j <;> simp_all [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]
    · simp [phase, HZ.State.addRow]

omit [Fintype J] in
theorem phase_run (p : ℕ) (b : J → F) (T : Finset J) :
    HZ.Run (phase p b ∅) T.card (phase p b T) := by
  induction T using Finset.induction_on with
  | empty => simpa using HZ.Run.nil (phase p b ∅)
  | @insert j T hj ih =>
    have hf := HZ.Run.cons (phase p b T)
      (HZ.Operation.add (.inl (j, false)) (.inl (j, true)) (-1) (by simp) (by decide))
      (HZ.Run.nil ((phase p b T).addRow (.inl (j, false)) (.inl (j, true)) (-1)))
    rw [phase_add p b T j hj] at hf
    simpa [HZ.Operation.cost, hj] using ih.trans hf

theorem phase_separated (p : ℕ) (b : J → F) : HZ.Separated (phase p b univ) := by
  intro i
  rcases i with ⟨j, v⟩ | (j | j)
  · cases v <;> simp [phase, HZ.State.charge, funext_iff]
  · simp [phase, HZ.State.charge]
  · simp [phase, HZ.State.charge]

theorem phase_total_charge (p : ℕ) (b : J → F) :
    ∑ i, (phase p b ∅).charge i = 0 := by
  have hr := phase_run p b univ
  have ht : ∑ i, (phase p b univ).charge i = 0 := sum_eq_zero (fun i _ => phase_separated p b i)
  rw [hr.total_charge] at ht
  exact ht

theorem phase_active_count (p : ℕ) (b : J → F) :
    HZ.activeCount (phase p b ∅) = 2 * Fintype.card J := by
  let e : J × Bool ↪ Coord J p := ⟨Sum.inl, Sum.inl_injective⟩
  have he : HZ.active (phase p b ∅).charge = univ.map e := by
    ext i
    rcases i with ⟨j, v⟩ | (j | j)
    · cases v <;> simp [HZ.active, phase, HZ.State.charge, e, funext_iff]
    · simp [HZ.active, phase, HZ.State.charge, e]
    · simp [HZ.active, phase, HZ.State.charge, e]
  unfold HZ.activeCount
  rw [he, card_map]
  simp [mul_comm]

theorem phase_S (p : ℕ) (b : J → F) : S (phase p b ∅) = Fintype.card J := by
  have hu := HZ.cost_lower_bound (phase_run p b univ) (phase_separated p b)
  have hl := HZ.twice_partitionCount_le (phase p b ∅) (phase_total_charge p b)
  have hc := phase_active_count p b
  unfold S
  simp only [card_univ] at hu
  omega

theorem phase_imbalance_initial (p : ℕ) (b : J → F) :
    imbalance (phase p b ∅) = 2 * (∑ j, lift (b j)) + p := by
  simp only [imbalance, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [phase, scalar, ← sum_add_distrib, two_mul]

theorem phase_imbalance_final (p : ℕ) (b : J → F) :
    imbalance (phase p b univ) = (∑ j, lift (b j + b j)) + p := by
  simp only [imbalance, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [phase, scalar]

omit [Fintype J] in
theorem phase_nonzero_slope (p : ℕ) (b : J → F) :
    ∃ i, (phase p b ∅).w i () ≠ 0 :=
  ⟨.inr (.inr ()), by simp [phase]⟩

end Ternary
