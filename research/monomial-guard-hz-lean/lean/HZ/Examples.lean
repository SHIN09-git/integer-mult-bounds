import HZ.Optimality
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Finset
namespace HZ

section BlockSize
variable {I K V : Type*} [DecidableEq I] [Fintype I]
  [Field K] [AddCommGroup V] [Module K V]

theorem twice_partitionCount_le (s : State I K V) (hs : ∑ i, s.charge i = 0) :
    2 * partitionCount s ≤ activeCount s := by
  classical
  obtain ⟨P, hp, hcard⟩ := exists_maxBlocks s.charge (active s.charge) (by rw [sum_active, hs])
  have hsize : ∀ B ∈ P.parts, 2 ≤ B.card := by
    intro B hB
    have hpos := card_pos.mpr (P.nonempty_of_mem_parts hB)
    by_contra hlt
    have hone : B.card = 1 := by omega
    obtain ⟨i, rfl⟩ := card_eq_one.mp hone
    have hz : s.charge i = 0 := by simpa using hp {i} hB
    have hi := P.subset hB (mem_singleton_self i)
    have hn : s.charge i ≠ 0 := by simpa [active] using hi
    exact hn hz
  have h := sum_le_sum hsize
  rw [P.sum_card_parts] at h
  change P.parts.card = partitionCount s at hcard
  simpa [hcard, activeCount, Nat.mul_comm] using h
end BlockSize

namespace Examples
abbrev F5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def paired : State (Fin 5) F5 F5 where
  u := fun _ => 1
  w := ![1, 4, 2, 3, 0]
  b := ![0, 0, 0, 0, 1]

def indivisible : State (Fin 5) F5 F5 where
  u := fun _ => 1
  w := ![1, 1, 1, 2, 0]
  b := ![0, 0, 0, 0, 1]

theorem paired_total : ∑ i, paired.charge i = 0 := by decide
theorem indivisible_total : ∑ i, indivisible.charge i = 0 := by decide

theorem paired_active : active paired.charge = {0, 1, 2, 3} := by
  ext i
  simp only [active, mem_filter, mem_univ, true_and]
  fin_cases i <;> decide

theorem indivisible_active : active indivisible.charge = {0, 1, 2, 3} := by
  ext i
  simp only [active, mem_filter, mem_univ, true_and]
  fin_cases i <;> decide

theorem paired_two_steps : ∃ t, Run paired 2 t ∧ Separated t := by
  let q := paired.addRow 0 1 4
  let t := q.addRow 2 3 4
  refine ⟨t, ?_, ?_⟩
  · exact Run.cons paired (.add 0 1 4 (by decide) (by decide))
      (Run.cons q (.add 2 3 4 (by decide) (by decide)) (Run.nil t))
  · unfold Separated
    decide

theorem paired_minimum : minimumCost paired = 2 := by
  rw [minimumCost_eq paired paired_total]
  have hh : activeCount paired = 4 := by rw [activeCount, paired_active]; decide
  have hz := twice_partitionCount_le paired paired_total
  obtain ⟨t, hr, ht⟩ := paired_two_steps
  have hn := cost_lower_bound hr ht
  omega

/-- A 32-subset kernel calculation; it is only an example, not the general theorem. -/
theorem indivisible_zero_subset : ∀ B : Finset (Fin 5), B.Nonempty →
    B ⊆ {0, 1, 2, 3} → (∑ i ∈ B, indivisible.charge i) = 0 → B = {0, 1, 2, 3} := by
  decide

theorem indivisible_partitionCount : partitionCount indivisible = 1 := by
  obtain ⟨P, hp, hcard⟩ := exists_maxBlocks indivisible.charge (active indivisible.charge)
    (by rw [sum_active, indivisible_total])
  have hpB : ∀ B ∈ P.parts, B = {0, 1, 2, 3} := by
    intro B hB
    exact indivisible_zero_subset B (P.nonempty_of_mem_parts hB)
      (indivisible_active ▸ P.subset hB) (hp B hB)
  have hle : P.parts.card ≤ 1 := by
    calc
      P.parts.card ≤ ({({0, 1, 2, 3} : Finset (Fin 5))} : Finset _).card :=
        card_le_card (fun B hB => mem_singleton.mpr (hpB B hB))
      _ = 1 := card_singleton _
  have hn : P.parts.Nonempty := P.parts_nonempty (by rw [indivisible_active]; decide)
  have hpos := card_pos.mpr hn
  change P.parts.card = partitionCount indivisible at hcard
  omega

theorem indivisible_minimum : minimumCost indivisible = 3 := by
  rw [minimumCost_eq indivisible indivisible_total, indivisible_partitionCount]
  rw [activeCount, indivisible_active]
  decide

theorem indivisible_three_steps : ∃ t, Run indivisible 3 t ∧ Separated t := by
  let q := indivisible.addRow 0 3 4
  let r := q.addRow 1 3 4
  let t := r.addRow 2 3 4
  refine ⟨t, ?_, ?_⟩
  · exact Run.cons indivisible (.add 0 3 4 (by decide) (by decide))
      (Run.cons q (.add 1 3 4 (by decide) (by decide))
        (Run.cons r (.add 2 3 4 (by decide) (by decide)) (Run.nil t)))
  · unfold Separated
    decide

end Examples
end HZ
