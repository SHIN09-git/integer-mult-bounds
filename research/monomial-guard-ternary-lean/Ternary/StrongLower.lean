import Ternary.Components
import Ternary.Envelope

open Finset
namespace Ternary

def weight (x : F) : ℤ := if x = 0 then 0 else if x = 1 then 1 else 2
@[simp] theorem weight_zero : weight 0 = 0 := by decide
@[simp] theorem weight_one : weight 1 = 1 := by decide
@[simp] theorem weight_neg_one : weight (-1) = 2 := by decide

theorem weight_bounds (x : F) : 0 ≤ weight x ∧ weight x ≤ 2 := by
  unfold weight
  split_ifs <;> omega

theorem cast_weight (x : F) : (weight x : F) = x := by
  revert x
  decide

variable {I V : Type*} [DecidableEq I] [Fintype I] [AddCommGroup V] [Module F V]

def weightSum (s : HZ.State I F V) : ℤ := ∑ i, weight (scalar s i)

omit [DecidableEq I] [Fintype I] [AddCommGroup V] [Module F V] in
theorem sum_lower (B : Finset I) (z : I → ℤ) (hz : ∀ i, -1 ≤ z i) :
    -(B.card : ℤ) ≤ ∑ i ∈ B, z i := by
  have hh := sum_le_sum (s := B) (fun i _ => hz i)
  simpa using hh

omit [Fintype I] [Module F V] in
theorem component_budget (s : HZ.State I F V)
    (hpure : ∀ i, s.w i = 0 → scalar s i = 1)
    (B : Finset I) (hB : B.Nonempty) (z : I → ℤ)
    (hz : ∀ i, -1 ≤ z i)
    (hc : ((∑ i ∈ B, z i : ℤ) : F) = ∑ i ∈ B, scalar s i)
    (hw : HasSlope s B → ∃ i ∈ B, z i = 0) :
    (∑ i ∈ B, weight (scalar s i)) ≤ 3 * ((B.card : ℤ) - 1) + ∑ i ∈ B, z i := by
  have hcast : ((∑ i ∈ B, weight (scalar s i) : ℤ) : F) = ((∑ i ∈ B, z i : ℤ) : F) := by
    rw [hc]
    simp [cast_weight]
  have hmod := (ZMod.intCast_eq_intCast_iff' (∑ i ∈ B, weight (scalar s i)) (∑ i ∈ B, z i) 3).mp hcast
  have hlow := sum_lower B z hz
  have hpos := card_pos.mpr hB
  by_cases hh : HasSlope s B
  · obtain ⟨i, hi, hzi⟩ := hw hh
    have hl := sum_lower (B.erase i) z hz
    have he := sum_erase_add B z hi
    rw [hzi, add_zero] at he
    have hcard := card_erase_add_one hi
    have hweight : (∑ i ∈ B, weight (scalar s i)) ≤ 2 * (B.card : ℤ) := by
      have ht := sum_le_sum (s := B) (fun i _ => (weight_bounds (scalar s i)).2)
      simpa [mul_comm] using ht
    omega
  · have hones : ∀ i ∈ B, scalar s i = 1 := by
      intro i hi
      apply hpure i
      by_contra hne
      exact hh ⟨i, hi, hne⟩
    have he : (∑ i ∈ B, weight (scalar s i)) = B.card := by
      calc
        _ = ∑ _i ∈ B, (1 : ℤ) := sum_congr rfl (fun i hi => by rw [hones i hi, weight_one])
        _ = _ := by simp
    omega

omit [AddCommGroup V] [Module F V] in
theorem partition_sum (P : Finpartition (univ : Finset I)) (f : I → ℤ) :
    (∑ B ∈ P.parts, ∑ i ∈ B, f i) = ∑ i, f i := by
  have hh := Finset.sum_biUnion (f := f) P.disjoint
  rw [P.biUnion_parts] at hh
  exact hh.symm

/-- A stronger lower bound when every initial zero-slope coordinate has scalar charge +1. -/
theorem strong_execution_bound {s t : HZ.State I F V} {n : ℕ}
    (hpure : ∀ i, s.w i = 0 → scalar s i = 1)
    (hr : HZ.Run s n t) (ht : HZ.Separated t) :
    weightSum s ≤ 3 * (n : ℤ) + imbalance t := by
  classical
  obtain ⟨P, z, hp, hz, htot, hcard⟩ := execution_components hr ht
  have hb := sum_le_sum (s := P.parts) (fun B hB => component_budget s hpure B
    (P.nonempty_of_mem_parts hB) z (fun i => (hz i).1) (hp B hB).1 (hp B hB).2)
  rw [sum_add_distrib, partition_sum, partition_sum, htot] at hb
  have hc : (∑ B ∈ P.parts, 3 * ((B.card : ℤ) - 1)) =
      3 * ((Fintype.card I : ℤ) - P.parts.card) := by
    rw [← mul_sum, sum_sub_distrib, ← Nat.cast_sum, P.sum_card_parts]
    simp
  rw [hc] at hb
  change weightSum s ≤ _ at hb
  omega

variable {D : Type*} [Fintype D]

theorem strong_guard_bound {s t : HZ.State I F (D → F)} {n : ℕ}
    (hpure : ∀ i, s.w i = 0 → scalar s i = 1)
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    (hr : HZ.Run s n t) (hg : FullGuard t) :
    weightSum s ≤ 3 * (n : ℤ) + 1 := by
  have hs := fullguard_separated t (hr.total_charge.trans hy) hg
  have hb := strong_execution_bound hpure hr hs
  have hd := fullguard_imbalance t ((scalar_total hr).trans hn) hg
  omega

end Ternary
