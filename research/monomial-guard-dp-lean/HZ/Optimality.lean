import HZ.Construction
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset
namespace HZ
variable {I K V : Type*} [DecidableEq I] [Fintype I]
  [Field K] [AddCommGroup V] [Module K V]

def Separated (s : State I K V) : Prop := ∀ i, s.charge i = 0

noncomputable def activeCount (s : State I K V) : ℕ := (active s.charge).card
noncomputable def partitionCount (s : State I K V) : ℕ := blockCount s.charge

/-- Every successful execution gives a zero-sum partition of *all* initial labels.
One paid operation can account for at most one lost block. -/
theorem execution_partition {s t : State I K V} {n : ℕ}
    (hr : Run s n t) (ht : Separated t) :
    ∃ P : Finpartition (univ : Finset I), ZeroSum s.charge P ∧
      Fintype.card I ≤ n + P.parts.card := by
  classical
  induction hr with
  | nil s =>
    refine ⟨⊥, ?_, by simp⟩
    intro B hB
    obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    simpa using ht i
  | @cons s g n t tail ih =>
    obtain ⟨P, hp, hn⟩ := ih ht
    cases g with
    | add i j a hij ha =>
      obtain ⟨Q, hq, hc⟩ := pullback_pair s.charge (s.addRow i j a).charge hij
        (fun k hki hkj => (charge_add_outside s a hki hkj).symm)
        (charge_add_pair s a hij).symm P hp
      refine ⟨Q, hq, ?_⟩
      simp only [Operation.cost]
      omega
    | permute e =>
      refine ⟨permPartition P e, zeroSum_permPartition s.charge P e hp, ?_⟩
      simpa [Operation.cost, permPartition_card] using hn
    | scale c hc =>
      refine ⟨P, ?_, by simpa [Operation.cost] using hn⟩
      intro B hB
      have h := hp B hB
      simpa [Operation.apply, charge_scale s c hc] using h

/-- Lower bound for arbitrary interleavings of paid additions and free monomial operations. -/
theorem cost_lower_bound {s t : State I K V} {n : ℕ}
    (hr : Run s n t) (ht : Separated t) : activeCount s - partitionCount s ≤ n := by
  obtain ⟨P, hp, hn⟩ := execution_partition hr ht
  exact active_bound s.charge P hp hn

omit [DecidableEq I] in
theorem sum_active (s : State I K V) :
    ∑ i ∈ active s.charge, s.charge i = ∑ i, s.charge i := by
  classical
  apply sum_subset (subset_univ _)
  intro i _ hi
  simpa [active] using hi

/-- A maximizing labeled zero-sum partition yields a legal attaining execution. -/
theorem cost_attained (s : State I K V) (hs : ∑ i, s.charge i = 0) :
    ∃ t : State I K V, Run s (activeCount s - partitionCount s) t ∧ Separated t ∧
      AgreeOutside (active s.charge) s t ∧
      ((∀ i ∈ active s.charge, s.b i = 0) → t.b = s.b) := by
  classical
  obtain ⟨P, hp, hcard⟩ := exists_maxBlocks s.charge (active s.charge) (by rw [sum_active, hs])
  obtain ⟨t, hr, ht, hout, hb⟩ := settle_family P.parts s
    (fun B hB => P.nonempty_of_mem_parts hB) P.disjoint
    (by intro B hB i hi; exact (mem_filter.mp (P.subset hB hi)).2) hp
  have hcost : (∑ B ∈ P.parts, (B.card - 1)) = activeCount s - partitionCount s := by
    have hadd : (∑ B ∈ P.parts, (B.card - 1)) + P.parts.card = (active s.charge).card := by
      calc
        _ = ∑ B ∈ P.parts, ((B.card - 1) + 1) := by simp [sum_add_distrib]
        _ = ∑ B ∈ P.parts, B.card := by
          apply sum_congr rfl
          intro B hB
          have hpos := card_pos.mpr (P.nonempty_of_mem_parts hB)
          omega
        _ = (active s.charge).card := P.sum_card_parts
    change P.parts.card = partitionCount s at hcard
    change _ = (active s.charge).card - partitionCount s
    omega
  rw [P.biUnion_parts] at ht hout hb
  refine ⟨t, hcost ▸ hr, ?_, hout, hb⟩
  intro i
  by_cases hi : i ∈ active s.charge
  · exact ht i hi
  · obtain ⟨hu, hw, _⟩ := hout i hi
    have hz : s.charge i = 0 := by simpa [active] using hi
    simpa [State.charge, hu, hw] using hz

/-- Exact h-Z theorem: the proposed cost is attainable and bounds every legal execution below. -/
theorem optimal_cost_eq_h_sub_Z (s : State I K V) (hs : ∑ i, s.charge i = 0) :
    (∃ t, Run s (activeCount s - partitionCount s) t ∧ Separated t) ∧
    (∀ n t, Run s n t → Separated t → activeCount s - partitionCount s ≤ n) := by
  obtain ⟨t, hr, ht, _, _⟩ := cost_attained s hs
  exact ⟨⟨t, hr, ht⟩, fun _ _ hr ht => cost_lower_bound hr ht⟩

noncomputable def minimumCost (s : State I K V) : ℕ :=
  sInf {n | ∃ t, Run s n t ∧ Separated t}

theorem minimumCost_eq (s : State I K V) (hs : ∑ i, s.charge i = 0) :
    minimumCost s = activeCount s - partitionCount s := by
  have h := optimal_cost_eq_h_sub_Z s hs
  have hl : IsLeast {n | ∃ t, Run s n t ∧ Separated t} (activeCount s - partitionCount s) :=
    ⟨h.1, by rintro n ⟨t, hr, ht⟩; exact h.2 n t hr ht⟩
  exact hl.csInf_eq

theorem Run.total_charge {s t : State I K V} {n : ℕ} (hr : Run s n t) :
    ∑ i, t.charge i = ∑ i, s.charge i := by
  induction hr with
  | nil => rfl
  | cons s g tail ih =>
    rw [ih]
    cases g with
    | add i j a hij ha =>
      exact sum_pair_conserved _ _ hij (fun k hki hkj => charge_add_outside s a hki hkj)
        (charge_add_pair s a hij) univ (by simp)
    | permute e => exact Equiv.sum_comp e s.charge
    | scale c hc => simp [Operation.apply, charge_scale s c hc]

end HZ
