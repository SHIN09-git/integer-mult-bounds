import Dummy.Construction

open Finset
namespace Dummy
variable {I K V : Type*} [DecidableEq I] [Fintype I]
  [Field K] [AddCommGroup V] [Module K V]

/-- Only real coordinates I occur in the state space and operation alphabet. -/
noncomputable def minimumCost (s : HZ.State I K V) (τ : V) : ℕ :=
  sInf {n | ∃ t, HZ.Run s n t ∧ Concentrated t τ}

theorem optimal_cost_eq_h_sub_Zstar (s : HZ.State I K V) (τ : V)
    (hτ : τ ≠ 0) (hs : ∑ i, s.charge i = τ) :
    (∃ t, HZ.Run s (HZ.activeCount s - Zstar s.charge τ) t ∧ Concentrated t τ) ∧
    (∀ n t, HZ.Run s n t → Concentrated t τ → HZ.activeCount s - Zstar s.charge τ ≤ n) :=
  ⟨cost_attained s τ hτ hs, fun _ _ hr ht => cost_lower_bound hτ hr ht⟩

theorem minimumCost_eq (s : HZ.State I K V) (τ : V)
    (hτ : τ ≠ 0) (hs : ∑ i, s.charge i = τ) :
    minimumCost s τ = HZ.activeCount s - Zstar s.charge τ := by
  have h := optimal_cost_eq_h_sub_Zstar s τ hτ hs
  have hl : IsLeast {n | ∃ t, HZ.Run s n t ∧ Concentrated t τ}
      (HZ.activeCount s - Zstar s.charge τ) :=
    ⟨h.1, by rintro n ⟨t, hr, ht⟩; exact h.2 n t hr ht⟩
  exact hl.csInf_eq

end Dummy

