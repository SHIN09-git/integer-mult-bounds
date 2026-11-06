import Binary.Guards

open Finset
namespace Binary
variable {I R : Type*} [DecidableEq I] [Fintype I] [Nonempty R]

/-- Exact full-family paid distance; the family need not be an affine flat. -/
noncomputable def C (s : HZ.State I F (R → F)) : ℕ :=
  sInf {n | ∃ t, HZ.Run s n t ∧ FullGuard t}

omit [Nonempty R] in
theorem normalized_run {s t : HZ.State I F (R → F)} {n : ℕ}
    (hs : Normalized s) (hr : HZ.Run s n t) : Normalized t :=
  hr.total_charge.trans hs

theorem guard_cost_lower_bound {s t : HZ.State I F (R → F)} {n : ℕ}
    (hs : Normalized s) (hr : HZ.Run s n t) (ht : FullGuard t) :
    HZ.activeCount s - Dummy.Zstar s.charge 1 ≤ n :=
  Dummy.cost_lower_bound one_ne_zero hr (fullguard_concentrated t (normalized_run hs hr) ht)

theorem guard_cost_attained (s : HZ.State I F (R → F)) (hs : Normalized s) :
    ∃ t, HZ.Run s (HZ.activeCount s - Dummy.Zstar s.charge 1) t ∧ FullGuard t := by
  obtain ⟨t, hr, ht⟩ := Dummy.cost_attained s 1 one_ne_zero hs
  exact ⟨t, hr, concentrated_fullguard t ht⟩

theorem cost_eq_h_sub_Zstar (s : HZ.State I F (R → F)) (hs : Normalized s) :
    C s = HZ.activeCount s - Dummy.Zstar s.charge 1 := by
  have hl : IsLeast {n | ∃ t, HZ.Run s n t ∧ FullGuard t}
      (HZ.activeCount s - Dummy.Zstar s.charge 1) :=
    ⟨guard_cost_attained s hs, by
      rintro n ⟨t, hr, ht⟩
      exact guard_cost_lower_bound hs hr ht⟩
  exact hl.csInf_eq

theorem cost_eq_concentration (s : HZ.State I F (R → F)) (hs : Normalized s) :
    C s = Dummy.minimumCost s 1 := by
  rw [cost_eq_h_sub_Zstar s hs, Dummy.minimumCost_eq s 1 one_ne_zero hs]

omit [DecidableEq I] [Fintype I] in
/-- The exact formula and attaining sequence for the original, fixed coordinate order. -/
theorem fixed_order_optimal {m : ℕ} (s : HZ.State (Fin m) F (R → F)) (hs : Normalized s) :
    (∃ t, HZ.Run s (HZ.activeCount s - Dummy.Zstar s.charge 1) t ∧ Passes t) ∧
    (∀ n t, HZ.Run s n t → Passes t → HZ.activeCount s - Dummy.Zstar s.charge 1 ≤ n) := by
  refine ⟨(fullguard_run_iff s).mp (guard_cost_attained s hs), ?_⟩
  intro n t hr ht
  exact guard_cost_lower_bound hs hr ⟨m, Equiv.refl _, ht⟩

end Binary

