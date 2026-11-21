import AffineGuard.OneParameter.Upper
import AffineGuard.OneParameter.Lower

/-! The exact worst cost and a nonconstant maximizing pencil in every dimension m ≥ 2. -/

namespace AffineGuard.OneParameter
open Ternary

/-- Attained minimum guard costs for the normalized inputs with m labeled rows. -/
def costs (m : ℕ) : Set ℕ := {n | ∃ s : Pencil (Fin m), Normalized s ∧ C s = n}

/-- The worst minimum number of paid row additions. -/
noncomputable def M₁ (m : ℕ) : ℕ := sSup (costs m)

theorem extremal_cost (n : ℕ) : C (extremal n) = 2*(n+1)/3 := by
  have lower := potential_lower (extremal n) (extremal_normalized n)
  rw [extremal_weight] at lower
  have upper := cost_upper (extremal n) (extremal_normalized n)
  rw [Fintype.card_fin] at upper
  omega

/-- The supremum is an attained maximum in each positive row dimension. -/
theorem greatest_cost (m : ℕ) (hm : 0 < m) : IsGreatest (costs m) (2*m/3) := by
  cases m with
  | zero => omega
  | succ n =>
    refine ⟨⟨extremal n,extremal_normalized n,extremal_cost n⟩,?_⟩
    rintro k ⟨s,hs,rfl⟩
    simpa using cost_upper s hs

theorem worst_case_eq (m : ℕ) (hm : 0 < m) : M₁ m = 2*m/3 := (greatest_cost m hm).csSup_eq

/-- For m ≥ 2 an explicit pencil with nonzero slope attains the same maximum. -/
theorem nonconstant_attainment (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Pencil (Fin m), Normalized s ∧ (∃ i, s.w i 0 ≠ 0) ∧ C s = M₁ m := by
  rw [worst_case_eq m (by omega)]
  cases m with
  | zero => omega
  | succ n => exact ⟨extremal n,extremal_normalized n,extremal_nonconstant n (by omega),extremal_cost n⟩

end AffineGuard.OneParameter
