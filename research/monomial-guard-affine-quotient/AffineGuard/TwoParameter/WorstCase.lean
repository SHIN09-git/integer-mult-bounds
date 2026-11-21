import AffineGuard.TwoParameter.Lower

namespace AffineGuard.TwoParameter
open Ternary Finset

def costs (m : ℕ) : Set ℕ := {k | ∃ s : Flat (Fin m), Normalized s ∧ C s=k}
noncomputable def M₂ (m : ℕ) : ℕ := sSup (costs m)

theorem greatest_cost (m : ℕ) (hm : 0<m) : IsGreatest (costs m) (bound m) := by
  constructor
  · match m with
    | 0 => omega
    | 1 =>
      have upper := cost_upper _ oneRow_normalized
      change C oneRow ≤ 0 at upper
      exact ⟨oneRow,oneRow_normalized,Nat.eq_zero_of_le_zero upper⟩
    | 2 => exact ⟨twoRows,twoRows_normalized,twoRows_cost⟩
    | n+3 => exact ⟨extremal n,extremal_normalized n,extremal_cost n⟩
  · rintro k ⟨s,hs,rfl⟩
    simpa using cost_upper s hs

/-- A single formula valid for all positive m, including ranks zero and one. -/
theorem worst_case_eq (m : ℕ) (hm : 0<m) : M₂ m=min (m-1) ((2*m+2)/3) := by
  have h : M₂ m=bound m := (greatest_cost m hm).csSup_eq
  rw [h,bound]
  omega

theorem worst_case_of_three_le (m : ℕ) (hm : 3≤m) : M₂ m=(2*m+2)/3 := by
  rw [worst_case_eq m (by omega)]
  omega

/-- The same maximum is attained within the class of genuinely two-dimensional families. -/
theorem rank_two_greatest (m : ℕ) (hm : 3≤m) :
    IsGreatest {k | ∃ s : Flat (Fin m), Normalized s ∧ RankTwo s ∧ C s=k} (M₂ m) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 3 n]
  have eq : M₂ (n+3)=bound (n+3) := (greatest_cost (n+3) (by omega)).csSup_eq
  rw [eq]
  exact ⟨⟨extremal n,extremal_normalized n,extremal_rank_two n,extremal_cost n⟩,
    fun _ ⟨s,hs,_,h⟩ => h ▸ (by simpa using cost_upper s hs)⟩

private theorem small_matrix : ∀ u v x y z w : F, (u≠0 ∨ v≠0) → u*x+v*z=0 → u*y+v*w=0 →
    ∃ a b : F, (a≠0 ∨ b≠0) ∧ a*x+b*y=0 ∧ a*z+b*w=0 := by decide

theorem rank_two_requires_three (m : ℕ) (s : Flat (Fin m)) (hs : Normalized s) (rank : RankTwo s) :
    3≤m := by
  by_contra! small
  interval_cases m
  · have norm := hs.2
    simp at norm
  · obtain ⟨a,b,nonzero,e,_⟩ := small_matrix 0 1 (s.w 0 0) (s.w 0 1) 0 0 (by decide) (by simp) (by simp)
    have zero := rank a b (fun i => by rw [show i=0 from Subsingleton.elim _ _]; exact e)
    exact nonzero.elim (fun h => h zero.1) (fun h => h zero.2)
  · have primal : s.u 0≠0 ∨ s.u 1≠0 := by
      by_contra! none
      have norm := hs.2
      simp [Fin.sum_univ_two,scalar,none.1,none.2] at norm
    have ortho (d : Fin 2) : s.u 0*s.w 0 d+s.u 1*s.w 1 d=0 := by
      simpa [Fin.sum_univ_two,HZ.State.charge,Pi.add_apply] using congrFun hs.1 d
    obtain ⟨a,b,nonzero,e,f⟩ := small_matrix _ _ _ _ _ _ primal (ortho 0) (ortho 1)
    have zero := rank a b (fun i => by fin_cases i <;> assumption)
    exact nonzero.elim (fun h => h zero.1) (fun h => h zero.2)

end AffineGuard.TwoParameter
