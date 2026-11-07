import Dummy.Optimality
import HZ.Guards
import Mathlib.Algebra.Field.ZMod

open Finset Matrix
namespace Binary
abbrev F := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem guard_scalar (x : F) : 1 - x ≠ 0 ↔ x = 0 := by
  revert x
  decide

variable {I R : Type*} [DecidableEq I] [Fintype I]

/-- w_i(r) is the r-th normalized guard row at real coordinate i. -/
def Normalized (s : HZ.State I F (R → F)) : Prop := ∑ i, s.charge i = 1

omit [DecidableEq I] in
theorem normalized_iff (s : HZ.State I F (R → F)) :
    Normalized s ↔ ∀ r, ∑ i, s.u i * s.w i r = 1 := by
  simp [Normalized, funext_iff, HZ.State.charge, Finset.sum_apply]

noncomputable def principalMinor (s : HZ.State I F (R → F)) (r : R) (B : Finset I) : F :=
  Matrix.det (1 - Matrix.vecMulVec (fun i : B => s.u i) (fun i : B => s.w i r))

omit [Fintype I] in
theorem principalMinor_eq (s : HZ.State I F (R → F)) (r : R) (B : Finset I) :
    principalMinor s r B = 1 - ∑ i ∈ B, s.u i * s.w i r := by
  rw [principalMinor, HZ.det_rank_one]
  exact congrArg (fun x : F => 1 - x) (sum_coe_sort B (fun i => s.u i * s.w i r))

omit [Fintype I] in
theorem principalMinor_submatrix (s : HZ.State I F (R → F)) (r : R) (B : Finset I) :
    principalMinor s r B =
      ((1 - Matrix.vecMulVec s.u (fun i => s.w i r)).submatrix
        (fun i : B => (i : I)) (fun i : B => (i : I))).det := by
  unfold principalMinor
  apply congrArg Matrix.det
  ext i j
  simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Subtype.ext_iff]

def Passes {m : ℕ} (s : HZ.State (Fin m) F (R → F)) : Prop :=
  ∀ k, k < m → ∀ r, principalMinor s r (HZ.prefixSet m k) ≠ 0

omit [DecidableEq I] [Fintype I] in
theorem prefix_zero {m : ℕ} (s : HZ.State (Fin m) F (R → F)) (hp : Passes s)
    (k : ℕ) (hk : k < m) : ∑ i ∈ HZ.prefixSet m k, s.charge i = 0 := by
  ext r
  have hh := hp k hk r
  rw [principalMinor_eq, guard_scalar] at hh
  simpa [HZ.State.charge, Finset.sum_apply] using hh

omit [DecidableEq I] [Fintype I] in
theorem passes_concentrated [Nonempty R] {m : ℕ} (s : HZ.State (Fin m) F (R → F))
    (hs : Normalized s) (hp : Passes s) : Dummy.Concentrated s 1 := by
  cases m with
  | zero => simp [Normalized] at hs
  | succ m =>
    let c : Fin (m + 1) := Fin.last m
    have hz : ∀ i : Fin (m + 1), i ≠ c → s.charge i = 0 := by
      intro i hi
      have hival : i.val ≠ m := by intro he; exact hi (Fin.ext he)
      have hh := prefix_zero s hp (i.val + 1) (by omega)
      rw [HZ.prefix_succ, sum_insert (by simp [HZ.prefixSet]), prefix_zero s hp i.val i.isLt,
        add_zero] at hh
      exact hh
    have hc : s.charge c = 1 := by
      have hh : (∑ i, s.charge i) = s.charge c :=
        sum_eq_single c (fun i _ hi => hz i hi) (by simp)
      exact hh.symm.trans hs
    refine ⟨c, ?_⟩
    intro i
    by_cases hi : i = c
    · simpa [hi] using hc
    · simp [hi, hz i hi]

def reindex {J : Type*} (s : HZ.State I F (R → F)) (e : J ≃ I) : HZ.State J F (R → F) :=
  ⟨s.u ∘ e, s.w ∘ e, s.b ∘ e⟩

def FullGuard (s : HZ.State I F (R → F)) : Prop :=
  ∃ (m : ℕ) (e : Fin m ≃ I), Passes (reindex s e)

omit [DecidableEq I] in
theorem normalized_reindex {J : Type*} [Fintype J]
    (s : HZ.State I F (R → F)) (e : J ≃ I) (hs : Normalized s) :
    Normalized (reindex s e) := by
  change (∑ j, s.charge (e j)) = 1
  rw [Equiv.sum_comp e]
  exact hs

theorem fullguard_concentrated [Nonempty R] (s : HZ.State I F (R → F))
    (hs : Normalized s) (hg : FullGuard s) : Dummy.Concentrated s 1 := by
  obtain ⟨m, e, hp⟩ := hg
  obtain ⟨c, hc⟩ := passes_concentrated (reindex s e) (normalized_reindex s e hs) hp
  refine ⟨e c, ?_⟩
  intro i
  have hh := hc (e.symm i)
  change s.charge (e (e.symm i)) = _ at hh
  have he : e.symm i = c ↔ i = e c := by
    constructor
    · intro h; simpa using congrArg e h
    · intro h; simpa using congrArg e.symm h
  simpa only [e.apply_symm_apply, he] using hh

theorem concentrated_fullguard (s : HZ.State I F (R → F))
    (hs : Dummy.Concentrated s 1) : FullGuard s := by
  classical
  obtain ⟨c, hc⟩ := hs
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨c⟩
  let e₀ : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let last : Fin (Fintype.card I) := ⟨Fintype.card I - 1, by omega⟩
  let e : Fin (Fintype.card I) ≃ I := (Equiv.swap last (e₀.symm c)).trans e₀
  have he : e last = c := by simp [e]
  refine ⟨Fintype.card I, e, ?_⟩
  intro k hk r
  rw [principalMinor_eq, guard_scalar]
  apply sum_eq_zero
  intro i hi
  have hil : i ≠ last := by
    intro hh
    have hval : i.val < k := (mem_filter.mp hi).2
    rw [hh] at hval
    dsimp [last] at hval
    omega
  have hic : e i ≠ c := by intro hh; exact hil (e.injective (hh.trans he.symm))
  have hh := congrFun (hc (e i)) r
  rw [if_neg hic] at hh
  simpa [reindex, HZ.State.charge] using hh

theorem fullguard_iff [Nonempty R] (s : HZ.State I F (R → F)) (hs : Normalized s) :
    FullGuard s ↔ Dummy.Concentrated s 1 :=
  ⟨fullguard_concentrated s hs, concentrated_fullguard s⟩

omit [DecidableEq I] [Fintype I] in
/-- Free choice of order gives the same operational cost as the literal fixed-order guard. -/
theorem fullguard_run_iff {m n : ℕ} (s : HZ.State (Fin m) F (R → F)) :
    (∃ t, HZ.Run s n t ∧ FullGuard t) ↔ (∃ t, HZ.Run s n t ∧ Passes t) := by
  constructor
  · rintro ⟨t, hr, j, e, he⟩
    have hj : j = m := by simpa using Fintype.card_congr e
    subst j
    refine ⟨t.permute e, ?_, he⟩
    have hf := HZ.Run.cons t (HZ.Operation.permute e) (HZ.Run.nil (t.permute e))
    simpa [HZ.Operation.cost] using hr.trans hf
  · rintro ⟨t, hr, hp⟩
    exact ⟨t, hr, m, Equiv.refl _, hp⟩

end Binary

