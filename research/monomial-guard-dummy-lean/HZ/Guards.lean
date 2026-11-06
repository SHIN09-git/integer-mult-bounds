import HZ.Optimality
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open Finset Matrix
namespace HZ
variable {I K D : Type*} [DecidableEq I] [Fintype I] [Field K]
  [DecidableEq D] [Fintype D]

def familyRow (s : State I K (D → K)) (a : D → K) (i : I) : K :=
  s.b i + ∑ d, a d * s.w i d

/-- The literal principal submatrix, with its original labeled coordinates. -/
noncomputable def principalMinor (s : State I K (D → K)) (a : D → K) (B : Finset I) : K :=
  Matrix.det (1 - Matrix.vecMulVec (fun i : B => s.u i) (fun i : B => familyRow s a i))

theorem det_rank_one {J : Type*} [DecidableEq J] [Fintype J] (u v : J → K) :
    Matrix.det (1 - Matrix.vecMulVec u v) = 1 - ∑ i, u i * v i := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp [Matrix.replicateRow_mul_replicateCol_apply, dotProduct, mul_comm]

omit [Fintype I] [DecidableEq D] in
theorem principalMinor_eq (s : State I K (D → K)) (a : D → K) (B : Finset I) :
    principalMinor s a B = 1 - ∑ i ∈ B, s.u i * familyRow s a i := by
  rw [principalMinor, det_rank_one]
  exact congrArg (fun x : K => 1 - x) (sum_coe_sort B (fun i => s.u i * familyRow s a i))

omit [Fintype I] [DecidableEq D] in
theorem principalMinor_submatrix (s : State I K (D → K)) (a : D → K) (B : Finset I) :
    principalMinor s a B =
      ((1 - Matrix.vecMulVec s.u (familyRow s a)).submatrix
        (fun i : B => (i : I)) (fun i : B => (i : I))).det := by
  unfold principalMinor
  apply congrArg Matrix.det
  ext i j
  simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Subtype.ext_iff]

omit [Fintype I] in
theorem minor_single (s : State I K (D → K)) (B : Finset I) (d : D) (a : K) :
    principalMinor s (Pi.single d a) B =
      1 - (∑ i ∈ B, s.u i * s.b i) - a * (∑ i ∈ B, s.u i * s.w i d) := by
  rw [principalMinor_eq]
  simp only [familyRow, Pi.single_apply, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  have he : (∑ i ∈ B, s.u i * (s.b i + a * s.w i d)) =
      (∑ i ∈ B, s.u i * s.b i) + a * (∑ i ∈ B, s.u i * s.w i d) := by
    simp_rw [mul_add, sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

omit [Fintype I] [DecidableEq D] in
/-- Quantification over the full parameter family forces the vector slope sum to vanish. -/
theorem full_family_forces_zero (s : State I K (D → K)) (B : Finset I)
    (hpass : ∀ a : D → K, principalMinor s a B ≠ 0) :
    ∑ i ∈ B, s.charge i = 0 := by
  classical
  ext d
  have hz : ∑ i ∈ B, s.u i * s.w i d = 0 := by
    by_contra hne
    let a := (1 - ∑ i ∈ B, s.u i * s.b i) / (∑ i ∈ B, s.u i * s.w i d)
    apply hpass (Pi.single d a)
    rw [minor_single]
    dsimp [a]
    rw [div_mul_cancel₀ _ hne]
    ring
  simpa [State.charge, Finset.sum_apply] using hz

def prefixSet (m k : ℕ) : Finset (Fin m) := univ.filter (fun i => i.val < k)

def Passes {m : ℕ} (s : State (Fin m) K (D → K)) : Prop :=
  ∀ k, k < m → ∀ a : D → K, principalMinor s a (prefixSet m k) ≠ 0

theorem prefix_succ {m : ℕ} (i : Fin m) : prefixSet m (i.val + 1) = insert i (prefixSet m i.val) := by
  ext j
  simp only [prefixSet, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    by_cases hj : j.val = i.val
    · exact Or.inl (Fin.ext hj)
    · exact Or.inr (by omega)
  · rintro (rfl | h) <;> omega

omit [DecidableEq D] in
theorem passes_implies_separated {m : ℕ} (s : State (Fin m) K (D → K))
    (hs : ∑ i, s.charge i = 0) (hp : Passes s) : Separated s := by
  have hz : ∀ k, k ≤ m → ∑ i ∈ prefixSet m k, s.charge i = 0 := by
    intro k hk
    by_cases he : k = m
    · subst k
      simpa [prefixSet] using hs
    · exact full_family_forces_zero s _ (hp k (by omega))
  intro i
  have h := hz (i.val + 1) (by omega)
  rw [prefix_succ, sum_insert (by simp [prefixSet]), hz i.val (by omega), add_zero] at h
  exact h

omit [Fintype I] [DecidableEq D] in
theorem separated_minor_one (s : State I K (D → K)) (hs : Separated s)
    (B : Finset I) (hb : ∀ i ∈ B, s.b i = 0) (a : D → K) : principalMinor s a B = 1 := by
  rw [principalMinor_eq]
  suffices ∑ i ∈ B, s.u i * familyRow s a i = 0 by rw [this, sub_zero]
  apply sum_eq_zero
  intro i hi
  rw [familyRow, hb i hi, zero_add, mul_sum]
  apply sum_eq_zero
  intro d _
  have hz : s.u i * s.w i d = 0 := by simpa [State.charge] using congrFun (hs i) d
  calc
    s.u i * (a d * s.w i d) = a d * (s.u i * s.w i d) := by ring
    _ = 0 := by rw [hz, mul_zero]

structure Anchored (s : State I K (D → K)) (c : I) : Prop where
  supported : ∀ i, i ≠ c → s.b i = 0
  normalized : s.u c * s.b c = 1
  zeroSlope : s.w c = 0

omit [DecidableEq D] in
/-- A final free swap places the preserved carrier last; every tested determinant is one. -/
theorem anchored_guard_attained {m : ℕ} (s : State (Fin m) K (D → K)) (c : Fin m)
    (ha : Anchored s c) (hs : ∑ i, s.charge i = 0) :
    ∃ t, Run s (activeCount s - partitionCount s) t ∧ Passes t := by
  classical
  obtain ⟨r, hr, hsep, hout, hb⟩ := cost_attained s hs
  have hc0 : s.charge c = 0 := by simp [State.charge, ha.zeroSlope]
  have hrb : r.b = s.b := hb (by
    intro i hi
    apply ha.supported i
    intro h
    subst i
    have hne : s.charge c ≠ 0 := by simpa [active] using hi
    exact hne hc0)
  let last : Fin m := ⟨m - 1, by have := c.isLt; omega⟩
  let e : Equiv.Perm (Fin m) := Equiv.swap last c
  let t := r.permute e
  refine ⟨t, ?_, ?_⟩
  · simpa [Operation.cost] using hr.trans (Run.cons r (Operation.permute e) (Run.nil t))
  · intro k hk a
    have htsep : Separated t := fun i => hsep (e i)
    have htb : ∀ i ∈ prefixSet m k, t.b i = 0 := by
      intro i hi
      change r.b (e i) = 0
      rw [hrb]
      apply ha.supported
      intro he
      have heilast : i = last := e.injective (he.trans (by simp [e]))
      have hi' : i.val < k := (mem_filter.mp hi).2
      rw [heilast] at hi'
      dsimp [last] at hi'
      omega
    rw [separated_minor_one t htsep _ htb a]
    exact one_ne_zero

omit [DecidableEq D] in
/-- Exact full proper-minor price under the original anchored/full-family hypotheses. -/
theorem anchored_guard_optimal {m : ℕ} (s : State (Fin m) K (D → K)) (c : Fin m)
    (ha : Anchored s c) (hs : ∑ i, s.charge i = 0) :
    (∃ t, Run s (activeCount s - partitionCount s) t ∧ Passes t) ∧
    (∀ n t, Run s n t → Passes t → activeCount s - partitionCount s ≤ n) := by
  refine ⟨anchored_guard_attained s c ha hs, ?_⟩
  intro n t hr hp
  apply cost_lower_bound hr
  apply passes_implies_separated t _ hp
  rw [hr.total_charge, hs]

end HZ
