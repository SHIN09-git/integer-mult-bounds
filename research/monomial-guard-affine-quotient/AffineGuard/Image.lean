import OrbitGuard.Fixed

namespace AffineGuard
open Finset Ternary OrbitGuard

/-- Ordered primal column and the set of all dual columns, independent of parameter dimension. -/
abbrev Data (I : Type*) := (I → F) × Finset (I → F)

variable {I J D E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

def data (s : State I D) : Data I := (s.u, univ.image (HZ.familyRow s))

omit [DecidableEq I] in
theorem mem_image (s : State I D) (z : I → F) :
    z ∈ (data s).2 ↔ ∃ a, HZ.familyRow s a = z := by simp [data]

def primal (op : HZ.Operation I F) (u : I → F) : I → F :=
  match op with
  | .add i j c _ _ => Function.update u i (u i + c * u j)
  | .permute e => u ∘ e
  | .scale c _ => fun i => c i * u i

def dual (op : HZ.Operation I F) (z : I → F) : I → F :=
  match op with
  | .add i j c _ _ => Function.update z j (z j - c * z i)
  | .permute e => z ∘ e
  | .scale c _ => fun i => (c i)⁻¹ * z i

def step (op : HZ.Operation I F) (x : Data I) : Data I :=
  (primal op x.1, x.2.image (dual op))

omit [Fintype I] [DecidableEq D] in
theorem family_step (op : HZ.Operation I F) (s : State I D) (a : D → F) :
    HZ.familyRow (op.apply s) a = dual op (HZ.familyRow s a) := by
  cases op with
  | add i j c hij hc =>
    funext k
    by_cases h : k = j
    · subst k
      simp [HZ.Operation.apply, HZ.State.addRow, HZ.familyRow, dual, mul_sub, mul_add,
        Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm]
      ring
    · simp [HZ.Operation.apply, HZ.State.addRow, HZ.familyRow, dual, h]
  | permute e => rfl
  | scale c hc =>
    funext k
    simp [HZ.Operation.apply, HZ.State.scale, HZ.familyRow, dual, mul_add, Finset.mul_sum,
      mul_left_comm]

theorem data_step (op : HZ.Operation I F) (s : State I D) :
    data (op.apply s) = step op (data s) := by
  apply Prod.ext
  · cases op <;> rfl
  · change univ.image _ = (univ.image (HZ.familyRow s)).image (dual op)
    rw [Finset.image_image]
    exact Finset.image_congr fun a _ => family_step op s a

theorem step_congr {s : State I D} {t : State I E} (h : data s = data t)
    (op : HZ.Operation I F) : data (op.apply s) = data (op.apply t) := by
  rw [data_step, data_step, h]

def execute (s : State I D) (ops : List (HZ.Operation I F)) : State I D :=
  ops.foldl (fun t op => op.apply t) s

theorem word_congr {s : State I D} {t : State I E} (h : data s = data t)
    (ops : List (HZ.Operation I F)) : data (execute s ops) = data (execute t ops) := by
  induction ops generalizing s t with
  | nil => exact h
  | cons op _ ih => exact ih (step_congr h op)

omit [DecidableEq I] [DecidableEq J] in
theorem data_reindex (s : State I D) (e : J ≃ I) :
    data (reindex s e) = ((data s).1 ∘ e, (data s).2.image (fun z => z ∘ e)) := by
  apply Prod.ext
  · rfl
  · change univ.image _ = (univ.image (HZ.familyRow s)).image _
    rw [Finset.image_image]
    rfl

theorem passes_data {m : ℕ} (s : State (Fin m) D) :
    HZ.Passes s ↔ ∀ k, k < m → ∀ z ∈ (data s).2,
      1 - ∑ i ∈ HZ.prefixSet m k, (data s).1 i * z i ≠ 0 := by
  constructor
  · intro h k hk z hz
    obtain ⟨a,rfl⟩ := (mem_image s z).mp hz
    simpa only [HZ.principalMinor_eq, data] using h k hk a
  · intro h k hk a
    rw [HZ.principalMinor_eq]
    exact h k hk _ ((mem_image s _).mpr ⟨a,rfl⟩)

theorem passes_congr {m : ℕ} {s : State (Fin m) D} {t : State (Fin m) E}
    (h : data s = data t) : HZ.Passes s ↔ HZ.Passes t := by rw [passes_data, passes_data, h]

/-- Identical physical word, identical final order, possibly different parameter dimensions. -/
theorem word_order_iff {m : ℕ} {s : State (Fin m) D} {t : State (Fin m) E}
    (h : data s = data t) (ops : List (HZ.Operation (Fin m) F)) (e : Equiv.Perm (Fin m)) :
    HZ.Passes ((execute s ops).permute e) ↔ HZ.Passes ((execute t ops).permute e) :=
  passes_congr (step_congr (word_congr h ops) (.permute e))

omit [DecidableEq I] in
theorem guard_congr {s : State I D} {t : State I E} (h : data s = data t) :
    FullGuard s ↔ FullGuard t := by
  unfold FullGuard
  refine exists_congr fun m => exists_congr fun e => passes_congr ?_
  rw [data_reindex, data_reindex, h]

/-- Pull back a presentation along the affine parameter map a ↦ t + A a. -/
def reparam (s : State I D) (A : D → E → F) (t : D → F) : State I E :=
  ⟨s.u, fun i j => ∑ d, A d j * s.w i d, HZ.familyRow s t⟩

def linearPart (A : D → E → F) (a : E → F) (d : D) : F := ∑ j, a j * A d j

omit [Fintype I] [DecidableEq I] [DecidableEq D] [DecidableEq E] in
theorem family_reparam (s : State I D) (A : D → E → F) (t : D → F) (a : E → F) :
    HZ.familyRow (reparam s A t) a = HZ.familyRow s (t + linearPart A a) := by
  funext i
  have swap : (∑ j, a j * ∑ d, A d j * s.w i d) =
      ∑ d, (∑ j, a j * A d j) * s.w i d := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  simp only [reparam, HZ.familyRow, linearPart, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [swap, add_assoc]

omit [DecidableEq I] in
theorem data_reparam (s : State I D) (A : D → E → F)
    (hA : Function.Surjective (linearPart A)) (t : D → F) :
    data (reparam s A t) = data s := by
  apply Prod.ext
  · rfl
  · ext z
    rw [mem_image, mem_image]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨_,(family_reparam s A t a).symm⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨x,hx⟩ := hA (a - t)
      exact ⟨x,by rw [family_reparam, hx, add_sub_cancel]⟩

end AffineGuard
