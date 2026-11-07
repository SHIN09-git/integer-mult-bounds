import StrideDP.Machine

namespace StrideDP
variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- One-word charge, under unit-cost scalar addition and equality. -/
def scalar (F : Type*) [AddCommGroup F] [DecidableEq F] : Arithmetic F F where
  zero := 0
  initWork := 1
  addType := fun v w => (v+w, 1)
  isZero := fun w => (decide (w=0), 1)
  denote := id
  payloadWords := fun _ => 1
  zero_ok := rfl
  add_ok := fun _ _ => rfl
  test_ok := fun _ => rfl

theorem scalar_costs : WordCosts (scalar F) 1 := by
  constructor <;> intros <;> simp [scalar]

abbrev Packed (F : Type*) (d : ℕ) := {l : List F // l.length = d}

def decode (p : Packed F d) (i : Fin d) : F := p.val[i.val]'(p.property.symm ▸ i.isLt)

/-- Each coordinate produces one eager scalar sum and one output list node. -/
def plusList [Add F'] : List F' → List F' → List F' × ℕ
  | x::xs, y::ys =>
    let r := plusList xs ys
    ((x+y)::r.1, 5 + r.2)
  | _, _ => ([], 1)

theorem plusList_value [Add F'] (xs ys : List F') : (plusList xs ys).1 = List.zipWith (·+·) xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [plusList, ih]

theorem plusList_work [Add F'] (xs ys : List F') : (plusList xs ys).2 ≤ 5 * xs.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [plusList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [plusList]
    | cons y ys =>
      have := ih ys
      simp only [plusList, List.length_cons]
      omega

def zeroList [Zero F'] [DecidableEq F'] : List F' → Bool × ℕ
  | [] => (true, 1)
  | x::xs =>
    let r := zeroList xs
    (decide (x=0) && r.1, 4 + r.2)

theorem zeroList_true [Zero F'] [DecidableEq F'] (xs : List F') :
    (zeroList xs).1 = true ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [zeroList]
  | cons x xs ih => simp [zeroList, ih]

theorem zeroList_work [Zero F'] [DecidableEq F'] (xs : List F') : (zeroList xs).2 = 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [zeroList, ih, List.length_cons]; omega

def denseAdd (v : Fin d → F) (p : Packed F d) : Packed F d × ℕ :=
  let a := plusList (List.ofFn v) p.val
  (⟨a.1, by simp [a, plusList_value, p.property]⟩, 1 + 4*d + a.2)

omit [DecidableEq F] in
theorem denseAdd_ok (v : Fin d → F) (p : Packed F d) :
    decode (denseAdd v p).1 = v + decode p := by
  funext i
  simp [decode, denseAdd, plusList_value, List.getElem_zipWith]

theorem denseTest_ok (p : Packed F d) :
    (zeroList p.val).1 = decide (decode p = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [zeroList_true, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact h _ (List.getElem_mem _)
  · intro h x hx
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
    have hi' : i < d := p.property ▸ hi
    have heq := congrFun h ⟨i, hi'⟩
    simpa only [decode, he, Pi.zero_apply] using heq

/-- The input exposes one indexed scalar per coordinate. Cached sums are eager lists;
    the denotation function is used only in proofs. -/
def dense (F : Type*) [AddCommGroup F] [DecidableEq F] (d : ℕ) : Arithmetic (Fin d → F) (Packed F d) where
  zero := ⟨List.replicate d 0, by simp⟩
  initWork := 1 + 3*d
  addType := denseAdd
  isZero := fun w => zeroList w.val
  denote := decode
  payloadWords := fun w => 1 + 3*w.val.length
  zero_ok := by funext i; simp [decode]
  add_ok := denseAdd_ok
  test_ok := denseTest_ok

theorem dense_costs (d : ℕ) : WordCosts (dense F d) d := by
  constructor
  · change 1 + 3*d ≤ _; omega
  · intro v w
    have h := plusList_work (List.ofFn v) w.val
    rw [List.length_ofFn] at h
    change 1 + 4*d + _ ≤ _
    omega
  · intro w
    change (zeroList w.val).2 ≤ _
    rw [zeroList_work, w.property]
    omega
  · intro w
    change 1 + 3*w.val.length ≤ _
    rw [w.property]
    omega

end StrideDP
