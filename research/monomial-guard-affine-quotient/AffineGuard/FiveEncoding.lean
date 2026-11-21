import AffineGuard.Examples

/-! Compact complete-row and affine-image keys for the five-row, one-parameter calculation. -/

namespace AffineGuard.Census
open Finset Ternary
open OrbitGuard (State Row Gate vertex row tag bag)

abbrev Model := State (Fin 5) (Fin 1)
abbrev R := Row (Fin 1)
abbrev Code := List ℕ

def raw (r : R) : ℕ := 9 * r.1.val + 3 * (r.2.1 0).val + r.2.2.val

def digit (r : R) : ℕ := min (raw r) (raw (OrbitGuard.flip r))

def unpack (x : ℕ) : R := (↑(x / 9), fun _ => ↑(x / 3 % 3), ↑(x % 3))

private theorem digit_tag : ∀ a b : R, digit a = digit b ↔ tag a = tag b := by decide

private theorem digit_unpack : ∀ r : R, digit (unpack (digit r)) = digit r := by decide

def rowKey (s : Model) : Code := (List.ofFn fun i => digit (row s i)).insertionSort (· ≤ ·)

/-- Read a stored list back into a labeled state. Reachable codes always have five digits. -/
def readCode (l : Code) : Model :=
  let f (i : Fin 5) := unpack (l[i.val]?.getD 0)
  ⟨fun i => (f i).1, fun i => (f i).2.1, fun i => (f i).2.2⟩

private theorem bag_ofFn (f : Fin 5 → α) : (↑(List.ofFn f) : Multiset α) = bag f := by
  have aux (n : ℕ) (g : Fin n → α) : (↑(List.ofFn g) : Multiset α) = ∑ i, {g i} := by
    induction n with
    | zero => simp
    | succ n ih => rw [List.ofFn_succ, ← Multiset.cons_coe, Fin.sum_univ_succ, Multiset.singleton_add, ih]
  exact aux 5 f

private theorem bag_transfer {f g : Fin 5 → α} {u v : Fin 5 → β}
    (h : ∀ i j, f i = g j → u i = v j) (hfg : bag f = bag g) : bag u = bag v := by
  classical
  obtain ⟨e,he⟩ := OrbitGuard.match_bag f g hfg
  have huv : (fun i => u (e i)) = v := funext fun i => h _ _ (he i)
  calc
    bag u = bag (fun i => u (e i)) := (Equiv.sum_comp e (fun i => ({u i} : Multiset β))).symm
    _ = bag v := congrArg bag huv

private theorem bag_digits (s : Model) : (↑(rowKey s) : Multiset ℕ) = bag (fun i => digit (row s i)) := by
  exact (Multiset.coe_eq_coe.mpr (List.perm_insertionSort (· ≤ ·) _)).trans (bag_ofFn _)

theorem rowKey_iff (s t : Model) : rowKey s = rowKey t ↔ vertex s = vertex t := by
  constructor
  · intro h
    have hb := (bag_digits s).symm.trans ((congrArg (fun l : Code => (l : Multiset ℕ)) h).trans (bag_digits t))
    exact Subtype.ext (bag_transfer (fun i j => (digit_tag (row s i) (row t j)).mp) hb)
  · intro h
    have hb := bag_transfer (fun i j => (digit_tag (row s i) (row t j)).mpr) (congrArg Subtype.val h)
    have he := (bag_digits s).trans (hb.trans (bag_digits t).symm)
    exact List.eq_of_perm_of_sorted (r := (LE.le : ℕ → ℕ → Prop)) (Multiset.coe_eq_coe.mp he)
      (List.sorted_insertionSort (· ≤ ·) _) (List.sorted_insertionSort (· ≤ ·) _)

theorem rowKey_read (s : Model) : rowKey (readCode (rowKey s)) = rowKey s := by
  let l := rowKey s
  have hl : l.length = 5 := by simp only [l, rowKey, List.length_insertionSort, List.length_ofFn]
  have hd (x) (hx : x ∈ l) : digit (unpack x) = x := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ((List.perm_insertionSort (· ≤ ·) _).mem_iff.mp hx)
    exact digit_unpack _
  have h : (List.ofFn fun i => digit (row (readCode l) i)) = l := by
    apply List.ext_getElem (by simp [hl])
    intro j hj hj'
    simp only [List.getElem_ofFn, readCode, row, List.getElem?_eq_getElem hj', Option.getD_some]
    exact hd _ (List.getElem_mem hj')
  change (List.ofFn _).insertionSort (· ≤ ·) = l
  rw [h]
  exact List.Sorted.insertionSort_eq (List.sorted_insertionSort (· ≤ ·) _)

def changeParam (s : Model) (c b : F) : Model :=
  ⟨s.u, fun i _ => c * s.w i 0, fun i => s.b i + b * s.w i 0⟩

def column (s : Model) (a : F) (i : Fin 5) : F := s.b i + a * s.w i 0

private theorem mem_column (s : Model) (z : Fin 5 → F) : z ∈ (data s).2 ↔ ∃ a, column s a = z := by
  rw [mem_image]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a 0, by funext i; simp [column,HZ.familyRow]⟩
  · rintro ⟨a,rfl⟩
    exact ⟨fun _ => a, by funext i; simp [column,HZ.familyRow]⟩

private theorem column_mem (s : Model) (a : F) : column s a ∈ (data s).2 :=
  (mem_column s _).mpr ⟨a,rfl⟩

private theorem column_change (s : Model) (c b a : F) :
    column (changeParam s c b) a = column s (b + a * c) := by
  funext i
  simp only [column, changeParam]
  ring

theorem data_change (s : Model) (c b : F) (hc : c ≠ 0) : data (changeParam s c b) = data s := by
  apply Prod.ext
  · rfl
  · ext z
    rw [mem_column,mem_column]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨_,(column_change s c b a).symm⟩
    · rintro ⟨a,rfl⟩
      refine ⟨(a-b)/c, ?_⟩
      rw [column_change,div_mul_cancel₀ _ hc,add_sub_cancel]

/-- Equal affine images of a single ternary parameter differ by a common invertible
parameter change, including when the image is a single point. -/
theorem change_of_data {s t : Model} (h : data s = data t) :
    ∃ c b : F, c ≠ 0 ∧ changeParam s c b = t := by
  have hu : s.u = t.u := congrArg Prod.fst h
  have hr : ∀ a, ∃ x, column s x = column t a := fun a =>
    (mem_column s _).mp (h ▸ column_mem t a)
  obtain ⟨b,hb⟩ := hr 0
  obtain ⟨v,hv⟩ := hr 1
  have base (i) : s.b i + b * s.w i 0 = t.b i := by simpa [column] using congrFun hb i
  have slope (i) : (v-b) * s.w i 0 = t.w i 0 := by
    have h1 : s.b i + v * s.w i 0 = t.b i + t.w i 0 := by simpa [column] using congrFun hv i
    linear_combination h1 - base i
  by_cases hvb : v = b
  · have ht (i) : t.w i 0 = 0 := by simpa [hvb] using (slope i).symm
    obtain ⟨x,hx⟩ := (mem_column t _).mp (h ▸ column_mem s 1)
    obtain ⟨y,hy⟩ := (mem_column t _).mp (h ▸ column_mem s 0)
    have hs (i) : s.w i 0 = 0 := by
      have h1 := congrFun hx i
      have h0 := congrFun hy i
      simp [column,ht] at h1 h0
      linear_combination h0 - h1
    refine ⟨1,b,one_ne_zero,HZ.State.ext hu ?_ (funext base)⟩
    funext i j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [changeParam,hj,hs,ht]
  · refine ⟨v-b,b,sub_ne_zero.mpr hvb,HZ.State.ext hu ?_ (funext base)⟩
    funext i j
    rw [show j = 0 from Subsingleton.elim _ _]
    exact slope i

private theorem frame_change (q : OrbitGuard.Frame (Fin 5)) (s : Model) (c b : F) :
    changeParam (q.act s) c b = q.act (changeParam s c b) := by
  apply HZ.State.ext
  · rfl
  · funext i j
    simp [changeParam,OrbitGuard.Frame.act,HZ.State.scale,HZ.State.permute,mul_left_comm]
  · funext i
    simp [changeParam,OrbitGuard.Frame.act,HZ.State.scale,HZ.State.permute,mul_add,mul_left_comm]

/-- The six one-parameter maps give a finite set of complete-row keys. -/
def variants (s : Model) : Finset Code :=
  (univ : Finset (Fˣ × F)).image fun p => rowKey (changeParam s p.1 p.2)

theorem key_iff_variant (s t : Model) : key s = key t ↔ rowKey t ∈ variants s := by
  simp only [variants,Finset.mem_image,mem_univ,true_and]
  constructor
  · intro h
    obtain ⟨q,hq⟩ := (key_eq_iff s t).mp h
    obtain ⟨c,b,hc,he⟩ := change_of_data hq
    refine ⟨(Units.mk0 c hc,b),(rowKey_iff _ _).mpr ?_⟩
    rw [← he,frame_change,OrbitGuard.vertex_frame]
    rfl
  · rintro ⟨⟨c,b⟩,h⟩
    exact (congrArg orbit (data_change s c b c.ne_zero)).symm.trans (key_of_vertex ((rowKey_iff _ _).mp h))

private theorem variant_mem (s : Model) (k : Code) :
    k ∈ variants s ↔ ∃ t : Model, key s = key t ∧ rowKey t = k := by
  constructor
  · intro hk
    obtain ⟨⟨c,b⟩,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨_,(congrArg orbit (data_change s c b c.ne_zero)).symm,rfl⟩
  · rintro ⟨t,h,rfl⟩
    exact (key_iff_variant s t).mp h

private theorem variants_ne (s : Model) : (variants s).Nonempty :=
  ⟨_,(key_iff_variant s s).mp rfl⟩

def affineKey (s : Model) : Code := (variants s).min' (variants_ne s)

theorem affineKey_iff (s t : Model) : affineKey s = affineKey t ↔ key s = key t := by
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := (variant_mem s _).mp (Finset.min'_mem _ (variants_ne s))
    obtain ⟨u,hu,hf⟩ := (variant_mem t _).mp (Finset.min'_mem _ (variants_ne t))
    exact hr.trans ((key_of_vertex ((rowKey_iff r u).mp (he.trans (h.trans hf.symm)))).trans hu.symm)
  · intro h
    have he : variants s = variants t := by ext k; rw [variant_mem,variant_mem,h]
    simp only [affineKey,he]

end AffineGuard.Census
