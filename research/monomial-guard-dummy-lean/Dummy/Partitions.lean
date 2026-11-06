import HZ.Optimality
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Option

open Finset
namespace Dummy

variable {I V : Type*} [DecidableEq I] [Fintype I] [AddCommGroup V]

/-- The extra label exists only in this bookkeeping function, never in a State or Run. -/
def augment (y : I → V) (τ : V) : Option I → V := Option.elim' (-τ) y

omit [DecidableEq I] [Fintype I] in
@[simp] theorem augment_none (y : I → V) (τ : V) : augment y τ none = -τ := rfl
omit [DecidableEq I] [Fintype I] in
@[simp] theorem augment_some (y : I → V) (τ : V) (i : I) : augment y τ (some i) = y i := rfl

noncomputable def Zstar (y : I → V) (τ : V) : ℕ := HZ.blockCount (augment y τ)

omit [DecidableEq I] in
theorem active_augment (y : I → V) (τ : V) (hτ : τ ≠ 0) :
    HZ.active (augment y τ) = (HZ.active y).insertNone := by
  classical
  ext i
  cases i <;> simp [HZ.active, augment, hτ]

omit [DecidableEq I] in
theorem active_augment_card (y : I → V) (τ : V) (hτ : τ ≠ 0) :
    (HZ.active (augment y τ)).card = (HZ.active y).card + 1 := by
  rw [active_augment y τ hτ, card_insertNone]

omit [DecidableEq I] in
theorem sum_active (y : I → V) :
    ∑ i ∈ HZ.active y, y i = ∑ i, y i := by
  classical
  apply sum_subset (subset_univ _)
  intro i _ hi
  simpa [HZ.active] using hi

omit [DecidableEq I] in
theorem sum_augmented_active (y : I → V) (τ : V) (hτ : τ ≠ 0)
    (hs : ∑ i, y i = τ) :
    ∑ i ∈ HZ.active (augment y τ), augment y τ i = 0 := by
  rw [active_augment y τ hτ, sum_insertNone]
  simp only [augment_none, augment_some, sum_active, hs, neg_add_cancel]

omit [Fintype I] in
theorem sum_real (y : I → V) (τ : V) (B : Finset (Option I)) :
    ∑ i ∈ B, augment y τ i =
      (if none ∈ B then -τ else 0) + ∑ i ∈ B.eraseNone, y i := by
  classical
  have hh : (∑ i ∈ B.eraseNone, y i) = ∑ i ∈ B.erase none, augment y τ i := by
    rw [← B.map_some_eraseNone, sum_map]
    rfl
  rw [hh]
  by_cases hn : none ∈ B
  · rw [if_pos hn, ← sum_erase_add B (augment y τ) hn, augment_none]
    abel
  · rw [if_neg hn, erase_eq_of_notMem hn, zero_add]

omit [Fintype I] in
theorem real_nonempty (y : I → V) (τ : V) (hτ : τ ≠ 0)
    (B : Finset (Option I)) (hB : B.Nonempty) (hs : ∑ i ∈ B, augment y τ i = 0) :
    B.eraseNone.Nonempty := by
  classical
  by_contra he
  have hz : B.eraseNone = ∅ := not_nonempty_iff_eq_empty.mp he
  obtain ⟨i, hi⟩ := hB
  cases i with
  | none =>
    rw [sum_real, if_pos hi, hz, sum_empty, add_zero] at hs
    exact hτ (neg_eq_zero.mp hs)
  | some i =>
    have hm : i ∈ B.eraseNone := mem_eraseNone.mpr hi
    simp [hz] at hm

omit [DecidableEq I] [Fintype I] in
theorem eraseNone_disjoint {A B : Finset (Option I)} (hd : Disjoint A B) :
    Disjoint A.eraseNone B.eraseNone := by
  apply disjoint_left.mpr
  intro i hi hj
  exact disjoint_left.mp hd (mem_eraseNone.mp hi) (mem_eraseNone.mp hj)

/-- Delete only the bookkeeping label from a zero-sum partition. No block disappears. -/
theorem real_parts (y : I → V) (τ : V) (hτ : τ ≠ 0)
    (P : Finpartition (HZ.active (augment y τ))) (hp : HZ.ZeroSum (augment y τ) P) :
    let F := P.parts.image Finset.eraseNone
    (∀ B ∈ F, B.Nonempty) ∧
    (F : Set (Finset I)).PairwiseDisjoint id ∧
    F.biUnion id = HZ.active y ∧
    F.card = P.parts.card ∧
    ∃ B ∈ F, (∑ i ∈ B, y i) = τ ∧
      ∀ A ∈ F, A ≠ B → (∑ i ∈ A, y i) = 0 := by
  classical
  let F := P.parts.image Finset.eraseNone
  have hne : ∀ B ∈ P.parts, B.eraseNone.Nonempty :=
    fun B hB => real_nonempty y τ hτ B (P.nonempty_of_mem_parts hB) (hp B hB)
  have hinj : Set.InjOn Finset.eraseNone (P.parts : Set (Finset (Option I))) := by
    intro A hA B hB he
    obtain ⟨i, hi⟩ := hne A hA
    have hj : i ∈ B.eraseNone := by rw [← he]; exact hi
    exact P.eq_of_mem_parts hA hB (mem_eraseNone.mp hi) (mem_eraseNone.mp hj)
  have hn : none ∈ HZ.active (augment y τ) := by rw [active_augment y τ hτ]; simp
  have hR : P.part none ∈ P.parts := P.part_mem.mpr hn
  have hnone : none ∈ P.part none := P.mem_part hn
  refine ⟨?_, ?_, ?_, card_image_of_injOn hinj, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hB
    exact hne A hA
  · intro A hA B hB hAB
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hA
    obtain ⟨Y, hY, rfl⟩ := mem_image.mp hB
    exact eraseNone_disjoint (P.disjoint hX hY (by intro he; exact hAB (congrArg _ he)))
  · ext i
    simp only [mem_biUnion, mem_image, id_eq]
    constructor
    · rintro ⟨B, ⟨A, hA, rfl⟩, hi⟩
      have hh := P.subset hA (mem_eraseNone.mp hi)
      rw [active_augment y τ hτ] at hh
      simpa using hh
    · intro hi
      have hs : some i ∈ HZ.active (augment y τ) := by rw [active_augment y τ hτ]; simpa
      exact ⟨(P.part (some i)).eraseNone, ⟨P.part (some i), P.part_mem.mpr hs, rfl⟩,
        mem_eraseNone.mpr (P.mem_part hs)⟩
  · refine ⟨(P.part none).eraseNone, mem_image.mpr ⟨_, hR, rfl⟩, ?_, ?_⟩
    · have hh := hp _ hR
      rw [sum_real, if_pos hnone] at hh
      exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hh)
    · intro A hA hAB
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hA
      have hnot : none ∉ X := by
        intro hx
        exact hAB (congrArg Finset.eraseNone (P.eq_of_mem_parts hX hR hx hnone))
      have hh := hp X hX
      simpa [sum_real, hnot] using hh

end Dummy

