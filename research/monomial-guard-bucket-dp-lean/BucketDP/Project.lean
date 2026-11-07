import BucketDP.Blocks
import Dummy.Partitions

namespace BucketDP
open Finset
variable {I V : Type*} [AddCommGroup V]

/-- Remove the unique dummy by its constructor. All some i survive. -/
def real (B : List (Option I)) : List I := B.filterMap id

theorem mem_real (i : I) (B : List (Option I)) : i ∈ real B ↔ some i ∈ B := by
  simp [real]

theorem real_flat (gs : List (List (Option I))) :
    (gs.map real).flatten = real gs.flatten := by
  induction gs with
  | nil => rfl
  | cons B gs ih => simp [real, ih, List.filterMap_append]

theorem real_nodup {B : List (Option I)} (h : B.Nodup) : (real B).Nodup := by
  induction B with
  | nil => simp [real]
  | cons i B ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp h
    cases i with
    | none => exact ih hn
    | some i => exact List.nodup_cons.mpr ⟨fun hm => hi ((mem_real i B).mp hm),ih hn⟩

theorem block_nodup {gs : List (List I)} (hn : gs.flatten.Nodup) {B : List I} (hb : B ∈ gs) : B.Nodup := by
  induction gs with
  | nil => simp at hb
  | cons C cs ih =>
    obtain ⟨hc,ht,_⟩ := List.nodup_append.mp hn
    rcases List.mem_cons.mp hb with e | h
    · exact e ▸ hc
    · exact ih ht h

theorem shared_block {gs : List (List I)} (hn : gs.flatten.Nodup) {B C : List I}
    (hb : B ∈ gs) (hc : C ∈ gs) {i : I} (hi : i ∈ B) (hj : i ∈ C) : B = C := by
  induction gs with
  | nil => simp at hb
  | cons B' bs ih =>
    obtain ⟨_,ht,hd⟩ := List.nodup_append.mp hn
    rcases List.mem_cons.mp hb with eb | hb'
    · rcases List.mem_cons.mp hc with ec | hc'
      · exact eb.trans ec.symm
      · exact False.elim (hd i (eb ▸ hi) i (List.mem_flatten.mpr ⟨C,hc',hj⟩) rfl)
    · rcases List.mem_cons.mp hc with ec | hc'
      · exact False.elim (hd i (ec ▸ hj) i (List.mem_flatten.mpr ⟨B,hb',hi⟩) rfl)
      · exact ih ht hb' hc'

variable [DecidableEq I]

theorem augment_sum (y : I → V) (τ : V) (B : List (Option I)) (hn : B.Nodup) :
    (B.map (Dummy.augment y τ)).sum = ((real B).map y).sum + (if none ∈ B then -τ else 0) := by
  induction B with
  | nil => simp [real]
  | cons i B ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hn
    cases i with
    | none =>
      rw [List.map_cons, List.sum_cons, ih ht]
      simp [Dummy.augment, real, hi, add_comm]
    | some i =>
      rw [List.map_cons, List.sum_cons, ih ht]
      simp [Dummy.augment, real, add_assoc]

structure Concentrating (y : I → V) (S : Finset I) (gs : List (List I)) (τ : V) : Prop where
  unique : gs.flatten.Nodup
  covered : gs.flatten.toFinset = S
  nonempty : ∀ B ∈ gs, B ≠ []
  carrier : ∃ B ∈ gs, (B.map y).sum = τ ∧ ∀ C ∈ gs, C ≠ B → (C.map y).sum = 0

theorem project_correct (y : I → V) (S : Finset I) (τ : V) (ht : τ ≠ 0)
    (gs : List (List (Option I))) (score : ℕ)
    (h : Partition (Dummy.augment y τ) (insert none (S.image some)) gs score) :
    Concentrating y S (gs.map real) τ ∧ (gs.map real).length = score := by
  have hit (B : List (Option I)) (hb : B ∈ gs) :
      ((real B).map y).sum = if none ∈ B then τ else 0 := by
    have hsum := augment_sum y τ B (block_nodup h.unique hb)
    rw [h.zero B hb] at hsum
    by_cases hn : none ∈ B
    · rw [if_pos hn] at hsum ⊢
      apply sub_eq_zero.mp
      simpa only [sub_eq_add_neg] using hsum.symm
    · simpa [hn] using hsum.symm
  have dummy : none ∈ gs.flatten := by
    apply List.mem_toFinset.mp
    rw [h.covered]; simp
  obtain ⟨D,hD,hd⟩ := List.mem_flatten.mp dummy
  refine ⟨⟨real_flat gs ▸ real_nodup h.unique, ?_, ?_, ?_⟩, by simpa using h.count⟩
  · ext i
    simp only [List.mem_toFinset, real_flat, mem_real]
    rw [← List.mem_toFinset, h.covered]
    simp
  · intro C hc he
    obtain ⟨B,hb,rfl⟩ := List.mem_map.mp hc
    by_cases hdum : none ∈ B
    · have := hit B hb
      simp [he, hdum, Ne.symm ht] at this
    · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (h.nonempty B hb)
      cases x with
      | none => exact hdum hx
      | some j => simpa [he] using (mem_real j B).mpr hx
  · refine ⟨real D, List.mem_map.mpr ⟨D,hD,rfl⟩, by simp [hit D hD, hd], ?_⟩
    intro C hc hne
    obtain ⟨B,hb,rfl⟩ := List.mem_map.mp hc
    have hn : none ∉ B := fun hm => hne (congrArg real (shared_block h.unique hb hD hm hd))
    simp [hit B hb,hn]

end BucketDP
