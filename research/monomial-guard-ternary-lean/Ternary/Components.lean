import Ternary.Scalar

open Finset
namespace Ternary
variable {I V : Type*} [DecidableEq I] [Fintype I] [AddCommGroup V] [Module F V]

def HasSlope (s : HZ.State I F V) (B : Finset I) : Prop := ∃ i ∈ B, s.w i ≠ 0

/-- A reverse component records final integer charges and a zero slot whenever
the restricted initial slope row is nonzero. -/
def Compatible (s : HZ.State I F V) (P : Finpartition (univ : Finset I))
    (z : I → ℤ) : Prop :=
  ∀ B ∈ P.parts,
    ((∑ i ∈ B, z i : ℤ) : F) = ∑ i ∈ B, scalar s i ∧
    (HasSlope s B → ∃ i ∈ B, z i = 0)

omit [Fintype I] in
theorem hasSlope_add (s : HZ.State I F V) {i j : I} (a : F) (hij : i ≠ j)
    (B : Finset I) (hB : i ∈ B ↔ j ∈ B) (hs : HasSlope s B) :
    HasSlope (s.addRow i j a) B := by
  obtain ⟨k, hk, hw⟩ := hs
  by_cases hkj : k = j
  · subst k
    by_cases hjw : (s.addRow i j a).w j = 0
    · have hiw : s.w i ≠ 0 := by
        intro hiw
        apply hw
        simpa [HZ.State.addRow, hiw] using hjw
      exact ⟨i, hB.mpr hk, by simpa [HZ.State.addRow, hij] using hiw⟩
    · exact ⟨j, hk, hjw⟩
  · exact ⟨k, hk, by simpa [HZ.State.addRow, hkj] using hw⟩

omit [Module F V] in
theorem compatible_merge (s : HZ.State I F V) (P : Finpartition (univ : Finset I))
    (z : I → ℤ) (hp : Compatible s P z) (A B : Finset I)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    Compatible s (HZ.mergeParts P A B hA hB hAB) z := by
  intro T hT
  rw [HZ.mergeParts_parts] at hT
  rcases mem_insert.mp hT with rfl | hT
  · have hd : Disjoint A B := P.disjoint hA hB hAB
    refine ⟨?_, ?_⟩
    · simp only [sum_union hd, Int.cast_add]
      rw [(hp A hA).1, (hp B hB).1]
    · rintro ⟨i, hi, hw⟩
      rcases mem_union.mp hi with hi | hi
      · obtain ⟨j, hj, hz⟩ := (hp A hA).2 ⟨i, hi, hw⟩
        exact ⟨j, mem_union_left _ hj, hz⟩
      · obtain ⟨j, hj, hz⟩ := (hp B hB).2 ⟨i, hi, hw⟩
        exact ⟨j, mem_union_right _ hj, hz⟩
  · exact hp T (mem_of_mem_erase (mem_of_mem_erase hT))

theorem compatible_pull (s : HZ.State I F V) {i j : I} (a : F) (hij : i ≠ j)
    (P : Finpartition (univ : Finset I)) (z : I → ℤ)
    (hp : Compatible (s.addRow i j a) P z)
    (hblocks : ∀ B ∈ P.parts, i ∈ B ↔ j ∈ B) : Compatible s P z := by
  intro B hB
  refine ⟨?_, fun hs => (hp B hB).2 (hasSlope_add s a hij B (hblocks B hB) hs)⟩
  rw [(hp B hB).1]
  exact HZ.sum_pair_conserved _ _ hij (fun k hki hkj => scalar_add_outside s a hki hkj)
    (scalar_add_pair s a hij) B (hblocks B hB)

theorem pullback_components (s : HZ.State I F V) {i j : I} (a : F) (hij : i ≠ j)
    (P : Finpartition (univ : Finset I)) (z : I → ℤ)
    (hp : Compatible (s.addRow i j a) P z) :
    ∃ Q : Finpartition (univ : Finset I), Compatible s Q z ∧ P.parts.card ≤ Q.parts.card + 1 := by
  classical
  have hi : P.part i ∈ P.parts := P.part_mem.mpr (mem_univ i)
  have hj : P.part j ∈ P.parts := P.part_mem.mpr (mem_univ j)
  have hxi : i ∈ P.part i := P.mem_part (mem_univ i)
  have hxj : j ∈ P.part j := P.mem_part (mem_univ j)
  by_cases he : P.part i = P.part j
  · refine ⟨P, compatible_pull s a hij P z hp ?_, by omega⟩
    intro B hB
    rw [← P.part_eq_iff_mem hB, ← P.part_eq_iff_mem hB, he]
  · let Q := HZ.mergeParts P (P.part i) (P.part j) hi hj he
    have hq := compatible_merge (s.addRow i j a) P z hp _ _ hi hj he
    refine ⟨Q, compatible_pull s a hij Q z hq ?_, (HZ.mergeParts_card P _ _ hi hj he).ge⟩
    intro B hB
    change B ∈ insert (P.part i ∪ P.part j) ((P.parts.erase (P.part i)).erase (P.part j)) at hB
    rcases mem_insert.mp hB with rfl | hB
    · exact iff_of_true (mem_union_left _ hxi) (mem_union_right _ hxj)
    · obtain ⟨hBj, hBi, hBP⟩ := mem_erase.mp hB |>.imp_right mem_erase.mp
      constructor
      · intro h; exact False.elim (hBi (P.part_eq_of_mem hBP h).symm)
      · intro h; exact False.elim (hBj (P.part_eq_of_mem hBP h).symm)

omit [Module F V] in
theorem compatible_permute (s : HZ.State I F V) (e : Equiv.Perm I)
    (P : Finpartition (univ : Finset I)) (z : I → ℤ)
    (hp : Compatible (s.permute e) P z) :
    Compatible s (HZ.permPartition P e) (z ∘ e.symm) := by
  intro B hB
  change B ∈ P.parts.map (HZ.finsetPerm e).toEmbedding at hB
  obtain ⟨A, hA, rfl⟩ := mem_map.mp hB
  refine ⟨?_, ?_⟩
  · simpa [HZ.finsetPerm, Equiv.finsetCongr_apply, Function.comp_def, scalar, HZ.State.permute]
      using (hp A hA).1
  · rintro ⟨i, hi, hw⟩
    change i ∈ A.map e.toEmbedding at hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    obtain ⟨k, hk, hz⟩ := (hp A hA).2 ⟨j, hj, hw⟩
    refine ⟨e k, ?_, by simpa using hz⟩
    exact mem_map.mpr ⟨k, hk, rfl⟩

theorem compatible_scale (s : HZ.State I F V) (c : I → F) (hc : ∀ i, c i ≠ 0)
    (P : Finpartition (univ : Finset I)) (z : I → ℤ)
    (hp : Compatible (s.scale c) P z) : Compatible s P z := by
  intro B hB
  refine ⟨?_, ?_⟩
  · rw [(hp B hB).1]
    apply sum_congr rfl
    intro i _
    simp only [scalar, HZ.State.scale]
    field_simp [hc i]
  · rintro ⟨i, hi, hw⟩
    apply (hp B hB).2
    refine ⟨i, hi, ?_⟩
    change (c i)⁻¹ • s.w i ≠ 0
    exact smul_ne_zero (inv_ne_zero (hc i)) hw

/-- Every successful word yields a labeled component certificate, including zero helpers. -/
theorem execution_components {s t : HZ.State I F V} {n : ℕ}
    (hr : HZ.Run s n t) (ht : HZ.Separated t) :
    ∃ (P : Finpartition (univ : Finset I)) (z : I → ℤ),
      Compatible s P z ∧ (∀ i, -1 ≤ z i ∧ z i ≤ 1) ∧
      (∑ i, z i) = imbalance t ∧ Fintype.card I ≤ n + P.parts.card := by
  classical
  induction hr with
  | nil s =>
    refine ⟨⊥, fun i => lift (scalar s i), ?_, fun i => lift_bounds _, rfl, by simp⟩
    intro B hB
    obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    refine ⟨by simp [cast_lift], ?_⟩
    rintro ⟨j, hj, hw⟩
    have hji : j = i := mem_singleton.mp hj
    subst j
    have hu : s.u i = 0 := (smul_eq_zero.mp (ht i)).resolve_right hw
    exact ⟨i, mem_singleton_self i, by simp [scalar, hu]⟩
  | @cons s g n t tail ih =>
    obtain ⟨P, z, hp, hz, htots, hn⟩ := ih ht
    cases g with
    | add i j a hij ha =>
      obtain ⟨Q, hq, hc⟩ := pullback_components s a hij P z hp
      exact ⟨Q, z, hq, hz, htots, by simp only [HZ.Operation.cost]; omega⟩
    | permute e =>
      refine ⟨HZ.permPartition P e, z ∘ e.symm, compatible_permute s e P z hp,
        fun i => hz (e.symm i), ?_, ?_⟩
      · exact (Equiv.sum_comp e.symm z).trans htots
      · simpa [HZ.Operation.cost, HZ.permPartition_card] using hn
    | scale c hc =>
      exact ⟨P, z, compatible_scale s c hc P z hp, hz, htots,
        by simpa [HZ.Operation.cost] using hn⟩

end Ternary
