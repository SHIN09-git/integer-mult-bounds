import GuardDP.Table

open Finset
namespace GuardDP
variable {I V : Type*} [DecidableEq I] [AddCommGroup V]
variable {y : I → V} {S T : Finset I} {F : Finset (Finset I)}

/-- A family of disjoint nonempty zero-sum groups inside a possibly larger set. -/
structure Packing (y : I → V) (S : Finset I) (F : Finset (Finset I)) : Prop where
  nonempty : ∀ B ∈ F, B.Nonempty
  disjoint : (F : Set (Finset I)).PairwiseDisjoint id
  zero : ∀ B ∈ F, ∑ i ∈ B, y i = 0
  subset : ∀ B ∈ F, B ⊆ S

theorem Packing.covered_subset (h : Packing y S F) : covered F ⊆ S := by
  intro i hi
  obtain ⟨B, hB, hi⟩ := mem_biUnion.mp hi
  exact h.subset B hB hi

theorem Packing.sum_covered (h : Packing y S F) : ∑ i ∈ covered F, y i = 0 := by
  rw [covered, sum_biUnion h.disjoint]
  exact sum_eq_zero h.zero

omit [DecidableEq I] in
theorem Packing.mono (h : Packing y S F) (hst : S ⊆ T) : Packing y T F :=
  { h with subset := fun B hB => (h.subset B hB).trans hst }

theorem Packing.erase_label (h : Packing y S F) {i : I} (hi : i ∉ covered F) :
    Packing y (S.erase i) F := by
  refine { h with subset := ?_ }
  intro B hB k hk
  exact mem_erase.mpr ⟨fun e => hi (e ▸ mem_biUnion.mpr ⟨B, hB, hk⟩), h.subset B hB hk⟩

theorem Packing.erase_group (h : Packing y S F) {B : Finset I} (hB : B ∈ F)
    {i : I} (hi : i ∈ B) : Packing y (S.erase i) (F.erase B) := by
  refine ⟨fun C hC => h.nonempty C (mem_of_mem_erase hC), h.disjoint.subset (erase_subset ..),
    fun C hC => h.zero C (mem_of_mem_erase hC), ?_⟩
  intro C hC k hk
  obtain ⟨hne, hCF⟩ := mem_erase.mp hC
  refine mem_erase.mpr ⟨?_, h.subset C hCF hk⟩
  rintro rfl
  exact disjoint_left.mp (h.disjoint hCF hB hne) hk hi

theorem Packing.close (h : Packing y S F) (hz : ∑ i ∈ S, y i = 0)
    {i : I} (hi : i ∈ S) (fresh : i ∉ covered F) :
    let B := S \ covered F
    B ∉ F ∧ Packing y S (insert B F) ∧ covered (insert B F) = S := by
  let B := S \ covered F
  have hiB : i ∈ B := mem_sdiff.mpr ⟨hi, fresh⟩
  have hd : ∀ C ∈ F, Disjoint B C := by
    intro C hC
    apply disjoint_left.mpr
    intro k hkB hkC
    exact (mem_sdiff.mp hkB).2 (mem_biUnion.mpr ⟨C, hC, hkC⟩)
  have hn : B ∉ F := fun hB => fresh (mem_biUnion.mpr ⟨B, hB, hiB⟩)
  have hsum := sum_sdiff h.covered_subset (f := y)
  rw [h.sum_covered, hz, add_zero] at hsum
  refine ⟨hn, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro C hC
    rcases mem_insert.mp hC with rfl | hc
    · exact ⟨i, hiB⟩
    · exact h.nonempty _ hc
  · intro C hC D hD hne
    rcases mem_insert.mp hC with rfl | hc <;> rcases mem_insert.mp hD with rfl | hd'
    · exact False.elim (hne rfl)
    · exact hd _ hd'
    · exact (hd _ hc).symm
    · exact h.disjoint hc hd' hne
  · intro C hC
    rcases mem_insert.mp hC with rfl | hc
    · exact hsum
    · exact h.zero _ hc
  · intro C hC
    rcases mem_insert.mp hC with rfl | hc
    · exact sdiff_subset
    · exact h.subset _ hc
  · change (insert B F).biUnion id = S
    rw [biUnion_insert, id_eq]
    exact sdiff_union_of_subset h.covered_subset

def Packing.partition (h : Packing y S F) (hc : covered F = S) : Finpartition S :=
  Finpartition.ofExistsUnique F h.subset (by
    intro i hi
    rw [← hc] at hi
    obtain ⟨B, hB, hiB⟩ := mem_biUnion.mp hi
    refine ⟨B, ⟨hB, hiB⟩, ?_⟩
    rintro C ⟨hC, hiC⟩
    by_contra hne
    exact disjoint_left.mp (h.disjoint hC hB hne) hiC hiB)
    (fun he => (h.nonempty _ he).ne_empty rfl)

theorem packing_of_partition (P : Finpartition S) (hz : HZ.ZeroSum y P) :
    Packing y S P.parts :=
  ⟨fun _ => P.nonempty_of_mem_parts, P.disjoint, hz, fun _ => P.subset⟩

end GuardDP
