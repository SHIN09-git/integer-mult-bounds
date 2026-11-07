import CountDP.Groups
import GuardDP.Solver

open Finset
namespace CountDP
variable {I K V : Type*} [LinearOrder I] [Fintype I] [Field K] [AddCommGroup V] [Module K V]

/-- Compile groups using the original state to compute each actual row coefficient. -/
def wordFromGroups (s : HZ.State I K V) (gs : GuardDP.Groups I) : List (GuardDP.Gate I K) :=
  GuardDP.emit s (GuardDP.schedule gs)

private theorem compiled_groups (s : HZ.State I K V) (gs : GuardDP.Groups I)
    (hn : gs.Nodup) (hne : ∀ B ∈ gs, B.Nonempty)
    (hd : (gs.toFinset : Set (Finset I)).PairwiseDisjoint id)
    (hc : GuardDP.covered gs.toFinset = HZ.active s.charge) :
    let w := wordFromGroups s gs
    let t := GuardDP.execute s w
    (∀ g ∈ w, g.Legal) ∧ w.length = HZ.activeCount s - gs.length ∧
    (∀ B (hB : B ∈ gs), ∀ i ∈ B, t.charge i =
      if i = B.min' (hne B hB) then ∑ k ∈ B, s.charge k else 0) ∧
    ∀ i ∉ GuardDP.covered gs.toFinset, t.charge i = 0 := by
  have ha B (hB : B ∈ gs) i (hi : i ∈ B) : s.charge i ≠ 0 := by
    have h : i ∈ GuardDP.covered gs.toFinset := mem_biUnion.mpr ⟨B, List.mem_toFinset.mpr hB, hi⟩
    rw [hc] at h
    simpa [HZ.active] using h
  obtain ⟨hf, hin, hout⟩ := GuardDP.schedule_spec gs s hn hne hd ha
  have hlen := GuardDP.schedule_length gs hn hne hd
  rw [hc] at hlen
  dsimp only [wordFromGroups]
  rw [GuardDP.execute_emit, GuardDP.emit_length]
  refine ⟨GuardDP.emit_legal _ _ hf, ?_, hin, ?_⟩
  · unfold HZ.activeCount
    omega
  · intro i hi
    rw [hout i hi]
    rw [hc] at hi
    simpa [HZ.active] using hi

variable [DecidableEq V]

def separationWord (s : HZ.State I K V) : List (GuardDP.Gate I K) := wordFromGroups s (zeroGroups s.charge)

def concentrationWord (s : HZ.State I K V) (τ : V) : List (GuardDP.Gate I K) :=
  wordFromGroups s (realGroups s.charge τ)

theorem separationWord_optimal (s : HZ.State I K V) (hs : ∑ i, s.charge i = 0) :
    GuardDP.OptimalWord s HZ.Separated (HZ.activeCount s - HZ.partitionCount s) (separationWord s) := by
  let gs := zeroGroups s.charge
  have opt := zero_optimal s.charge hs
  have hne (B : Finset I) (hB : B ∈ gs) := opt.packing.nonempty B (List.mem_toFinset.mpr hB)
  obtain ⟨hl, hlen, hin, hout⟩ := compiled_groups s gs opt.nodup hne opt.packing.disjoint
    (opt.full ((Dummy.sum_active _).trans hs))
  have he : gs.length = HZ.partitionCount s := computes_Z _ hs
  rw [he] at hlen
  refine ⟨hl, ?_, hlen, fun hr ht => hlen ▸ HZ.cost_lower_bound hr ht⟩
  intro i
  by_cases hi : i ∈ GuardDP.covered gs.toFinset
  · obtain ⟨B, hB, hiB⟩ := mem_biUnion.mp hi
    change (GuardDP.execute s (wordFromGroups s gs)).charge i = 0
    rw [hin B (List.mem_toFinset.mp hB) i hiB, opt.packing.zero B hB, ite_self]
  · exact hout i hi

/-- Projection erases the actual virtual label, even when its charge is also a real type. -/
theorem real_partition (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    let gs := realGroups y τ
    gs.Nodup ∧ (∀ B ∈ gs, B.Nonempty) ∧ (gs.toFinset : Set (Finset I)).PairwiseDisjoint id ∧
    GuardDP.covered gs.toFinset = HZ.active y ∧
    ∃ B ∈ gs, (∑ i ∈ B, y i) = τ ∧ ∀ A ∈ gs, A ≠ B → (∑ i ∈ A, y i) = 0 := by
  let a := augmentedGroups y τ
  have opt := augmented_optimal y τ ht hs
  let P := opt.packing.partition (opt.full (Dummy.sum_augmented_active y τ ht hs))
  obtain ⟨hne, hd, hc, hcard, B, hB, hsum, hother⟩ := Dummy.real_parts y τ ht P opt.packing.zero
  have he : (realGroups y τ).toFinset = P.parts.image Finset.eraseNone := by
    change (a.map Finset.eraseNone).toFinset = a.toFinset.image Finset.eraseNone
    ext C
    simp
  have hn : (realGroups y τ).Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (⟦realGroups y τ⟧ : Multiset (Finset I)))).mp
    change (realGroups y τ).toFinset.card = (realGroups y τ).length
    rw [he, hcard]
    change a.toFinset.card = (a.map Finset.eraseNone).length
    rw [List.length_map, List.toFinset_card_of_nodup opt.nodup]
  refine ⟨hn, ?_, by rw [he]; exact hd, by rw [he]; exact hc, B, ?_, hsum, ?_⟩
  · exact fun C hm => hne C (he ▸ List.mem_toFinset.mpr hm)
  · exact List.mem_toFinset.mp (he ▸ hB)
  · exact fun C hm hCB => hother C (he ▸ List.mem_toFinset.mpr hm) hCB

omit [Fintype I] [DecidableEq V] in
private theorem charges_concentrated (gs : GuardDP.Groups I) (y q : I → V) (τ : V)
    (hne : ∀ B ∈ gs, B.Nonempty) (B : Finset I) (hB : B ∈ gs) (hτ : ∑ i ∈ B, y i = τ)
    (hz : ∀ C ∈ gs, C ≠ B → ∑ i ∈ C, y i = 0)
    (hin : ∀ C (hC : C ∈ gs), ∀ i ∈ C, q i = if i = C.min' (hne C hC) then ∑ k ∈ C, y k else 0)
    (hout : ∀ i ∉ GuardDP.covered gs.toFinset, q i = 0) :
    ∃ c, ∀ i, q i = if i = c then τ else 0 := by
  let c := B.min' (hne B hB)
  refine ⟨c, fun i => ?_⟩
  by_cases hic : i = c
  · subst i
    rw [hin B hB c (B.min'_mem _), if_pos (rfl : c = B.min' _), hτ, if_pos rfl]
  · rw [if_neg hic]
    by_cases hi : i ∈ GuardDP.covered gs.toFinset
    · obtain ⟨C, hC, hiC⟩ := mem_biUnion.mp hi
      have hm := List.mem_toFinset.mp hC
      rw [hin C hm i hiC]
      by_cases he : C = B
      · subst C
        exact if_neg hic
      · rw [hz C hm he, ite_self]
    · exact hout i hi

theorem concentrationWord_optimal (s : HZ.State I K V) (τ : V) (ht : τ ≠ 0)
    (hs : ∑ i, s.charge i = τ) :
    GuardDP.OptimalWord s (fun t => Dummy.Concentrated t τ)
      (HZ.activeCount s - Dummy.Zstar s.charge τ) (concentrationWord s τ) := by
  let gs := realGroups s.charge τ
  obtain ⟨hn, hne, hd, hc, B, hB, hτ, hz⟩ := real_partition s.charge τ ht hs
  obtain ⟨hl, hlen, hin, hout⟩ := compiled_groups s gs hn hne hd hc
  have he : gs.length = Dummy.Zstar s.charge τ := by
    simpa only [gs, realGroups, List.length_map] using computes_Zstar s.charge τ ht hs
  rw [he] at hlen
  refine ⟨hl, ?_, hlen, fun hr hg => hlen ▸ Dummy.cost_lower_bound ht hr hg⟩
  exact charges_concentrated gs s.charge (GuardDP.execute s (wordFromGroups s gs)).charge τ
    hne B hB hτ hz hin hout

end CountDP
