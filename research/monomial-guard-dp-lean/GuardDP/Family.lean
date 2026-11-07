import GuardDP.Packing
import GuardDP.Word

open Finset
namespace GuardDP
variable {I : Type*} [LinearOrder I]

def schedule (gs : Groups I) : Plan I := gs.flatMap blockPlan

theorem disjoint_tail {B : Finset I} {gs : Groups I} (hn : (B :: gs).Nodup)
    (hd : ((B :: gs).toFinset : Set (Finset I)).PairwiseDisjoint id) :
    Disjoint B (covered gs.toFinset) ∧ (gs.toFinset : Set (Finset I)).PairwiseDisjoint id := by
  have hs : gs.toFinset ⊆ (B :: gs).toFinset := by simp
  refine ⟨disjoint_left.mpr ?_, hd.subset hs⟩
  intro i hi htail
  obtain ⟨C, hC, hiC⟩ := mem_biUnion.mp htail
  have hne : B ≠ C := fun he => (List.nodup_cons.mp hn).1 (he ▸ List.mem_toFinset.mp hC)
  exact disjoint_left.mp (hd (by simp) (hs hC) hne) hi hiC

theorem schedule_length (gs : Groups I) (hn : gs.Nodup) (hne : ∀ B ∈ gs, B.Nonempty)
    (hd : (gs.toFinset : Set (Finset I)).PairwiseDisjoint id) :
    (schedule gs).length + gs.length = (covered gs.toFinset).card := by
  induction gs with
  | nil => simp [schedule, covered]
  | cons B gs ih =>
    obtain ⟨hdis, hdt⟩ := disjoint_tail hn hd
    have htail := ih (List.nodup_cons.mp hn).2 (fun C hc => hne C (List.mem_cons_of_mem _ hc)) hdt
    have hlen := blockPlan_length B (hne B List.mem_cons_self)
    have he : covered (B :: gs).toFinset = B ∪ covered gs.toFinset := by simp [covered]
    rw [he, card_union_of_disjoint hdis]
    change (blockPlan B ++ schedule gs).length + (gs.length + 1) = _
    rw [List.length_append]
    omega

theorem schedule_target (gs : Groups I) {p : I × I} (hp : p ∈ schedule gs) :
    p.1 ∈ covered gs.toFinset := by
  obtain ⟨B, hB, hp⟩ := List.mem_flatMap.mp hp
  exact mem_biUnion.mpr ⟨B, List.mem_toFinset.mpr hB, blockPlan_target B hp⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Run each disjoint group independently. Its least label receives precisely its total. -/
theorem schedule_spec (gs : Groups I) (s : HZ.State I K V) (hn : gs.Nodup)
    (hne : ∀ B ∈ gs, B.Nonempty) (hd : (gs.toFinset : Set (Finset I)).PairwiseDisjoint id)
    (ha : ∀ B ∈ gs, ∀ i ∈ B, s.charge i ≠ 0) :
    Feasible s (schedule gs) ∧
    (∀ B (hB : B ∈ gs), ∀ i ∈ B, (runPlan s (schedule gs)).charge i =
      if i = B.min' (hne B hB) then ∑ k ∈ B, s.charge k else 0) ∧
    ∀ i ∉ covered gs.toFinset, (runPlan s (schedule gs)).charge i = s.charge i := by
  induction gs generalizing s with
  | nil => exact ⟨trivial, by simp, fun _ _ => rfl⟩
  | cons B gs ih =>
    have hb := hne B List.mem_cons_self
    obtain ⟨hdis, hdt⟩ := disjoint_tail hn hd
    let q := runPlan s (blockPlan B)
    obtain ⟨hf, hc⟩ := blockPlan_spec B hb s (ha B List.mem_cons_self)
    have out (k : I) (hk : k ∉ B) : q.charge k = s.charge k := by
      have hkj : k ≠ B.min' hb := fun e => hk (e ▸ B.min'_mem hb)
      simpa only [if_neg hkj, if_neg hk] using hc k
    have htail (C : Finset I) (hC : C ∈ gs) (k : I) (hk : k ∈ C) : q.charge k = s.charge k :=
      out k (fun hB => disjoint_left.mp hdis hB (mem_biUnion.mpr ⟨C, List.mem_toFinset.mpr hC, hk⟩))
    obtain ⟨hft, hct, hot⟩ := ih q (List.nodup_cons.mp hn).2
      (fun C hC => hne C (List.mem_cons_of_mem _ hC)) hdt
      (by intro C hC k hk; rw [htail C hC k hk]; exact ha C (List.mem_cons_of_mem _ hC) k hk)
    change Feasible s (blockPlan B ++ schedule gs) ∧ _
    refine ⟨(feasible_append ..).mpr ⟨hf, hft⟩, ?_, ?_⟩
    · intro C hC i hi
      change (runPlan s (blockPlan B ++ schedule gs)).charge i = _
      rw [runPlan_append]
      rcases List.mem_cons.mp hC with rfl | hC
      · rw [hot i (fun h => disjoint_left.mp hdis hi h), hc]
        simp [hi]
      · rw [hct C hC i hi, sum_congr rfl (fun k hk => htail C hC k hk)]
    · intro i hi
      have he : covered (B :: gs).toFinset = B ∪ covered gs.toFinset := by simp [covered]
      rw [he, mem_union, not_or] at hi
      change (runPlan s (blockPlan B ++ schedule gs)).charge i = _
      rw [runPlan_append, hot i hi.2, out i hi.1]

end GuardDP
