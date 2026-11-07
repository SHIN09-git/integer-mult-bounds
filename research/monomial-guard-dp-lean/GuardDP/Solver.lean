import GuardDP.Labels
import GuardDP.Family
import Dummy.Optimality

open Finset
namespace GuardDP
variable {I K V : Type*} [LinearOrder I] [Fintype I] [Field K] [AddCommGroup V] [Module K V]

/-- The emitted instructions are legal, reach the goal, and have minimum paid cost. -/
structure OptimalWord (s : HZ.State I K V) (goal : HZ.State I K V → Prop) (cost : ℕ)
    (word : List (Gate I K)) : Prop where
  legal : ∀ g ∈ word, g.Legal
  reaches : goal (execute s word)
  length_eq : word.length = cost
  minimum : ∀ {n t}, HZ.Run s n t → goal t → word.length ≤ n

omit [Fintype I] in
theorem OptimalWord.run {s : HZ.State I K V} {goal : HZ.State I K V → Prop} {n : ℕ}
    {word : List (Gate I K)} (h : OptimalWord s goal n word) :
    HZ.Run s n (execute s word) := h.length_eq ▸ execute_run s word h.legal

variable [DecidableEq V]

def separationWord (s : HZ.State I K V) : List (Gate I K) :=
  emit s (schedule (zeroGroups s.charge))

def concentrationWord (s : HZ.State I K V) (τ : V) : List (Gate I K) :=
  emit s (schedule (realGroups s.charge τ))

omit [DecidableEq V] in
private theorem covered_active {s : HZ.State I K V} {gs : Groups I}
    (h : covered gs.toFinset = HZ.active s.charge) {B : Finset I} (hB : B ∈ gs) {i : I}
    (hi : i ∈ B) : s.charge i ≠ 0 := by
  have hm : i ∈ covered gs.toFinset := mem_biUnion.mpr ⟨B, List.mem_toFinset.mpr hB, hi⟩
  rw [h] at hm
  simpa [HZ.active] using hm

theorem separationWord_optimal (s : HZ.State I K V) (hs : ∑ i, s.charge i = 0) :
    OptimalWord s HZ.Separated (HZ.activeCount s - HZ.partitionCount s) (separationWord s) := by
  let gs := zeroGroups s.charge
  have opt := zeroGroups_optimal s.charge
  have hc := opt.full ((Dummy.sum_active _).trans hs)
  have hne (B : Finset I) (hB : B ∈ gs) := opt.packing.nonempty B (List.mem_toFinset.mpr hB)
  obtain ⟨hf, hin, hout⟩ := schedule_spec gs s opt.nodup hne opt.packing.disjoint
    (fun _ hB _ hi => covered_active hc hB hi)
  have hlen : (separationWord s).length = HZ.activeCount s - HZ.partitionCount s := by
    have h := schedule_length gs opt.nodup hne opt.packing.disjoint
    change (covered gs.toFinset) = HZ.active s.charge at hc
    rw [hc] at h
    have hz : gs.length = HZ.partitionCount s := computes_Z _ hs
    change (emit s (schedule gs)).length = (HZ.active s.charge).card - HZ.partitionCount s
    rw [emit_length]
    omega
  refine ⟨emit_legal _ _ hf, ?_, hlen, fun hr ht => hlen ▸ HZ.cost_lower_bound hr ht⟩
  change HZ.Separated (execute s (emit s (schedule gs)))
  rw [execute_emit]
  intro i
  by_cases hi : i ∈ covered gs.toFinset
  · obtain ⟨B, hB, hiB⟩ := mem_biUnion.mp hi
    rw [hin B (List.mem_toFinset.mp hB) i hiB, opt.packing.zero B hB, ite_self]
  · rw [hout i hi]
    rw [show covered gs.toFinset = _ from hc] at hi
    simpa [HZ.active] using hi

theorem concentrationWord_optimal (s : HZ.State I K V) (τ : V) (ht : τ ≠ 0)
    (hs : ∑ i, s.charge i = τ) :
    OptimalWord s (fun t => Dummy.Concentrated t τ) (HZ.activeCount s - Dummy.Zstar s.charge τ)
      (concentrationWord s τ) := by
  let gs := realGroups s.charge τ
  obtain ⟨hn, hne, hd, hc, B, hB, hτ, hz⟩ := realGroups_spec s.charge τ ht hs
  obtain ⟨hf, hin, hout⟩ := schedule_spec gs s hn hne hd
    (fun _ hC _ hi => covered_active hc hC hi)
  have hlen : (concentrationWord s τ).length = HZ.activeCount s - Dummy.Zstar s.charge τ := by
    have h := schedule_length gs hn hne hd
    rw [show covered gs.toFinset = _ from hc] at h
    have hnum : gs.length = Dummy.Zstar s.charge τ := by
      simpa only [gs, realGroups, List.length_map] using computes_Zstar s.charge τ ht hs
    change (emit s (schedule gs)).length = (HZ.active s.charge).card - Dummy.Zstar s.charge τ
    rw [emit_length]
    omega
  refine ⟨emit_legal _ _ hf, ?_, hlen, fun hr hgoal => hlen ▸ Dummy.cost_lower_bound ht hr hgoal⟩
  change Dummy.Concentrated (execute s (emit s (schedule gs))) τ
  rw [execute_emit]
  let c := B.min' (hne B hB)
  have hcb : c ∈ B := B.min'_mem _
  refine ⟨c, fun i => ?_⟩
  by_cases hi : i ∈ covered gs.toFinset
  · obtain ⟨C, hC, hiC⟩ := mem_biUnion.mp hi
    have hm := List.mem_toFinset.mp hC
    rw [hin C hm i hiC]
    by_cases he : C = B
    · subst C
      rw [hτ]
    · have hic : i ≠ c := by
        rintro rfl
        exact disjoint_left.mp (hd hC (List.mem_toFinset.mpr hB) he) hiC hcb
      rw [hz C hm he, if_neg hic, ite_self]
  · have hic : i ≠ c := by
      rintro rfl
      exact hi (mem_biUnion.mpr ⟨B, List.mem_toFinset.mpr hB, hcb⟩)
    rw [hout i hi, if_neg hic]
    rw [show covered gs.toFinset = _ from hc] at hi
    simpa [HZ.active] using hi

end GuardDP
