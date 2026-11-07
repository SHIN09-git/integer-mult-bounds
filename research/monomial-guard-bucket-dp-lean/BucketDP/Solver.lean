import BucketDP.Raw
import BucketDP.Recover
import BucketDP.Emit
import StrideDP.Dense

namespace BucketDP
open CountDP Finset GuardDP
variable {I K V : Type*} [LinearOrder I] [Fintype I] [Field K] [AddCommGroup V] [Module K V]

private theorem compile_zero (s : HZ.State I K V) (gs : List (List I))
    (h : Partition s.charge (HZ.active s.charge) gs (HZ.partitionCount s)) :
    OptimalWord s HZ.Separated (HZ.activeCount s - HZ.partitionCount s) (word s.u gs) := by
  have act (i : I) : i ∈ gs.flatten ↔ s.charge i ≠ 0 := by
    rw [← List.mem_toFinset, h.covered]; simp [HZ.active]
  obtain ⟨leg,inside,outside⟩ := word_effect s s.u gs h.unique (fun i hi => (act i).mp hi) (fun _ _ => rfl)
  have size : gs.flatten.length = HZ.activeCount s := by
    rw [← List.toFinset_card_of_nodup h.unique,h.covered]; rfl
  have steps := word_length s.u gs h.nonempty
  rw [size,h.count] at steps
  have len : (word s.u gs).length = HZ.activeCount s-HZ.partitionCount s := by omega
  refine ⟨leg,?_,len,fun hr hg => len ▸ HZ.cost_lower_bound hr hg⟩
  intro i
  by_cases hi : i ∈ gs.flatten
  · obtain ⟨B,hB,hiB⟩ := List.mem_flatten.mp hi
    cases B with
    | nil => simp at hiB
    | cons j xs =>
      obtain ⟨hj,hx⟩ := inside j xs hB
      rcases List.mem_cons.mp hiB with he|hm
      · exact he ▸ hj.trans (h.zero _ hB)
      · exact hx i hm
  · exact (outside i hi).trans (not_not.mp (fun h => hi ((act i).mpr h)))

private theorem compile_target (s : HZ.State I K V) (τ : V) (ht : τ ≠ 0) (gs : List (List I))
    (h : Concentrating s.charge (HZ.active s.charge) gs τ) (count : gs.length = Dummy.Zstar s.charge τ) :
    OptimalWord s (fun t => Dummy.Concentrated t τ) (HZ.activeCount s-Dummy.Zstar s.charge τ) (word s.u gs) := by
  have act (i : I) : i ∈ gs.flatten ↔ s.charge i ≠ 0 := by
    rw [← List.mem_toFinset,h.covered]; simp [HZ.active]
  obtain ⟨leg,inside,outside⟩ := word_effect s s.u gs h.unique (fun i hi => (act i).mp hi) (fun _ _ => rfl)
  have size : gs.flatten.length = HZ.activeCount s := by
    rw [← List.toFinset_card_of_nodup h.unique,h.covered]; rfl
  have steps := word_length s.u gs h.nonempty
  rw [size,count] at steps
  have len : (word s.u gs).length = HZ.activeCount s-Dummy.Zstar s.charge τ := by omega
  refine ⟨leg,?_,len,fun hr hg => len ▸ Dummy.cost_lower_bound ht hr hg⟩
  obtain ⟨D,hD,hτ,others⟩ := h.carrier
  cases D with
  | nil => exact False.elim (h.nonempty [] hD rfl)
  | cons j xs =>
    refine ⟨j,fun i => ?_⟩
    by_cases hj : i = j
    · subst i
      simpa using (inside j xs hD).1.trans hτ
    rw [if_neg hj]
    by_cases hi : i ∈ gs.flatten
    · obtain ⟨B,hB,hiB⟩ := List.mem_flatten.mp hi
      cases B with
      | nil => simp at hiB
      | cons a bs =>
        rcases List.mem_cons.mp hiB with he|hh
        · subst a
          exact (inside i bs hB).1.trans (others _ hB (fun e => hj (List.cons.inj e).1))
        · exact (inside a bs hB).2 i hh
    · exact (outside i hi).trans (not_not.mp (fun h => hi ((act i).mpr h)))

structure Answer (J I K : Type*) where
  recovered : Recovery J
  groups : List (List I)
  gates : List (Gate I K)
  deriving Repr

variable {m d : ℕ} [DecidableEq K]

def separate (r : Raw K m d) : Answer (Fin m) (Fin m) K :=
  let recov := recover (denseEq K d) (StrideDP.dense K d) (rawRows r)
  let gs := (splitPath recov.path).2
  ⟨recov,gs,word r.u.get gs⟩

def concentrate (r : Raw K m d) (τ : Fin d → K) : Answer (Option (Fin m)) (Fin m) K :=
  let recov := recover (denseEq K d) (StrideDP.dense K d) (augmentedRows r τ)
  let gs := (splitPath recov.path).2.map real
  ⟨recov,gs,word r.u.get gs⟩

theorem separate_correct (r : Raw K m d) (hs : ∑ i, r.state.charge i = 0) :
    let a := separate r
    Partition r.state.charge (HZ.active r.state.charge) a.groups (HZ.partitionCount r.state) ∧
      a.recovered.score = HZ.partitionCount r.state ∧
      a.recovered.steps = HZ.activeCount r.state ∧
      OptimalWord r.state HZ.Separated (HZ.activeCount r.state-HZ.partitionCount r.state) a.gates := by
  let y := r.state.charge
  let ks := activeLabels r
  have hz : ∑ i ∈ ks.toFinset, y i = 0 := by rw [labels_cover,Dummy.sum_active,hs]
  have h := recovery_correct (denseEq K d) (StrideDP.dense K d) y ks (labels_unique r) hz
  dsimp only at h
  rw [← rawRows_eq r, labels_cover r] at h
  obtain ⟨part,score,steps,_,_⟩ := h
  rw [score] at part
  have len : ks.length = HZ.activeCount r.state := by rw [← List.toFinset_card_of_nodup (labels_unique r),labels_cover]; rfl
  exact ⟨part,score,steps.trans len,compile_zero r.state _ part⟩

set_option maxHeartbeats 1200000 in
theorem concentrate_correct (r : Raw K m d) (τ : Fin d → K) (ht : τ ≠ 0) (hs : ∑ i, r.state.charge i = τ) :
    let a := concentrate r τ
    Concentrating r.state.charge (HZ.active r.state.charge) a.groups τ ∧
      a.recovered.score = Dummy.Zstar r.state.charge τ ∧
      a.recovered.steps = HZ.activeCount r.state + 1 ∧
      a.groups.length = a.recovered.score ∧
      OptimalWord r.state (fun t => Dummy.Concentrated t τ)
        (HZ.activeCount r.state-Dummy.Zstar r.state.charge τ) a.gates := by
  let ks := activeLabels r
  let y := r.state.charge
  let z := Dummy.augment y τ
  have base : ks.toFinset = HZ.active y := labels_cover r
  have eqset : (tags ks).toFinset = HZ.active z := by
    rw [tags_set,base,Dummy.active_augment y τ ht]
    ext i; cases i <;> simp
  have hz : ∑ i ∈ (tags ks).toFinset, z i = 0 := eqset ▸ Dummy.sum_augmented_active y τ ht hs
  have h := recovery_correct (denseEq K d) (StrideDP.dense K d) z (tags ks) (tags_nodup _ (labels_unique r)) hz
  dsimp only at h
  rw [show records z (tags ks) = augmentedRows r τ from (augmentedRows_eq ..).symm] at h
  obtain ⟨part,score,steps,_,_⟩ := h
  rw [tags_set,base] at part
  obtain ⟨cert,count⟩ := project_correct y (HZ.active y) τ ht _ _ part
  rw [eqset] at score
  have len : ks.length = HZ.activeCount r.state := by rw [← List.toFinset_card_of_nodup (labels_unique r),base]; rfl
  have len' : (tags ks).length = HZ.activeCount r.state+1 := by simp [tags,len]
  exact ⟨cert,score,steps.trans len',count,compile_target r.state τ ht _ cert (count.trans score)⟩

end BucketDP
