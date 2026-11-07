import BucketDP.Costs

namespace BucketDP
open CountDP StrideDP Finset GuardDP
variable {K : Type*} [Field K] [DecidableEq K] {m d : ℕ}

theorem recovery_shape [DecidableEq I] (y : I → Fin d → K) (ks : List I) (hn : ks.Nodup) :
    let a := recover (denseEq K d) (dense K d) (records y ks)
    a.types = (alphabet y ks).length ∧ a.states = ∏ v ∈ (alphabet y ks).toFinset, (capacity y ks v+1) := by
  dsimp only [recover]
  rw [prepared_keys,volume_eq _ _ _ hn]
  exact ⟨rfl,slots_eq_prod (alphabet y ks) _ (List.nodup_dedup _)⟩

private theorem recovery_counts {I : Type*} [DecidableEq I] (y : I → Fin d → K) (ks : List I) (hn : ks.Nodup)
    (hs : ∑ i ∈ ks.toFinset, y i = 0) (j : I) :
    ((recover (denseEq K d) (dense K d) (records y ks)).path.map Prod.fst).count j =
      if j ∈ ks then 1 else 0 := by
  obtain ⟨_,_,_,unique,covered⟩ := recovery_correct (denseEq K d) (dense K d) y ks hn hs
  rw [List.count_eq_of_nodup unique]
  have he := Finset.ext_iff.mp covered j
  simp only [List.mem_toFinset] at he
  simp only [he]

/-- Count actual bucket pops separately for each physical row. -/
theorem zero_pops_once (r : Raw K m d) (hs : ∑ i, r.state.charge i = 0) (i : Fin m) :
    ((separate r).recovered.path.map Prod.fst).count i = if r.state.charge i = 0 then 0 else 1 := by
  have hz : ∑ j ∈ (activeLabels r).toFinset, r.state.charge j = 0 := by rw [labels_cover,Dummy.sum_active,hs]
  unfold separate
  rw [rawRows_eq]
  simpa [activeLabels,ite_not] using recovery_counts r.state.charge _ (labels_unique r) hz i

set_option maxHeartbeats 1200000 in
/-- Option constructors distinguish the dummy even when its value equals a real charge. -/
theorem target_pops_once (r : Raw K m d) (τ : Fin d → K) (ht : τ ≠ 0) (hs : ∑ i, r.state.charge i = τ) :
    let a := concentrate r τ
    (a.recovered.path.map Prod.fst).count none = 1 ∧
    ∀ i : Fin m, ((a.recovered.path.map Prod.fst).count (some i) = if r.state.charge i = 0 then 0 else 1) ∧
      (a.groups.flatten.count i = if r.state.charge i = 0 then 0 else 1) := by
  let ks := activeLabels r
  let y := r.state.charge
  let z := Dummy.augment y τ
  have eqset : (tags ks).toFinset = HZ.active z := by
    rw [tags_set,labels_cover,Dummy.active_augment y τ ht]
    ext j; cases j <;> simp [y]
  have hz : ∑ j ∈ (tags ks).toFinset, z j = 0 := eqset ▸ Dummy.sum_augmented_active y τ ht hs
  have count (j : Option (Fin m)) :
      (((concentrate r τ).recovered.path.map Prod.fst).count j) = if j ∈ tags ks then 1 else 0 := by
    unfold concentrate
    rw [augmentedRows_eq]
    let ids := (recover (denseEq K d) (dense K d) (records z (tags ks))).path.map Prod.fst
    change ids.count j = _
    have ec : ids.count j = @List.count _ instBEqOfDecidableEq j ids :=
      congrArg (fun b => @List.count _ b j ids) (lawful_beq_subsingleton _ _)
    have old := recovery_counts z _ (tags_nodup _ (labels_unique r)) hz j
    by_cases hj : j ∈ tags ks
    · exact ((ec.trans old).trans (if_pos hj)).trans (if_pos hj).symm
    · exact ((ec.trans old).trans (if_neg hj)).trans (if_neg hj).symm
  have cert := (concentrate_correct r τ ht hs).1
  refine ⟨(count none).trans (by simp [tags]), fun i => ⟨?_,?_⟩⟩
  · simpa [tags,ks,activeLabels,ite_not] using count (some i)
  · have mem := Finset.ext_iff.mp cert.covered i
    simp only [List.mem_toFinset,HZ.active,Finset.mem_filter,Finset.mem_univ,true_and] at mem
    simp only [List.count_eq_of_nodup cert.unique,mem,ite_not]

/-- Eager accumulation prevents chains of deferred additions when the target is inferred. -/
def sumRows (r : Raw K m d) (acc : Vector K d) : List (Fin m) → Vector K d
  | [] => acc
  | i::is => sumRows r (pack (acc.get + r.state.charge i)) is

def totalVector (r : Raw K m d) := sumRows r (Vector.replicate d 0) (List.finRange m)

def total (r : Raw K m d) := (totalVector r).get

omit [DecidableEq K] in
theorem sumRows_eq (r : Raw K m d) (is : List (Fin m)) (acc : Vector K d) :
    (sumRows r acc is).get = acc.get+(is.map r.state.charge).sum := by
  induction is generalizing acc with
  | nil => simp [sumRows]
  | cons i is ih => rw [sumRows,ih,pack_get,List.map_cons,List.sum_cons,add_assoc]

omit [DecidableEq K] in
theorem total_eq (r : Raw K m d) : total r = ∑ i, r.state.charge i := by
  have zero : (Vector.replicate d (0 : K)).get = 0 := by funext i; simp [Vector.get]
  rw [total,totalVector,sumRows_eq,zero,zero_add,← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

omit [DecidableEq K] in
private theorem get_total (r : Raw K m d) : (totalVector r).get = total r := rfl

abbrev Solution (K : Type*) (m : ℕ) :=
  Sum (Answer (Fin m) (Fin m) K) (Answer (Option (Fin m)) (Fin m) K)

/-- Public entry point taking only physical arrays. The inferred total selects the objective. -/
def solve (r : Raw K m d) : Solution K m :=
  let v := totalVector r
  if (denseEq K d).test v.get 0 then .inl (separate r) else .inr (concentrate r v.get)

def solutionEvents (r : Raw K m d) : Events :=
  let v := totalVector r
  if (denseEq K d).test v.get 0 then zeroEvents r else targetEvents r v.get

theorem solve_correct (r : Raw K m d) :
    match solve r with
    | .inl a => total r = 0 ∧
      OptimalWord r.state HZ.Separated (HZ.activeCount r.state - HZ.partitionCount r.state) a.gates
    | .inr a => total r ≠ 0 ∧
      OptimalWord r.state (fun s => Dummy.Concentrated s (total r))
        (HZ.activeCount r.state - Dummy.Zstar r.state.charge (total r)) a.gates := by
  by_cases h : (denseEq K d).test (total r) 0 = true
  · simp only [solve, get_total, h, if_true]
    have hz := ((denseEq K d).correct _ _).mp h
    exact ⟨hz,(separate_correct r ((total_eq r).symm.trans hz)).2.2.2⟩
  · simp only [solve, get_total, if_neg h]
    have ht : total r ≠ 0 := fun e => h (((denseEq K d).correct _ _).mpr e)
    exact ⟨ht,(concentrate_correct r _ ht (total_eq r).symm).2.2.2.2⟩

theorem solve_resources (r : Raw K m d) :
    (solutionEvents r).time ≤ 384*(solutionEvents r).timeScale ∧
    (solutionEvents r).space ≤ 192*(solutionEvents r).spaceScale := by
  by_cases h : (denseEq K d).test (total r) 0 = true
  · simpa only [solutionEvents,get_total,h,if_true] using zero_resources r
  · simpa only [solutionEvents,get_total,if_neg h] using target_resources r (total r)

theorem solve_bigO {ι : Type*} (l : Filter ι) {ms ds : ι → ℕ}
    (r : (i : ι) → Raw K (ms i) (ds i)) : Bounds l (fun i => solutionEvents (r i)) := by
  apply bounds_of_limits
  intro i
  by_cases h : (denseEq K (ds i)).test (total (r i)) 0 = true
  · simpa only [solutionEvents,get_total,h,if_true] using zero_limits (r i)
  · simpa only [solutionEvents,get_total,if_neg h] using target_limits (r i) (total (r i))

end BucketDP
