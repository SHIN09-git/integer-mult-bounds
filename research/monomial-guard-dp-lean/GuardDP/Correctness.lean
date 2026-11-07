import GuardDP.Packing

open Finset
namespace GuardDP
variable {I V : Type*} [DecidableEq I] [AddCommGroup V]

/-- The partial result is a maximum packing and covers every label at a zero sum. -/
structure Optimal (y : I → V) (S : Finset I) (g : Groups I) : Prop where
  nodup : g.Nodup
  packing : Packing y S g.toFinset
  full : (∑ i ∈ S, y i = 0) → covered g.toFinset = S
  maximum : ∀ F, Packing y S F → F.card ≤ g.length

theorem optimal_empty (y : I → V) : Optimal y ∅ [] := by
  refine ⟨by simp, ⟨by simp, by simp, by simp, by simp⟩, by simp [covered], ?_⟩
  intro F hf
  have he : F = ∅ := eq_empty_iff_forall_notMem.mpr (by
    intro B hB
    obtain ⟨i, hi⟩ := hf.nonempty B hB
    exact notMem_empty i (hf.subset B hB hi))
  simp [he]

variable [DecidableEq V]

theorem optimal_step (y : I → V) (keys : List I) (prev : Finset I → Groups I)
    (S : Finset I) (hkeys : S ⊆ keys.toFinset) (hne : S.Nonempty)
    (ih : ∀ i ∈ S, Optimal y (S.erase i) (prev (S.erase i))) :
    Optimal y S (step y keys prev S) := by
  let f := fun i => (prev (S.erase i)).length
  have hmem (i : I) : i ∈ keys.filter (· ∈ S) ↔ i ∈ S := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨List.mem_toFinset.mp (hkeys h), h⟩⟩
  cases he : keys.filter (· ∈ S) with
  | nil =>
    obtain ⟨i, hi⟩ := hne
    simpa [he] using (hmem i).mpr hi
  | cons a as =>
    let j := pick f a as
    have hj : j ∈ S := (hmem j).mp (he ▸ (pick_spec f a as).1)
    have best (i : I) (hi : i ∈ S) : f i ≤ f j :=
      (pick_spec f a as).2 i (he ▸ (hmem i).mpr hi)
    let g := prev (S.erase j)
    have opt : Optimal y (S.erase j) g := ih j hj
    have pack := opt.packing.mono (erase_subset j S)
    have fresh : j ∉ covered g.toFinset := fun h => notMem_erase j S (opt.packing.covered_subset h)
    have hstep : step y keys prev S = finish y S g := by simp [step, he, f, g, j]
    rw [hstep]
    by_cases hz : ∑ i ∈ S, y i = 0
    · obtain ⟨hn, hp, hc⟩ := pack.close hz hj fresh
      simp only [finish, if_pos hz]
      refine ⟨List.nodup_cons.mpr ⟨fun h => hn (List.mem_toFinset.mpr h), opt.nodup⟩,
        by simpa using hp, fun _ => by simpa using hc, ?_⟩
      intro F hf
      by_cases hem : F = ∅
      · simp [hem]
      obtain ⟨B, hB⟩ := nonempty_iff_ne_empty.mpr hem
      obtain ⟨i, hi⟩ := hf.nonempty B hB
      have hiS := hf.subset B hB hi
      have hcard := (ih i hiS).maximum _ (hf.erase_group hB hi)
      have hle := best i hiS
      change (F.erase B).card ≤ f i at hcard
      have hcount := card_erase_add_one hB
      change F.card ≤ f j + 1
      omega
    · simp only [finish, if_neg hz]
      refine ⟨opt.nodup, pack, fun hh => (hz hh).elim, ?_⟩
      intro F hf
      have hn : ¬ S ⊆ covered F := by
        intro hs
        exact hz ((subset_antisymm hs hf.covered_subset) ▸ hf.sum_covered)
      obtain ⟨i, hi, hout⟩ := not_subset.mp hn
      exact ((ih i hi).maximum _ (hf.erase_label hout)).trans (best i hi)

theorem layers_correct (y : I → V) (keys : List I) (n : ℕ)
    (S : Finset I) (hsub : S ⊆ keys.toFinset) (hc : S.card ≤ n) :
    Optimal y S ((layers y keys n).read S) := by
  induction n generalizing S with
  | zero =>
    obtain rfl : S = ∅ := card_eq_zero.mp (by omega)
    exact optimal_empty y
  | succ n ih =>
    simp only [layers, read_tabulate, empty_union, inter_eq_left.mpr hsub]
    split_ifs with h
    · apply optimal_step _ _ _ _ hsub (card_pos.mp (by omega))
      intro i hi
      apply ih _ ((erase_subset ..).trans hsub)
      have := card_erase_add_one hi
      omega
    · exact ih S hsub (by omega)

theorem partitionDP_optimal (y : I → V) (keys : List I) :
    Optimal y keys.toFinset (partitionDP y keys) :=
  layers_correct y keys _ _ (Subset.rfl) le_rfl

omit [DecidableEq V] in
theorem Optimal.count_eq {y : I → V} {S : Finset I} {g : Groups I}
    (h : Optimal y S g) (hz : ∑ i ∈ S, y i = 0) : g.length = HZ.maxBlocks y S := by
  let P := h.packing.partition (h.full hz)
  have low := HZ.le_maxBlocks y P h.packing.zero
  change g.toFinset.card ≤ HZ.maxBlocks y S at low
  rw [List.toFinset_card_of_nodup h.nodup] at low
  obtain ⟨Q, hQ, he⟩ := HZ.exists_maxBlocks y S hz
  exact le_antisymm low (he ▸ h.maximum Q.parts (packing_of_partition Q hQ))

theorem partitionDP_count (y : I → V) (keys : List I)
    (hz : ∑ i ∈ keys.toFinset, y i = 0) :
    (partitionDP y keys).length = HZ.maxBlocks y keys.toFinset :=
  (partitionDP_optimal y keys).count_eq hz

end GuardDP
