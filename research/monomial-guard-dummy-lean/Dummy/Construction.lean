import Dummy.Lower

open Finset
namespace Dummy
variable {I K V : Type*} [DecidableEq I] [Fintype I]
  [Field K] [AddCommGroup V] [Module K V]

omit [Fintype I] in
theorem gather_block (s : HZ.State I K V) (B : Finset I) (hB : B.Nonempty)
    (hactive : ∀ i ∈ B, s.charge i ≠ 0) :
    ∃ c ∈ B, ∃ t : HZ.State I K V, HZ.Run s (B.card - 1) t ∧
      (∀ i ∈ B, t.charge i = if i = c then ∑ j ∈ B, s.charge j else 0) ∧
      HZ.AgreeOutside B s t := by
  classical
  obtain ⟨c, hc⟩ := hB
  have hu : ∀ i ∈ B, s.u i ≠ 0 := by
    intro i hi hz
    apply hactive i hi
    simp [HZ.State.charge, hz]
  obtain ⟨t, hr, hU, hW, hB', hC, _⟩ :=
    HZ.gather (B.erase c) c s (hu c hc) (notMem_erase _ _) (fun i hi => hu i (mem_of_mem_erase hi))
  refine ⟨c, hc, t, ?_, ?_, ?_⟩
  · simpa [card_erase_of_mem hc] using hr
  · intro i hi
    by_cases he : i = c
    · subst i
      rw [if_pos rfl, hC, sum_erase_add B s.charge hc]
    · have hz : t.u i = 0 := by rw [hU]; simp [hi, he]
      simp [he, HZ.State.charge, hz]
  · intro i hi
    have hic : i ≠ c := by intro he; subst i; exact hi hc
    exact ⟨by rw [hU]; simp [hi], hW i hic, hB' i hic⟩

/-- Consolidate the one nonzero-total block and settle every other block on real coordinates. -/
theorem concentrate_partition (s : HZ.State I K V) (τ : V) (F : Finset (Finset I))
    (hne : ∀ A ∈ F, A.Nonempty) (hdis : (F : Set (Finset I)).PairwiseDisjoint id)
    (hcover : F.biUnion id = HZ.active s.charge)
    (B : Finset I) (hBF : B ∈ F) (hBsum : ∑ i ∈ B, s.charge i = τ)
    (hzero : ∀ A ∈ F, A ≠ B → ∑ i ∈ A, s.charge i = 0) :
    ∃ t, HZ.Run s (∑ A ∈ F, (A.card - 1)) t ∧ Concentrated t τ := by
  classical
  have hactive : ∀ A ∈ F, ∀ i ∈ A, s.charge i ≠ 0 := by
    intro A hA i hi
    have hm : i ∈ F.biUnion id := mem_biUnion.mpr ⟨A, hA, hi⟩
    rw [hcover] at hm
    exact (mem_filter.mp hm).2
  obtain ⟨q, hsq, hq, hqout, _⟩ := HZ.settle_family (F.erase B) s
    (fun A hA => hne A (mem_of_mem_erase hA))
    (hdis.subset (erase_subset B F))
    (fun A hA => hactive A (mem_of_mem_erase hA))
    (fun A hA => hzero A (mem_of_mem_erase hA) (mem_erase.mp hA).1)
  have hBout : ∀ i ∈ B, i ∉ (F.erase B).biUnion id := by
    intro i hi hm
    obtain ⟨A, hA, hiA⟩ := mem_biUnion.mp hm
    exact disjoint_left.mp (hdis (mem_of_mem_erase hA) hBF (mem_erase.mp hA).1) hiA hi
  have hsame : ∀ i ∈ B, q.charge i = s.charge i := by
    intro i hi
    obtain ⟨hu, hw, _⟩ := hqout i (hBout i hi)
    simp [HZ.State.charge, hu, hw]
  obtain ⟨c, hc, t, hqt, ht, htout⟩ := gather_block q B (hne B hBF)
    (by intro i hi; rw [hsame i hi]; exact hactive B hBF i hi)
  have hsB : (∑ i ∈ B, q.charge i) = τ := (sum_congr rfl hsame).trans hBsum
  refine ⟨t, ?_, c, ?_⟩
  · have hr := hsq.trans hqt
    rw [sum_erase_add F (fun A => A.card - 1) hBF] at hr
    exact hr
  · intro i
    by_cases hiB : i ∈ B
    · simpa [hsB] using ht i hiB
    · have hic : i ≠ c := by intro he; subst i; exact hiB hc
      rw [if_neg hic]
      obtain ⟨hu, hw, _⟩ := htout i hiB
      have hti : t.charge i = q.charge i := by simp [HZ.State.charge, hu, hw]
      rw [hti]
      by_cases hiF : i ∈ (F.erase B).biUnion id
      · exact hq i hiF
      · obtain ⟨huq, hwq, _⟩ := hqout i hiF
        have hi : i ∉ HZ.active s.charge := by
          rw [← hcover]
          intro hm
          obtain ⟨A, hA, hiA⟩ := mem_biUnion.mp hm
          by_cases he : A = B
          · exact hiB (he ▸ hiA)
          · exact hiF (mem_biUnion.mpr ⟨A, mem_erase.mpr ⟨he, hA⟩, hiA⟩)
        have hz : s.charge i = 0 := by simpa [HZ.active] using hi
        simpa [HZ.State.charge, huq, hwq] using hz

/-- A maximizing augmented partition yields a word using only the original coordinate type I. -/
theorem cost_attained (s : HZ.State I K V) (τ : V) (hτ : τ ≠ 0)
    (hs : ∑ i, s.charge i = τ) :
    ∃ t, HZ.Run s (HZ.activeCount s - Zstar s.charge τ) t ∧ Concentrated t τ := by
  classical
  obtain ⟨P, hp, hcard⟩ := HZ.exists_maxBlocks (augment s.charge τ)
    (HZ.active (augment s.charge τ)) (sum_augmented_active s.charge τ hτ hs)
  obtain ⟨hne, hdis, hcover, hFcard, B, hBF, hBsum, hzero⟩ := real_parts s.charge τ hτ P hp
  let F := P.parts.image Finset.eraseNone
  obtain ⟨t, hr, ht⟩ := concentrate_partition s τ F hne hdis hcover B hBF hBsum hzero
  have hcost : (∑ A ∈ F, (A.card - 1)) = HZ.activeCount s - Zstar s.charge τ := by
    have hadd : (∑ A ∈ F, (A.card - 1)) + F.card = (HZ.active s.charge).card := by
      calc
        _ = ∑ A ∈ F, ((A.card - 1) + 1) := by simp [sum_add_distrib]
        _ = ∑ A ∈ F, A.card := by
          apply sum_congr rfl
          intro A hA
          have hh := card_pos.mpr (hne A hA)
          omega
        _ = (F.biUnion id).card := (card_biUnion hdis).symm
        _ = _ := congrArg Finset.card hcover
    have hc : F.card = Zstar s.charge τ := hFcard.trans hcard
    change _ = (HZ.active s.charge).card - Zstar s.charge τ
    omega
  exact ⟨t, hcost ▸ hr, ht⟩

end Dummy

