import HZ.Operations

open Finset
namespace HZ
variable {I K V : Type*} [DecidableEq I] [Field K] [AddCommGroup V] [Module K V]

/-- Consolidate a labeled set onto an unchanged, nonzero donor column coordinate. -/
theorem gather (T : Finset I) (j : I) (s : State I K V)
    (hj : s.u j ≠ 0) (hjT : j ∉ T) (hu : ∀ i ∈ T, s.u i ≠ 0) :
    ∃ t : State I K V, Run s T.card t ∧
      (∀ k, t.u k = if k ∈ T then 0 else s.u k) ∧
      (∀ k, k ≠ j → t.w k = s.w k) ∧
      (∀ k, k ≠ j → t.b k = s.b k) ∧
      t.charge j = (∑ i ∈ T, s.charge i) + s.charge j ∧
      ((∀ k ∈ insert j T, s.b k = 0) → t.b = s.b) := by
  classical
  induction T using Finset.induction_on generalizing s with
  | empty => exact ⟨s, Run.nil s, by simp, by simp, by simp, by simp, by simp⟩
  | @insert i T hi ih =>
    have hij : i ≠ j := by intro h; subst i; exact hjT (mem_insert_self _ _)
    have hjT' : j ∉ T := fun h => hjT (mem_insert_of_mem h)
    have hui := hu i (mem_insert_self _ _)
    let a := -s.u i / s.u j
    let s' := s.addRow i j a
    obtain ⟨ha, hz, hd, _, hc⟩ := elimination s hij hui hj
    have hu' : ∀ k ∈ T, s'.u k ≠ 0 := by
      intro k hk
      have hki : k ≠ i := by intro h; subst k; exact hi hk
      simpa [s', State.addRow, hki] using hu k (mem_insert_of_mem hk)
    obtain ⟨t, hr, hU, hW, hB, hC, hpres⟩ :=
      ih s' (by simpa [s', a, hd] using hj) hjT' hu'
    refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Operation.cost, card_insert_of_notMem hi, Nat.add_comm] using
        (Run.cons s (Operation.add i j a hij ha) hr)
    · intro k
      rw [hU k]
      by_cases hk : k ∈ T
      · simp [hk]
      · by_cases hki : k = i
        · subst k
          simpa [hi] using hz
        · simp [hk, hki, s', State.addRow]
    · intro k hkj
      rw [hW k hkj]
      simp [s', State.addRow, hkj]
    · intro k hkj
      rw [hB k hkj]
      simp [s', State.addRow, hkj]
    · have hs : ∑ k ∈ T, s'.charge k = ∑ k ∈ T, s.charge k := by
        apply sum_congr rfl
        intro k hk
        apply charge_add_outside
        · intro h; subst k; exact hi hk
        · intro h; subst k; exact hjT' hk
      rw [hC, hs]
      change (∑ k ∈ T, s.charge k) + (s.addRow i j a).charge j = _
      rw [hc, sum_insert hi]
      abel
    · intro hb
      have hbStep : s'.b = s.b := by
        funext k
        have hbi : s.b i = 0 := hb i (by simp)
        simp [s', State.addRow, hbi]
      rw [hpres, hbStep]
      intro k hk
      rw [hbStep]
      apply hb k
      rcases mem_insert.mp hk with rfl | hk
      · simp
      · simp [hk]

def AgreeOutside (B : Finset I) (s t : State I K V) : Prop :=
  ∀ k, k ∉ B → t.u k = s.u k ∧ t.w k = s.w k ∧ t.b k = s.b k

theorem settle_block (s : State I K V) (B : Finset I) (hB : B.Nonempty)
    (hactive : ∀ i ∈ B, s.charge i ≠ 0) (hsum : ∑ i ∈ B, s.charge i = 0) :
    ∃ t : State I K V, Run s (B.card - 1) t ∧
      (∀ i ∈ B, t.charge i = 0) ∧ AgreeOutside B s t ∧
      ((∀ i ∈ B, s.b i = 0) → t.b = s.b) := by
  classical
  obtain ⟨j, hjB⟩ := hB
  have hu : ∀ i ∈ B, s.u i ≠ 0 := by
    intro i hi hz
    apply hactive i hi
    simp [State.charge, hz]
  obtain ⟨t, hr, hU, hW, hB', hC, hpres⟩ :=
    gather (B.erase j) j s (hu j hjB) (notMem_erase _ _) (fun i hi => hu i (mem_of_mem_erase hi))
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · simpa [card_erase_of_mem hjB] using hr
  · intro i hi
    by_cases hij : i = j
    · subst i
      rw [hC, sum_erase_add _ _ hjB, hsum]
    · have hz : t.u i = 0 := by rw [hU]; simp [hi, hij]
      simp [State.charge, hz]
  · intro k hk
    have hkj : k ≠ j := by intro h; subst k; exact hk hjB
    exact ⟨by rw [hU]; simp [hk], hW k hkj, hB' k hkj⟩
  · intro hb
    apply hpres
    simpa [insert_erase hjB] using hb

/-- Disjoint blocks are settled independently; previously settled coordinates stay settled. -/
theorem settle_family (F : Finset (Finset I)) (s : State I K V)
    (hne : ∀ B ∈ F, B.Nonempty) (hdis : (F : Set (Finset I)).PairwiseDisjoint id)
    (hactive : ∀ B ∈ F, ∀ i ∈ B, s.charge i ≠ 0)
    (hsum : ∀ B ∈ F, ∑ i ∈ B, s.charge i = 0) :
    ∃ t : State I K V, Run s (∑ B ∈ F, (B.card - 1)) t ∧
      (∀ i ∈ F.biUnion id, t.charge i = 0) ∧ AgreeOutside (F.biUnion id) s t ∧
      ((∀ i ∈ F.biUnion id, s.b i = 0) → t.b = s.b) := by
  classical
  induction F using Finset.induction_on generalizing s with
  | empty => exact ⟨s, by simpa using Run.nil s, by simp, by simp [AgreeOutside], by simp⟩
  | @insert B F hBF ih =>
    have hd : ∀ C ∈ F, Disjoint B C := by
      intro C hC
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hC) (by intro h; subst C; exact hBF hC)
    obtain ⟨q, hsq, hq, hqout, hqpres⟩ :=
      settle_block s B (hne B (mem_insert_self _ _)) (hactive B (mem_insert_self _ _))
        (hsum B (mem_insert_self _ _))
    have hout : ∀ C ∈ F, ∀ i ∈ C, i ∉ B := by
      intro C hC i hi hiB
      exact Finset.disjoint_left.mp (hd C hC) hiB hi
    have hsame : ∀ C ∈ F, ∀ i ∈ C, q.charge i = s.charge i := by
      intro C hC i hi
      obtain ⟨hu, hw, _⟩ := hqout i (hout C hC i hi)
      simp [State.charge, hu, hw]
    obtain ⟨t, hqt, ht, htout, htpres⟩ := ih q
      (fun C hC => hne C (mem_insert_of_mem hC))
      (hdis.subset (by intro C hC; exact mem_insert_of_mem hC))
      (by intro C hC i hi; rw [hsame C hC i hi]; exact hactive C (mem_insert_of_mem hC) i hi)
      (by intro C hC; rw [sum_congr rfl (fun i hi => hsame C hC i hi)]; exact hsum C (mem_insert_of_mem hC))
    refine ⟨t, ?_, ?_, ?_, ?_⟩
    · simpa [sum_insert hBF] using hsq.trans hqt
    · intro i hi
      simp only [biUnion_insert, id_eq, mem_union] at hi
      rcases hi with hiB | hiF
      · have hiout : i ∉ F.biUnion id := by
          intro h
          obtain ⟨C, hC, hiC⟩ := mem_biUnion.mp h
          exact hout C hC i hiC hiB
        obtain ⟨hu, hw, _⟩ := htout i hiout
        simpa [State.charge, hu, hw] using hq i hiB
      · exact ht i hiF
    · intro i hi
      have hiB : i ∉ B := by intro h; exact hi (by simp [h])
      have hiF : i ∉ F.biUnion id := by intro h; exact hi (by simp [h])
      obtain ⟨hu1, hw1, hb1⟩ := hqout i hiB
      obtain ⟨hu2, hw2, hb2⟩ := htout i hiF
      exact ⟨hu2.trans hu1, hw2.trans hw1, hb2.trans hb1⟩
    · intro hb
      have hqb : q.b = s.b := hqpres (by intro i hi; exact hb i (by simp [hi]))
      have htb : t.b = q.b := htpres (by
        intro i hi
        rw [hqb]
        exact hb i (by simp [hi]))
      exact htb.trans hqb

end HZ
