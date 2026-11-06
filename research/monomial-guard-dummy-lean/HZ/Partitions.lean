import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel
import Aesop

open Finset

namespace HZ

variable {I : Type*} [DecidableEq I] {s : Finset I}

/-- Merge two distinct blocks, keeping every label, including zero-charge helpers. -/
noncomputable def mergeParts (P : Finpartition s) (A B : Finset I)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (_hAB : A ≠ B) : Finpartition s := by
  classical
  refine Finpartition.ofExistsUnique (insert (A ∪ B) ((P.parts.erase A).erase B)) ?_ ?_ ?_
  · intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact union_subset (P.subset hA) (P.subset hB)
    · exact P.subset (mem_of_mem_erase (mem_of_mem_erase ht))
  · intro x hx
    by_cases hxAB : x ∈ A ∪ B
    · refine ⟨A ∪ B, ⟨mem_insert_self _ _, hxAB⟩, ?_⟩
      rintro t ⟨ht, hxt⟩
      rcases mem_insert.mp ht with rfl | ht
      · rfl
      · obtain ⟨htB, htA, htP⟩ := mem_erase.mp ht |>.imp_right mem_erase.mp
        rcases mem_union.mp hxAB with hxA | hxB
        · exact False.elim (htA (P.eq_of_mem_parts htP hA hxt hxA))
        · exact False.elim (htB (P.eq_of_mem_parts htP hB hxt hxB))
    · have hi : P.part x ∈ P.parts := P.part_mem.mpr hx
      have hxi : x ∈ P.part x := P.mem_part hx
      have hiA : P.part x ≠ A := by intro h; apply hxAB; rw [h] at hxi; exact mem_union_left _ hxi
      have hiB : P.part x ≠ B := by intro h; apply hxAB; rw [h] at hxi; exact mem_union_right _ hxi
      refine ⟨P.part x, ⟨mem_insert_of_mem (mem_erase.mpr ⟨hiB, mem_erase.mpr ⟨hiA, hi⟩⟩), hxi⟩, ?_⟩
      rintro t ⟨ht, hxt⟩
      rcases mem_insert.mp ht with rfl | ht
      · exact False.elim (hxAB hxt)
      · exact P.eq_of_mem_parts (mem_of_mem_erase (mem_of_mem_erase ht)) hi hxt hxi
  · intro ht
    rcases mem_insert.mp ht with h | h
    · have hempty : A = ∅ := by simpa using union_eq_empty.mp h.symm |>.1
      exact P.ne_empty hA hempty
    · exact P.empty_notMem_parts (mem_of_mem_erase (mem_of_mem_erase h))

theorem mergeParts_parts (P : Finpartition s) (A B : Finset I)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    (mergeParts P A B hA hB hAB).parts = insert (A ∪ B) ((P.parts.erase A).erase B) := rfl

theorem mergeParts_card (P : Finpartition s) (A B : Finset I)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    (mergeParts P A B hA hB hAB).parts.card + 1 = P.parts.card := by
  classical
  have hn : A ∪ B ∉ (P.parts.erase A).erase B := by
    intro hc
    have hcA := (mem_erase.mp (mem_erase.mp hc).2).1
    have hcP := mem_of_mem_erase (mem_of_mem_erase hc)
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hA
    exact hcA (P.eq_of_mem_parts hcP hA (mem_union_left _ hx) hx)
  rw [mergeParts_parts, card_insert_of_notMem hn]
  have h1 := card_erase_add_one hA
  have h2 := card_erase_add_one (mem_erase.mpr ⟨Ne.symm hAB, hB⟩)
  omega

variable {V : Type*} [AddCommGroup V]

def ZeroSum (y : I → V) (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, ∑ i ∈ B, y i = 0

theorem zeroSum_merge (y : I → V) (P : Finpartition s) (hp : ZeroSum y P)
    (A B : Finset I) (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    ZeroSum y (mergeParts P A B hA hB hAB) := by
  intro t ht
  rw [mergeParts_parts] at ht
  rcases mem_insert.mp ht with rfl | ht
  · rw [sum_union (show Disjoint A B from P.disjoint hA hB hAB), hp A hA, hp B hB, zero_add]
  · exact hp t (mem_of_mem_erase (mem_of_mem_erase ht))

/-- The sum over a set is preserved when it contains both changed labels or neither. -/
theorem sum_pair_conserved (y z : I → V) {i j : I} (hij : i ≠ j)
    (hout : ∀ k, k ≠ i → k ≠ j → y k = z k)
    (hpair : y i + y j = z i + z j) (B : Finset I) (hB : i ∈ B ↔ j ∈ B) :
    ∑ k ∈ B, y k = ∑ k ∈ B, z k := by
  classical
  by_cases hi : i ∈ B
  · have hj := hB.mp hi
    have hj' : j ∈ B.erase i := mem_erase.mpr ⟨Ne.symm hij, hj⟩
    have he : ∑ k ∈ (B.erase i).erase j, y k = ∑ k ∈ (B.erase i).erase j, z k := by
      apply sum_congr rfl
      intro k hk
      exact hout k (mem_erase.mp (mem_erase.mp hk).2).1 (mem_erase.mp hk).1
    have hy1 := sum_erase_add B y hi
    have hz1 := sum_erase_add B z hi
    have hy2 := sum_erase_add (B.erase i) y hj'
    have hz2 := sum_erase_add (B.erase i) z hj'
    rw [← hy1, ← hz1, ← hy2, ← hz2, he]
    simpa only [add_assoc, add_left_comm, add_comm] using
      congrArg (fun x => (∑ k ∈ (B.erase i).erase j, z k) + x) hpair
  · apply sum_congr rfl
    intro k hk
    apply hout k
    · intro h; exact hi (h ▸ hk)
    · intro h; exact hi (hB.mpr (h ▸ hk))

variable [Fintype I]

/-- Pull a zero-sum partition back across a two-coordinate conservative change. -/
theorem pullback_pair (y z : I → V) {i j : I} (hij : i ≠ j)
    (hout : ∀ k, k ≠ i → k ≠ j → y k = z k)
    (hpair : y i + y j = z i + z j)
    (P : Finpartition (univ : Finset I)) (hp : ZeroSum z P) :
    ∃ Q : Finpartition (univ : Finset I), ZeroSum y Q ∧ P.parts.card ≤ Q.parts.card + 1 := by
  classical
  have hi : P.part i ∈ P.parts := P.part_mem.mpr (mem_univ i)
  have hj : P.part j ∈ P.parts := P.part_mem.mpr (mem_univ j)
  have hxi : i ∈ P.part i := P.mem_part (mem_univ i)
  have hxj : j ∈ P.part j := P.mem_part (mem_univ j)
  by_cases he : P.part i = P.part j
  · refine ⟨P, ?_, by omega⟩
    intro B hB
    rw [sum_pair_conserved y z hij hout hpair B]
    · exact hp B hB
    · rw [← P.part_eq_iff_mem hB, ← P.part_eq_iff_mem hB, he]
  · let Q := mergeParts P (P.part i) (P.part j) hi hj he
    refine ⟨Q, ?_, (mergeParts_card P _ _ hi hj he).ge⟩
    have hq := zeroSum_merge z P hp _ _ hi hj he
    intro B hB
    rw [sum_pair_conserved y z hij hout hpair B]
    · exact hq B hB
    · change B ∈ insert (P.part i ∪ P.part j) ((P.parts.erase (P.part i)).erase (P.part j)) at hB
      rcases mem_insert.mp hB with rfl | hB
      · exact iff_of_true (mem_union_left _ hxi) (mem_union_right _ hxj)
      · obtain ⟨hBj, hBi, hBP⟩ := mem_erase.mp hB |>.imp_right mem_erase.mp
        constructor
        · intro h; exact False.elim (hBi (P.part_eq_of_mem hBP h).symm)
        · intro h; exact False.elim (hBj (P.part_eq_of_mem hBP h).symm)

noncomputable def finsetPerm (e : Equiv.Perm I) : Finset I ≃o Finset I :=
  { e.finsetCongr with map_rel_iff' := by intro a b; exact map_subset_map }

noncomputable def permPartition (P : Finpartition (univ : Finset I)) (e : Equiv.Perm I) :
    Finpartition (univ : Finset I) :=
  (P.map (finsetPerm e)).copy (by ext i; simp [finsetPerm, Equiv.finsetCongr_apply])

theorem permPartition_card (P : Finpartition (univ : Finset I)) (e : Equiv.Perm I) :
    (permPartition P e).parts.card = P.parts.card := by
  simp [permPartition, Finpartition.copy, Finpartition.map]

theorem zeroSum_permPartition (y : I → V) (P : Finpartition (univ : Finset I))
    (e : Equiv.Perm I) (hp : ZeroSum (y ∘ e) P) : ZeroSum y (permPartition P e) := by
  intro B hB
  change B ∈ P.parts.map (finsetPerm e).toEmbedding at hB
  obtain ⟨A, hA, rfl⟩ := mem_map.mp hB
  simpa [finsetPerm, Equiv.finsetCongr_apply, Function.comp_def] using hp A hA

omit [Fintype I] in
/-- Removing labels loses at most one partition block per removed label. -/
theorem card_avoid (P : Finpartition s) (t : Finset I) :
    P.parts.card ≤ (P.avoid t).parts.card + t.card := by
  classical
  let good := P.parts.filter (fun B => ¬ B ⊆ t)
  let bad := P.parts.filter (fun B => B ⊆ t)
  have himage : (P.avoid t).parts = good.image (fun B => B \ t) := by
    ext B
    simp only [Finpartition.mem_avoid, mem_image, good, mem_filter]
    aesop
  have hinj : Set.InjOn (fun B : Finset I => B \ t) (good : Set (Finset I)) := by
    intro A hA B hB he
    obtain ⟨hAP, hAt⟩ := mem_filter.mp hA
    obtain ⟨hBP, _⟩ := mem_filter.mp hB
    have hne : (A \ t).Nonempty := nonempty_iff_ne_empty.mpr (by simpa using hAt)
    obtain ⟨x, hx⟩ := hne
    have hxB : x ∈ B \ t := by change A \ t = B \ t at he; rw [← he]; exact hx
    exact P.eq_of_mem_parts hAP hBP (mem_sdiff.mp hx).1 (mem_sdiff.mp hxB).1
  have hgood : (P.avoid t).parts.card = good.card := by
    rw [himage, card_image_of_injOn hinj]
  let R : Finpartition (bad.sup id) := P.ofSubset (filter_subset _ _) rfl
  have hbcard : bad.card ≤ t.card := by
    calc
      bad.card = R.parts.card := rfl
      _ ≤ (bad.sup id).card := R.card_parts_le_card
      _ ≤ t.card := card_le_card (by
        exact Finset.sup_le (s := bad) (f := id) (a := t) (fun B hB => (mem_filter.mp hB).2))
  have hc : bad.card + good.card = P.parts.card := by
    exact filter_card_add_filter_neg_card_eq_card (fun B : Finset I => B ⊆ t)
  omega

omit [Fintype I] in
theorem zeroSum_avoid (y : I → V) (P : Finpartition s) (hp : ZeroSum y P)
    (t : Finset I) (ht : ∀ i ∈ t, y i = 0) : ZeroSum y (P.avoid t) := by
  intro B hB
  rw [Finpartition.mem_avoid] at hB
  obtain ⟨A, hA, _, rfl⟩ := hB
  calc
    ∑ i ∈ A \ t, y i = ∑ i ∈ A, y i := sum_subset sdiff_subset (by
      intro i hi hnot
      exact ht i (by simpa [hi] using hnot))
    _ = 0 := hp A hA

noncomputable def active (y : I → V) : Finset I := by
  classical
  exact univ.filter (fun i => y i ≠ 0)

noncomputable def zeroPartitions (y : I → V) (s : Finset I) : Finset (Finpartition s) := by
  classical
  exact univ.filter (ZeroSum y)

noncomputable def maxBlocks (y : I → V) (s : Finset I) : ℕ :=
  (zeroPartitions y s).sup (fun P => P.parts.card)

noncomputable def blockCount (y : I → V) : ℕ := maxBlocks y (active y)

omit [Fintype I] in
theorem le_maxBlocks (y : I → V) (P : Finpartition s) (hp : ZeroSum y P) :
    P.parts.card ≤ maxBlocks y s := by
  classical
  exact le_sup (f := fun P : Finpartition s => P.parts.card) (by simp [zeroPartitions, hp])

omit [Fintype I] in
theorem maxBlocks_le_card (y : I → V) (s : Finset I) : maxBlocks y s ≤ s.card := by
  classical
  apply Finset.sup_le
  intro P _
  exact P.card_parts_le_card

omit [Fintype I] in
theorem exists_maxBlocks (y : I → V) (s : Finset I) (hy : ∑ i ∈ s, y i = 0) :
    ∃ P : Finpartition s, ZeroSum y P ∧ P.parts.card = maxBlocks y s := by
  classical
  have ht : ZeroSum y (⊤ : Finpartition s) := by
    intro B hB
    have h := Finpartition.parts_top_subset s hB
    obtain rfl := mem_singleton.mp h
    exact hy
  have hn : (zeroPartitions y s).Nonempty := ⟨⊤, by simp [zeroPartitions, ht]⟩
  obtain ⟨P, hP, he⟩ := exists_mem_eq_sup (zeroPartitions y s) hn (fun P => P.parts.card)
  exact ⟨P, (mem_filter.mp hP).2, he.symm⟩

/-- The all-label lower bound implies exactly the active-label h-Z bound. -/
theorem active_bound (y : I → V) (P : Finpartition (univ : Finset I))
    (hp : ZeroSum y P) {n : ℕ} (hn : Fintype.card I ≤ n + P.parts.card) :
    (active y).card - blockCount y ≤ n := by
  classical
  let t := univ \ active y
  have he : (univ : Finset I) \ t = active y := by ext i; simp [t]
  let Q : Finpartition (active y) := (P.avoid t).copy he
  have hq : ZeroSum y Q := zeroSum_avoid y P hp t (by
    intro i hi
    simpa [t, active] using (mem_sdiff.mp hi).2)
  have hz := le_maxBlocks y Q hq
  have hc := card_avoid P t
  have htcard : t.card + (active y).card = Fintype.card I := by
    simpa [t] using card_sdiff_add_card_eq_card (subset_univ (active y))
  change Q.parts.card ≤ blockCount y at hz
  change P.parts.card ≤ Q.parts.card + t.card at hc
  omega

end HZ
