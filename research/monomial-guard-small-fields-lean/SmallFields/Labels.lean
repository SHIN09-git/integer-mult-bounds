import SmallFields.Blocks
import Dummy.Partitions

namespace SmallFields
open Finset CountDP
variable {I V : Type*} [DecidableEq I] [AddCommGroup V] (y : I → V)

omit [AddCommGroup V] in
theorem histogram_singletons (s : Finset I) :
    histogram y s = ∑ i ∈ s, ({y i} : Multiset V) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi,← ih]
    simp [histogram,Finset.insert_val_of_notMem hi,Multiset.singleton_add]

omit [AddCommGroup V] in
/-- Allocate an arbitrary requested submultiset back to distinct original labels. -/
theorem split_histogram (a b : Multiset V) (s : Finset I) (he : histogram y s = a+b) :
    ∃ A T : Finset I, Disjoint T A ∧ T ∪ A = s ∧ histogram y A = a ∧ histogram y T = b := by
  classical
  induction a using Multiset.induction_on generalizing s with
  | empty => exact ⟨∅,s,by simp,by simp,rfl,by simpa using he⟩
  | cons v a ih =>
    have hv : v ∈ histogram y s := he ▸ (by simp)
    obtain ⟨i,hi,hi'⟩ := mem_histogram.mp hv
    have h0 : histogram y s = v ::ₘ (a+b) := by simpa using he
    have ht : histogram y (s.erase i) = a+b := by rw [histogram_erase y s hi, hi',h0,Multiset.erase_cons_head]
    obtain ⟨A,T,hd,hu,hA,hT⟩ := ih (s.erase i) ht
    have fresh : i ∉ T ∪ A := hu ▸ notMem_erase i s
    have hia : i ∉ A := fun h => fresh (mem_union_right _ h)
    refine ⟨insert i A,T,?_,?_,?_,hT⟩
    · exact disjoint_left.mpr (by
        intro j hj hj'
        rcases mem_insert.mp hj' with rfl|hj'
        · exact fresh (mem_union_left _ hj)
        · exact disjoint_left.mp hd hj hj')
    · rw [union_insert,hu,insert_erase hi]
    · simp [histogram,Finset.insert_val_of_notMem hia,hi',← hA]

theorem Blocks.lift {m : Multiset V} {k : ℕ} (h : Blocks m k) (s : Finset I) (hs : histogram y s = m) :
    ∃ P : Finpartition s, HZ.ZeroSum y P ∧ P.parts.card = k := by
  classical
  induction h generalizing s with
  | empty =>
    have hcard := congrArg Multiset.card hs
    have : s = ∅ := card_eq_zero.mp (by simpa using hcard)
    subst s
    exact ⟨⊥,by simp [HZ.ZeroSum],by simp⟩
  | @join b m k hb hz _ ih =>
    obtain ⟨A,T,hd,hu,hA,hT⟩ := split_histogram y b m s hs
    obtain ⟨P,hp,hk⟩ := ih T hT
    have ha : A ≠ ∅ := fun e => hb (hA.symm.trans (e ▸ histogram_empty y))
    refine ⟨P.extend ha hd hu,?_,(Finpartition.card_extend P A s).trans (congrArg (·+1) hk)⟩
    intro B hB
    change B ∈ insert A P.parts at hB
    rcases mem_insert.mp hB with rfl|hB
    · rw [← histogram_sum,hA,hz]
    · exact hp _ hB

theorem partition_blocks {s : Finset I} (P : Finpartition s) (hz : HZ.ZeroSum y P) :
    Blocks (histogram y s) P.parts.card := by
  classical
  have cover : ∑ B ∈ P.parts, histogram y B = histogram y s := by
    simp only [histogram_singletons]
    have hu := Finset.sum_biUnion (f := fun i => ({y i} : Multiset V)) P.disjoint
    rw [P.biUnion_parts] at hu
    exact hu.symm
  have pack (F : Finset (Finset I)) (sub : F ⊆ P.parts) :
      Blocks (∑ B ∈ F, histogram y B) F.card := by
    induction F using Finset.induction_on with
    | empty => simpa using (Blocks.empty (V := V))
    | insert B F hf ih =>
      have hB := sub (mem_insert_self _ _)
      have hn : histogram y B ≠ 0 := by
        intro e
        have := congrArg Multiset.card e
        exact P.ne_empty hB (card_eq_zero.mp (by simpa using this))
      rw [sum_insert hf,card_insert_of_notMem hf]
      exact Blocks.join hn ((histogram_sum y B).trans (hz _ hB)) (ih ((subset_insert ..).trans sub))
  rw [← cover]
  exact pack _ Subset.rfl

theorem maxBlocks_eq_Z (s : Finset I) (hs : ∑ i ∈ s, y i = 0) :
    HZ.maxBlocks y s = Z (histogram y s) := by
  obtain ⟨P,hp,hc⟩ := HZ.exists_maxBlocks y s hs
  obtain ⟨Q,hq,hk⟩ := (attaining _ ((histogram_sum y s).trans hs)).lift y s rfl
  exact le_antisymm (hc ▸ (partition_blocks y P hp).le_Z) (hk ▸ HZ.le_maxBlocks y Q hq)

variable [Fintype I]

noncomputable def input (y : I → V) := histogram y (HZ.active y)

theorem blockCount_eq_Z (hs : ∑ i, y i = 0) : HZ.blockCount y = Z (input y) :=
  maxBlocks_eq_Z y _ ((Dummy.sum_active y).trans hs)

omit [DecidableEq I] in
theorem input_sum : (input y).sum = ∑ i, y i := (histogram_sum ..).trans (Dummy.sum_active y)

omit [DecidableEq I] in
theorem zero_notMem_input : 0 ∉ input y := by
  classical
  simp [input,HZ.active]

theorem input_singletons [DecidableEq V] : input y = ∑ i, if y i = 0 then 0 else ({y i} : Multiset V) := by
  classical
  simp [input,HZ.active,histogram_singletons,Finset.sum_filter,ite_not]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : y i = 0 <;> simp [h]

end SmallFields
