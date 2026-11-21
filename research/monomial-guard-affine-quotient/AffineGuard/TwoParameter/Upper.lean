import AffineGuard.TwoParameter.Plan
import Mathlib.Algebra.BigOperators.Pi

namespace AffineGuard.TwoParameter
open Finset Ternary

abbrev Flat (I : Type*) := HZ.State I F (Fin 2 → F)

def slope (s : Flat I) (i : I) : V := (s.charge i 0, s.charge i 1)

def Normalized [Fintype I] (s : Flat I) : Prop :=
  (∑ i, s.charge i)=0 ∧ (∑ i, scalar s i)=1

variable {I : Type*} [DecidableEq I] [Fintype I]

private theorem block_run (s : Flat I) (B : Finset I) (ne : B.Nonempty)
    (hu : ∀ i ∈ B, s.u i≠0) (hz : ∑ i ∈ B, slope s i=0) :
    ∃ t, HZ.Run s (B.card-1) t ∧ HZ.AgreeOutside B s t ∧
      (∀ i ∈ B, t.charge i=0) ∧ (∑ i ∈ B, lift (scalar t i))=lift (∑ i ∈ B, scalar s i) := by
  obtain ⟨j,hj⟩ := ne
  obtain ⟨t,r,u,w,b,pivot,_⟩ := HZ.gather (B.erase j) j s (hu j hj)
    (notMem_erase _ _) (fun i hi => hu i (mem_of_mem_erase hi))
  have out : HZ.AgreeOutside B s t := by
    intro i hi
    have ij : i≠j := fun e => hi (e ▸ hj)
    exact ⟨by rw [u]; simp [hi],w i ij,b i ij⟩
  have off (i) (hi : i∈B) (ij : i≠j) : t.u i=0 := by rw [u]; simp [hi,ij]
  have total : (∑ i ∈ B, s.charge i)=0 := by
    funext d
    fin_cases d
    · simpa [Prod.fst_sum,slope,sum_apply] using congrArg Prod.fst hz
    · simpa [Prod.snd_sum,slope,sum_apply] using congrArg Prod.snd hz
  have scalarSum := Ternary.scalar_total r
  have comp : ∑ i ∈ Bᶜ, scalar t i = ∑ i ∈ Bᶜ, scalar s i :=
    sum_congr rfl fun i hi => by
      obtain ⟨e,_,f⟩ := out i (mem_compl.mp hi)
      simp [scalar,e,f]
  rw [← sum_add_sum_compl B,← sum_add_sum_compl B (scalar s),comp] at scalarSum
  have block := add_right_cancel scalarSum
  have other (i) (hi : i∈B) (ij : i≠j) : scalar t i=0 := by simp [scalar,off i hi ij]
  have sole : ∑ i ∈ B, scalar t i=scalar t j := sum_eq_single_of_mem j hj other
  refine ⟨t,by simpa [card_erase_of_mem hj] using r,out,?_,?_⟩
  · intro i hi
    by_cases ij : i=j
    · subst i
      rwa [pivot,sum_erase_add _ _ hj]
    · simp [HZ.State.charge,off i hi ij]
  · rw [← block,sole]
    exact sum_eq_single_of_mem j hj fun i hi ij => by simp [other i hi ij]

theorem Plan.realize {p : I → V} {b : I → F} {A : Finset I} {k d} (h : Plan p b A k d)
    (s : Flat I) (hu : ∀ i ∈ A, s.u i≠0)
    (hp : ∀ i ∈ A, slope s i=p i) (hb : ∀ i ∈ A, scalar s i=b i) :
    ∃ t, HZ.Run s k t ∧ HZ.AgreeOutside A s t ∧ (∀ i ∈ A, t.charge i=0) ∧
      (∑ i ∈ A, lift (scalar t i))=d := by
  induction h generalizing s with
  | nil => exact ⟨s,HZ.Run.nil _,fun _ _ => ⟨rfl,rfl,rfl⟩,by simp,by simp⟩
  | @cons B D k d ne dis zero tail ih =>
    have subB : B ⊆ B ∪ D := subset_union_left
    have subD : D ⊆ B ∪ D := subset_union_right
    have hz : ∑ i ∈ B, slope s i=0 := (sum_congr rfl fun i hi => hp i (subB hi)).trans zero
    obtain ⟨q,r,out,doneB,sumB⟩ := block_run s B ne (fun i hi => hu i (subB hi)) hz
    have agreeD (i) (hi : i ∈ D) := out i (fun hB => disjoint_left.mp dis hB hi)
    have sq (i) (hi : i ∈ D) : slope q i=slope s i := by
      obtain ⟨e,f,_⟩ := agreeD i hi
      simp [slope,HZ.State.charge,e,f]
    have bq (i) (hi : i ∈ D) : scalar q i=scalar s i := by
      obtain ⟨e,_,f⟩ := agreeD i hi
      simp [scalar,e,f]
    obtain ⟨t,r',out',doneD,sumD⟩ := ih q
      (fun i hi => (agreeD i hi).1 ▸ hu i (subD hi))
      (fun i hi => (sq i hi).trans (hp i (subD hi))) (fun i hi => (bq i hi).trans (hb i (subD hi)))
    have agreeB (i) (hi : i ∈ B) := out' i (disjoint_left.mp dis hi)
    refine ⟨_,r.trans r',?_,?_,?_⟩
    · intro i hi
      obtain ⟨u,w,b⟩ := out i (fun h => hi (subB h))
      obtain ⟨u',w',b'⟩ := out' i (fun h => hi (subD h))
      exact ⟨u'.trans u,w'.trans w,b'.trans b⟩
    · intro i hi
      rcases mem_union.mp hi with hB|hD
      · obtain ⟨u,w,_⟩ := agreeB i hB
        simpa only [HZ.State.charge,u,w] using doneB i hB
      · exact doneD i hD
    · have keep : ∑ i ∈ B, lift (scalar t i)=∑ i ∈ B, lift (scalar q i) :=
        sum_congr rfl fun i hi => by
          obtain ⟨u,_,b⟩ := agreeB i hi
          simp [scalar,u,b]
      rw [sum_union dis,sumD,keep,sumB,sum_congr rfl (fun i hi => hb i (subB hi))]

theorem cost_upper (s : Flat I) (hs : Normalized s) : C s ≤ bound (Fintype.card I) := by
  let A := univ.filter fun i => s.u i≠0
  have outside (i) (hi : i∉A) : s.u i=0 := by simpa [A] using hi
  have slopeTotal : ∑ i ∈ A, slope s i=0 := by
    rw [sum_subset (s₁ := A) (s₂ := univ) (f := slope s) (subset_univ _)
      (fun i _ hi => by simp [slope,HZ.State.charge,outside i hi])]
    apply Prod.ext
    · simpa [Prod.fst_sum,slope,sum_apply] using congrFun hs.1 0
    · simpa [Prod.snd_sum,slope,sum_apply] using congrFun hs.1 1
  have scalarTotal : ∑ i ∈ A, scalar s i=1 :=
    (sum_subset (subset_univ _) (fun i _ hi => by simp [scalar,outside i hi])).trans hs.2
  obtain ⟨k,d,plan,cost,good⟩ := cost_plan A (slope s) (scalar s) slopeTotal (by rw [scalarTotal]; decide)
  obtain ⟨t,run,out,sep,imb⟩ := plan.realize s (fun _ hi => (mem_filter.mp hi).2) (fun _ _ => rfl) (fun _ _ => rfl)
  have inactive (i) (hi : i∉A) : t.u i=0 := (out i hi).1.trans (outside i hi)
  have sep' : HZ.Separated t := fun i => by
    by_cases hi : i∈A
    · exact sep i hi
    · simp [HZ.State.charge,inactive i hi]
  have eq : (∑ i ∈ A, lift (scalar t i))=imbalance t :=
    sum_subset (subset_univ _) fun i _ hi => by simp [scalar,inactive i hi]
  rw [eq] at imb
  rw [scalarTotal] at good
  have guard := separated_good_fullguard t sep' (by simpa [Good,← imb] using good)
  have minCost := Nat.sInf_le (show k ∈ {j | ∃ t, HZ.Run s j t ∧ FullGuard t} from ⟨t,run,guard⟩)
  have cards : A.card ≤ Fintype.card I := card_le_univ _
  exact minCost.trans (cost.trans (by unfold bound; omega))

end AffineGuard.TwoParameter
