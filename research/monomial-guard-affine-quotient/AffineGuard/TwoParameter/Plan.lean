import AffineGuard.TwoParameter.ShortBlock
import Mathlib.Tactic.IntervalCases

namespace AffineGuard.TwoParameter
open Finset Ternary

variable {I : Type*} [DecidableEq I]

/-- Disjoint zero-slope blocks, with total gathering cost and signed final scalar sum. -/
inductive Plan (p : I → V) (b : I → F) : Finset I → ℕ → ℤ → Prop where
  | nil : Plan p b ∅ 0 0
  | cons {B D : Finset I} {k : ℕ} {d : ℤ} (ne : B.Nonempty) (dis : Disjoint B D)
      (zero : ∑ i ∈ B, p i = 0) (tail : Plan p b D k d) :
      Plan p b (B ∪ D) (B.card-1+k) (lift (∑ i ∈ B, b i)+d)

variable {p : I → V} {b : I → F} {A B : Finset I}

theorem Plan.prepend {k d} (sub : B ⊆ A) (ne : B.Nonempty) (zero : ∑ i ∈ B, p i=0)
    (tail : Plan p b (A \ B) k d) : Plan p b A (B.card-1+k) (lift (∑ i ∈ B, b i)+d) := by
  simpa only [union_comm B,sdiff_union_of_subset sub] using
    Plan.cons ne disjoint_sdiff_self_right zero tail

theorem Plan.scalar_total {k d} (h : Plan p b A k d) : (d : F) = ∑ i ∈ A, b i := by
  induction h with
  | nil => simp
  | cons _ dis _ _ ih => simp only [Int.cast_add,cast_lift,ih,sum_union dis]

theorem Plan.singletonBlock (ne : A.Nonempty) (hz : ∑ i ∈ A, p i=0) :
    Plan p b A (A.card-1) (lift (∑ i ∈ A, b i)) := by
  simpa using (Plan.cons (b := b) ne (show Disjoint A ∅ by simp) hz Plan.nil)

/-- Make k+1 blocks. The last two blocks can be split off using the five-term lemma. -/
private theorem groups (k : ℕ) (A : Finset I) (hz : ∑ i ∈ A, p i=0)
    (ne : A.Nonempty) (size : k=0 ∨ 3*(k+1) ≤ A.card) :
    ∃ d, Plan p b A (A.card-(k+1)) d ∧ -((k+1 : ℕ) : ℤ) ≤ d ∧ d ≤ ((k+1 : ℕ) : ℤ) := by
  induction k generalizing A with
  | zero => exact ⟨_,Plan.singletonBlock ne hz,by simpa using lift_bounds (∑ i ∈ A, b i)⟩
  | succ k ih =>
    have large : 3*(k+2) ≤ A.card := by omega
    obtain ⟨B,sub,bne,positive,room,hB⟩ :
        ∃ B ⊆ A, B.Nonempty ∧ B.card < A.card ∧ (k=0 ∨ 3*(k+1) ≤ A.card-B.card) ∧ ∑ i ∈ B, p i=0 := by
      by_cases z : k=0
      · obtain ⟨B,sub,bne,sz,hB⟩ := five_block A p (by omega)
        exact ⟨B,sub,bne,by omega,Or.inl z,hB⟩
      · obtain ⟨B,sub,sz,hB⟩ := OneParameter.plane_triple A p (by omega)
        exact ⟨B,sub,card_pos.mp (by omega),by omega,Or.inr (by omega),hB⟩
    have szD := card_sdiff_of_subset sub
    have hD : ∑ i ∈ A \ B, p i=0 := by simpa [hB,hz] using sum_sdiff (f := p) sub
    obtain ⟨d,tail,lo,up⟩ := ih (A \ B) hD (card_pos.mp (by omega)) (by rwa [szD])
    have bn := bne.card_pos
    have weight := lift_bounds (∑ i ∈ B, b i)
    have count : B.card-1+((A \ B).card-(k+1))=A.card-(k+1+1) := by omega
    exact ⟨_,count ▸ tail.prepend sub bne hB,by push_cast at *; omega,by push_cast at *; omega⟩

/-- One or minus two times the signed lift of the nonzero scalar total. -/
abbrev Good (t : F) (d : ℤ) := d=lift t ∨ d= -2*lift t

private theorem good_small (t : F) (d : ℤ) (ht : t≠0) (cast : (d:F)=t)
    (lo : -3≤d) (up : d≤3) : Good t d := by
  subst t
  interval_cases d <;> first | exact False.elim (ht (by decide)) | decide

private theorem good_join (t r : F) (d : ℤ) (ht : t≠0) (hr : r≠t)
    (h : Good (t-r) d) : Good t (lift r+d) := by
  rcases h with rfl|rfl <;> revert t r <;> decide

/-- For positive m this is min(m-1, ceil(2m/3)). -/
def bound (m : ℕ) := m - max 1 (m/3)

theorem cost_plan (A : Finset I) (p : I → V) (b : I → F)
    (hp : ∑ i ∈ A, p i=0) (ht : ∑ i ∈ A, b i≠0) :
    ∃ k d, Plan p b A k d ∧ k ≤ bound A.card ∧ Good (∑ i ∈ A, b i) d := by
  induction hsize : A.card using Nat.strong_induction_on generalizing A with
  | h m ih =>
    by_cases large : 12 ≤ m
    · let t := ∑ i ∈ A, b i
      obtain ⟨B,sub,ne,short,hB,diff⟩ := twelve_block A p b t ht (by omega)
      let D := A \ B
      have sizeD : D.card = A.card-B.card := card_sdiff_of_subset sub
      have bn := ne.card_pos
      have hd : ∑ i ∈ D, p i=0 := by simpa [D,hB,hp] using sum_sdiff (f := p) sub
      have scalarD : ∑ i ∈ D, b i=t-∑ i ∈ B, b i := eq_sub_of_add_eq (sum_sdiff (f := b) sub)
      obtain ⟨k,d,tail,cost,good⟩ := ih D.card (by omega) D hd (by rw [scalarD]; exact sub_ne_zero.mpr diff.symm) rfl
      refine ⟨_,_,tail.prepend sub ne hB,?_,good_join t _ _ ht diff (scalarD ▸ good)⟩
      unfold bound at *
      omega
    · have ne : A.Nonempty := by
        by_contra hn
        have empty : A=∅ := not_nonempty_iff_eq_empty.mp hn
        exact ht (by rw [empty,sum_empty])
      let k := max 1 (m/3)-1
      obtain ⟨d,run,lo,up⟩ := groups (p := p) (b := b) k A hp ne (by dsimp [k]; omega)
      have count : A.card-(k+1)=bound m := by dsimp [k,bound]; omega
      have small : k+1≤3 := by dsimp [k]; omega
      exact ⟨_,_,run,count.le,good_small _ d ht run.scalar_total (by omega) (by omega)⟩

end AffineGuard.TwoParameter
