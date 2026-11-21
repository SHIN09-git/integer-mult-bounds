import Ternary.Envelope

namespace AffineGuard.OneParameter
open Finset Ternary

private theorem plane_cap : ∀ P : Finset (F × F), 5 ≤ P.card →
    ∃ x ∈ P, ∃ y ∈ P, ∃ z ∈ P, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x + y + z = 0 := by
  decide +kernel

private theorem triple_same : ∀ x : F × F, x+x+x = 0 := by decide

/-- Nine labeled entries of the ternary plane always contain a zero-sum triple. -/
theorem plane_triple {I : Type*} [DecidableEq I] (A : Finset I) (f : I → F × F) (h : 9 ≤ A.card) :
    ∃ B ⊆ A, B.card = 3 ∧ ∑ i ∈ B, f i = 0 := by
  have make (i j k : I) (hi : i ∈ A) (hj : j ∈ A) (hk : k ∈ A)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hs : f i + f j + f k = 0) :
      ∃ B ⊆ A, B.card = 3 ∧ ∑ i ∈ B, f i = 0 := by
    refine ⟨{i,j,k},by simpa [insert_subset_iff] using And.intro hi (And.intro hj hk),by simp [hij,hik,hjk],?_⟩
    simpa [hij,hik,hjk,add_assoc] using hs
  by_cases large : 5 ≤ (A.image f).card
  · obtain ⟨_,hx,_,hy,_,hz,hxy,hxz,hyz,hs⟩ := plane_cap _ large
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact make i j k hi hj hk (fun e => hxy (congrArg f e)) (fun e => hxz (congrArg f e))
      (fun e => hyz (congrArg f e)) hs
  · have many : ∃ x ∈ A.image f, 2 < (A.filter (fun i => f i = x)).card := by
      by_contra! small
      have hc := Finset.sum_le_sum small
      rw [← card_eq_sum_card_image f A] at hc
      simp only [sum_const, smul_eq_mul] at hc
      omega
    obtain ⟨x,_,hx⟩ := many
    obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩ := two_lt_card.mp hx
    obtain ⟨hi,ei⟩ := mem_filter.mp hi
    obtain ⟨hj,ej⟩ := mem_filter.mp hj
    obtain ⟨hk,ek⟩ := mem_filter.mp hk
    exact make i j k hi hj hk hij hik hjk (by rw [ei,ej,ek]; exact triple_same x)

private theorem three_scalars : ∀ a b c : F,
    a = 0 ∨ b = 0 ∨ c = 0 ∨ a+b = 0 ∨ a+c = 0 ∨ b+c = 0 ∨ a+b+c = 0 := by decide

/-- A block of at most three slopes summing to zero can be cut from any three rows. -/
theorem slope_block {I : Type*} [DecidableEq I] (A : Finset I) (p : I → F) (h : 3 ≤ A.card) :
    ∃ B ⊆ A, B.Nonempty ∧ B.card ≤ 3 ∧ ∑ i ∈ B, p i = 0 := by
  obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩ := two_lt_card.mp h
  rcases three_scalars (p i) (p j) (p k) with e|e|e|e|e|e|e
  · exact ⟨{i},by simpa,by simp,by simp,by simpa⟩
  · exact ⟨{j},by simpa,by simp,by simp,by simpa⟩
  · exact ⟨{k},by simpa,by simp,by simp,by simpa⟩
  · exact ⟨{i,j},by simpa [insert_subset_iff] using And.intro hi hj,by simp,by simp [hij],by simpa [hij]⟩
  · exact ⟨{i,k},by simpa [insert_subset_iff] using And.intro hi hk,by simp,by simp [hik],by simpa [hik]⟩
  · exact ⟨{j,k},by simpa [insert_subset_iff] using And.intro hj hk,by simp,by simp [hjk],by simpa [hjk]⟩
  · exact ⟨{i,j,k},by simpa [insert_subset_iff] using And.intro hi (And.intro hj hk),by simp,
      by simp [hij,hik,hjk],by simpa [hij,hik,hjk,add_assoc] using e⟩

end AffineGuard.OneParameter
