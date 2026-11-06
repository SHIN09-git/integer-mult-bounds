import Ternary.Scalar
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Algebra.BigOperators.Group.List.Basic

open Finset
namespace Ternary

def Safe (xs : List F) : Prop := ∀ k, k < xs.length → (xs.take k).sum ≠ 1
def Quiet (xs : List F) : Prop := ∀ k, k ≤ xs.length → (xs.take k).sum ≠ 1

theorem lift_quiet_step (a b : F) (ha : a ≠ 1) (hab : a + b ≠ 1) :
    lift (a + b) = lift a + lift b := by
  revert a b
  decide

theorem lift_last_step (a b : F) (ha : a ≠ 1) (hab : a + b = 1) :
    lift a + lift b = 1 ∨ lift a + lift b = -2 := by
  revert a b
  decide

theorem quiet_lift_sum (xs : List F) (hq : Quiet xs) :
    (xs.map lift).sum = lift xs.sum := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    have hp : Quiet xs := by
      intro k hk
      have hh := hq k (by simp; omega)
      simpa [List.take_append_of_le_length hk] using hh
    have hs : xs.sum ≠ 1 := by simpa using hp xs.length (by omega)
    have ht : xs.sum + x ≠ 1 := by
      simpa using hq (xs ++ [x]).length (by omega)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [ih hp, lift_quiet_step _ _ hs ht]

theorem safe_lift_sum (xs : List F) (hs : Safe xs) (ht : xs.sum = 1) :
    (xs.map lift).sum = 1 ∨ (xs.map lift).sum = -2 := by
  cases xs using List.reverseRecOn with
  | nil => simp at ht
  | append_singleton xs x =>
    have hp : Quiet xs := by
      intro k hk
      have hh := hs k (by simp; omega)
      simpa [List.take_append_of_le_length hk] using hh
    have hneq : xs.sum ≠ 1 := by simpa using hp xs.length (by omega)
    have hend : xs.sum + x = 1 := by simpa using ht
    simpa [List.map_append, quiet_lift_sum xs hp] using lift_last_step xs.sum x hneq hend

theorem safe_zero_cons {xs : List F} (h : Safe xs) : Safe (0 :: xs) := by
  intro k hk
  cases k with
  | zero => simp
  | succ k => simpa using h k (by simpa using hk)

theorem safe_neg_pos_cons {xs : List F} (h : Safe xs) : Safe ((-1) :: 1 :: xs) := by
  intro k hk
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => change (-1 : F) ≠ 1; decide
    | succ k => simpa [add_assoc] using h k (by simpa using hk)

theorem safe_singleton_one : Safe [1] := by
  intro k hk
  have : k = 0 := by simpa using hk
  subst k
  simp

theorem safe_two_neg : Safe [(-1), (-1)] := by
  intro k hk
  have : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases this with rfl | rfl <;> decide

theorem field_cases (x : F) : x = 0 ∨ x = 1 ∨ x = -1 := by
  revert x
  decide

theorem exists_safe_order {I : Type*} [DecidableEq I] (x : I → F) (A : Finset I)
    (hd : (∑ i ∈ A, lift (x i)) = 1 ∨ (∑ i ∈ A, lift (x i)) = -2) :
    ∃ xs : List I, xs.Nodup ∧ xs.toFinset = A ∧ Safe (xs.map x) := by
  revert hd
  refine Finset.strongInductionOn A ?_
  · intro A ih hd
    by_cases hz : ∃ i ∈ A, x i = 0
    · obtain ⟨i, hi, hxi⟩ := hz
      have hd' : (∑ j ∈ A.erase i, lift (x j)) = 1 ∨
          (∑ j ∈ A.erase i, lift (x j)) = -2 := by
        have hh := sum_erase_add A (fun j => lift (x j)) hi
        simp only [hxi, lift_zero, add_zero] at hh
        rwa [hh]
      obtain ⟨xs, hn, he, hs⟩ := ih (A.erase i) (erase_ssubset hi) hd'
      have hni : i ∉ xs := by
        intro hh
        have hm : i ∈ xs.toFinset := List.mem_toFinset.mpr hh
        simp [he] at hm
      refine ⟨i :: xs, List.nodup_cons.mpr ⟨hni, hn⟩, ?_, ?_⟩
      · simp [he, hi]
      · simpa [hxi] using safe_zero_cons hs
    · by_cases hp : ∃ p ∈ A, x p = 1
      · obtain ⟨p, hp, hxp⟩ := hp
        by_cases hm : ∃ m ∈ A, x m = -1
        · obtain ⟨m, hm, hxm⟩ := hm
          have hpm : p ≠ m := by intro he; subst m; rw [hxp] at hxm; contradiction
          have hp' : p ∈ A.erase m := mem_erase.mpr ⟨hpm, hp⟩
          have hd' : (∑ j ∈ (A.erase m).erase p, lift (x j)) = 1 ∨
              (∑ j ∈ (A.erase m).erase p, lift (x j)) = -2 := by
            have h₁ := sum_erase_add A (fun j => lift (x j)) hm
            have h₂ := sum_erase_add (A.erase m) (fun j => lift (x j)) hp'
            simp only [hxp, hxm, lift_one, lift_neg_one] at h₁ h₂
            omega
          obtain ⟨xs, hn, he, hs⟩ := ih ((A.erase m).erase p)
            (Finset.ssubset_of_subset_of_ssubset (erase_subset p (A.erase m)) (erase_ssubset hm)) hd'
          have hnm : m ∉ xs := by
            intro hh
            have hm' : m ∈ (A.erase m).erase p := he ▸ List.mem_toFinset.mpr hh
            exact notMem_erase m A (mem_of_mem_erase hm')
          have hnp : p ∉ xs := by
            intro hh
            have hp'' : p ∈ (A.erase m).erase p := he ▸ List.mem_toFinset.mpr hh
            exact notMem_erase p (A.erase m) hp''
          refine ⟨m :: p :: xs, by simp [hnm, hnp, hn, hpm.symm], ?_, ?_⟩
          · simp only [List.toFinset_cons, he]
            ext j
            simp only [mem_insert, mem_erase]
            constructor
            · rintro (rfl | rfl | h) <;> aesop
            · intro hj
              by_cases hjm : j = m
              · exact Or.inl hjm
              · by_cases hjp : j = p
                · exact Or.inr (Or.inl hjp)
                · exact Or.inr (Or.inr ⟨hjp, hjm, hj⟩)
          · simpa [hxp, hxm] using safe_neg_pos_cons hs
        · have hall : ∀ i ∈ A, x i = 1 := by
            intro i hi
            rcases field_cases (x i) with h | h | h
            · exact False.elim (hz ⟨i, hi, h⟩)
            · exact h
            · exact False.elim (hm ⟨i, hi, h⟩)
          have hsum : (∑ i ∈ A, lift (x i)) = A.card := by
            calc
              _ = ∑ _i ∈ A, (1 : ℤ) := sum_congr rfl (fun i hi => by rw [hall i hi, lift_one])
              _ = _ := by simp
          have hc : A.card = 1 := by omega
          obtain ⟨i, rfl⟩ := card_eq_one.mp hc
          refine ⟨[i], by simp, by simp, ?_⟩
          simpa [hall i (by simp)] using safe_singleton_one
      · have hall : ∀ i ∈ A, x i = -1 := by
          intro i hi
          rcases field_cases (x i) with h | h | h
          · exact False.elim (hz ⟨i, hi, h⟩)
          · exact False.elim (hp ⟨i, hi, h⟩)
          · exact h
        have hsum : (∑ i ∈ A, lift (x i)) = -(A.card : ℤ) := by
          calc
            _ = ∑ _i ∈ A, (-1 : ℤ) := sum_congr rfl (fun i hi => by rw [hall i hi, lift_neg_one])
            _ = _ := by simp
        have hc : A.card = 2 := by omega
        obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hc
        refine ⟨[i, j], by simp [hij], by simp, ?_⟩
        simpa [hall i (by simp), hall j (by simp)] using safe_two_neg

end Ternary
