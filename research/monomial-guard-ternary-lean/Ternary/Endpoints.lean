import Ternary.PairFamily
import Ternary.StrongLower

open Finset
namespace Ternary

abbrev LowerPairs (r n : ℕ) := Fin (min r n) ⊕ Fin (r - min r n)
def lowerPure (r n : ℕ) : ℕ := 3 * n + 1 - 2 * min r n
def lowerBase (r n : ℕ) : LowerPairs r n → F := Sum.elim (fun _ => 1) (fun _ => 0)
def lower (r n : ℕ) : Pencil (Coord (LowerPairs r n) (lowerPure r n)) :=
  phase (lowerPure r n) (lowerBase r n) ∅
def upper (r n : ℕ) : Pencil (Coord (Fin r) (2 * r + 3 * n + 1)) :=
  phase (2 * r + 3 * n + 1) (fun _ => -1) ∅

theorem lower_pairs_card (r n : ℕ) : Fintype.card (LowerPairs r n) = r := by
  simp only [LowerPairs, Fintype.card_sum, Fintype.card_fin]
  have := min_le_left r n
  omega

theorem lower_S (r n : ℕ) : S (lower r n) = r := by
  rw [lower, phase_S, lower_pairs_card]

theorem upper_S (r n : ℕ) : S (upper r n) = r := by
  simp [upper, phase_S]

theorem lower_D (r n : ℕ) : imbalance (lower r n) = 3 * n + 1 := by
  rw [lower, phase_imbalance_initial]
  have hs : (∑ j : LowerPairs r n, lift (lowerBase r n j)) = min r n := by
    simp [lowerBase, Fintype.sum_sum_type]
  rw [hs]
  unfold lowerPure
  have := min_le_right r n
  omega

theorem upper_D (r n : ℕ) : imbalance (upper r n) = 3 * n + 1 := by
  simp only [upper, phase_imbalance_initial, lift_neg_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem lower_L (r n : ℕ) : L (lower r n) = n := by
  unfold L
  rw [lower_D, price_three_mul_add_one]

theorem upper_L (r n : ℕ) : L (upper r n) = n := by
  unfold L
  rw [upper_D, price_three_mul_add_one]

theorem normalized_of_D {I V : Type*} [Fintype I] (s : HZ.State I F V) (n : ℕ)
    (hd : imbalance s = 3 * n + 1) : ∑ i, scalar s i = 1 := by
  rw [← cast_imbalance, hd]
  push_cast
  have hthree : (3 : F) = 0 := by decide
  rw [hthree, zero_mul, zero_add]

theorem lower_normalized (r n : ℕ) : ∑ i, scalar (lower r n) i = 1 :=
  normalized_of_D _ n (lower_D r n)

theorem upper_normalized (r n : ℕ) : ∑ i, scalar (upper r n) i = 1 :=
  normalized_of_D _ n (upper_D r n)

theorem lower_total_charge (r n : ℕ) : ∑ i, (lower r n).charge i = 0 :=
  phase_total_charge _ _

theorem upper_total_charge (r n : ℕ) : ∑ i, (upper r n).charge i = 0 :=
  phase_total_charge _ _

theorem lower_final_D (r n : ℕ) :
    imbalance (phase (lowerPure r n) (lowerBase r n) univ) = 3 * (n - min r n) + 1 := by
  rw [phase_imbalance_final]
  have hq : lift ((1 : F) + 1) = -1 := by decide
  have hs : (∑ j : LowerPairs r n, lift (lowerBase r n j + lowerBase r n j)) = -(min r n : ℤ) := by
    simp [lowerBase, Fintype.sum_sum_type, hq]
  rw [hs]
  unfold lowerPure
  have := min_le_right r n
  omega

theorem upper_final_D (r n : ℕ) :
    imbalance (phase (2 * r + 3 * n + 1) (fun _ : Fin r => (-1 : F)) univ) =
      3 * (r + n) + 1 := by
  rw [phase_imbalance_final]
  have hq : lift ((-1 : F) + (-1)) = 1 := by decide
  simp only [hq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem pair_repair_attained {J : Type*} [DecidableEq J] [Fintype J]
    (p : ℕ) (b : J → F) (hn : ∑ i, scalar (phase p b ∅) i = 1) :
    ∃ t, HZ.Run (phase p b ∅) (Fintype.card J + L (phase p b univ)) t ∧ FullGuard t := by
  have hr : HZ.Run (phase p b ∅) (Fintype.card J) (phase p b univ) := by
    simpa using phase_run p b univ
  obtain ⟨t, ht, hs, hd⟩ := separated_repair (phase p b univ) ((scalar_total hr).trans hn)
    (phase_separated p b)
  exact ⟨t, hr.trans ht, separated_good_fullguard t hs hd⟩

theorem lower_attained (r n : ℕ) :
    ∃ t, HZ.Run (lower r n) (max r n) t ∧ FullGuard t := by
  have hp : L (phase (lowerPure r n) (lowerBase r n) univ) = n - min r n := by
    unfold L
    rw [lower_final_D]
    simpa [Nat.cast_sub (min_le_right r n)] using price_three_mul_add_one (n - min r n)
  obtain ⟨t, hr, hg⟩ := pair_repair_attained (lowerPure r n) (lowerBase r n) (lower_normalized r n)
  rw [lower_pairs_card, hp] at hr
  have hc : r + (n - min r n) = max r n := by omega
  rw [hc] at hr
  exact ⟨t, hr, hg⟩

theorem upper_attained (r n : ℕ) :
    ∃ t, HZ.Run (upper r n) (2 * r + n) t ∧ FullGuard t := by
  have hp : L (phase (2 * r + 3 * n + 1) (fun _ : Fin r => (-1 : F)) univ) = r + n := by
    unfold L
    rw [upper_final_D]
    simpa using price_three_mul_add_one (r + n)
  obtain ⟨t, hr, hg⟩ := pair_repair_attained (2 * r + 3 * n + 1) (fun _ : Fin r => (-1 : F))
    (upper_normalized r n)
  simp only [Fintype.card_fin, hp] at hr
  have hc : r + (r + n) = 2 * r + n := by omega
  rw [hc] at hr
  exact ⟨t, hr, hg⟩

theorem upper_pure (r n : ℕ) : ∀ i, (upper r n).w i = 0 → scalar (upper r n) i = 1 := by
  intro i hw
  rcases i with ⟨j, v⟩ | (j | j)
  · cases v <;> simp [upper, phase, funext_iff] at hw
  · simp [upper, phase, scalar]
  · simp [upper, phase, funext_iff] at hw

theorem upper_weight (r n : ℕ) : weightSum (upper r n) = 6 * r + 3 * n + 1 := by
  simp only [weightSum, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [upper, phase, scalar, weight_neg_one]
  ring

theorem upper_word_lower_bound (r n k : ℕ) (t : Pencil (Coord (Fin r) (2 * r + 3 * n + 1)))
    (hr : HZ.Run (upper r n) k t) (hg : FullGuard t) : 2 * r + n ≤ k := by
  have hb := strong_guard_bound (upper_pure r n) (upper_total_charge r n) (upper_normalized r n) hr hg
  rw [upper_weight] at hb
  omega

theorem lower_cost (r n : ℕ) : C (lower r n) = max r n := by
  have hb := (envelope (lower r n) (lower_total_charge r n) (lower_normalized r n)).1
  rw [lower_S, lower_L] at hb
  have hu : C (lower r n) ≤ max r n := Nat.sInf_le (lower_attained r n)
  omega

theorem upper_cost (r n : ℕ) : C (upper r n) = 2 * r + n := by
  obtain ⟨t, hr, hg⟩ := C_attained (upper r n) (upper_total_charge r n) (upper_normalized r n)
  have hl := upper_word_lower_bound r n (C (upper r n)) t hr hg
  have hu : C (upper r n) ≤ 2 * r + n := Nat.sInf_le (upper_attained r n)
  omega

/-- Both ends are attained for every prescribed nonnegative pair, including either zero. -/
theorem sharp_endpoints (r n : ℕ) :
    (S (lower r n) = r ∧ L (lower r n) = n ∧ C (lower r n) = max r n) ∧
    (S (upper r n) = r ∧ L (upper r n) = n ∧ C (upper r n) = 2 * r + n) :=
  ⟨⟨lower_S r n, lower_L r n, lower_cost r n⟩,
   ⟨upper_S r n, upper_L r n, upper_cost r n⟩⟩

theorem endpoint_nonzero_slopes (r n : ℕ) :
    (∃ i, (lower r n).w i () ≠ 0) ∧ (∃ i, (upper r n).w i () ≠ 0) :=
  ⟨phase_nonzero_slope _ _, phase_nonzero_slope _ _⟩

end Ternary
