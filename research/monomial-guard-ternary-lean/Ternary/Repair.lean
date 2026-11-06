import Ternary.Scalar

open Finset
namespace Ternary

theorem lift_as_counts (x : F) :
    lift x = (if x = 1 then 1 else 0) - (if x = -1 then 1 else 0) := by
  revert x
  decide

variable {I V : Type*} [DecidableEq I] [Fintype I] [AddCommGroup V] [Module F V]

def positives (s : HZ.State I F V) : Finset I := univ.filter (fun i => scalar s i = 1)
def negatives (s : HZ.State I F V) : Finset I := univ.filter (fun i => scalar s i = -1)

omit [DecidableEq I] [AddCommGroup V] [Module F V] in
theorem imbalance_counts (s : HZ.State I F V) :
    imbalance s = (positives s).card - (negatives s).card := by
  simp only [imbalance, lift_as_counts, sum_sub_distrib]
  simp [positives, negatives, sum_boole]

omit [DecidableEq I] [AddCommGroup V] [Module F V] in
theorem two_positive (s : HZ.State I F V) (hd : 1 < imbalance s) :
    ∃ i j, i ≠ j ∧ scalar s i = 1 ∧ scalar s j = 1 := by
  have hc : 1 < (positives s).card := by rw [imbalance_counts] at hd; omega
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hc
  exact ⟨i, j, hij, (mem_filter.mp hi).2, (mem_filter.mp hj).2⟩

omit [DecidableEq I] [AddCommGroup V] [Module F V] in
theorem two_negative (s : HZ.State I F V) (hd : imbalance s < -2) :
    ∃ i j, i ≠ j ∧ scalar s i = -1 ∧ scalar s j = -1 := by
  have hc : 1 < (negatives s).card := by rw [imbalance_counts] at hd; omega
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hc
  exact ⟨i, j, hij, (mem_filter.mp hi).2, (mem_filter.mp hj).2⟩

theorem merge_equal (s : HZ.State I F V) {i j : I} (hij : i ≠ j) (q : F)
    (hq : q ≠ 0) (hi : scalar s i = q) (hj : scalar s j = q) :
    ∃ t, HZ.Run s 1 t ∧
      (HZ.Separated s → HZ.Separated t) ∧
      imbalance t = imbalance s + lift (q + q) - 2 * lift q ∧
      scalar t i = 0 ∧ scalar t j = q + q := by
  have hui : s.u i ≠ 0 := by intro hz; simp [scalar, hz] at hi; exact hq hi.symm
  have huj : s.u j ≠ 0 := by intro hz; simp [scalar, hz] at hj; exact hq hj.symm
  let a := -s.u i / s.u j
  let t := s.addRow i j a
  obtain ⟨ha, hzero, _, hyi, hyj⟩ := HZ.elimination s hij hui huj
  have hxi : scalar t i = 0 := by simp [scalar, t, a, hzero]
  have hxj : scalar t j = q + q := by
    have hh := scalar_add_pair s a hij
    change scalar t i + scalar t j = _ at hh
    simpa [hxi, hi, hj] using hh
  refine ⟨t, ?_, ?_, ?_, hxi, hxj⟩
  · simpa [HZ.Operation.cost] using
      HZ.Run.cons s (HZ.Operation.add i j a hij ha) (HZ.Run.nil t)
  · intro hs k
    by_cases hki : k = i
    · subst k; exact hyi
    · by_cases hkj : k = j
      · subst k; simpa [hs i, hs j] using hyj
      · exact (HZ.charge_add_outside s a hki hkj).trans (hs k)
  · have hh := sum_diff_pair (fun k => lift (scalar t k)) (fun k => lift (scalar s k))
      hij (fun k hki hkj => congrArg lift (scalar_add_outside s a hki hkj))
    change imbalance t - imbalance s = _ at hh
    dsimp only at hh
    rw [hxi, hxj, hi, hj, lift_zero] at hh
    omega

theorem repair_step (s : HZ.State I F V) (hn : ∑ i, scalar s i = 1)
    (hs : HZ.Separated s) (hp : L s ≠ 0) :
    ∃ t, HZ.Run s 1 t ∧ HZ.Separated t ∧ L t + 1 = L s := by
  have hm := mod_three (imbalance s) ((cast_imbalance s).trans hn)
  rcases price_pos_cases (imbalance s) hm hp with hd | hd
  · obtain ⟨i, j, hij, hi, hj⟩ := two_positive s hd
    obtain ⟨t, hr, ht, he, _, _⟩ := merge_equal s hij 1 one_ne_zero hi hj
    have hx : imbalance t = imbalance s - 3 := by
      have hq : lift ((1 : F) + 1) = -1 := by decide
      rw [hq, lift_one] at he
      omega
    refine ⟨t, hr, ht hs, ?_⟩
    unfold L
    rw [hx]
    exact price_sub_three _ hm hd
  · obtain ⟨i, j, hij, hi, hj⟩ := two_negative s hd
    obtain ⟨t, hr, ht, he, _, _⟩ := merge_equal s hij (-1) (by decide) hi hj
    have hx : imbalance t = imbalance s + 3 := by
      have hq : lift ((-1 : F) + (-1)) = 1 := by decide
      rw [hq, lift_neg_one] at he
      omega
    refine ⟨t, hr, ht hs, ?_⟩
    unfold L
    rw [hx]
    exact price_add_three _ hm hd

theorem separated_repair (s : HZ.State I F V) (hn : ∑ i, scalar s i = 1)
    (hs : HZ.Separated s) :
    ∃ t, HZ.Run s (L s) t ∧ HZ.Separated t ∧
      (imbalance t = 1 ∨ imbalance t = -2) := by
  generalize he : L s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hz : n = 0
    · have hzL : L s = 0 := he.trans hz
      refine ⟨s, ?_, hs, ?_⟩
      · rw [hz]; exact HZ.Run.nil s
      · exact (price_zero_iff _ (mod_three _ ((cast_imbalance s).trans hn))).mp hzL
    · obtain ⟨t, hr, ht, hp⟩ := repair_step s hn hs (by omega)
      have hnt : ∑ i, scalar t i = 1 := (scalar_total hr).trans hn
      obtain ⟨r, hrun, hsep, hgood⟩ := ih (L t) (by omega) t hnt ht rfl
      refine ⟨r, ?_, hsep, hgood⟩
      have hc : 1 + L t = n := by omega
      simpa [hc] using hr.trans hrun

end Ternary
