import HZ.Guards
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Finset
namespace Ternary
abbrev F := ZMod 3
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def lift (x : F) : ℤ := if x = 0 then 0 else if x = 1 then 1 else -1

theorem lift_bounds (x : F) : -1 ≤ lift x ∧ lift x ≤ 1 := by
  unfold lift
  split_ifs <;> omega

@[simp] theorem lift_zero : lift 0 = 0 := by decide
@[simp] theorem lift_one : lift 1 = 1 := by decide
@[simp] theorem lift_neg_one : lift (-1) = -1 := by decide

theorem cast_lift (x : F) : (lift x : F) = x := by
  fin_cases x <;> decide

theorem lift_pair_change (a b c d : F) (h : a + b = c + d) :
    |lift a + lift b - (lift c + lift d)| ≤ 3 := by
  revert a b c d
  decide

def price (d : ℤ) : ℕ := min (d - 1).natAbs (d + 2).natAbs / 3

theorem price_lipschitz (d e : ℤ) (h : |d - e| ≤ 3) : price d ≤ price e + 1 := by
  have hab : (d - e).natAbs ≤ 3 := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have h₁ := Int.natAbs_add_le (e - 1) (d - e)
  have h₂ := Int.natAbs_add_le (e + 2) (d - e)
  have he₁ : e - 1 + (d - e) = d - 1 := by omega
  have he₂ : e + 2 + (d - e) = d + 2 := by omega
  rw [he₁] at h₁
  rw [he₂] at h₂
  unfold price
  omega

theorem price_formula (d : ℤ) :
    price d = max ((d - 1) / 3).toNat ((-d - 2) / 3).toNat := by
  unfold price
  omega

theorem mod_three (d : ℤ) (h : (d : F) = 1) : d % 3 = 1 := by
  have hh := (ZMod.intCast_eq_intCast_iff' d 1 3).mp (by simpa using h)
  norm_num at hh
  exact hh

theorem price_zero_iff (d : ℤ) (h : d % 3 = 1) :
    price d = 0 ↔ d = 1 ∨ d = -2 := by
  rw [price_formula]
  omega

theorem price_pos_cases (d : ℤ) (h : d % 3 = 1) (hp : price d ≠ 0) :
    1 < d ∨ d < -2 := by
  rw [price_formula] at hp
  omega

theorem price_sub_three (d : ℤ) (h : d % 3 = 1) (hd : 1 < d) :
    price (d - 3) + 1 = price d := by
  simp only [price_formula]
  omega

theorem price_add_three (d : ℤ) (h : d % 3 = 1) (hd : d < -2) :
    price (d + 3) + 1 = price d := by
  simp only [price_formula]
  omega

@[simp] theorem price_three_mul_add_one (n : ℕ) : price (3 * n + 1) = n := by
  rw [price_formula]
  omega

variable {I V : Type*} [DecidableEq I] [Fintype I] [AddCommGroup V] [Module F V]

def scalar (s : HZ.State I F V) (i : I) : F := s.u i * s.b i
def imbalance (s : HZ.State I F V) : ℤ := ∑ i, lift (scalar s i)
def L (s : HZ.State I F V) : ℕ := price (imbalance s)
noncomputable def S (s : HZ.State I F V) : ℕ := HZ.activeCount s - HZ.partitionCount s

def scalarState (s : HZ.State I F V) : HZ.State I F F := ⟨s.u, s.b, s.b⟩

omit [Fintype I] in
theorem run_scalar {s t : HZ.State I F V} {n : ℕ} (hr : HZ.Run s n t) :
    HZ.Run (scalarState s) n (scalarState t) := by
  induction hr with
  | nil => exact HZ.Run.nil _
  | cons s g tail ih =>
    have he : scalarState (g.apply s) = g.apply (scalarState s) := by
      cases g <;> ext i <;> simp [scalarState, HZ.Operation.apply, HZ.State.addRow,
        HZ.State.permute, HZ.State.scale, smul_eq_mul]
    rw [he] at ih
    exact HZ.Run.cons _ _ ih

theorem scalar_total {s t : HZ.State I F V} {n : ℕ} (hr : HZ.Run s n t) :
    ∑ i, scalar t i = ∑ i, scalar s i := by
  simpa [scalar, scalarState, HZ.State.charge, smul_eq_mul] using (run_scalar hr).total_charge

omit [DecidableEq I] [AddCommGroup V] [Module F V] in
theorem cast_imbalance (s : HZ.State I F V) : (imbalance s : F) = ∑ i, scalar s i := by
  simp [imbalance, cast_lift]

omit [Fintype I] in
theorem scalar_add_pair (s : HZ.State I F V) {i j : I} (a : F) (hij : i ≠ j) :
    scalar (s.addRow i j a) i + scalar (s.addRow i j a) j = scalar s i + scalar s j := by
  simp only [scalar, HZ.State.addRow, Function.update_self,
    Function.update_of_ne hij, Function.update_of_ne hij.symm]
  ring

omit [Fintype I] in
theorem scalar_add_outside (s : HZ.State I F V) {i j k : I} (a : F)
    (hki : k ≠ i) (hkj : k ≠ j) : scalar (s.addRow i j a) k = scalar s k := by
  simp [scalar, HZ.State.addRow, hki, hkj]

theorem sum_diff_pair (f g : I → ℤ) {i j : I} (hij : i ≠ j)
    (hout : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (∑ k, f k) - (∑ k, g k) = f i + f j - (g i + g j) := by
  rw [← sum_sub_distrib]
  have hh : (∑ k ∈ ({i, j} : Finset I), (f k - g k)) = ∑ k, (f k - g k) := by
    apply sum_subset (subset_univ _)
    intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    exact sub_eq_zero.mpr (hout k hk.1 hk.2)
  rw [← hh]
  simp [hij]

theorem imbalance_add_change (s : HZ.State I F V) {i j : I} (a : F) (hij : i ≠ j) :
    |imbalance (s.addRow i j a) - imbalance s| ≤ 3 := by
  unfold imbalance
  rw [sum_diff_pair _ _ hij (fun k hki hkj => congrArg lift (scalar_add_outside s a hki hkj))]
  exact lift_pair_change _ _ _ _ (scalar_add_pair s a hij)

omit [DecidableEq I] [AddCommGroup V] [Module F V] in
theorem imbalance_permute (s : HZ.State I F V) (e : Equiv.Perm I) :
    imbalance (s.permute e) = imbalance s := Equiv.sum_comp e (fun i => lift (scalar s i))

omit [DecidableEq I] in
theorem imbalance_scale (s : HZ.State I F V) (c : I → F) (hc : ∀ i, c i ≠ 0) :
    imbalance (s.scale c) = imbalance s := by
  apply sum_congr rfl
  intro i _
  congr 1
  simp only [scalar, HZ.State.scale]
  field_simp [hc i]

theorem operation_price (s : HZ.State I F V) (g : HZ.Operation I F) :
    L (g.apply s) ≤ L s + g.cost ∧ L s ≤ L (g.apply s) + g.cost := by
  cases g with
  | add i j a hij ha =>
    have hh := imbalance_add_change s a hij
    exact ⟨price_lipschitz _ _ hh, price_lipschitz _ _ (by rwa [abs_sub_comm])⟩
  | permute e => simp [L, HZ.Operation.apply, HZ.Operation.cost, imbalance_permute]
  | scale c hc => simp [L, HZ.Operation.apply, HZ.Operation.cost, imbalance_scale s c hc]

theorem run_price {s t : HZ.State I F V} {n : ℕ} (hr : HZ.Run s n t) :
    L t ≤ L s + n ∧ L s ≤ L t + n := by
  induction hr with
  | nil => omega
  | cons s g tail ih =>
    have hh := operation_price s g
    omega

end Ternary
