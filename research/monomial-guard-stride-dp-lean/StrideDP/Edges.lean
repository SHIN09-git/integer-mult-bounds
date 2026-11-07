import StrideDP.Grid
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace StrideDP
open CountDP Finset
variable {V : Type*}

/-- Count the nonzero digits in the mixed-radix representation of an address. -/
def legalDigits (n : V → ℕ) : List V → ℕ → ℕ
  | [], _ => 0
  | v :: vs, k =>
    (if k % (n v + 1) = 0 then 0 else 1) + legalDigits n vs (k / (n v + 1))

def edges (n : V → ℕ) : List V → ℕ
  | [] => 0
  | v :: vs => n v * slots n vs + (n v + 1) * edges n vs

private theorem sum_blocks (f : ℕ → ℕ) (b q : ℕ) :
    ∑ k ∈ range (q*b), f k = ∑ j ∈ range q, ∑ r ∈ range b, f (j*b+r) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem sum_legalDigits (n : V → ℕ) (xs : List V) :
    ∑ k ∈ range (slots n xs), legalDigits n xs k = edges n xs := by
  induction xs with
  | nil => simp [slots, legalDigits, edges]
  | cons v vs ih =>
    let b := n v + 1
    have h (j : ℕ) : ∑ r ∈ range b, legalDigits n (v::vs) (j*b+r) =
        n v + b * legalDigits n vs j := by
      have term (r : ℕ) (hr : r ∈ range b) : legalDigits n (v::vs) (j*b+r) =
          (if r = 0 then 0 else 1) + legalDigits n vs j := by
        have hr' := mem_range.mp hr
        have hb : 0 < b := Nat.succ_pos _
        have hm : (j*b+r)%b = r := by simp [Nat.add_comm, Nat.mod_eq_of_lt hr']
        have hq : (j*b+r)/b = j := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hr', Nat.zero_add]
        change (if (j*b+r)%b = 0 then 0 else 1) + legalDigits n vs ((j*b+r)/b) = _
        rw [hm, hq]
      rw [sum_congr rfl term, sum_add_distrib]
      have hcount : (∑ r ∈ range b, (if r = 0 then 0 else 1 : ℕ)) = n v := by
        dsimp [b]
        rw [sum_range_succ']
        simp
      simp [hcount]
    rw [slots, Nat.mul_comm, sum_blocks, sum_congr rfl (fun j _ => h j), sum_add_distrib,
      ← mul_sum, ih]
    simp [edges, b, Nat.mul_comm]

theorem edges_formula [DecidableEq V] (n : V → ℕ) (xs : List V) (hd : xs.Nodup) :
    edges n xs = ∑ v ∈ xs.toFinset, n v * ∏ w ∈ xs.toFinset.erase v, (n w + 1) := by
  induction xs with
  | nil => simp [edges]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    have hnot : v ∉ vs.toFinset := by simpa using hv
    rw [edges, slots_eq_prod _ _ hvs, ih hvs, List.toFinset_cons, sum_insert hnot,
      erase_insert hnot, mul_sum]
    congr 1
    apply sum_congr rfl
    intro w hw
    have hne : w ≠ v := fun e => hnot (e ▸ hw)
    rw [erase_insert_of_ne hne.symm, prod_insert (fun h => hnot (mem_of_mem_erase h))]
    ac_rfl

theorem legalDigits_le (n : V → ℕ) (xs : List V) (k : ℕ) : legalDigits n xs k ≤ xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons v vs ih =>
    have := ih (k/(n v + 1))
    simp only [legalDigits, List.length_cons]
    split <;> omega

theorem edges_le (n : V → ℕ) (xs : List V) : edges n xs ≤ xs.length * slots n xs := by
  rw [← sum_legalDigits]
  calc
    _ ≤ ∑ _ ∈ range (slots n xs), xs.length := sum_le_sum (fun k _ => legalDigits_le n xs k)
    _ = _ := by simp [Nat.mul_comm]

end StrideDP
