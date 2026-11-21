import AffineGuard.OneParameter.Blocks

namespace AffineGuard.OneParameter
open Finset Ternary

/-- The least nonnegative residue of the negative slope charge, viewed as an integer. -/
def weight (x : F) : ℤ := (-x).val

def potential [Fintype I] (s : Pencil I) : ℤ := ∑ i, weight (slope s i)

private theorem weight_pair : ∀ a b c d : F, a+b = c+d →
    weight a + weight b ≤ weight c + weight d + 3 := by decide

variable {I : Type*} [DecidableEq I] [Fintype I]

private theorem weight_step (s : Pencil I) (op : HZ.Operation I F) :
    potential s ≤ potential (op.apply s) + 3 * op.cost := by
  cases op with
  | add i j c hij _ =>
    have change := sum_diff_pair (fun k => weight (slope s k))
      (fun k => weight (slope (s.addRow i j c) k)) hij
      (fun k hi hj => congrArg (fun v : Fin 1 → F => weight (v 0)) (HZ.charge_add_outside s c hi hj).symm)
    have pair := weight_pair (slope s i) (slope s j)
      (slope (s.addRow i j c) i) (slope (s.addRow i j c) j)
      (congrFun (HZ.charge_add_pair s c hij).symm 0)
    change potential s ≤ potential (s.addRow i j c) + 3 * (1 : ℤ)
    have drop : potential s - potential (s.addRow i j c) ≤ 3 := by
      rw [show potential s - potential (s.addRow i j c) = _ from change]
      change weight (slope s i) + weight (slope s j) -
        (weight (slope (s.addRow i j c) i) + weight (slope (s.addRow i j c) j)) ≤ 3
      omega
    omega
  | permute e =>
    have eq : potential (s.permute e) = potential s :=
      Equiv.sum_comp e (fun i => weight (slope s i))
    simp [HZ.Operation.apply,HZ.Operation.cost,eq]
  | scale c hc =>
    have eq : potential (s.scale c) = potential s :=
      sum_congr rfl fun i _ => congrArg (fun v : Fin 1 → F => weight (v 0)) (HZ.charge_scale s c hc i)
    simp [HZ.Operation.apply,HZ.Operation.cost,eq]

theorem weight_run {s t : Pencil I} {n} (r : HZ.Run s n t) :
    potential s ≤ potential t + 3*(n : ℤ) := by
  induction r with
  | nil => simp
  | cons s op _ ih =>
    have h := weight_step s op
    push_cast
    omega

theorem potential_lower (s : Pencil I) (hs : Normalized s) : potential s ≤ 3*(C s : ℤ) := by
  obtain ⟨t,r,guard⟩ := C_attained s hs.1 hs.2
  have sep := fullguard_separated t (r.total_charge.trans hs.1) guard
  have zero (i : I) : slope t i = 0 := congrFun (sep i) 0
  simpa [potential,zero,weight] using weight_run r

/-- One exceptional slope followed by n ones. The scalar column is the first unit vector. -/
def extremal (n : ℕ) : Pencil (Fin (n+1)) :=
  ⟨fun _ => 1, Fin.cons (fun _ => -(n : F)) (fun _ _ => 1), Fin.cons 1 (fun _ => 0)⟩

theorem extremal_normalized (n : ℕ) : Normalized (extremal n) := by
  constructor
  · funext d
    simp [extremal,HZ.State.charge,Finset.sum_apply,Fin.sum_univ_succ]
  · simp [extremal,scalar,Fin.sum_univ_succ]

theorem extremal_nonconstant (n : ℕ) (hn : 0 < n) : ∃ i, (extremal n).w i 0 ≠ 0 := by
  refine ⟨(⟨0,hn⟩ : Fin n).succ,?_⟩
  have tail (i : Fin n) : (extremal n).w i.succ 0 = 1 := by simp only [extremal,Fin.cons_succ]
  rw [tail]
  exact one_ne_zero

theorem extremal_weight (n : ℕ) :
    potential (extremal n) = 3 * ((2*(n+1)/3 : ℕ) : ℤ) := by
  have one : weight 1 = 2 := by decide
  have initial : slope (extremal n) 0 = -(n : F) := by simp [slope,extremal,HZ.State.charge]
  have tail (i : Fin n) : slope (extremal n) i.succ = 1 := by
    simp only [slope,extremal,HZ.State.charge,one_smul,Fin.cons_succ]
  have w0 : weight (-(n : F)) = ((n%3 : ℕ) : ℤ) := by
    unfold weight
    rw [neg_neg,ZMod.val_natCast]
  rw [potential,Fin.sum_univ_succ,initial,w0]
  simp_rw [tail,one]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  omega

end AffineGuard.OneParameter
