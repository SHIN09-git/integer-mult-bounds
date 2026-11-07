import SmallFields.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace SmallFields
open Multiset
variable {V : Type*}

def weight (f : V → ℕ) (m : Multiset V) := (m.map f).sum

@[simp] theorem weight_add (f : V → ℕ) (a b : Multiset V) :
    weight f (a+b) = weight f a + weight f b := by simp [weight]

@[simp] theorem weight_replicate (f : V → ℕ) (a : ℕ) (v : V) :
    weight f (replicate a v) = a*f v := by simp [weight]

theorem weight_pos (f : V → ℕ) (b : Multiset V) (hn : b ≠ 0) (hf : ∀ v ∈ b, 0 < f v) :
    0 < weight f b := by
  obtain ⟨x,hx⟩ := Multiset.exists_mem_of_ne_zero hn
  obtain ⟨c,rfl⟩ := Multiset.exists_cons_of_mem hx
  have pos := hf x (mem_cons_self ..)
  simp only [weight,map_cons,sum_cons]
  omega

def residue {p : ℕ} (u v : ZMod p) := (u*v).val

theorem cast_weight {p : ℕ} [NeZero p] (u : ZMod p) (m : Multiset (ZMod p)) :
    (weight (residue u) m : ZMod p) = u*m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp [weight]
  | cons x xs ih =>
    simpa only [weight,map_cons,sum_cons,Nat.cast_add,residue,ZMod.natCast_zmod_val,mul_add] using
      congrArg (u*x + ·) ih

theorem Blocks.weight_bound {p : ℕ} [NeZero p] (u : ZMod p) {m : Multiset (ZMod p)} {k : ℕ}
    (pr : Blocks m k) (hn : ∀ v ∈ m, u*v ≠ 0) : p*k ≤ weight (residue u) m := by
  induction pr with
  | empty => simp [weight]
  | @join b m k hb hz _ ih =>
    have hpos := weight_pos (residue u) b hb (fun v hv =>
      Nat.pos_of_ne_zero (fun e => hn v (Multiset.mem_add.mpr (.inl hv))
        ((ZMod.val_eq_zero _).mp e)))
    have dvd := (ZMod.natCast_eq_zero_iff _ p).mp ((cast_weight u b).trans (by rw [hz,mul_zero]))
    have hB := Nat.le_of_dvd hpos dvd
    have hM := ih (fun v hv => hn v (Multiset.mem_add.mpr (.inr hv)))
    rw [weight_add,Nat.mul_succ]
    omega

theorem Z_weight_bound {p : ℕ} [NeZero p] (u : ZMod p) (m : Multiset (ZMod p))
    (hz : m.sum = 0) (hn : ∀ v ∈ m, u*v ≠ 0) : p*Z m ≤ weight (residue u) m :=
  (attaining m hz).weight_bound u hn

theorem scale_sum {F : Type*} [Field F] (u : F) (m : Multiset F) :
    (m.map (u*·)).sum = u*m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x xs ih => simp [ih,mul_add]

theorem Blocks.map_scale {F : Type*} [Field F] (u : F) {m : Multiset F} {k : ℕ} (pr : Blocks m k) :
    Blocks (m.map (u*·)) k := by
  induction pr with
  | empty => exact Blocks.empty
  | @join b m k hb hz _ ih =>
    rw [Multiset.map_add]
    exact Blocks.join (by simpa using hb) ((scale_sum u b).trans (by rw [hz,mul_zero])) ih

theorem Z_scale {F : Type*} [Field F] {u : F} (hu : u ≠ 0) (m : Multiset F) (hz : m.sum = 0) :
    Z (m.map (u*·)) = Z m := by
  have hz' : (m.map (u*·)).sum = 0 := by rw [scale_sum,hz,mul_zero]
  have upper := (attaining _ hz').map_scale u⁻¹
  have he : (m.map (u*·)).map (u⁻¹*·) = m := by
    simp [Multiset.map_map,hu]
  rw [he] at upper
  exact le_antisymm upper.le_Z ((attaining _ hz).map_scale u).le_Z

end SmallFields
