import SmallFields.Residual
import SmallFields.PairLabels
import Mathlib.Algebra.Field.ZMod

namespace SmallFields
open Multiset
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Absolute difference of natural multiplicities. -/
def gap (a b : ℕ) := a-b+(b-a)

def formula3 (n₁ n₂ : ℕ) := min n₁ n₂ + gap n₁ n₂ / 3

/-- Arguments are in residue order 1,2,3,4. Opposite residual signs require
    exchanging the two types to normalize them to a unit multiple of (1,2). -/
def formula5 (n₁ n₂ n₃ n₄ : ℕ) :=
  let a := gap n₁ n₄
  let b := gap n₂ n₃
  min n₁ n₄ + min n₂ n₃ + if (n₄ ≤ n₁ ↔ n₃ ≤ n₂) then fiveResidual a b else fiveResidual b a

private theorem repr3 (m : Multiset (ZMod 3)) (hn : 0 ∉ m) :
    m = two 1 (-1) (m.count 1) (m.count (-1)) := by
  apply Multiset.ext.mpr
  intro v
  have cases3 : ∀ z : ZMod 3, z=0 ∨ z=1 ∨ z= -1 := by decide
  rcases cases3 v with rfl|rfl|rfl <;>
    simp +decide [two,count_replicate,count_eq_zero.mpr hn]

private theorem repr5 (m : Multiset (ZMod 5)) (hn : 0 ∉ m) :
    m = two 1 (-1) (m.count 1) (m.count (-1)) + two 2 (-2) (m.count 2) (m.count (-2)) := by
  apply Multiset.ext.mpr
  intro v
  have cases5 : ∀ z : ZMod 5, z=0 ∨ z=1 ∨ z= -1 ∨ z=2 ∨ z= -2 := by decide
  rcases cases5 v with rfl|rfl|rfl|rfl|rfl <;>
    simp +decide [two,count_replicate,count_eq_zero.mpr hn]

theorem three_of_counts (a b : ℕ) (hz : (two (1 : ZMod 3) (-1) a b).sum = 0) :
    Z (two (1 : ZMod 3) (-1) a b) = formula3 a b := by
  let x : ZMod 3 := if b ≤ a then 1 else -1
  let d := gap a b
  have hx : x ≠ 0 := by dsimp [x]; split <;> decide
  have eq : two (1 : ZMod 3) (-1) a b = pairs 1 (min a b)+replicate d x := peel _ _ _
  rw [eq] at hz ⊢
  simp only [sum_add,pairs_sum,zero_add] at hz
  rw [Z_add_pairs _ hz _ (by decide)]
  have hs : (two x (x*0) d 0).sum = 0 := by simpa only [two,replicate_zero,add_zero] using hz
  obtain ⟨h1,he⟩ := normalize_two (F := ZMod 3) hx 0 d 0 hs
  simp only [two,replicate_zero,add_zero] at h1 he
  rw [he,three_ones d h1]
  rfl

private theorem scaled_five (u v : ZMod 5) (hu : u ≠ 0) (hv : v = u*2) (a b : ℕ)
    (hz : (two u v a b).sum = 0) : Z (two u v a b) = fiveResidual a b := by
  subst v
  obtain ⟨hs,he⟩ := normalize_two (F := ZMod 5) hu 2 a b hz
  exact he.trans (five_ones_twos a b hs)

private theorem reverse_five (u v : ZMod 5) (hv : v ≠ 0) (hu : u = v*2) (a b : ℕ)
    (hz : (two u v a b).sum = 0) : Z (two u v a b) = fiveResidual b a := by
  have swap : two u v a b = two v u b a := add_comm ..
  rw [swap] at hz ⊢
  exact scaled_five v u hv hu b a hz

theorem five_of_counts (n₁ n₂ n₃ n₄ : ℕ)
    (hz : (two (1 : ZMod 5) (-1) n₁ n₄ + two 2 (-2) n₂ n₃).sum = 0) :
    Z (two (1 : ZMod 5) (-1) n₁ n₄ + two 2 (-2) n₂ n₃) = formula5 n₁ n₂ n₃ n₄ := by
  let a := gap n₁ n₄
  let b := gap n₂ n₃
  let u : ZMod 5 := if n₄ ≤ n₁ then 1 else -1
  let v : ZMod 5 := if n₃ ≤ n₂ then 2 else -2
  let r := two u v a b
  have eq : two (1 : ZMod 5) (-1) n₁ n₄ + two 2 (-2) n₂ n₃ =
      pairs 1 (min n₁ n₄) + (pairs 2 (min n₂ n₃) + r) := by
    rw [peel,peel]
    unfold r two u v a b gap
    ac_rfl
  rw [eq] at hz ⊢
  simp only [sum_add,pairs_sum,zero_add] at hz
  rw [Z_add_pairs _ (by simp [hz]) _ (by decide),Z_add_pairs _ hz _ (by decide)]
  change _+(_+Z (two u v a b)) = _+_+(if _ then fiveResidual a b else fiveResidual b a)
  rw [← Nat.add_assoc]
  apply congrArg (min n₁ n₄ + min n₂ n₃ + ·)
  change (two u v a b).sum = 0 at hz
  by_cases h : n₄ ≤ n₁ <;> by_cases j : n₃ ≤ n₂ <;> simp only [u,v,h,j,iff_self,iff_false,
    iff_true,not_true_eq_false,if_true,if_false] at hz ⊢
  · exact scaled_five _ _ (by decide) (by decide) _ _ hz
  · exact reverse_five _ _ (by decide) (by decide) _ _ hz
  · exact reverse_five _ _ (by decide) (by decide) _ _ hz
  · exact scaled_five _ _ (by decide) (by decide) _ _ hz

theorem Z_three (m : Multiset (ZMod 3)) (hn : 0 ∉ m) (hs : m.sum = 0) :
    Z m = formula3 (m.count 1) (m.count 2) := by
  have he := repr3 m hn
  have hz := congrArg Multiset.sum he.symm
  exact (congrArg Z he).trans (three_of_counts _ _ (hz.trans hs))

theorem Z_five (m : Multiset (ZMod 5)) (hn : 0 ∉ m) (hs : m.sum = 0) :
    Z m = formula5 (m.count 1) (m.count 2) (m.count 3) (m.count 4) := by
  have he := repr5 m hn
  have hz := congrArg Multiset.sum he.symm
  exact (congrArg Z he).trans (five_of_counts _ _ _ _ (hz.trans hs))

end SmallFields
