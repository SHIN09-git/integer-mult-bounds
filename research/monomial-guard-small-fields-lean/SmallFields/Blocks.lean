import CountDP.Address
import HZ.Partitions
import Mathlib.Data.Nat.Find

namespace SmallFields
open Multiset
variable {V : Type*} [AddCommGroup V]

/-- An exact cover of a multiset by k nonempty zero-sum blocks. -/
inductive Blocks : Multiset V → ℕ → Prop
  | empty : Blocks 0 0
  | join {b m : Multiset V} {k : ℕ} (nonempty : b ≠ 0) (zero : b.sum = 0)
      (tail : Blocks m k) : Blocks (b+m) (k+1)

theorem Blocks.card_bound {m : Multiset V} {k : ℕ} (h : Blocks m k) : k ≤ m.card := by
  induction h with
  | empty => rfl
  | join hb _ _ ih =>
    rw [card_add]
    have := Multiset.card_pos.mpr hb
    omega

theorem Blocks.total {m : Multiset V} {k : ℕ} (h : Blocks m k) : m.sum = 0 := by
  induction h with
  | empty => rfl
  | join _ hz _ ih => simp [hz,ih]

theorem Blocks.one {b : Multiset V} (hn : b ≠ 0) (hs : b.sum = 0) : Blocks b 1 := by
  simpa only [add_zero] using Blocks.join hn hs Blocks.empty

theorem Blocks.append {m n : Multiset V} {j k : ℕ} (hm : Blocks m j) (hn : Blocks n k) :
    Blocks (m+n) (j+k) := by
  induction hm with
  | empty => simpa using hn
  | join hb hz _ ih =>
    rw [add_assoc,Nat.succ_add]
    exact Blocks.join hb hz ih

noncomputable def Z (m : Multiset V) : ℕ := by
  classical exact Nat.findGreatest (Blocks m) m.card

theorem Blocks.le_Z {m : Multiset V} {k : ℕ} (h : Blocks m k) : k ≤ Z m := by
  classical exact Nat.le_findGreatest h.card_bound h

theorem attaining (m : Multiset V) (h : m.sum = 0) : Blocks m (Z m) := by
  classical
  have step {k : ℕ} (p : Blocks m k) : Blocks m (Z m) := Nat.findGreatest_spec p.card_bound p
  by_cases he : m = 0
  · subst m; exact step Blocks.empty
  · exact step (Blocks.one he h)

@[simp] theorem Z_empty : Z (0 : Multiset V) = 0 := by
  have := (attaining (0 : Multiset V) (by simp)).card_bound
  simpa using this

/-- Select one occurrence and expose the entire block containing it. -/
theorem Blocks.pick {m : Multiset V} {k : ℕ} (h : Blocks m k) {x : V} (hx : x ∈ m) :
    ∃ b r n, x ∈ b ∧ b.sum = 0 ∧ Blocks r n ∧ m = b+r ∧ k = n+1 := by
  induction h with
  | empty => simp at hx
  | @join b m k hb hz tail ih =>
    rcases Multiset.mem_add.mp hx with hxb|hxm
    · exact ⟨b,m,k,hxb,hz,tail,rfl,rfl⟩
    · obtain ⟨c,r,n,hc,hs,pr,em,ek⟩ := ih hxm
      refine ⟨c,b+r,n+1,hc,hs,Blocks.join hb hz pr,?_,by omega⟩
      rw [em]; ac_rfl

end SmallFields
