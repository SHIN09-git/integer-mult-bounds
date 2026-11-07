import SmallFields.Blocks

namespace SmallFields
open Multiset
variable {V : Type*} [AddCommGroup V]

def pair (x : V) : Multiset V := x ::ₘ -x ::ₘ 0

theorem remove_inverse {m : Multiset V} {x : V} (hx : x ≠ 0) {k : ℕ}
    (p : Blocks (x ::ₘ -x ::ₘ m) k) : ∃ j, Blocks m j ∧ k ≤ j+1 := by
  classical
  obtain ⟨b,r,n,hxB,hb,pr,he,hk⟩ := p.pick (Multiset.mem_cons_self ..)
  obtain ⟨b',rfl⟩ := Multiset.exists_cons_of_mem hxB
  rw [Multiset.cons_add,Multiset.cons_inj_right] at he
  rw [Multiset.sum_cons] at hb
  by_cases hn : -x ∈ b'
  · obtain ⟨u,rfl⟩ := Multiset.exists_cons_of_mem hn
    rw [Multiset.cons_add,Multiset.cons_inj_right] at he
    rw [Multiset.sum_cons,← add_assoc,add_neg_cancel,zero_add] at hb
    by_cases hu : u = 0
    · rw [hu,zero_add] at he
      exact ⟨n,he ▸ pr,by omega⟩
    · exact ⟨n+1,he ▸ Blocks.join hu hb pr,by omega⟩
  · have hmem : -x ∈ b'+r := he ▸ Multiset.mem_cons_self ..
    obtain ⟨c,s,l,hc,hz,ps,er,en⟩ := pr.pick ((Multiset.mem_add.mp hmem).resolve_left hn)
    obtain ⟨c',rfl⟩ := Multiset.exists_cons_of_mem hc
    rw [er,Multiset.cons_add,Multiset.add_cons,Multiset.cons_inj_right,← add_assoc] at he
    have hneq : b'+c' ≠ 0 := by
      intro eq
      have eb : b' = 0 := by
        have ec := congrArg Multiset.card eq
        rw [Multiset.card_add,Multiset.card_zero] at ec
        exact Multiset.card_eq_zero.mp (by omega)
      exact hx (by simpa [eb] using hb)
    have hs : (b'+c').sum = 0 := by
      rw [Multiset.sum_add]
      rw [Multiset.sum_cons] at hz
      calc
        _ = (x+b'.sum)+(-x+c'.sum) := by abel
        _ = 0 := by rw [hb,hz,zero_add]
    exact ⟨l+1,he ▸ Blocks.join hneq hs ps,by omega⟩

/-- Existing blocks may be rearranged, but two new opposite occurrences
    increase the maximum by exactly one, also in characteristic two. -/
theorem Z_add_inverse (m : Multiset V) (hm : m.sum = 0) (x : V) (hx : x ≠ 0) :
    Z (pair x+m) = Z m+1 := by
  have ez : (pair x+m).sum = 0 := by simp [pair,hm]
  have eq : pair x+m = x ::ₘ -x ::ₘ m := by simp [pair]
  have full : Blocks (x ::ₘ -x ::ₘ m) (Z (pair x+m)) := by rw [← eq]; exact attaining _ ez
  obtain ⟨j,p,h⟩ := remove_inverse hx full
  exact le_antisymm (by have := p.le_Z; omega)
    (Blocks.join (b := pair x) (by simp [pair]) (by simp [pair]) (attaining m hm)).le_Z

def pairs (x : V) (n : ℕ) := replicate n x + replicate n (-x)

@[simp] theorem pairs_sum (x : V) (n : ℕ) : (pairs x n).sum = 0 := by simp [pairs]

theorem Z_add_pairs (m : Multiset V) (hm : m.sum = 0) (x : V) (hx : x ≠ 0) (n : ℕ) :
    Z (pairs x n+m) = n+Z m := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    have eq : pairs x (n+1)+m = pair x+(pairs x n+m) := by
      simp [pairs,pair,Multiset.replicate_succ,Multiset.cons_swap]
    rw [eq,Z_add_inverse _ (by simp [hm]) _ hx,ih]; omega

def two (u v : V) (a b : ℕ) := replicate a u + replicate b v

/-- Cancel all opposite pairs of a given type, preserving the residual sign. -/
theorem peel (x : V) (a b : ℕ) : two x (-x) a b =
    pairs x (min a b) + replicate (a-b+(b-a)) (if b ≤ a then x else -x) := by
  by_cases h : b ≤ a
  · rw [if_pos h,min_eq_right h,Nat.sub_eq_zero_of_le h,Nat.add_zero]
    unfold two pairs
    conv_lhs => rw [show a = b+(a-b) by omega,Multiset.replicate_add]
    ac_rfl
  · have le : a ≤ b := by omega
    rw [if_neg h,min_eq_left le,Nat.sub_eq_zero_of_le le,Nat.zero_add]
    unfold two pairs
    conv_lhs => rw [show b = a+(b-a) by omega,Multiset.replicate_add]
    ac_rfl

end SmallFields
