import GuardDP.Correctness
import Mathlib.Data.Multiset.Replicate

open Finset
namespace CountDP
variable {I V : Type*}

/-- Sparse count vector. Its coordinate at v is the number of labels with charge v. -/
def histogram (y : I → V) (S : Finset I) : Multiset V := S.val.map y

@[simp] theorem mem_histogram {y : I → V} {S : Finset I} {v : V} :
    v ∈ histogram y S ↔ ∃ i ∈ S, y i = v := Multiset.mem_map

@[simp] theorem histogram_empty (y : I → V) : histogram y ∅ = 0 := rfl

@[simp] theorem histogram_card (y : I → V) (S : Finset I) : (histogram y S).card = S.card :=
  Multiset.card_map _ _

theorem histogram_erase [DecidableEq V] [DecidableEq I] (y : I → V) (S : Finset I) {i : I} (hi : i ∈ S) :
    histogram y (S.erase i) = (histogram y S).erase (y i) := by
  have h : histogram y S = y i ::ₘ histogram y (S.erase i) := by
    change S.val.map y = y i ::ₘ (S.erase i).val.map y
    rw [← Multiset.map_cons, erase_val, Multiset.cons_erase hi]
  rw [h, Multiset.erase_cons_head]

theorem histogram_sum [AddCommGroup V] (y : I → V) (S : Finset I) :
    (histogram y S).sum = ∑ i ∈ S, y i := rfl

variable [DecidableEq V]

/-- Each digit uses exactly n(v)+1 values, including zero. -/
def slots (n : V → ℕ) : List V → ℕ
  | [] => 1
  | v :: vs => (n v + 1) * slots n vs

def address (n : V → ℕ) : List V → Multiset V → ℕ
  | [], _ => 0
  | v :: vs, m => m.count v + (n v + 1) * address n vs m

def unpack (n : V → ℕ) : List V → ℕ → Multiset V
  | [], _ => 0
  | v :: vs, k =>
    Multiset.replicate (k % (n v + 1)) v + unpack n vs (k / (n v + 1))

structure Fits (types : List V) (n : V → ℕ) (m : Multiset V) : Prop where
  support : ∀ v ∈ m, v ∈ types
  bounded : ∀ v ∈ types, m.count v ≤ n v

theorem slots_eq_prod (types : List V) (n : V → ℕ) (hd : types.Nodup) :
    slots n types = ∏ v ∈ types.toFinset, (n v + 1) := by
  induction types with
  | nil => simp [slots]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    simp [slots, hv, ih hvs]

theorem address_lt_slots (types : List V) (n : V → ℕ) (m : Multiset V)
    (hb : ∀ v ∈ types, m.count v ≤ n v) : address n types m < slots n types := by
  induction types with
  | nil => exact Nat.zero_lt_one
  | cons v vs ih =>
    have hv := hb v List.mem_cons_self
    have htail := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    calc
      _ < (n v + 1) + (n v + 1) * address n vs m := Nat.add_lt_add_right (by omega) _
      _ = (n v + 1) * (address n vs m + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ slots n (v :: vs) := Nat.mul_le_mul_left _ htail

private theorem count_unpack_address (types : List V) (n : V → ℕ) (m : Multiset V)
    (hd : types.Nodup) (hb : ∀ v ∈ types, m.count v ≤ n v) (w : V) :
    (unpack n types (address n types m)).count w = if w ∈ types then m.count w else 0 := by
  induction types with
  | nil => simp [unpack]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    have hsmall : m.count v < n v + 1 := Nat.lt_succ_of_le (hb v List.mem_cons_self)
    have hmod : (m.count v + (n v + 1) * address n vs m) % (n v + 1) = m.count v := by
      simp [Nat.mod_eq_of_lt hsmall]
    have hdiv : (m.count v + (n v + 1) * address n vs m) / (n v + 1) = address n vs m := by
      simp [Nat.add_mul_div_left, Nat.div_eq_of_lt hsmall]
    rw [address, unpack, hmod, hdiv, Multiset.count_add, ih hvs (fun a ha => hb a (List.mem_cons_of_mem _ ha))]
    by_cases h : w = v
    · subst w
      simp [hv]
    · simp [Multiset.count_replicate, h, Ne.symm h]

theorem unpack_address (types : List V) (n : V → ℕ) (m : Multiset V) (hd : types.Nodup)
    (hf : Fits types n m) : unpack n types (address n types m) = m := by
  ext v
  rw [count_unpack_address types n m hd hf.bounded]
  by_cases hv : v ∈ types
  · simp [hv]
  · have hm : v ∉ m := fun h => hv (hf.support v h)
    simp [hv, hm]

theorem address_injective_on_box {types : List V} {n : V → ℕ} (hd : types.Nodup)
    {a b : Multiset V} (ha : Fits types n a) (hb : Fits types n b)
    (he : address n types a = address n types b) : a = b :=
  (unpack_address _ _ _ hd ha).symm.trans ((congrArg (unpack n types) he).trans (unpack_address _ _ _ hd hb))

theorem Fits.erase {types : List V} {n : V → ℕ} {m : Multiset V} (hf : Fits types n m) (v : V) :
    Fits types n (m.erase v) :=
  ⟨fun w hw => hf.support w (Multiset.mem_of_mem_erase hw),
   fun w hw => (Multiset.count_le_of_le w (Multiset.erase_le v m)).trans (hf.bounded w hw)⟩

private theorem address_erase_le (types : List V) (n : V → ℕ) (m : Multiset V) (v : V) :
    address n types (m.erase v) ≤ address n types m := by
  induction types with
  | nil => rfl
  | cons w ws ih =>
    exact Nat.add_le_add (Multiset.count_le_of_le w (Multiset.erase_le v m)) (Nat.mul_le_mul_left _ ih)

theorem address_erase_lt (types : List V) (n : V → ℕ) (m : Multiset V) {v : V}
    (hm : v ∈ m) (ht : v ∈ types) : address n types (m.erase v) < address n types m := by
  induction types with
  | nil => simp at ht
  | cons w ws ih =>
    rcases List.mem_cons.mp ht with rfl | hv
    · have hpos := Multiset.count_pos.mpr hm
      apply Nat.add_lt_add_of_lt_of_le _ (Nat.mul_le_mul_left _ (address_erase_le ws n m v))
      rw [Multiset.count_erase_self]
      omega
    · exact Nat.add_lt_add_of_le_of_lt (Multiset.count_le_of_le w (Multiset.erase_le v m))
        (Nat.mul_lt_mul_of_pos_left (ih hv) (Nat.succ_pos _))

end CountDP
