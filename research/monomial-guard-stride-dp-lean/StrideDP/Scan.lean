import StrideDP.Grid
import StrideDP.Machine

namespace StrideDP
open CountDP
variable {V W : Type*}

def choose (mk : V → Candidate V W) : List V → Option (Candidate V W)
  | [] => none
  | x::xs => prefer (mk x) (choose mk xs)

theorem choose_pick (mk : V → Candidate V W) (f : V → ℕ) (x : V) (xs : List V)
    (scores : ∀ v ∈ x::xs, (mk v).cell.entry.score = f v) :
    choose mk (x::xs) = some (mk (GuardDP.pick f x xs)) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    let z := GuardDP.pick f y ys
    have hm : z ∈ y::ys := (GuardDP.pick_spec f y ys).1
    have ht := ih y (fun v hv => scores v (List.mem_cons_of_mem _ hv))
    change prefer (mk x) (choose mk (y::ys)) = _
    rw [ht]
    simp only [prefer, scores x List.mem_cons_self, scores (GuardDP.pick f y ys) (List.mem_cons_of_mem _ hm), GuardDP.pick]
    split <;> rfl

variable [DecidableEq V]

/-- At a canonical address the scan agrees with choosing from the present types in alphabet order. -/
theorem scan_choose (get : ℕ → Cell V W) (k : ℕ) (n : V → ℕ) (m : Multiset V)
    (p : V → ℕ) (xs : List V) (s : ℕ) (hd : xs.Nodup)
    (hb : ∀ v ∈ xs, m.count v ≤ n v)
    (hp : ∀ v ∈ xs, v ∈ m → k - s * stride n v xs = p v) :
    (scan get k (layout n xs s) (address n xs m)).winner =
      choose (fun v => ⟨v, p v, get (p v)⟩) (xs.filter (· ∈ m)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    let b := n v + 1
    have hs : m.count v < b := Nat.lt_succ_of_le (hb v List.mem_cons_self)
    have hmod : address n (v::vs) m % b = m.count v := by
      simp [address, b, Nat.mod_eq_of_lt hs]
    have hdiv : address n (v::vs) m / b = address n vs m := by
      simp [address, b, Nat.add_mul_div_left, Nat.div_eq_of_lt hs]
    have off (w : V) (hw : w ∈ vs) (hm : w ∈ m) : k - s*b*stride n w vs = p w := by
      have hne : w ≠ v := fun e => hv (e ▸ hw)
      simpa [stride, hne, b, Nat.mul_assoc] using hp w (List.mem_cons_of_mem _ hw) hm
    have ht := ih (s*b) hvs (fun w hw => hb w (List.mem_cons_of_mem _ hw)) off
    simp only [layout, scan]
    dsimp only [b] at hmod hdiv ht
    rw [hmod]
    by_cases hm : v ∈ m
    · have hn := Multiset.count_pos.mpr hm
      have haddr : k - s = p v := by simpa [stride] using hp v List.mem_cons_self hm
      simp only [if_neg (Nat.ne_of_gt hn), hdiv, ht, haddr, List.filter_cons,
        decide_eq_true hm, if_true, choose]
    · have hn : m.count v = 0 := Multiset.count_eq_zero.mpr hm
      simp only [hn, if_true, hdiv, ht, List.filter_cons, decide_eq_false hm, Bool.false_eq_true, if_false]

end StrideDP
