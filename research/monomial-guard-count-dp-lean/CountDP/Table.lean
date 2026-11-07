import CountDP.Address

namespace CountDP
variable {V : Type*} [DecidableEq V] [AddCommGroup V]

/-- A table cell stores a score, one winning charge type, and a zero-sum boundary. -/
structure Entry (V : Type*) where
  score : ℕ
  parent : Option V
  cut : Bool
  deriving Repr, DecidableEq

def emptyEntry : Entry V := ⟨0, none, false⟩

def bonus (m : Multiset V) : ℕ := if m.sum = 0 then 1 else 0

def next (types : List V) (value : Multiset V → ℕ) (m : Multiset V) : Entry V :=
  match types.filter (· ∈ m) with
  | [] => emptyEntry
  | v :: vs =>
    let w := GuardDP.pick (fun u => value (m.erase u)) v vs
    ⟨value (m.erase w) + bonus m, some w, decide (m.sum = 0)⟩

def readAt (a : Array (Entry V)) (k : ℕ) : Entry V := a[k]?.getD emptyEntry

/-- Fill one array, in mixed-radix order. All decremented vectors occur earlier. -/
def rows (types : List V) (n : V → ℕ) : ℕ → Array (Entry V)
  | 0 => #[]
  | k + 1 =>
    let a := rows types n k
    let e := next types (fun m => (readAt a (address n types m)).score) (unpack n types k)
    a.push e

def table (types : List V) (n : V → ℕ) : Array (Entry V) := rows types n (slots n types)

def lookup (types : List V) (n : V → ℕ) (a : Array (Entry V)) (m : Multiset V) : Entry V :=
  readAt a (address n types m)

theorem rows_size (types : List V) (n : V → ℕ) (k : ℕ) : (rows types n k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rows, ih]

theorem table_cells (types : List V) (n : V → ℕ) (hd : types.Nodup) :
    (table types n).size = ∏ v ∈ types.toFinset, (n v + 1) := by
  rw [table, rows_size, slots_eq_prod types n hd]

private theorem earlier_row (types : List V) (n : V → ℕ) {i j k : ℕ} (hi : i < j) (hj : j ≤ k) :
    readAt (rows types n k) i = readAt (rows types n j) i := by
  induction k, hj using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    have hne : i ≠ k := by omega
    simpa only [rows, readAt, Array.getElem?_push, rows_size, if_neg hne] using ih

private theorem read_row (types : List V) (n : V → ℕ) {k : ℕ} (hk : k < slots n types) :
    readAt (table types n) k =
      next types (fun m => (lookup types n (rows types n k) m).score) (unpack n types k) := by
  rw [table, earlier_row types n (Nat.lt_succ_self k) hk]
  simp only [rows, readAt, Array.getElem?_push, rows_size, if_true, Option.getD_some, lookup]

/-- Characterization of the winning predecessor and of every permitted competing deletion. -/
def BestAt (value : Multiset V → ℕ) (m : Multiset V) (e : Entry V) : Prop :=
  if m = 0 then e = emptyEntry else
    ∃ v ∈ m, e.parent = some v ∧ e.cut = decide (m.sum = 0) ∧
      e.score = value (m.erase v) + bonus m ∧
      ∀ w ∈ m, value (m.erase w) ≤ value (m.erase v)

theorem next_best (types : List V) (value : Multiset V → ℕ) (m : Multiset V)
    (hs : ∀ v ∈ m, v ∈ types) : BestAt value m (next types value m) := by
  by_cases h : m = 0
  · subst m
    simp [BestAt, next]
  rw [BestAt, if_neg h]
  have hm (w : V) : w ∈ types.filter (· ∈ m) ↔ w ∈ m := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hw => ⟨hs w hw, hw⟩⟩
  cases he : types.filter (· ∈ m) with
  | nil =>
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero h
    simpa [he] using (hm v).mpr hv
  | cons v vs =>
    let f := fun w => value (m.erase w)
    obtain ⟨hp, hbest⟩ := GuardDP.pick_spec f v vs
    refine ⟨GuardDP.pick f v vs, (hm _).mp (he ▸ hp), ?_, ?_, ?_, ?_⟩
    · simp [next, he, f]
    · simp [next, he]
    · simp [next, he, f]
    · exact fun w hw => hbest w (he ▸ (hm w).mpr hw)

theorem table_best (types : List V) (n : V → ℕ) (hd : types.Nodup) (m : Multiset V)
    (hf : Fits types n m) :
    let get := lookup types n (table types n)
    BestAt (fun p => (get p).score) m (get m) := by
  let k := address n types m
  have hk : k < slots n types := address_lt_slots _ _ _ hf.bounded
  let prev := lookup types n (rows types n k)
  have hr : lookup types n (table types n) m = next types (fun p => (prev p).score) m := by
    change readAt (table types n) k = _
    rw [read_row types n hk, show unpack n types k = m from unpack_address _ _ _ hd hf]
  have same (w : V) (hw : w ∈ m) :
      lookup types n (table types n) (m.erase w) = prev (m.erase w) :=
    earlier_row types n (address_erase_lt types n m hw (hf.support w hw)) hk.le
  have best := next_best types (fun p => (prev p).score) m hf.support
  dsimp only
  rw [hr]
  by_cases he : m = 0
  · simpa only [BestAt, if_pos he] using best
  · rw [BestAt, if_neg he] at best ⊢
    obtain ⟨v, hv, hp, hc, hs, hb⟩ := best
    refine ⟨v, hv, hp, hc, ?_, ?_⟩
    · rw [same v hv, hs]
    · intro w hw
      rw [same w hw, same v hv]
      exact hb w hw

end CountDP
