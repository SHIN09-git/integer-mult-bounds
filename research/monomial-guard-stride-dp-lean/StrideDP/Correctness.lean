import StrideDP.Scan
import CountDP.Score

namespace StrideDP
open CountDP
variable {V W : Type*} [AddCommGroup V] [DecidableEq V]

structure CellOK (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (m : Multiset V)
    (ref : Entry V) (c : Cell V W) : Prop where
  entry : c.entry = ref
  total : A.denote c.total = m.sum
  parent : ∀ v, c.entry.parent = some v → v ∈ m ∧ c.prev = address n xs (m.erase v)

theorem new_cell_ok (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (m : Multiset V) (hf : Fits xs n m) (get : ℕ → Cell V W) (ref : Multiset V → Entry V)
    (prev : ∀ v ∈ m, CellOK A xs n (m.erase v) (ref (m.erase v)) (get (address n xs (m.erase v)))) :
    let k := address n xs m
    CellOK A xs n m (next xs (fun b => (ref b).score) m)
      (finish A (scan get k (layout n xs 1) k).winner).1 := by
  let k := address n xs m
  let p := fun v => address n xs (m.erase v)
  let mk := fun v => (⟨v, p v, get (p v)⟩ : Candidate V W)
  let f := fun v => (ref (m.erase v)).score
  have off (v : V) (hv : v ∈ xs) (hm : v ∈ m) : k - 1 * stride n v xs = p v := by
    simpa [k, p] using (predecessor_address xs n m hd hv hm).symm
  have sc := scan_choose get k n m p xs 1 hd hf.bounded off
  change (scan get k (layout n xs 1) k).winner = choose mk (xs.filter (· ∈ m)) at sc
  dsimp only
  change CellOK _ _ _ _ _ (finish A (scan get k (layout n xs 1) k).winner).1
  rw [sc]
  cases he : xs.filter (· ∈ m) with
  | nil =>
    have hm : m = 0 := by
      by_contra hn
      obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hn
      have : v ∈ xs.filter (· ∈ m) := List.mem_filter.mpr ⟨hf.support v hv, decide_eq_true hv⟩
      simp [he] at this
    constructor
    · simp [next, he, choose, finish, blank]
    · simp [choose, finish, blank, A.zero_ok, hm]
    · simp [choose, finish, blank, emptyEntry]
  | cons x ys =>
    have mem (v : V) (h : v ∈ x::ys) : v ∈ m := by
      rw [← he] at h
      exact of_decide_eq_true (List.mem_filter.mp h).2
    let w := GuardDP.pick f x ys
    have hw : w ∈ m := mem w (GuardDP.pick_spec f x ys).1
    have hscore (v : V) (h : v ∈ x::ys) : (mk v).cell.entry.score = f v :=
      congrArg Entry.score (prev v (mem v h)).entry
    rw [choose_pick mk f x ys hscore]
    have hz : A.denote (A.addType w (get (p w)).total).1 = m.sum := by
      rw [A.add_ok, (prev w hw).total, ← Multiset.sum_cons, Multiset.cons_erase hw]
    have hb := (A.test_ok (A.addType w (get (p w)).total).1).trans (congrArg (fun z => decide (z=0)) hz)
    constructor
    · simp only [next, he, finish]
      change (⟨(get (p w)).entry.score + _, some w, _⟩ : Entry V) = ⟨f w + bonus m, some w, _⟩
      rw [show (get (p w)).entry.score = f w from congrArg Entry.score (prev w hw).entry]
      simp [mk, w, hb, bonus]
    · exact hz
    · intro v hv
      change some w = some v at hv
      obtain rfl := Option.some.inj hv
      exact ⟨hw, rfl⟩

theorem built_ok (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (N j : ℕ) (m : Multiset V) (hf : Fits xs n m) (hj : address n xs m < j) :
    CellOK A xs n m (readAt (rows xs n j) (address n xs m))
      (read A (built A (layout n xs 1) N j).cells (address n xs m)) := by
  induction j generalizing m with
  | zero => omega
  | succ j ih =>
    by_cases he : address n xs m = j
    · have hprev (v : V) (hv : v ∈ m) := ih (m.erase v) (hf.erase v)
        (he ▸ address_erase_lt xs n m hv (hf.support v hv))
      let r := built A (layout n xs 1) N j
      have hc := new_cell_ok A xs n hd m hf (read A r.cells)
        (fun b => readAt (rows xs n j) (address n xs b)) hprev
      have hu : unpack n xs j = m := he ▸ unpack_address xs n m hd hf
      simp only [built, step, read, rows, readAt, Array.getElem?_push, rows_size, built_size, he, if_true,
        Option.getD_some, hu]
      dsimp only at hc
      rw [he] at hc
      exact hc
    · have hsmall : address n xs m < j := by omega
      simpa only [built, step, read, rows, Array.getElem?_push, rows_size, built_size, readAt, if_neg he]
        using ih m hf hsmall

def runTable (A : Arithmetic V W) (xs : List V) (n : V → ℕ) :=
  fill A (layout n xs 1) (slots n xs)

theorem table_ok (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (m : Multiset V) (hf : Fits xs n m) :
    CellOK A xs n m (lookup xs n (table xs n) m)
      (read A (runTable A xs n).cells (address n xs m)) := by
  rw [runTable, fill_eq_built]
  exact built_ok A xs n hd _ _ m hf (address_lt_slots _ _ _ hf.bounded)

theorem cell_eq_D (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (k : ℕ) (hk : k < slots n xs) :
    (read A (runTable A xs n).cells k).entry.score = D xs n (unpack n xs k) := by
  have h := congrArg Entry.score (table_ok A xs n hd _ (unpack_fits xs n hd k)).entry
  rw [address_unpack xs n hd hk] at h
  exact h

end StrideDP
