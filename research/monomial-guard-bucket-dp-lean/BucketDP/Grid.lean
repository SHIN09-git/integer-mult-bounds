import BucketDP.Queues
import BucketDP.Prepare
import StrideDP.Witness
import StrideDP.Cost

namespace BucketDP
open CountDP StrideDP Finset
variable {I V W : Type*} [DecidableEq V]

theorem stride_range (n : V → ℕ) (xs : List V) {v : V} (hv : v ∈ xs)
    (pos : ∀ w ∈ xs, 0 < n w) : 0 < stride n v xs ∧ stride n v xs < slots n xs := by
  induction xs with
  | nil => simp at hv
  | cons w ws ih =>
    have hw := pos w List.mem_cons_self
    have hs : 0 < slots n ws := StrideDP.slots_pos ..
    by_cases h : v = w
    · simp only [stride, if_pos h, slots]
      exact ⟨by decide, lt_of_lt_of_le (by omega : 1 < n w + 1) (Nat.le_mul_of_pos_right _ hs)⟩
    · obtain ⟨hp,hb⟩ := ih ((List.mem_cons.mp hv).resolve_left h) (fun a ha => pos a (List.mem_cons_of_mem _ ha))
      simp only [stride, if_neg h, slots]
      exact ⟨Nat.mul_pos (Nat.succ_pos _) hp, Nat.mul_lt_mul_of_pos_left hb (Nat.succ_pos _)⟩

theorem stride_unique (n : V → ℕ) (xs : List V) (pos : ∀ v ∈ xs, 0 < n v)
    (v : V) (hv : v ∈ xs) (w : V) (hw : w ∈ xs) (he : stride n v xs = stride n w xs) : v = w := by
  induction xs with
  | nil => simp at hv
  | cons a as ih =>
    have p := pos a List.mem_cons_self
    have tail := fun x (hx : x ∈ as) => pos x (List.mem_cons_of_mem _ hx)
    have gt (x : V) (hh : x ∈ a::as) (hx : x ≠ a) : 1 < (n a+1)*stride n x as :=
      lt_of_lt_of_le (by omega : 1 < n a+1) (Nat.le_mul_of_pos_right _
        (stride_range n as ((List.mem_cons.mp hh).resolve_left hx) tail).1)
    by_cases ha : v = a <;> by_cases hb : w = a
    · exact ha.trans hb.symm
    · have := gt w hw hb
      simp only [stride, if_pos ha, if_neg hb] at he
      omega
    · have := gt v hv ha
      simp only [stride, if_neg ha, if_pos hb] at he
      omega
    · simp only [stride, if_neg ha, if_neg hb, Nat.mul_right_inj (Nat.succ_ne_zero _)] at he
      exact ih tail ((List.mem_cons.mp hv).resolve_left ha) ((List.mem_cons.mp hw).resolve_left hb) he

variable [DecidableEq I]

theorem capacity_pos (y : I → V) (ks : List I) {w : V} (hw : w ∈ alphabet y ks) : 0 < capacity y ks w := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp (List.mem_dedup.mp hw)
  exact Multiset.count_pos.mpr (mem_histogram.mpr ⟨i,List.mem_toFinset.mpr hi,he⟩)

theorem find_stride (e : Equality V) (y : I → V) (ks : List I) (hn : ks.Nodup) (xs : List V)
    (s : ℕ) (hs : 0 < s) (pos : ∀ w ∈ xs, 0 < capacity y ks w) {v : V} (hv : v ∈ xs) :
    findQueue (s * stride (capacity y ks) v xs) (directory e (records y ks) xs s) =
      collect e (records y ks) v := by
  let n := capacity y ks
  induction xs generalizing s with
  | nil => simp at hv
  | cons a as ih =>
    by_cases h : v = a
    · subst v; simp [directory, stride, findQueue]
    · have hv' := (List.mem_cons.mp hv).resolve_left h
      have pt := fun w (hw : w ∈ as) => pos w (List.mem_cons_of_mem _ hw)
      have hg : 1 < (n a + 1)*stride n v as :=
        lt_of_lt_of_le (by have := pos a List.mem_cons_self; dsimp [n]; omega)
          (Nat.le_mul_of_pos_right _ (stride_range n as hv' pt).1)
      have ne : s * ((n a+1)*stride n v as) ≠ s := by
        have := Nat.mul_lt_mul_of_pos_left hg hs
        simpa using Nat.ne_of_gt this
      simp only [directory, stride, if_neg h, findQueue, collect_count e y ks hn]
      change (if s*((n a+1)*stride n v as) = s then _ else _) = _
      rw [if_neg ne, ← Nat.mul_assoc]
      exact ih (s*(n a+1)) (Nat.mul_pos hs (Nat.succ_pos _)) pt hv'

theorem queues_ready (e : Equality V) (y : I → V) (ks : List I) (hn : ks.Nodup) :
    let xs := alphabet y ks
    let n := capacity y ks
    Ready y ks xs (fun v => stride n v xs)
      (queues (directory e (records y ks) xs 1) (slots n xs)) ks.toFinset := by
  dsimp only
  intro v hv
  let n := capacity y ks
  let xs := alphabet y ks
  have pos (w : V) (hw : w ∈ xs) := capacity_pos y ks hw
  have hl : stride n v xs < slots n xs + 1 := Nat.lt_succ_of_lt (stride_range n xs hv pos).2
  have he := find_stride e y ks hn xs 1 Nat.zero_lt_one pos hv
  simp only [Nat.one_mul] at he
  change queueAt (queues _ _) (stride n v xs) = _
  rw [queueAt, queues_get _ _ _ hl]
  change findQueue (stride (capacity y ks) v xs) (directory e (records y ks) xs 1) = _
  rw [he, collect_records, waiting]
  apply List.filter_congr
  intro i hi
  simp [hi]

theorem full_address (n : V → ℕ) (xs : List V) (m : Multiset V) (h : ∀ v ∈ xs, m.count v = n v) :
    address n xs m + 1 = slots n xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    have ht := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [address, slots, h v List.mem_cons_self, ← ht, Nat.mul_succ]
    omega

end BucketDP
