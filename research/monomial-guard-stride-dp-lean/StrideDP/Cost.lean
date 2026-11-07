import StrideDP.Machine
import StrideDP.Edges

namespace StrideDP
open CountDP Finset
variable {V W : Type*}

theorem scan_reads (get : ℕ → Cell V W) (k : ℕ) (n : V → ℕ) (xs : List V) (s q : ℕ) :
    (scan get k (layout n xs s) q).reads = legalDigits n xs q := by
  induction xs generalizing s q with
  | nil => rfl
  | cons v vs ih =>
    simp only [layout, scan, legalDigits]
    split <;> simp [ih]

/-- Exact control charge: six words of work per digit, ten more for a positive digit. -/
theorem scan_ticks (get : ℕ → Cell V W) (k : ℕ) (axes : List (Axis V)) (q : ℕ) :
    (scan get k axes q).ticks = 1 + 6*axes.length + 10*(scan get k axes q).reads := by
  induction axes generalizing q with
  | nil => rfl
  | cons a tail ih =>
    have := ih (q/a.radix)
    simp only [scan, List.length_cons]
    split <;> dsimp only <;> omega

theorem scan_bound (get : ℕ → Cell V W) (k : ℕ) (axes : List (Axis V)) (q : ℕ) :
    (scan get k axes q).ticks ≤ 1 + 16*axes.length := by
  induction axes generalizing q with
  | nil => rfl
  | cons a tail ih =>
    have := ih (q/a.radix)
    simp only [scan, List.length_cons]
    split <;> dsimp only <;> omega

variable [AddCommGroup V] [DecidableEq V]

theorem reads_prefix (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (N j : ℕ) :
    (built A (layout n xs 1) N j).reads = ∑ k ∈ range j, legalDigits n xs k := by
  induction j with
  | zero => simp [built, initial]
  | succ j ih => simp only [built, step, built_size, scan_reads, sum_range_succ, ih]

theorem legal_predecessor_total (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup) :
    (fill A (layout n xs 1) (slots n xs)).reads =
      ∑ v ∈ xs.toFinset, n v * ∏ w ∈ xs.toFinset.erase v, (n w + 1) := by
  rw [fill_eq_built, reads_prefix, sum_legalDigits, edges_formula n xs hd]

theorem finish_bound (A : Arithmetic V W) {d : ℕ} (h : WordCosts A d) (w : Option (Candidate V W)) :
    (finish A w).2 ≤ 24 + 15*d := by
  cases w with
  | none => change 3 ≤ _; omega
  | some w =>
    have ha := h.add w.key w.cell.total
    have ht := h.test (A.addType w.key w.cell.total).1
    simp only [finish]
    omega

theorem ticks_prefix (A : Arithmetic V W) {d : ℕ} (h : WordCosts A d) (axes : List (Axis V))
    (N j : ℕ) : (built A axes N j).ticks ≤ N + A.initWork + 3 + j*(33+16*axes.length+15*d) := by
  induction j with
  | zero => simp [built, initial]
  | succ j ih =>
    let r := built A axes N j
    have hs := scan_bound (read A r.cells) r.cells.size axes r.cells.size
    have hf := finish_bound A h (scan (read A r.cells) r.cells.size axes r.cells.size).winner
    change r.ticks + _ + _ + 8 ≤ _
    change r.ticks ≤ _ at ih
    rw [Nat.succ_mul]
    dsimp only [r] at hs hf ih ⊢
    omega

theorem fill_time_bound (A : Arithmetic V W) {d : ℕ} (h : WordCosts A d) (axes : List (Axis V))
    (N : ℕ) (hp : 0 < N) : (fill A axes N).ticks ≤ 48 * ((1+axes.length+d)*N) := by
  rw [fill_eq_built]
  apply (ticks_prefix A h axes N N).trans
  let B := 1+axes.length+d
  have hB : 0 < B := by dsimp [B]; omega
  have hn : N ≤ B*N := Nat.le_mul_of_pos_left _ hB
  have hb : B ≤ B*N := Nat.le_mul_of_pos_right _ hp
  have hi : N + A.initWork + 3 ≤ 10*(B*N) := by
    have := h.init
    have : 1+d ≤ B := by dsimp [B]; omega
    omega
  have hc : 33+16*axes.length+15*d ≤ 33*B := by dsimp [B]; omega
  have hj : N*(33+16*axes.length+15*d) ≤ 33*(B*N) := by
    simpa only [Nat.mul_comm N _, Nat.mul_assoc] using Nat.mul_le_mul_left N hc
  change _ ≤ 48*(B*N)
  omega

/-- Array header and per-row words, including the slot, metadata, parent reference,
    and the entire packed charge payload. Shared payloads may be charged twice. -/
def tableWords (A : Arithmetic V W) (a : Array (Cell V W)) : ℕ :=
  3 + (a.toList.map (fun c => 9 + A.payloadWords c.total)).sum

private theorem list_words_le (A : Arithmetic V W) {d : ℕ} (h : WordCosts A d) (cs : List (Cell V W)) :
    (cs.map (fun c => 9 + A.payloadWords c.total)).sum ≤ (9+4*(1+d))*cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have := h.words c.total
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem fill_space_bound (A : Arithmetic V W) {d : ℕ} (h : WordCosts A d) (axes : List (Axis V))
    (N : ℕ) (hp : 0 < N) : tableWords A (fill A axes N).cells ≤ 16*((1+d)*N) := by
  rw [fill_eq_built]
  let a := (built A axes N N).cells
  have hl := list_words_le A h a.toList
  rw [Array.length_toList, show a.size = N from built_size ..] at hl
  have hc : 9+4*(1+d) ≤ 13*(1+d) := by omega
  have hu : (9+4*(1+d))*N ≤ 13*((1+d)*N) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right N hc
  have hp' : 0 < (1+d)*N := Nat.mul_pos (by omega) hp
  change 3 + (a.toList.map _).sum ≤ _
  omega

omit [AddCommGroup V] [DecidableEq V] in
theorem slots_pos (n : V → ℕ) (xs : List V) : 0 < slots n xs := by
  induction xs with
  | nil => exact Nat.zero_lt_one
  | cons _ _ ih => exact Nat.mul_pos (Nat.succ_pos _) ih

end StrideDP
