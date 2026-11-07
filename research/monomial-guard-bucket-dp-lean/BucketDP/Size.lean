import BucketDP.Recover
import StrideDP.Dense
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BucketDP
open CountDP StrideDP
variable {I V W : Type*}
section
variable [DecidableEq I] [DecidableEq V]

/-- Every original occurrence occupies exactly one queue node. -/
theorem sum_capacities (y : I → V) (ks : List I) (hn : ks.Nodup) :
    ((alphabet y ks).map (capacity y ks)).sum = ks.length := by
  have h (v : V) : capacity y ks v = (ks.map y).count v := by
    rw [capacity,histogram,List.toFinset_val,List.dedup_eq_self.mpr hn,Multiset.map_coe,Multiset.coe_count]
  rw [← List.sum_toFinset _ (show (alphabet y ks).Nodup from List.nodup_dedup _)]
  have he : (alphabet y ks).toFinset = (ks.map y).toFinset := by ext v; simp [alphabet]
  rw [he]
  simpa only [h,List.length_map] using List.sum_toFinset_count_eq_length (ks.map y)

theorem dir_nodes (e : Equality V) (y : I → V) (ks : List I) (hn : ks.Nodup) (xs : List V) (s : ℕ) :
    ((directory e (records y ks) xs s).map (fun h => h.2.length)).sum = (xs.map (capacity y ks)).sum := by
  induction xs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [directory,collect_count e y ks hn,ih]

end

/-- This pays for deterministic comparison-based identification and bucket construction:
    even a very unbalanced observed alphabet has H(t+1) ≤ 2N−2. -/
theorem box_bounds (xs : List V) (n : V → ℕ) (pos : ∀ v ∈ xs, 0 < n v) :
    1+(xs.map n).sum ≤ slots n xs ∧ 1+xs.length ≤ slots n xs ∧
    2+(1+xs.length)*(xs.map n).sum ≤ 2*slots n xs := by
  induction xs with
  | nil => simp [slots]
  | cons x xs ih =>
    obtain ⟨hH,hT,hP⟩ := ih (fun v hv => pos v (List.mem_cons_of_mem _ hv))
    have hx := pos x List.mem_cons_self
    have h1 := Nat.mul_le_mul_left (n x) hH
    have h2 := Nat.mul_le_mul_left (n x) hT
    have h3 := Nat.le_mul_of_pos_left (xs.map n).sum hx
    have h4 := Nat.le_mul_of_pos_left (slots n xs) hx
    simp only [List.map_cons,List.sum_cons,List.length_cons,slots]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at h1 h2 hP ⊢
    have h2' : xs.length*n x = n x*xs.length := Nat.mul_comm _ _
    omega

def bucketVisits (e : Equality V) (rs : List (I × V)) (xs : List V) : ℕ :=
  (xs.map (fun v => (scanBucket e v rs).2)).sum

theorem bucketVisits_eq (e : Equality V) (rs : List (I × V)) (xs : List V) :
    bucketVisits e rs xs = xs.length * rs.length := by
  induction xs with
  | nil => simp [bucketVisits]
  | cons v vs ih => simp [bucketVisits,scanBucket_visits,Nat.succ_mul,Nat.add_comm] at ih ⊢

theorem jumps_length [AddCommGroup V] [DecidableEq V] (A : Arithmetic V W) (a : Array (Cell V W)) (j k : ℕ) :
    (jumps A a j k).length ≤ j := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    simp only [jumps]
    split
    · simp
    · exact Nat.succ_le_succ (ih _)

theorem pop_length (a : Array (List I)) (ds : List (ℕ × Bool)) : (popPath a ds).length ≤ ds.length := by
  induction ds generalizing a with
  | nil => rfl
  | cons p ds ih =>
    cases p
    simp only [popPath,List.length_cons]
    split
    · simp
    · exact Nat.succ_le_succ (ih _)

theorem split_length (p : Path I) : (splitPath p).2.flatten.length ≤ p.length := by
  have h := congrArg List.length (split_join p)
  simp only [List.length_append,List.length_map] at h
  omega

theorem dense_table_words {F : Type*} [AddCommGroup F] [DecidableEq F]
    (axes : List (Axis (Fin d → F))) (N : ℕ) :
    tableWords (dense F d) (fill (dense F d) axes N).cells = 3+(10+3*d)*N := by
  let A := dense F d
  have h (ls : List (Cell (Fin d → F) (Packed F d))) :
      (ls.map (fun c => 9+A.payloadWords c.total)).sum = (10+3*d)*ls.length := by
    induction ls with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,ih]
      change 9+(1+3*c.total.val.length)+_ = _
      rw [c.total.property]; omega
  rw [tableWords,h,Array.length_toList,fill_eq_built,built_size]

end BucketDP
