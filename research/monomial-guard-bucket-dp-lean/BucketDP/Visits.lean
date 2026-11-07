import BucketDP.Raw
import BucketDP.Size

namespace BucketDP

variable {F I : Type*} [DecidableEq F] {d : ℕ}
abbrev Charge (F : Type*) (d : ℕ) := Fin d → F

/-- This counter follows the same coordinate-level early exits as denseEq. -/
def coords (v w : Charge F d) := (compareCoords v w (List.finRange d)).2

theorem coords_le (v w : Charge F d) : coords v w ≤ d := by
  simpa only [coords,List.length_finRange] using (compareCoords_spec v w (List.finRange d)).2

def probeCoords (v : Charge F d) : List (Charge F d) → ℕ
  | [] => 0
  | w::ws => coords v w + (if (denseEq F d).test v w then 0 else probeCoords v ws)

theorem probeCoords_le (v : Charge F d) (xs : List (Charge F d)) :
    probeCoords v xs ≤ d*(probe (denseEq F d) v xs).2 := by
  induction xs with
  | nil => simp [probeCoords,probe]
  | cons w xs ih =>
    have h := coords_le v w
    simp only [probeCoords,probe]
    split <;> simp only [Nat.mul_one,Nat.mul_add,Nat.add_zero] <;> omega

def identifyCoords : List (Charge F d) → ℕ
  | [] => 0
  | v::vs => identifyCoords vs + probeCoords v (identify (denseEq F d) vs).keys

theorem identifyCoords_le (vs : List (Charge F d)) :
    identifyCoords vs ≤ d*(identify (denseEq F d) vs).comparisons := by
  induction vs with
  | nil => simp [identifyCoords,identify]
  | cons v vs ih =>
    have h := probeCoords_le v (identify (denseEq F d) vs).keys
    simp only [identifyCoords,identify,Nat.mul_add]
    omega

def scanCoords (v : Charge F d) (rs : List (I × Charge F d)) := (rs.map (fun p => coords p.2 v)).sum
def bucketCoords (rs : List (I × Charge F d)) (xs : List (Charge F d)) := (xs.map (fun v => scanCoords v rs)).sum

theorem scanCoords_le (v : Charge F d) (rs : List (I × Charge F d)) :
    scanCoords v rs ≤ d*(scanBucket (denseEq F d) v rs).2 := by
  rw [scanBucket_visits]
  induction rs with
  | nil => simp [scanCoords]
  | cons p rs ih =>
    have h := coords_le p.2 v
    simp only [scanCoords,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ] at ih ⊢
    omega

theorem bucketCoords_le (rs : List (I × Charge F d)) (xs : List (Charge F d)) :
    bucketCoords rs xs ≤ d*bucketVisits (denseEq F d) rs xs := by
  induction xs with
  | nil => simp [bucketCoords,bucketVisits]
  | cons v xs ih =>
    have h := scanCoords_le v rs
    simp only [bucketCoords,bucketVisits,List.map_cons,List.sum_cons,Nat.mul_add] at ih ⊢
    omega

end BucketDP
