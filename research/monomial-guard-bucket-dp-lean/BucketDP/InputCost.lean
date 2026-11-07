import BucketDP.EndToEnd

namespace BucketDP
open GuardDP
variable {K : Type*} [Field K] [DecidableEq K] {m d : ℕ}

/-- Charge the dense addition and new accumulator vector at each physical row.
    The tail call has one live accumulator, independent of the number of rows. -/
def countedSum (r : Raw K m d) (acc : Vector K d) : List (Fin m) → Vector K d × ℕ
  | [] => (acc,1)
  | i::is =>
    let tail := countedSum r (pack (acc.get + r.state.charge i)) is
    (tail.1,8+10*d+tail.2)

omit [DecidableEq K] in
theorem countedSum_spec (r : Raw K m d) (is : List (Fin m)) (acc : Vector K d) :
    (countedSum r acc is).1 = sumRows r acc is ∧ (countedSum r acc is).2 = 1+(8+10*d)*is.length := by
  induction is generalizing acc with
  | nil => simp [countedSum,sumRows]
  | cons i is ih =>
    obtain ⟨eq,cost⟩ := ih (pack (acc.get+r.state.charge i))
    constructor
    · exact eq
    · change 8+10*d+(countedSum r (pack (acc.get+r.state.charge i)) is).2 = _
      rw [cost,List.length_cons,Nat.mul_succ]
      omega

/-- Cost interpretation of the raw filter. The successful arm writes a record.
    The full index list and materialization are charged before coordinate comparisons. -/
def countedScan (r : Raw K m d) : List (Fin m) → List (Fin m × (Fin d → K)) × ℕ
  | [] => ([],1)
  | i::is =>
    let v := pack (r.state.charge i)
    let c := compareCoords v.get 0 (List.finRange d)
    let tail := countedScan r is
    let common := 8+10*d+5*c.2+tail.2
    if c.1 then (tail.1,common) else ((i,v.get)::tail.1,common+4)

theorem countedScan_spec (r : Raw K m d) (is : List (Fin m)) :
    (countedScan r is).1 = scanRaw r is ∧ (countedScan r is).2 ≤ 1+(12+15*d)*is.length := by
  induction is with
  | nil => simp [countedScan,scanRaw]
  | cons i is ih =>
    have cap : (compareCoords (pack (r.state.charge i)).get 0 (List.finRange d)).2 ≤ d := coords_le _ _
    obtain ⟨hv,sz⟩ := ih
    unfold scanRaw at hv
    by_cases h : (compareCoords (pack (r.state.charge i)).get 0 (List.finRange d)).1 = true <;>
      simp [countedScan,scanRaw,denseEq,h,hv,Nat.mul_succ] <;> omega

/-- Index-list construction, initial zero vector and final dense zero test. -/
def sumWork (r : Raw K m d) :=
  8+3*m+8*d+(countedSum r (Vector.replicate d 0) (List.finRange m)).2+4*coords (total r) 0

/-- Allow for the augmented list and the cached negative target in either mode. -/
def scanWork (r : Raw K m d) :=
  10+3*m+8*d+(countedScan r (List.finRange m)).2+6*(rawRows r).length

theorem raw_phase_bounds (r : Raw K m d) :
    sumWork r ≤ 24*((m+1)*(1+d)) ∧ scanWork r ≤ 32*((m+1)*(1+d)) := by
  have h := (countedSum_spec r (List.finRange m) (Vector.replicate d 0)).2
  have j := (countedScan_spec r (List.finRange m)).2
  have hc := coords_le (total r) 0
  have hl : (rawRows r).length ≤ m := by
    simpa only [rawRows,scanRaw,List.length_finRange] using
      List.length_filterMap_le (fun i : Fin m =>
        let v := pack (r.state.charge i)
        if (denseEq K d).test v.get 0 then none else some (i,v.get)) (List.finRange m)
  simp only [List.length_finRange,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one,Nat.mul_assoc] at h j ⊢
  unfold sumWork scanWork
  have comm := Nat.mul_comm m d
  omega

/-- One scalar negation and division, two original scalar reads and a gate
    allocation for each non-pivot. Charge flatMap's copying of the produced spine. -/
def starTicks : List I → ℕ
  | [] => 1
  | _::xs => 2+10*xs.length

def wordTicks (gs : List (List I)) := (gs.map starTicks).sum + 3*gs.length + 3*divisions gs + 1

omit [DecidableEq K] in
theorem emit_phase_bound (u : I → K) (gs : List (List I)) :
    wordTicks gs ≤ 8*(1+gs.length+gs.flatten.length)+16*(word u gs).length := by
  have cap : (gs.map starTicks).sum ≤ 2*gs.length+10*divisions gs := by
    induction gs with
    | nil => simp [divisions]
    | cons b gs ih =>
      cases b <;> simp only [starTicks,divisions,List.map_cons,List.sum_cons,List.tail_cons,List.length_cons,
        List.tail_nil,List.length_nil,Nat.mul_succ,Nat.mul_add] at ih ⊢ <;> omega
  unfold wordTicks
  rw [← divisions_eq]
  omega

end BucketDP
