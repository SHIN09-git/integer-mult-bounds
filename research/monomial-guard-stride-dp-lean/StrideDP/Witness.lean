import StrideDP.Correctness
import CountDP.Operations

namespace StrideDP
open CountDP Finset
variable {I K V W : Type*} [AddCommGroup V] [DecidableEq V]

/-- Follow stored addresses. No histogram is decoded, erased or re-encoded on the path. -/
def trace (A : Arithmetic V W) (a : Array (Cell V W)) : ℕ → ℕ → CountDP.Path V
  | 0, _ => []
  | fuel+1, k =>
    let c := read A a k
    match c.entry.parent with
    | none => []
    | some v => (v, c.entry.cut) :: trace A a fuel c.prev

theorem trace_eq_backtrack (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (fuel : ℕ) (m : Multiset V) (hf : Fits xs n m) :
    trace A (runTable A xs n).cells fuel (address n xs m) =
      backtrack (lookup xs n (table xs n)) fuel m := by
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel ih =>
    let c := read A (runTable A xs n).cells (address n xs m)
    have hc := table_ok A xs n hd m hf
    change CellOK _ _ _ _ _ c at hc
    simp only [trace, backtrack]
    change (match c.entry.parent with
      | none => []
      | some v => (v, c.entry.cut) :: trace A _ fuel c.prev) = _
    rw [← hc.entry]
    cases he : c.entry.parent with
    | none => rfl
    | some v =>
      have hp := hc.parent v he
      simp only [hp.2, ih (m.erase v) (hf.erase v)]

def solve (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (m : Multiset V) : CountDP.Solution V :=
  let a := (runTable A xs n).cells
  let k := address n xs m
  ⟨(read A a k).entry.score, (splitPath (trace A a m.card k)).2⟩

theorem solve_eq (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (m : Multiset V) (hf : Fits xs n m) : solve A xs n m = solveCounts xs n m := by
  dsimp only [solve, solveCounts]
  rw [trace_eq_backtrack A xs n hd m.card m hf, (table_ok A xs n hd m hf).entry]

variable [DecidableEq I]

def groups (A : Arithmetic V W) (y : I → V) (keys : List I) (S : Finset I) : GuardDP.Groups I :=
  let sol := solve A (alphabet y keys) (capacity y keys) (histogram y S)
  (restoreGroups? y keys S sol.groups).getD []

theorem groups_eq (A : Arithmetic V W) (y : I → V) (keys : List I) (S : Finset I)
    (h : S ⊆ keys.toFinset) : groups A y keys S = labeledGroups y keys S := by
  dsimp only [groups, labeledGroups, compressed]
  rw [solve_eq A (alphabet y keys) (capacity y keys) (List.nodup_dedup _) _ (histogram_fits y keys h)]

end StrideDP

namespace StrideDP
open CountDP Finset
variable {I K V W : Type*} [LinearOrder I] [Fintype I] [Field K] [AddCommGroup V] [Module K V] [DecidableEq V]

def separationWord (A : Arithmetic V W) (s : HZ.State I K V) :=
  let keys := GuardDP.labels s.charge
  wordFromGroups s (groups A s.charge keys keys.toFinset)

def concentrationWord (A : Arithmetic V W) (s : HZ.State I K V) (τ : V) :=
  let keys := GuardDP.augmentedKeys s.charge
  let gs := groups A (Dummy.augment s.charge τ) keys keys.toFinset
  wordFromGroups s (gs.map Finset.eraseNone)

theorem separationWord_optimal (A : Arithmetic V W) (s : HZ.State I K V) (hs : ∑ i, s.charge i = 0) :
    GuardDP.OptimalWord s HZ.Separated (HZ.activeCount s - HZ.partitionCount s) (separationWord A s) := by
  dsimp only [separationWord]
  rw [groups_eq A _ _ _ Subset.rfl]
  exact CountDP.separationWord_optimal s hs

theorem concentrationWord_optimal (A : Arithmetic V W) (s : HZ.State I K V) (τ : V) (ht : τ ≠ 0)
    (hs : ∑ i, s.charge i = τ) :
    GuardDP.OptimalWord s (fun t => Dummy.Concentrated t τ)
      (HZ.activeCount s - Dummy.Zstar s.charge τ) (concentrationWord A s τ) := by
  dsimp only [concentrationWord]
  rw [groups_eq A _ _ _ Subset.rfl]
  exact CountDP.concentrationWord_optimal s τ ht hs

end StrideDP
