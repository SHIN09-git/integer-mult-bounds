import AffineGuard.Search
import OrbitGuard.Examples
import HZ.Examples

namespace AffineGuard.Examples
open Finset Ternary
open OrbitGuard (State Gate replay replay_run least_paid)
open OrbitGuard.Examples (oneSlope five directPass directPass_iff)

def leftEndpoint := oneSlope (m := 2) ![1,0] ![0,1] ![1,0]
def rightEndpoint := oneSlope (m := 2) ![1,0] ![0,1] ![1,1]

/-- Section 2: one affine key can contain two distinct zero-cost physical orbits. -/
theorem endpoint_example :
    key leftEndpoint = key rightEndpoint ∧ ¬ HZ.Run leftEndpoint 0 rightEndpoint := by
  constructor
  · exact congrArg orbit (show data leftEndpoint = data rightEndpoint by decide)
  · rw [OrbitGuard.zero_run_iff]
    decide

/-- A second independent parameter index with a zero slope leaves the data unchanged. -/
def redundant : State (Fin 2) (Fin 2) :=
  ⟨![1,0], ![![0,0],![1,0]], ![1,0]⟩

theorem redundant_data : data redundant = data leftEndpoint := by decide

def fiveWord : List (Gate (Fin 5)) :=
  [⟨0,1,1,by decide,by decide⟩, ⟨0,2,1,by decide,by decide⟩, ⟨3,4,-1,by decide,by decide⟩]

theorem five_passes : HZ.Passes (replay five fiveWord) := by
  apply (directPass_iff _).mp
  decide

/-- Five active charges cost at least three additions; the paper's three instructions attain it. -/
theorem five_distance : distance (key five) = 3 := by
  rw [distance_eq_C]
  have hy : ∑ i, five.charge i = 0 := by decide
  have hn : ∑ i, scalar five i = 1 := by decide
  have ha : HZ.active five.charge = univ := by
    ext i
    simp only [HZ.active, mem_filter, mem_univ, true_and, iff_true]
    fin_cases i <;> decide
  have hc : HZ.activeCount five = 5 := by simp [HZ.activeCount,ha]
  have hb := HZ.twice_partitionCount_le five hy
  have hs : S five ≤ C five := (le_max_left _ _).trans (envelope five hy hn).1
  unfold S at hs
  apply Nat.le_antisymm
  · exact least_paid (replay_run five fiveWord) ⟨5, Equiv.refl _, five_passes⟩
  · omega

end AffineGuard.Examples
