import StrideDP.Cost
import StrideDP.Dense
import Mathlib.Analysis.Asymptotics.Defs

namespace StrideDP
open Asymptotics CountDP Filter

private theorem nat_bigO {ι : Type*} (l : Filter ι) (f g : ι → ℕ) (c : ℕ)
    (h : ∀ i, f i ≤ c*g i) : (fun i => (f i : ℝ)) =O[l] (fun i => (g i : ℝ)) := by
  apply IsBigO.of_bound (c : ℝ)
  apply Filter.Eventually.of_forall
  intro i
  simp only [Real.norm_natCast]
  exact_mod_cast h i

/-- Dimension, alphabet and capacities can all vary along the same family of inputs. -/
theorem dense_fill_time_bigO {ι F : Type*} [AddCommGroup F] [DecidableEq F] (l : Filter ι)
    (d : ι → ℕ) (xs : (i : ι) → List (Fin (d i) → F)) (n : (i : ι) → (Fin (d i) → F) → ℕ) :
    (fun i => ((fill (dense F (d i)) (layout (n i) (xs i) 1) (slots (n i) (xs i))).ticks : ℝ)) =O[l]
      (fun i => (((1+(xs i).length+d i)*slots (n i) (xs i) : ℕ) : ℝ)) := by
  apply nat_bigO _ _ _ 48
  intro i
  simpa only [layout_length] using fill_time_bound (dense F (d i)) (dense_costs _) (layout (n i) (xs i) 1)
    (slots (n i) (xs i)) (slots_pos _ _)

theorem dense_table_space_bigO {ι F : Type*} [AddCommGroup F] [DecidableEq F] (l : Filter ι)
    (d : ι → ℕ) (xs : (i : ι) → List (Fin (d i) → F)) (n : (i : ι) → (Fin (d i) → F) → ℕ) :
    (fun i => (tableWords (dense F (d i))
      (fill (dense F (d i)) (layout (n i) (xs i) 1) (slots (n i) (xs i))).cells : ℝ)) =O[l]
      (fun i => (((1+d i)*slots (n i) (xs i) : ℕ) : ℝ)) := by
  apply nat_bigO _ _ _ 16
  intro i
  exact fill_space_bound (dense F (d i)) (dense_costs _) (layout (n i) (xs i) 1)
    (slots (n i) (xs i)) (slots_pos _ _)

end StrideDP
