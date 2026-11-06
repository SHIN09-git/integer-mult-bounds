import Ternary.Ordering
import Ternary.Repair
import Mathlib.Algebra.BigOperators.Fin

open Finset
namespace Ternary

def reindex {I J V : Type*} (s : HZ.State I F V) (e : J ≃ I) : HZ.State J F V :=
  ⟨s.u ∘ e, s.w ∘ e, s.b ∘ e⟩

@[simp] theorem scalar_reindex {I J V : Type*} (s : HZ.State I F V) (e : J ≃ I) (j : J) :
    scalar (reindex s e) j = scalar s (e j) := rfl

theorem imbalance_reindex {I J V : Type*} [Fintype I] [Fintype J]
    (s : HZ.State I F V) (e : J ≃ I) : imbalance (reindex s e) = imbalance s :=
  Equiv.sum_comp e (fun i => lift (scalar s i))

theorem prefix_ofFn {m : ℕ} (f : Fin m → F) (k : ℕ) (hk : k ≤ m) :
    ∑ i ∈ HZ.prefixSet m k, f i = ((List.ofFn f).take k).sum := by
  induction k with
  | zero => simp [HZ.prefixSet]
  | succ k ih =>
    let i : Fin m := ⟨k, by omega⟩
    have hp := HZ.prefix_succ i
    change HZ.prefixSet m (k + 1) = insert i (HZ.prefixSet m k) at hp
    rw [hp, sum_insert (by simp [HZ.prefixSet, i]), ih (by omega),
      List.sum_take_succ (List.ofFn f) k (by simp; omega)]
    simp [i, add_comm]

variable {I D : Type*} [DecidableEq I] [Fintype I] [Fintype D]

/-- Success under some free coordinate ordering, using actual proper principal minors. -/
def FullGuard (s : HZ.State I F (D → F)) : Prop :=
  ∃ (m : ℕ) (e : Fin m ≃ I), HZ.Passes (reindex s e)

omit [Fintype I] in
theorem minor_separated (s : HZ.State I F (D → F)) (hs : HZ.Separated s)
    (a : D → F) (B : Finset I) :
    HZ.principalMinor s a B = 1 - ∑ i ∈ B, scalar s i := by
  classical
  rw [HZ.principalMinor_eq]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [HZ.familyRow, mul_add, mul_sum]
  have hz : ∑ d, s.u i * (a d * s.w i d) = 0 := by
    apply sum_eq_zero
    intro d _
    have hy : s.u i * s.w i d = 0 := by simpa [HZ.State.charge] using congrFun (hs i) d
    calc
      _ = a d * (s.u i * s.w i d) := by ring
      _ = 0 := by rw [hy, mul_zero]
  rw [hz, add_zero]
  rfl

omit [DecidableEq I] in
theorem fullguard_separated (s : HZ.State I F (D → F))
    (hy : ∑ i, s.charge i = 0) (hg : FullGuard s) : HZ.Separated s := by
  obtain ⟨m, e, he⟩ := hg
  have ht : ∑ i, (reindex s e).charge i = 0 := by
    change (∑ i, s.charge (e i)) = 0
    rw [Equiv.sum_comp e, hy]
  have hh := HZ.passes_implies_separated (reindex s e) ht he
  intro i
  simpa [HZ.State.charge, reindex] using hh (e.symm i)

omit [DecidableEq I] in
theorem fullguard_imbalance (s : HZ.State I F (D → F))
    (hn : ∑ i, scalar s i = 1) (hg : FullGuard s) :
    imbalance s = 1 ∨ imbalance s = -2 := by
  obtain ⟨m, e, he⟩ := hg
  let t := reindex s e
  let xs := List.ofFn (scalar t)
  have hs : Safe xs := by
    intro k hk
    have hk' : k < m := by simpa [xs] using hk
    have hp := he k hk' 0
    rw [HZ.principalMinor_eq] at hp
    simp only [HZ.familyRow, Pi.zero_apply, zero_mul, sum_const_zero, add_zero] at hp
    rw [← prefix_ofFn (scalar t) k (by omega)]
    intro hz
    apply hp
    change 1 - (∑ i ∈ HZ.prefixSet m k, scalar t i) = 0
    rw [hz, sub_self]
  have ht : xs.sum = 1 := by
    simp only [xs, List.sum_ofFn]
    change (∑ i, scalar s (e i)) = 1
    rw [Equiv.sum_comp e, hn]
  have hl : (xs.map lift).sum = imbalance s := by
    simp only [xs, List.map_ofFn, List.sum_ofFn]
    exact imbalance_reindex s e
  rw [← hl]
  exact safe_lift_sum xs hs ht

theorem separated_good_fullguard (s : HZ.State I F (D → F)) (hs : HZ.Separated s)
    (hd : imbalance s = 1 ∨ imbalance s = -2) : FullGuard s := by
  classical
  obtain ⟨xs, hn, hset, hsafe⟩ := exists_safe_order (scalar s) univ hd
  have hall : ∀ i : I, i ∈ xs := by intro i; rw [← List.mem_toFinset, hset]; simp
  let e : Fin xs.length ≃ I := hn.getEquivOfForallMemList xs hall
  have hlist : List.ofFn (scalar (reindex s e)) = xs.map (scalar s) := by
    change List.ofFn (fun i : Fin xs.length => scalar s (xs.get i)) = xs.map (scalar s)
    exact List.ofFn_getElem_eq_map xs (scalar s)
  refine ⟨xs.length, e, ?_⟩
  intro k hk a
  have ht : HZ.Separated (reindex s e) := fun i => hs (e i)
  rw [minor_separated _ ht]
  rw [prefix_ofFn _ k (by omega), hlist]
  exact sub_ne_zero.mpr (Ne.symm (hsafe k (by simpa using hk)))

theorem fullguard_iff (s : HZ.State I F (D → F))
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    FullGuard s ↔ HZ.Separated s ∧ (imbalance s = 1 ∨ imbalance s = -2) :=
  ⟨fun hg => ⟨fullguard_separated s hy hg, fullguard_imbalance s hn hg⟩,
   fun h => separated_good_fullguard s h.1 h.2⟩

end Ternary
