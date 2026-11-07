import CountDP.Table
import GuardDP.Recurrence

open Finset
namespace CountDP
variable {I V : Type*} [DecidableEq I] [DecidableEq V] [AddCommGroup V]

/-- Distinct observed types, including any value shared by real and virtual labels. -/
def alphabet (y : I → V) (keys : List I) : List V := (keys.map y).dedup

def capacity (y : I → V) (keys : List I) (v : V) : ℕ := (histogram y keys.toFinset).count v

omit [AddCommGroup V] in
theorem histogram_fits (y : I → V) (keys : List I) {S : Finset I} (hS : S ⊆ keys.toFinset) :
    Fits (alphabet y keys) (capacity y keys) (histogram y S) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_histogram.mp hv
    simp only [alphabet, List.mem_dedup, List.mem_map]
    exact ⟨i, List.mem_toFinset.mp (hS hi), rfl⟩
  · intro v _
    exact Multiset.count_le_of_le v (Multiset.map_le_map (val_le_iff.mpr hS))

/-- P is the score at S of the previously verified labeled subset algorithm. -/
def P (y : I → V) (keys : List I) (S : Finset I) : ℕ :=
  ((GuardDP.layers y keys S.card).read S).length

/-- D looks up the score in the single table for the full input's multiplicities. -/
def D (types : List V) (n : V → ℕ) (m : Multiset V) : ℕ :=
  (lookup types n (table types n) m).score

theorem P_recurrence (y : I → V) (keys : List I) (S : Finset I)
    (hS : S ⊆ keys.toFinset) (hn : S.Nonempty) :
    P y keys S = bonus (histogram y S) + S.sup (fun i => P y keys (S.erase i)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hn)
  unfold P
  rw [hk, GuardDP.layers, GuardDP.read_tabulate, empty_union, inter_eq_left.mpr hS, if_pos hk,
      GuardDP.step_recurrence _ _ _ _ hS hn]
  rw [bonus, histogram_sum]
  congr 1
  apply Finset.sup_congr rfl
  intro i hi
  have hh := card_erase_add_one hi
  rw [show (S.erase i).card = k by omega]

/-- Pointwise equality, including subsets with nonzero total charge. -/
theorem P_eq_D_of_fits (y : I → V) (keys : List I) (types : List V) (n : V → ℕ)
    (hd : types.Nodup) (S : Finset I) (hS : S ⊆ keys.toFinset)
    (hf : Fits types n (histogram y S)) :
    P y keys S = D types n (histogram y S) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    let m := histogram y S
    let get := lookup types n (table types n)
    have best := table_best types n hd m hf
    change BestAt (fun p => (get p).score) m (get m) at best
    by_cases he : S = ∅
    · subst S
      have hm : m = 0 := rfl
      rw [BestAt, if_pos hm] at best
      exact (congrArg Entry.score best).symm
    have hn := nonempty_iff_ne_empty.mpr he
    have hm : m ≠ 0 := by
      intro hz
      have h := congrArg Multiset.card hz
      simp [m, he] at h
    rw [BestAt, if_neg hm] at best
    obtain ⟨v, hv, _, _, hs, hmax⟩ := best
    have hpred (i : I) (hi : i ∈ S) : P y keys (S.erase i) = (get (m.erase (y i))).score := by
      have heq : histogram y (S.erase i) = m.erase (y i) := histogram_erase y S hi
      rw [← heq]
      exact ih (S.erase i) (erase_ssubset hi) ((erase_subset ..).trans hS) (heq ▸ hf.erase (y i))
    have hsup : S.sup (fun i => P y keys (S.erase i)) = (get (m.erase v)).score := by
      apply le_antisymm
      · apply Finset.sup_le
        intro i hi
        rw [hpred i hi]
        exact hmax (y i) (mem_histogram.mpr ⟨i, hi, rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := mem_histogram.mp hv
        rw [← hpred i hi]
        exact le_sup (f := fun j => P y keys (S.erase j)) hi
    change P y keys S = (get m).score
    rw [P_recurrence y keys S hS hn, hsup, hs, Nat.add_comm]

theorem P_eq_D (y : I → V) (keys : List I) (S : Finset I) (hS : S ⊆ keys.toFinset) :
    P y keys S = D (alphabet y keys) (capacity y keys) (histogram y S) :=
  P_eq_D_of_fits y keys _ _ (List.nodup_dedup _) S hS (histogram_fits y keys hS)

theorem same_histogram_same_score (y : I → V) (keys : List I) {S T : Finset I}
    (hs : S ⊆ keys.toFinset) (ht : T ⊆ keys.toFinset) (he : histogram y S = histogram y T) :
    P y keys S = P y keys T := by rw [P_eq_D y keys S hs, P_eq_D y keys T ht, he]

/-- The same equality holds when all subset queries use the already-built last labeled layer. -/
theorem layer_score_eq_D (y : I → V) (keys : List I) (S : Finset I) (hS : S ⊆ keys.toFinset)
    (k : ℕ) (hk : S.card ≤ k) :
    ((GuardDP.layers y keys k).read S).length =
      D (alphabet y keys) (capacity y keys) (histogram y S) := by
  induction k, hk using Nat.le_induction with
  | base => exact P_eq_D y keys S hS
  | succ k h ih =>
    have hne : S.card ≠ k + 1 := by omega
    simpa only [GuardDP.layers, GuardDP.read_tabulate, empty_union, inter_eq_left.mpr hS, if_neg hne] using ih

theorem state_count (y : I → V) (keys : List I) :
    (table (alphabet y keys) (capacity y keys)).size =
      ∏ v ∈ (alphabet y keys).toFinset, (capacity y keys v + 1) :=
  table_cells _ _ (List.nodup_dedup _)

omit [AddCommGroup V] in
/-- Distinct count vectors attained by actual labeled subsets fit in the same product bound. -/
theorem reachable_state_bound (y : I → V) (keys : List I) :
    (keys.toFinset.powerset.image (histogram y)).card ≤
      ∏ v ∈ (alphabet y keys).toFinset, (capacity y keys v + 1) := by
  let reachable := keys.toFinset.powerset.image (histogram y)
  let types := alphabet y keys
  let n := capacity y keys
  have hd : types.Nodup := List.nodup_dedup _
  have fits (m : Multiset V) (hm : m ∈ reachable) : Fits types n m := by
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hm
    exact histogram_fits y keys (mem_powerset.mp hS)
  have inj : Set.InjOn (address n types) (reachable : Set (Multiset V)) :=
    fun a ha b hb he => address_injective_on_box hd (fits a ha) (fits b hb) he
  have hsub : reachable.image (address n types) ⊆ range (slots n types) := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (address_lt_slots types n m (fits m hm).bounded)
  calc
    reachable.card = (reachable.image (address n types)).card := (card_image_of_injOn inj).symm
    _ ≤ (range (slots n types)).card := card_le_card hsub
    _ = _ := by rw [card_range, slots_eq_prod types n hd]

end CountDP
