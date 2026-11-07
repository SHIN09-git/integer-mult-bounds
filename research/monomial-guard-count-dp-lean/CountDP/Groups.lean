import CountDP.Restore
import GuardDP.Labels

open Finset
namespace CountDP
variable {I V : Type*} [DecidableEq I] [DecidableEq V] [AddCommGroup V]

structure Solution (V : Type*) where
  score : ℕ
  groups : List (List V)
  deriving Repr

/-- Only the observed multiplicities and the requested count vector enter this routine. -/
def solveCounts (types : List V) (n : V → ℕ) (m : Multiset V) : Solution V :=
  let a := table types n
  let get := lookup types n a
  ⟨(get m).score, (splitPath (backtrack get m.card m)).2⟩

def compressed (y : I → V) (keys : List I) (S : Finset I) : Solution V :=
  solveCounts (alphabet y keys) (capacity y keys) (histogram y S)

def labeledGroups (y : I → V) (keys : List I) (S : Finset I) : GuardDP.Groups I :=
  (restoreGroups? y keys S (compressed y keys S).groups).getD []

/-- On a zero total the returned groups use every label exactly once. Their individual
charge multisets agree with the compressed groups and their number is the computed score. -/
theorem compressed_certificate (y : I → V) (keys : List I) (S : Finset I)
    (hS : S ⊆ keys.toFinset) (hz : ∑ i ∈ S, y i = 0) :
    let a := compressed y keys S
    let gs := labeledGroups y keys S
    restoreGroups? y keys S a.groups = some gs ∧ GuardDP.Optimal y S gs ∧
    gs.length = a.score ∧ gs.map (histogram y) = a.groups.map (fun b => (⟦b⟧ : Multiset V)) := by
  let m := histogram y S
  let types := alphabet y keys
  let n := capacity y keys
  let get := lookup types n (table types n)
  let path := backtrack get m.card m
  have ht := backtrack_correct types n (List.nodup_dedup _) m (histogram_fits y keys hS)
  change Follows m path ∧ cuts path = (get m).score at ht
  have hm : m.sum = 0 := (histogram_sum y S).trans hz
  obtain ⟨g, hrestore, lift⟩ := restore_correct y keys path S hS ht.1
  have hread : restoreGroups? y keys S (compressed y keys S).groups = some g := by
    change restoreTrace? y keys (markGroups (splitPath path).2) S = some g
    rw [closed_roundtrip ht.1 hm]
    exact hrestore
  have hg : labeledGroups y keys S = g := by simp [labeledGroups, hread]
  have hlen : g.length = (get m).score := lift.length_eq.trans ht.2
  have hP : P y keys S = (get m).score := P_eq_D y keys S hS
  have ref := GuardDP.layers_correct y keys S.card S hS le_rfl
  dsimp only
  rw [hg]
  refine ⟨hread, ⟨lift.nodup, lift.packing, fun _ => lift.full ht.1 hm, ?_⟩, hlen, lift.projection⟩
  intro F hf
  rw [hlen, ← hP]
  exact ref.maximum F hf

theorem compressed_score (y : I → V) (keys : List I) (S : Finset I) (hS : S ⊆ keys.toFinset) :
    (compressed y keys S).score = P y keys S := (P_eq_D y keys S hS).symm

end CountDP

namespace CountDP
open Finset
variable {I V : Type*} [LinearOrder I] [Fintype I] [AddCommGroup V] [DecidableEq V]

def zeroGroups (y : I → V) : GuardDP.Groups I :=
  let keys := GuardDP.labels y
  labeledGroups y keys keys.toFinset

def augmentedGroups (y : I → V) (τ : V) : GuardDP.Groups (Option I) :=
  let keys := GuardDP.augmentedKeys y
  labeledGroups (Dummy.augment y τ) keys keys.toFinset

def realGroups (y : I → V) (τ : V) : GuardDP.Groups I := (augmentedGroups y τ).map Finset.eraseNone

theorem zero_optimal (y : I → V) (hs : ∑ i, y i = 0) : GuardDP.Optimal y (HZ.active y) (zeroGroups y) := by
  let keys := GuardDP.labels y
  have he : keys.toFinset = HZ.active y := GuardDP.labels_set y
  have hz : ∑ i ∈ keys.toFinset, y i = 0 := by rw [he, Dummy.sum_active, hs]
  exact he ▸ (compressed_certificate y keys keys.toFinset Subset.rfl hz).2.1

theorem augmented_optimal (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    GuardDP.Optimal (Dummy.augment y τ) (HZ.active (Dummy.augment y τ)) (augmentedGroups y τ) := by
  let keys := GuardDP.augmentedKeys y
  have he : keys.toFinset = HZ.active (Dummy.augment y τ) := GuardDP.augmentedKeys_set y τ ht
  have hz : ∑ i ∈ keys.toFinset, Dummy.augment y τ i = 0 := he ▸ Dummy.sum_augmented_active y τ ht hs
  exact he ▸ (compressed_certificate _ keys keys.toFinset Subset.rfl hz).2.1

theorem computes_Z (y : I → V) (hs : ∑ i, y i = 0) : (zeroGroups y).length = HZ.blockCount y :=
  (zero_optimal y hs).count_eq ((Dummy.sum_active y).trans hs)

theorem computes_Zstar (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    (augmentedGroups y τ).length = Dummy.Zstar y τ :=
  (augmented_optimal y τ ht hs).count_eq (Dummy.sum_augmented_active y τ ht hs)

end CountDP

namespace CountDP
open Finset
variable {I V : Type*} [DecidableEq I] [AddCommGroup V] [DecidableEq V]

/-- Score-only entry point: no traceback or row labels are allocated for the witness. -/
def fullScore (y : I → V) (keys : List I) : ℕ :=
  D (alphabet y keys) (capacity y keys) (histogram y keys.toFinset)

theorem fullScore_eq_maxBlocks (y : I → V) (keys : List I)
    (hz : ∑ i ∈ keys.toFinset, y i = 0) : fullScore y keys = HZ.maxBlocks y keys.toFinset := by
  have h := compressed_certificate y keys keys.toFinset Subset.rfl hz
  exact h.2.2.1.symm.trans (h.2.1.count_eq hz)

end CountDP

namespace CountDP
open Finset
variable {I V : Type*} [LinearOrder I] [Fintype I] [AddCommGroup V] [DecidableEq V]

theorem score_Z (y : I → V) (hs : ∑ i, y i = 0) : fullScore y (GuardDP.labels y) = HZ.blockCount y := by
  rw [fullScore_eq_maxBlocks, GuardDP.labels_set]
  · rfl
  · rw [GuardDP.labels_set, Dummy.sum_active, hs]

theorem score_Zstar (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    fullScore (Dummy.augment y τ) (GuardDP.augmentedKeys y) = Dummy.Zstar y τ := by
  rw [fullScore_eq_maxBlocks, GuardDP.augmentedKeys_set y τ ht]
  · rfl
  · rw [GuardDP.augmentedKeys_set y τ ht]
    exact Dummy.sum_augmented_active y τ ht hs

end CountDP
