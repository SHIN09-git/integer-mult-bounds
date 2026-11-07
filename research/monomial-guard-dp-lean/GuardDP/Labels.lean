import GuardDP.Correctness
import Dummy.Partitions
import Mathlib.Data.Finset.Sort

open Finset
namespace GuardDP
variable {I V : Type*} [LinearOrder I] [Fintype I] [AddCommGroup V] [DecidableEq V]

/-- Sorting gives deterministic labels even when several charges have the same value. -/
def labels (y : I → V) : List I := (univ.filter (fun i => y i ≠ 0)).sort (· ≤ ·)

theorem labels_set (y : I → V) : (labels y).toFinset = HZ.active y := by
  ext i
  simp [labels, HZ.active]

def zeroGroups (y : I → V) : Groups I := partitionDP y (labels y)

/-- In the nonzero-target problem the bookkeeping label carries charge minus the target. -/
def augmentedKeys (y : I → V) : List (Option I) := none :: (labels y).map some

def augmentedGroups (y : I → V) (τ : V) : Groups (Option I) :=
  partitionDP (Dummy.augment y τ) (augmentedKeys y)

def realGroups (y : I → V) (τ : V) : Groups I := (augmentedGroups y τ).map Finset.eraseNone

theorem augmentedKeys_set (y : I → V) (τ : V) (ht : τ ≠ 0) :
    (augmentedKeys y).toFinset = HZ.active (Dummy.augment y τ) := by
  rw [Dummy.active_augment y τ ht, ← labels_set]
  ext i
  cases i <;> simp [augmentedKeys]

theorem zeroGroups_optimal (y : I → V) : Optimal y (HZ.active y) (zeroGroups y) := by
  simpa only [zeroGroups, labels_set] using partitionDP_optimal y (labels y)

theorem augmentedGroups_optimal (y : I → V) (τ : V) (ht : τ ≠ 0) :
    Optimal (Dummy.augment y τ) (HZ.active (Dummy.augment y τ)) (augmentedGroups y τ) := by
  simpa only [augmentedGroups, augmentedKeys_set y τ ht] using
    partitionDP_optimal (Dummy.augment y τ) (augmentedKeys y)

theorem computes_Z (y : I → V) (hs : ∑ i, y i = 0) :
    (zeroGroups y).length = HZ.blockCount y :=
  (zeroGroups_optimal y).count_eq ((Dummy.sum_active y).trans hs)

theorem computes_Zstar (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    (augmentedGroups y τ).length = Dummy.Zstar y τ :=
  (augmentedGroups_optimal y τ ht).count_eq (Dummy.sum_augmented_active y τ ht hs)

/-- Removing the virtual label preserves every block; exactly one real group carries τ. -/
theorem realGroups_spec (y : I → V) (τ : V) (ht : τ ≠ 0) (hs : ∑ i, y i = τ) :
    let g := realGroups y τ
    g.Nodup ∧ (∀ B ∈ g, B.Nonempty) ∧
    (g.toFinset : Set (Finset I)).PairwiseDisjoint id ∧ covered g.toFinset = HZ.active y ∧
    ∃ B ∈ g, (∑ i ∈ B, y i) = τ ∧ ∀ A ∈ g, A ≠ B → (∑ i ∈ A, y i) = 0 := by
  let a := augmentedGroups y τ
  have opt := augmentedGroups_optimal y τ ht
  let P := opt.packing.partition (opt.full (Dummy.sum_augmented_active y τ ht hs))
  obtain ⟨hne, hd, hcover, hcard, B, hB, hsum, hother⟩ :=
    Dummy.real_parts y τ ht P opt.packing.zero
  have he : (realGroups y τ).toFinset = P.parts.image Finset.eraseNone := by
    change (a.map Finset.eraseNone).toFinset = a.toFinset.image Finset.eraseNone
    ext C
    simp
  have hn : (realGroups y τ).Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (⟦realGroups y τ⟧ : Multiset (Finset I)))).mp
    change (realGroups y τ).toFinset.card = (realGroups y τ).length
    rw [he, hcard]
    change a.toFinset.card = (a.map Finset.eraseNone).length
    rw [List.length_map, List.toFinset_card_of_nodup opt.nodup]
  refine ⟨hn, ?_, by rw [he]; exact hd, by rw [he]; exact hcover, B, ?_, hsum, ?_⟩
  · intro C hC
    exact hne C (he ▸ List.mem_toFinset.mpr hC)
  · exact List.mem_toFinset.mp (he ▸ hB)
  · intro C hC hCB
    exact hother C (he ▸ List.mem_toFinset.mpr hC) hCB
end GuardDP
