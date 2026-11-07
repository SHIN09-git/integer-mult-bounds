import CountDP.Trace

open Finset
namespace CountDP
variable {I V : Type*} [DecidableEq I] [DecidableEq V] [AddCommGroup V]

def selectLabel (y : I → V) (keys : List I) (S : Finset I) (v : V) : Option I :=
  keys.find? (fun i => decide (i ∈ S ∧ y i = v))

/-- The caller can supply charge groups alone. A missing or leftover label causes failure. -/
def restoreTrace? (y : I → V) (keys : List I) : Path V → Finset I → Option (GuardDP.Groups I)
  | [], S => if S = ∅ then some [] else none
  | (v, cut) :: ps, S => do
    let i ← selectLabel y keys S v
    let gs ← restoreTrace? y keys ps (S.erase i)
    return if cut then (S \ GuardDP.covered gs.toFinset) :: gs else gs

def restoreGroups? (y : I → V) (keys : List I) (S : Finset I) (gs : List (List V)) :
    Option (GuardDP.Groups I) := restoreTrace? y keys (markGroups gs) S

omit [AddCommGroup V] in
private theorem select_found (y : I → V) (keys : List I) (S : Finset I) (v : V)
    (hS : S ⊆ keys.toFinset) (hv : v ∈ histogram y S) :
    ∃ i, selectLabel y keys S v = some i ∧ i ∈ S ∧ y i = v := by
  obtain ⟨j, hj, hjv⟩ := mem_histogram.mp hv
  cases h : selectLabel y keys S v with
  | none =>
    have hnone := List.find?_eq_none.mp h j (List.mem_toFinset.mp (hS hj))
    exact (hnone (decide_eq_true ⟨hj, hjv⟩)).elim
  | some i =>
    have hi := List.find?_some (p := fun j : I => decide (j ∈ S ∧ y j = v)) h
    exact ⟨i, rfl, of_decide_eq_true hi⟩

/-- The projection is group-by-group, including multiplicities and the order of groups. -/
structure Lifted (y : I → V) (S : Finset I) (ps : Path V) (gs : GuardDP.Groups I) : Prop where
  nodup : gs.Nodup
  packing : GuardDP.Packing y S gs.toFinset
  pending : histogram y (S \ GuardDP.covered gs.toFinset) = ⟦(splitPath ps).1⟧
  projection : gs.map (histogram y) = (splitPath ps).2.map (fun vs => (⟦vs⟧ : Multiset V))

theorem restore_correct (y : I → V) (keys : List I) (ps : Path V) (S : Finset I)
    (hS : S ⊆ keys.toFinset) (h : Follows (histogram y S) ps) :
    ∃ gs, restoreTrace? y keys ps S = some gs ∧ Lifted y S ps gs := by
  induction ps generalizing S with
  | nil =>
    have hc := congrArg Multiset.card (show histogram y S = 0 from h)
    obtain rfl : S = ∅ := card_eq_zero.mp (by simpa using hc)
    exact ⟨[], by simp [restoreTrace?], by simp, (GuardDP.optimal_empty y).packing, rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨v, b⟩ := p
    obtain ⟨hv, hb, ht⟩ := h
    obtain ⟨i, hfind, hi, hiv⟩ := select_found y keys S v hS hv
    have he : histogram y (S.erase i) = (histogram y S).erase v := by rw [histogram_erase _ _ hi, hiv]
    obtain ⟨gs, hr, lift⟩ := ih (S.erase i) ((erase_subset ..).trans hS) (he ▸ ht)
    let C := GuardDP.covered gs.toFinset
    have fresh : i ∉ C := fun hh => notMem_erase i S (lift.packing.covered_subset hh)
    have pack := lift.packing.mono (erase_subset i S)
    have hrem : histogram y (S \ C) = v ::ₘ (⟦(splitPath ps).1⟧ : Multiset V) := by
      have hd : S \ C = insert i ((S.erase i) \ C) := by
        ext j
        by_cases hj : j = i <;> simp [hj, hi, fresh]
      rw [hd]
      change (insert i ((S.erase i) \ C)).val.map y = _
      rw [insert_val_of_notMem (by simp), Multiset.map_cons, hiv]
      exact congrArg (Multiset.cons v) lift.pending
    cases b with
    | false =>
      refine ⟨gs, by simp [restoreTrace?, hfind, hr], lift.nodup, pack, ?_, ?_⟩
      · exact hrem
      · exact lift.projection
    | true =>
      have hz : ∑ k ∈ S, y k = 0 := by
        rw [← histogram_sum]
        exact of_decide_eq_true hb.symm
      obtain ⟨hn, hp, hc⟩ := pack.close hz hi fresh
      refine ⟨(S \ C) :: gs, by simp [restoreTrace?, hfind, hr, C],
        List.nodup_cons.mpr ⟨fun hm => hn (List.mem_toFinset.mpr hm), lift.nodup⟩, ?_, ?_, ?_⟩
      · simpa only [List.toFinset_cons] using hp
      · change histogram y (S \ GuardDP.covered ((S \ C) :: gs).toFinset) = 0
        rw [List.toFinset_cons, show GuardDP.covered (insert (S \ C) gs.toFinset) = S from hc]
        simp
      · simp [splitPath, hrem, lift.projection]

theorem Lifted.full {y : I → V} {S : Finset I} {ps : Path V} {gs : GuardDP.Groups I}
    (l : Lifted y S ps gs) (h : Follows (histogram y S) ps) (hz : (histogram y S).sum = 0) :
    GuardDP.covered gs.toFinset = S := by
  have hp := l.pending
  rw [no_pending h hz] at hp
  have hc := congrArg Multiset.card hp
  have he : S \ GuardDP.covered gs.toFinset = ∅ := card_eq_zero.mp (by simpa using hc)
  exact subset_antisymm l.packing.covered_subset (sdiff_eq_empty_iff_subset.mp he)

omit [DecidableEq V] in
theorem Lifted.length_eq {y : I → V} {S : Finset I} {ps : Path V} {gs : GuardDP.Groups I}
    (l : Lifted y S ps gs) : gs.length = cuts ps := by
  have h := congrArg List.length l.projection
  simpa only [List.length_map, split_count] using h

end CountDP
