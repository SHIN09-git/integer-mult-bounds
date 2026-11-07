import BucketDP.Queues

namespace BucketDP
open CountDP

theorem split_join (p : Path I) :
    (splitPath p).1 ++ (splitPath p).2.flatten = p.map Prod.fst := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    obtain ⟨i,b⟩ := z
    cases b <;> simpa [splitPath] using congrArg (List.cons i) ih

theorem split_nonempty (p : Path I) : ∀ B ∈ (splitPath p).2, B ≠ [] := by
  induction p with
  | nil => simp [splitPath]
  | cons z p ih =>
    obtain ⟨i,b⟩ := z
    cases b <;> simpa [splitPath] using ih

theorem split_relabel (y : I → V) (p : Path I) :
    splitPath (relabel y p) = ((splitPath p).1.map y, (splitPath p).2.map (List.map y)) := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    obtain ⟨i,b⟩ := z
    change splitPath ((y i,b)::relabel y p) = _
    cases b <;> simp [splitPath, ih]

theorem split_sums [AddCommGroup V] [DecidableEq V] (m : Multiset V) (p : Path V)
    (hp : Follows m p) :
    (splitPath p).1.sum = m.sum ∧ ∀ B ∈ (splitPath p).2, B.sum = 0 := by
  induction p generalizing m with
  | nil => simp [splitPath, show m = 0 from hp]
  | cons z p ih =>
    obtain ⟨v,b⟩ := z
    obtain ⟨hv,hb,hp⟩ := hp
    obtain ⟨hs,hg⟩ := ih (m.erase v) hp
    have hsum : v + (m.erase v).sum = m.sum := by rw [← Multiset.sum_cons, Multiset.cons_erase hv]
    cases b with
    | false => simpa [splitPath, hs, hsum] using hg
    | true =>
      have hz : m.sum = 0 := of_decide_eq_true hb.symm
      simpa [splitPath, hs, hsum, hz] using hg

structure Partition (y : I → V) [AddCommGroup V] [DecidableEq I]
    (labels : Finset I) (gs : List (List I)) (score : ℕ) : Prop where
  unique : gs.flatten.Nodup
  covered : gs.flatten.toFinset = labels
  nonempty : ∀ B ∈ gs, B ≠ []
  zero : ∀ B ∈ gs, (B.map y).sum = 0
  count : gs.length = score

theorem partition_of_trace [DecidableEq I] [AddCommGroup V] [DecidableEq V]
    (y : I → V) (S : Finset I) (p : Path I) (q : Path V) (hp : relabel y p = q)
    (hn : (p.map Prod.fst).Nodup) (hs : (p.map Prod.fst).toFinset = S)
    (hf : Follows (histogram y S) q) (hz : (histogram y S).sum = 0) :
    Partition y S (splitPath p).2 (cuts q) := by
  have rel := split_relabel y p
  rw [hp] at rel
  have empty' := no_pending hf hz
  rw [rel] at empty'
  have empty : (splitPath p).1 = [] := List.map_eq_nil_iff.mp empty'
  have full := split_join p
  rw [empty, List.nil_append] at full
  refine ⟨full ▸ hn, full ▸ hs, split_nonempty _, ?_, ?_⟩
  · intro B hB
    obtain ⟨_,groups⟩ := split_sums _ _ hf
    rw [rel] at groups
    exact groups (B.map y) (List.mem_map.mpr ⟨B,hB,rfl⟩)
  · rw [← split_count, rel, List.length_map]

end BucketDP
