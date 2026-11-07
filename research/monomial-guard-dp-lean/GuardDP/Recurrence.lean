import GuardDP.Table

open Finset
namespace GuardDP
variable {I V : Type*} [DecidableEq I] [AddCommGroup V] [DecidableEq V]

/-- The score of the executable transition is the labeled one-deletion recurrence. -/
theorem step_recurrence (y : I → V) (keys : List I) (prev : Finset I → Groups I)
    (S : Finset I) (hs : S ⊆ keys.toFinset) (hn : S.Nonempty) :
    (step y keys prev S).length =
      (if ∑ i ∈ S, y i = 0 then 1 else 0) + S.sup (fun i => (prev (S.erase i)).length) := by
  let f := fun i => (prev (S.erase i)).length
  have hm (i : I) : i ∈ keys.filter (· ∈ S) ↔ i ∈ S := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨List.mem_toFinset.mp (hs h), h⟩⟩
  cases he : keys.filter (· ∈ S) with
  | nil =>
    obtain ⟨i, hi⟩ := hn
    simpa [he] using (hm i).mpr hi
  | cons a as =>
    let j := pick f a as
    obtain ⟨hj, hbest⟩ := pick_spec f a as
    have hscore : S.sup f = f j := le_antisymm
      (Finset.sup_le (fun i hi => hbest i (he ▸ (hm i).mpr hi)))
      (le_sup (f := f) ((hm j).mp (he ▸ hj)))
    change _ = _ + S.sup f
    rw [hscore]
    by_cases hz : ∑ i ∈ S, y i = 0 <;> simp [step, he, finish, hz, f, j, Nat.add_comm]

end GuardDP
