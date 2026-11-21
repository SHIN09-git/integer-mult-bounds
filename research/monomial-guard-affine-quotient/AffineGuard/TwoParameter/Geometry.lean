import AffineGuard.OneParameter.Plane

/-! The support calculation takes place on the nine points of the slope plane. -/
namespace AffineGuard.TwoParameter
open Finset Ternary
abbrev V := F × F

abbrev Pair (P : Finset V) (x y : V) :=
  x ∈ P ∧ y ∈ P ∧ x ≠ y ∧ x+y=0

abbrev Triple (P : Finset V) (x y z : V) :=
  x ∈ P ∧ y ∈ P ∧ z ∈ P ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x+y+z=0

abbrev Rigid (P : Finset V) (x : V) :=
  Pair P x (-x) ∨ ∃ y ∈ P, ∃ z ∈ P, Triple P x y z

def capacity (P : Finset V) (x : V) : ℕ :=
  if x=0 then 1 else if Rigid P x then 2 else 3

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
/-- Supports of capacity at least twelve contain inconsistent pair/triple equations. -/
theorem support_geometry : ∀ P : Finset V, (∑ x ∈ P, capacity P x) ≤ 11 ∨
    (∃ x ∈ P, Pair P x (-x) ∧ Triple P x (-x) 0) ∨
    (∃ x ∈ P, ∃ y ∈ P, Pair P x (-x) ∧ Pair P y (-y) ∧
      ((Pair P (x+y) (-(x+y)) ∧ Triple P x y (-(x+y)) ∧ Triple P (-x) (-y) (x+y)) ∨
       (Triple P (-x) (-y) (x+y) ∧ Triple P (-x) y (x-y) ∧ Triple P (x+y) (x-y) x))) := by
  unfold Pair Triple
  decide +kernel

/-- Nonempty subsequence with a prescribed sum, keeping arbitrary row labels. -/
private def hasSum (l : List V) (t : V) : Bool :=
  match l with
  | [] => false
  | v :: vs => v == t || hasSum vs t || hasSum vs (t-v)

private theorem hasSum_sound {I : Type*} [DecidableEq I] (p : I → V) (l : List I)
    (hn : l.Nodup) (t : V) (h : hasSum (l.map p) t = true) :
    ∃ B ⊆ l.toFinset, B.Nonempty ∧ ∑ i ∈ B, p i = t := by
  induction l generalizing t with
  | nil => simp [hasSum] at h
  | cons i l ih =>
    have ni := (List.nodup_cons.mp hn).1
    have nl := (List.nodup_cons.mp hn).2
    simp only [List.map_cons,hasSum,Bool.or_eq_true,beq_iff_eq] at h
    rcases h with (eq|skip)|take
    · exact ⟨{i},by simp,by simp,by simpa using eq⟩
    · obtain ⟨B,sub,ne,e⟩ := ih nl _ skip
      exact ⟨B,sub.trans (by simp),ne,e⟩
    · obtain ⟨B,sub,_,e⟩ := ih nl _ take
      have niB : i ∉ B := fun hi => ni (List.mem_toFinset.mp (sub hi))
      exact ⟨insert i B,by simpa using insert_subset_insert i sub,insert_nonempty _ _,by rw [sum_insert niB,e]; abel⟩

set_option maxHeartbeats 0 in
private theorem five_test : ∀ a b c d e : V, hasSum [a,b,c,d,e] 0 = true := by decide +kernel

/-- The elementary five-term zero-sum property of the ternary plane. -/
theorem five_block {I : Type*} [DecidableEq I] (A : Finset I) (p : I → V) (h : 5 ≤ A.card) :
    ∃ B ⊆ A, B.Nonempty ∧ B.card ≤ 5 ∧ ∑ i ∈ B, p i = 0 := by
  obtain ⟨T,sub,size⟩ := exists_subset_card_eq h
  have len : T.toList.length = 5 := by simpa using size
  have test : hasSum (T.toList.map p) 0 = true := by
    generalize he : T.toList = l at len ⊢
    rcases l with _|⟨a,l⟩ <;> simp only [List.length_nil,List.length_cons] at len
    · contradiction
    rcases l with _|⟨b,l⟩ <;> simp only [List.length_nil,List.length_cons] at len
    · contradiction
    rcases l with _|⟨c,l⟩ <;> simp only [List.length_nil,List.length_cons] at len
    · contradiction
    rcases l with _|⟨d,l⟩ <;> simp only [List.length_nil,List.length_cons] at len
    · contradiction
    rcases l with _|⟨e,l⟩ <;> simp only [List.length_nil,List.length_cons] at len
    · contradiction
    have emp : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact five_test _ _ _ _ _
  obtain ⟨B,hB,ne,eq⟩ := hasSum_sound p T.toList T.nodup_toList 0 test
  have bt : B ⊆ T := by simpa using hB
  exact ⟨B,bt.trans sub,ne,(card_le_card bt).trans size.le,eq⟩

end AffineGuard.TwoParameter
