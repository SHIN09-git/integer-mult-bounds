import CountDP.Score

namespace CountDP
variable {V : Type*} [DecidableEq V] [AddCommGroup V]

/-- A true bit begins a closed group when reading the deletion path from the full vector. -/
abbrev Path (V : Type*) := List (V × Bool)

def backtrack (get : Multiset V → Entry V) : ℕ → Multiset V → Path V
  | 0, _ => []
  | k + 1, m =>
    let e := get m
    match e.parent with
    | none => []
    | some v => (v, e.cut) :: backtrack get k (m.erase v)

def cuts : Path V → ℕ
  | [] => 0
  | (_, b) :: ps => cuts ps + (if b then 1 else 0)

def Follows (m : Multiset V) : Path V → Prop
  | [] => m = 0
  | (v, b) :: ps => v ∈ m ∧ b = decide (m.sum = 0) ∧ Follows (m.erase v) ps

theorem Follows.contents (m : Multiset V) (ps : Path V) (h : Follows m ps) :
    (⟦ps.map Prod.fst⟧ : Multiset V) = m := by
  induction ps generalizing m with
  | nil => exact h.symm
  | cons p ps ih =>
    obtain ⟨v, b⟩ := p
    obtain ⟨hv, _, ht⟩ := h
    change v ::ₘ (⟦ps.map Prod.fst⟧ : Multiset V) = m
    rw [ih _ ht, Multiset.cons_erase hv]

/-- A compressed witness contains each occurrence once and exactly D closed groups. -/
theorem backtrack_correct (types : List V) (n : V → ℕ) (hd : types.Nodup)
    (m : Multiset V) (hf : Fits types n m) :
    let get := lookup types n (table types n)
    let path := backtrack get m.card m
    Follows m path ∧ cuts path = (get m).score := by
  let get := lookup types n (table types n)
  suffices aux : ∀ k (m : Multiset V), Fits types n m → m.card = k →
      Follows m (backtrack get k m) ∧ cuts (backtrack get k m) = (get m).score from
    aux m.card m hf rfl
  intro k
  induction k with
  | zero =>
    intro m hm he
    obtain rfl : m = 0 := Multiset.card_eq_zero.mp he
    have h := table_best types n hd 0 hm
    change BestAt _ 0 (get 0) at h
    rw [BestAt, if_pos rfl] at h
    exact ⟨rfl, (congrArg Entry.score h).symm⟩
  | succ k ih =>
    intro m hm he
    have hne : m ≠ 0 := by rintro rfl; simp at he
    have h := table_best types n hd m hm
    change BestAt (fun p => (get p).score) m (get m) at h
    rw [BestAt, if_neg hne] at h
    obtain ⟨v, hv, hp, hc, hs, _⟩ := h
    have hk := congrArg Multiset.card (Multiset.cons_erase hv)
    simp only [Multiset.card_cons, he, Nat.add_right_cancel_iff] at hk
    obtain ⟨ht, hn⟩ := ih (m.erase v) (hm.erase v) hk
    simp only [backtrack, hp]
    refine ⟨⟨hv, hc, ht⟩, ?_⟩
    simp only [cuts, hn, hc, decide_eq_true_eq, hs, bonus]

/-- The unclosed prefix and ordered closed groups, still containing only charge types. -/
def splitPath : Path V → List V × List (List V)
  | [] => ([], [])
  | (v, b) :: ps =>
    let (pending, groups) := splitPath ps
    if b then ([], (v :: pending) :: groups) else (v :: pending, groups)

def markGroup : List V → Path V
  | [] => []
  | v :: vs => (v, true) :: vs.map (fun w => (w, false))

def markGroups (gs : List (List V)) : Path V := gs.flatMap markGroup

omit [DecidableEq V] [AddCommGroup V] in
theorem split_roundtrip (ps : Path V) :
    (splitPath ps).1.map (fun w => (w, false)) ++ markGroups (splitPath ps).2 = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨v, b⟩ := p
    cases b <;> simp [splitPath, markGroups, markGroup] at ih ⊢ <;> exact ih

omit [DecidableEq V] [AddCommGroup V] in
theorem split_count (ps : Path V) : (splitPath ps).2.length = cuts ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨v, b⟩ := p
    cases b <;> simp [splitPath, cuts, ih]

theorem no_pending {m : Multiset V} {ps : Path V} (h : Follows m ps) (hz : m.sum = 0) :
    (splitPath ps).1 = [] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    obtain ⟨v, b⟩ := p
    obtain ⟨_, hb, _⟩ := h
    simp [splitPath, hb, hz]

theorem closed_roundtrip {m : Multiset V} {ps : Path V} (h : Follows m ps) (hz : m.sum = 0) :
    markGroups (splitPath ps).2 = ps := by
  simpa only [no_pending h hz, List.map_nil, List.nil_append] using split_roundtrip ps

end CountDP
