import CountDP.Trace

namespace BucketDP
open CountDP Finset
variable {I V : Type*}

/-- Bind a parent stride directly to the head of its live label queue. -/
def queueAt (a : Array (List I)) (k : ℕ) : List I := a[k]?.getD []

def popPath (a : Array (List I)) : List (ℕ × Bool) → Path I
  | [] => []
  | (k,b)::ps =>
    match queueAt a k with
    | [] => []
    | i::is => (i,b) :: popPath (a.setIfInBounds k is) ps

def relabel (f : I → V) (p : Path I) : Path V := p.map (fun z => (f z.1,z.2))

def addressesOf (idx : V → ℕ) (p : Path V) := relabel idx p

variable [DecidableEq I] [DecidableEq V] [AddCommGroup V]

def waiting (y : I → V) (keys : List I) (S : Finset I) (v : V) :=
  keys.filter (fun i => decide (i ∈ S ∧ y i = v))

/-- Every bucket agrees in order with the remaining real or augmented identities. -/
def Ready (y : I → V) (keys : List I) (xs : List V) (idx : V → ℕ)
    (a : Array (List I)) (S : Finset I) : Prop :=
  ∀ v ∈ xs, queueAt a (idx v) = waiting y keys S v

omit [AddCommGroup V] in
private theorem waiting_erase (y : I → V) (keys : List I) (S : Finset I) (w : V) (i : I) :
    waiting y keys (S.erase i) w = (waiting y keys S w).filter (· != i) := by
  unfold waiting
  rw [List.filter_filter]
  apply congrArg (fun f : I → Bool => keys.filter f)
  funext j
  by_cases he : j = i <;> simp [he, Finset.mem_erase]

theorem popPath_correct (y : I → V) (keys : List I) (hn : keys.Nodup) (xs : List V) (idx : V → ℕ)
    (inj : ∀ v ∈ xs, ∀ w ∈ xs, idx v = idx w → v = w)
    (ps : Path V) (S : Finset I) (a : Array (List I))
    (sub : S ⊆ keys.toFinset) (support : ∀ i ∈ S, y i ∈ xs)
    (ready : Ready y keys xs idx a S) (hp : Follows (histogram y S) ps) :
    let out := popPath a (addressesOf idx ps)
    relabel y out = ps ∧ (out.map Prod.fst).Nodup ∧ (out.map Prod.fst).toFinset = S := by
  induction ps generalizing S a with
  | nil =>
    have h := congrArg Multiset.card hp
    have he : S = ∅ := Finset.card_eq_zero.mp (by simpa using h)
    simp [popPath, addressesOf, relabel, he]
  | cons p ps ih =>
    obtain ⟨v,b⟩ := p
    obtain ⟨hm, _, ht⟩ := hp
    obtain ⟨j,hj,hy⟩ := mem_histogram.mp hm
    have hv : v ∈ xs := hy ▸ support j hj
    have hmem : j ∈ waiting y keys S v := List.mem_filter.mpr ⟨List.mem_toFinset.mp (sub hj), by simp [hj, hy]⟩
    cases he : waiting y keys S v with
    | nil => simp [he] at hmem
    | cons i is =>
      have hq := (ready v hv).trans he
      have hi : i ∈ waiting y keys S v := he ▸ List.mem_cons_self
      obtain ⟨his, hiv⟩ := of_decide_eq_true (List.mem_filter.mp hi).2
      have hni : i ∉ is := (List.nodup_cons.mp (he ▸ hn.filter _)).1
      have inside : idx v < a.size := by
        by_contra h
        simp [queueAt, Array.getElem?_eq_none (Nat.le_of_not_gt h)] at hq
      have nr : Ready y keys xs idx (a.setIfInBounds (idx v) is) (S.erase i) := by
        intro w hw
        rw [waiting_erase]
        by_cases eq : w = v
        · subst w
          rw [he]
          have hall : is.filter (· != i) = is := List.filter_eq_self.mpr (fun j hj =>
            bne_iff_ne.mpr (fun e : j = i => hni (e ▸ hj)))
          simp [queueAt, Array.setIfInBounds, inside, hall]
        · have hne : idx w ≠ idx v := fun h => eq (inj w hw v hv h)
          have all : ∀ j ∈ waiting y keys S w, (j != i) = true := by
            intro j hj
            have hjw := (of_decide_eq_true (List.mem_filter.mp hj).2).2
            exact bne_iff_ne.mpr (fun e => eq (hjw.symm.trans (e ▸ hiv)))
          rw [List.filter_eq_self.mpr all, ← ready w hw]
          simp [queueAt, Array.setIfInBounds, inside, Ne.symm hne]
      have hhist := histogram_erase y S his
      rw [hiv] at hhist
      have hh := ih (S.erase i) _ (fun _ h => sub (mem_of_mem_erase h))
        (fun j h => support j (mem_of_mem_erase h)) nr (hhist ▸ ht)
      obtain ⟨hmap,hnd,hset⟩ := hh
      dsimp only [addressesOf, relabel] at hset
      simp only [addressesOf, relabel, List.map_cons, popPath, hq]
      refine ⟨?_, List.nodup_cons.mpr ⟨?_,hnd⟩, ?_⟩
      · rw [hiv]
        exact congrArg (List.cons (v,b)) hmap
      · intro hx
        have := List.mem_toFinset.mpr hx
        rw [hset] at this
        exact (Finset.notMem_erase i S) this
      · rw [List.toFinset_cons, hset, Finset.insert_erase his]

end BucketDP
