import HZ.Partitions

open Finset
namespace GuardDP

/-- A materialized lookup table indexed by membership of the input labels. -/
inductive Table (I α : Type*) where
  | leaf (value : α)
  | branch (label : I) (absent present : Table I α)

def Table.read [DecidableEq I] (S : Finset I) : Table I α → α
  | .leaf a => a
  | .branch i l r => if i ∈ S then r.read S else l.read S

def tabulate [DecidableEq I] (f : Finset I → α) : List I → Finset I → Table I α
  | [], B => .leaf (f B)
  | i :: is, B => .branch i (tabulate f is B) (tabulate f is (insert i B))

theorem read_tabulate [DecidableEq I] (f : Finset I → α) (keys : List I) (B S : Finset I) :
    (tabulate f keys B).read S = f (B ∪ (S ∩ keys.toFinset)) := by
  induction keys generalizing B with
  | nil => simp [tabulate, Table.read]
  | cons i is ih =>
    by_cases hi : i ∈ S <;> simp only [tabulate, Table.read, hi, if_true, if_false, ih]
    all_goals congr 1; ext x; simp; aesop

/-- Pick a label of maximal score, resolving ties by input order. -/
def pick (f : I → ℕ) (x : I) : List I → I
  | [] => x
  | i :: is => let j := pick f i is; if f j ≤ f x then x else j

theorem pick_spec (f : I → ℕ) (x : I) (xs : List I) :
    pick f x xs ∈ x :: xs ∧ ∀ i ∈ x :: xs, f i ≤ f (pick f x xs) := by
  induction xs generalizing x with
  | nil => simp [pick]
  | cons a as ih =>
    obtain ⟨hm, hmax⟩ := ih a
    by_cases h : f (pick f a as) ≤ f x
    · simp only [pick, if_pos h]
      refine ⟨List.mem_cons_self, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rfl
      · exact (hmax i hi).trans h
    · simp only [pick, if_neg h]
      refine ⟨List.mem_cons_of_mem _ hm, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · exact hmax i hi

abbrev Groups (I : Type*) := List (Finset I)

/-- The real labels already assigned to closed groups. -/
def covered [DecidableEq I] (F : Finset (Finset I)) : Finset I := F.biUnion id

/-- Carry the winning predecessor's groups. At a zero sum, close its remaining labels. -/
def finish [DecidableEq I] [AddCommGroup V] [DecidableEq V] (y : I → V)
    (S : Finset I) (groups : Groups I) : Groups I :=
  if ∑ i ∈ S, y i = 0 then (S \ covered groups.toFinset) :: groups else groups

def step [DecidableEq I] [AddCommGroup V] [DecidableEq V] (y : I → V) (keys : List I)
    (prev : Finset I → Groups I) (S : Finset I) : Groups I :=
  match keys.filter (· ∈ S) with
  | [] => []
  | i :: is =>
    let j := pick (fun k => (prev (S.erase k)).length) i is
    finish y S (prev (S.erase j))

/-- Each round computes the new cardinality layer from the shared preceding table. -/
def layers [DecidableEq I] [AddCommGroup V] [DecidableEq V] (y : I → V)
    (keys : List I) : ℕ → Table I (Groups I)
  | 0 => .leaf []
  | n + 1 =>
    let old := layers y keys n
    tabulate (fun S => if S.card = n + 1 then step y keys (fun T => old.read T) S
      else old.read S) keys ∅

def partitionDP [DecidableEq I] [AddCommGroup V] [DecidableEq V] (y : I → V)
    (keys : List I) : Groups I := (layers y keys keys.toFinset.card).read keys.toFinset

end GuardDP
