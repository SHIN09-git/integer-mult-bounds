import OrbitGuard.Distance

namespace OrbitGuard
open Ternary Finset

/-- Keep the first witness for each key absent from earlier layers. -/
def fresh [DecidableEq K] (key : A → K) (seen : Finset K) : List A → List A
  | [] => []
  | a :: xs => if key a ∈ seen then fresh key seen xs
               else a :: fresh key (insert (key a) seen) xs

theorem mem_of_mem_fresh [DecidableEq K] (key : A → K) (seen : Finset K) {a : A} {xs : List A}
    (h : a ∈ fresh key seen xs) : a ∈ xs := by
  induction xs generalizing seen with
  | nil => simp [fresh] at h
  | cons b xs ih =>
    rw [fresh] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih _ h)
    · rcases List.mem_cons.mp h with rfl|hm
      · simp
      · exact List.mem_cons_of_mem _ (ih _ hm)

theorem fresh_keys [DecidableEq K] (key : A → K) (seen : Finset K) (xs : List A) (v : K) :
    v ∈ (fresh key seen xs).map key ↔ v ∉ seen ∧ v ∈ xs.map key := by
  induction xs generalizing seen with
  | nil => simp [fresh]
  | cons a xs ih =>
    by_cases hm : key a ∈ seen
    · simp only [fresh,if_pos hm,ih,List.map_cons,List.mem_cons]
      aesop
    · simp only [fresh,if_neg hm,List.map_cons,List.mem_cons,ih,Finset.mem_insert]
      by_cases he : v = key a
      · subst v; simp [hm]
      · simp [he]

theorem fresh_nodup [DecidableEq K] (key : A → K) (seen : Finset K) (xs : List A) :
    ((fresh key seen xs).map key).Nodup := by
  induction xs generalizing seen with
  | nil => simp [fresh]
  | cons a xs ih =>
    by_cases hm : key a ∈ seen
    · simpa [fresh,hm] using ih seen
    · simp [fresh,hm,fresh_keys,ih]

variable {I D : Type*}

def replay [DecidableEq I] (s : State I D) : List (Gate I) → State I D
  | [] => s
  | g :: rest => replay (g.act s) rest

theorem replay_append [DecidableEq I] (s : State I D) (xs ys : List (Gate I)) :
    replay s (xs ++ ys) = replay (replay s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons g _ ih => exact ih (g.act s)

theorem replay_run [DecidableEq I] (s : State I D) (xs : List (Gate I)) :
    HZ.Run s xs.length (replay s xs) := by
  induction xs generalizing s with
  | nil => exact HZ.Run.nil s
  | cons g xs ih => simpa [Nat.add_comm] using (g.run s).trans (ih (g.act s))

structure Item (I D : Type*) where
  state : State I D
  revWord : List (Gate I)

variable [Fintype I] [LinearOrder I] [Fintype D]

def Item.key (p : Item I D) := vertex p.state

def Item.child (p : Item I D) (g : Gate I) : Item I D := ⟨g.act p.state,g :: p.revWord⟩

def generate (front : List (Item I D)) : List (Item I D) :=
  front.flatMap fun p => (gates I).map p.child

def advance (seen : Finset (Vertex I D)) (front : List (Item I D)) :=
  fresh Item.key seen (generate front)

def remember (seen : Finset (Vertex I D)) (front : List (Item I D)) :=
  seen ∪ (front.map Item.key).toFinset

def Nearest (a : Vertex I D) (n : ℕ) (b : Vertex I D) : Prop :=
  Walk a n b ∧ ∀ j, Walk a j b → n ≤ j

theorem nearest_last {a c : Vertex I D} {n} (h : Nearest a (n+1) c) :
    ∃ b, Nearest a n b ∧ Edge b c := by
  obtain ⟨b,w,e⟩ := walk_last h.1
  refine ⟨b,⟨w,fun j p => ?_⟩,e⟩
  exact Nat.le_of_succ_le_succ (h.2 (j+1) (p.snoc e))

/-- Every retained word replays; visited keys are reachable; every nearest key has a witness. -/
structure Layer (s : State I D) (n : ℕ) (seen : Finset (Vertex I D)) (front : List (Item I D)) : Prop where
  valid : ∀ p ∈ front, replay s p.revWord.reverse = p.state ∧ p.revWord.length = n
  visited : ∀ q ∈ seen, ∃ j ≤ n, Walk (vertex s) j q
  covers : ∀ q, Nearest (vertex s) n q → q ∈ front.map Item.key

def initial (s : State I D) : List (Item I D) := [⟨s,[]⟩]

theorem initial_layer (s : State I D) : Layer s 0 {vertex s} (initial s) := by
  constructor
  · intro p h
    obtain rfl : p = ⟨s,[]⟩ := by simpa [initial] using h
    exact ⟨rfl,rfl⟩
  · intro q h
    obtain rfl : q = vertex s := by simpa using h
    exact ⟨0,le_rfl,Walk.nil⟩
  · intro q h
    simp [initial,Item.key,walk_zero h.1]

theorem advance_layer {s : State I D} {n seen front} (l : Layer s n seen front) :
    Layer s (n+1) (remember seen (advance seen front)) (advance seen front) := by
  have valid (p : Item I D) (hp : p ∈ advance seen front) :
      replay s p.revWord.reverse = p.state ∧ p.revWord.length = n+1 := by
    obtain ⟨b,hb,hp⟩ := List.mem_flatMap.mp (mem_of_mem_fresh _ _ hp)
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hr,hl⟩ := l.valid b hb
    exact ⟨by simp [Item.child,replay_append,hr,replay],by simp [Item.child,hl]⟩
  refine ⟨valid,?_,?_⟩
  · intro q h
    rcases Finset.mem_union.mp h with ho | hf
    · obtain ⟨j,hj,w⟩ := l.visited q ho
      exact ⟨j,Nat.le_succ_of_le hj,w⟩
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
      obtain ⟨hr,hl⟩ := valid p hp
      exact ⟨n+1,le_rfl,by simpa [Item.key,← hr,← hl] using project_run (replay_run s p.revWord.reverse)⟩
  · intro q h
    apply (fresh_keys _ _ _ _).mpr
    constructor
    · intro hv
      obtain ⟨j,hj,w⟩ := l.visited q hv
      have := h.2 j w
      omega
    · obtain ⟨b,hb,e⟩ := nearest_last h
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (l.covers _ hb)
      obtain ⟨g,hg⟩ := (edge_from p.state _).mp e
      apply List.mem_map.mpr
      refine ⟨p.child g,List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨g,mem_gates g,rfl⟩⟩,hg⟩

end OrbitGuard
