import AffineGuard.Distance

/-! The layer and fuel inductions adapt OrbitGuard.Layers, Solver and Fixed to affine-image keys.
At the minimum depth the proof transfers success between representatives of an affine class. -/

namespace AffineGuard
open Ternary Finset
open OrbitGuard (State Gate Item replay replay_run replay_append initial generate fresh mem_of_mem_fresh
  fresh_keys mem_gates accepts accepts_spec accepts_iff_guard cap C_le_cap least_paid finishOrder
  finishOrder_correct)

variable {I D : Type*} [Fintype I] [LinearOrder I] [Fintype D] [DecidableEq D]

/-- Deduplication reads only the signed orbit of the affine image. Each item still stores a physical state. -/
def itemKey (p : Item I D) := key p.state

def advance (seen : Finset (Key I)) (front : List (Item I D)) :=
  fresh itemKey seen (generate front)

def remember (seen : Finset (Key I)) (front : List (Item I D)) :=
  seen ∪ (front.map itemKey).toFinset

def Nearest (a : Key I) (n : ℕ) (b : Key I) : Prop :=
  Walk a n b ∧ ∀ j, Walk a j b → n ≤ j

theorem nearest_last {a c : Key I} {n} (h : Nearest a (n+1) c) :
    ∃ b, Nearest a n b ∧ Edge b c := by
  obtain ⟨b,w,e⟩ := walk_last h.1
  refine ⟨b,⟨w,fun j p => ?_⟩,e⟩
  exact Nat.le_of_succ_le_succ (h.2 (j+1) (p.snoc e))

/-- Every retained word replays; visited keys are reachable; every nearest key has a witness. -/
structure Layer (s : State I D) (n : ℕ) (seen : Finset (Key I)) (front : List (Item I D)) : Prop where
  valid : ∀ p ∈ front, replay s p.revWord.reverse = p.state ∧ p.revWord.length = n
  visited : ∀ q ∈ seen, ∃ j ≤ n, Walk (key s) j q
  covers : ∀ q, Nearest (key s) n q → q ∈ front.map itemKey

theorem initial_layer (s : State I D) : Layer s 0 {key s} (initial s) := by
  constructor
  · intro p h
    obtain rfl : p = ⟨s,[]⟩ := by simpa [initial] using h
    exact ⟨rfl,rfl⟩
  · intro q h
    obtain rfl : q = key s := by simpa using h
    exact ⟨0,le_rfl,Walk.nil⟩
  · intro q h
    simp [initial,itemKey,walk_zero h.1]

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
      exact ⟨n+1,le_rfl,by simpa [itemKey,← hr,← hl] using project_run (replay_run s p.revWord.reverse)⟩
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

/-- Each newly reached affine class has exactly one retained representative. -/
theorem advance_nodup (seen : Finset (Key I)) (front : List (Item I D)) :
    ((advance seen front).map itemKey).Nodup := OrbitGuard.fresh_nodup _ _ _

/-- Search a layer before generating its successors, retaining one concrete word per new class. -/
def search (fuel : ℕ) (seen : Finset (Key I)) (front : List (Item I D)) : Option (List (Gate I)) :=
  match front.find? (fun p => accepts p.state) with
  | some p => some p.revWord.reverse
  | none =>
    match fuel with
    | 0 => none
    | k+1 =>
      let next := advance seen front
      search k (remember seen next) next

def solve (s : State I D) : Option (List (Gate I)) :=
  search (cap s) {key s} (initial s)

private theorem hit_correct {s : State I D} {n seen front} (l : Layer s n seen front)
    (hn : n ≤ C s) {p : Item I D} (hit : front.find? (fun a => accepts a.state) = some p) :
    p.revWord.reverse.length = C s ∧ FullGuard (replay s p.revWord.reverse) := by
  obtain ⟨hr,hl⟩ := l.valid p (List.mem_of_find?_eq_some hit)
  have good := (accepts_spec p.state).mp (List.find?_some (p := fun a : Item I D => accepts a.state) hit)
  have hg := separated_good_fullguard p.state good.1 good.2
  rw [← hr] at hg
  have hb := least_paid (replay_run s p.revWord.reverse) hg
  simp only [List.length_reverse,hl] at hb ⊢
  exact ⟨Nat.le_antisymm hn hb,hg⟩

private theorem hit_at_C {s : State I D} (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    {seen front} (l : Layer s (C s) seen front) :
    (front.find? fun p => accepts p.state).isSome := by
  obtain ⟨t,r,hg⟩ := C_attained s hy hn
  have near : Nearest (key s) (C s) (key t) :=
    ⟨project_run r, fun j w => by
      rw [← distance_eq_C]
      exact Nat.sInf_le (show WinningCost (key s) j from ⟨_, w, (winning_key t).mpr hg⟩)⟩
  obtain ⟨p,hp,hkey⟩ := List.mem_map.mp (l.covers _ near)
  obtain ⟨hr, _⟩ := l.valid p hp
  have rp := replay_run s p.revWord.reverse
  rw [hr] at rp
  have good := (guard_key (s := p.state) (t := t) hkey).mpr hg
  exact List.find?_isSome.mpr ⟨p, hp,
    (accepts_iff_guard _ (rp.total_charge.trans hy) ((scalar_total rp).trans hn)).mpr good⟩

theorem search_complete {s : State I D} (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    (fuel : ℕ) {n seen front} (l : Layer s n seen front) (lo : n ≤ C s) (hi : C s ≤ n+fuel) :
    ∃ w, search fuel seen front = some w ∧ w.length = C s ∧ FullGuard (replay s w) := by
  induction fuel generalizing n seen front with
  | zero =>
    have eq : n = C s := by omega
    subst n
    obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp (hit_at_C hy hn l)
    exact ⟨_,by rw [search,hp],hit_correct l lo hp⟩
  | succ k ih =>
    cases hh : front.find? (fun p => accepts p.state) with
    | some p => exact ⟨_,by rw [search,hh],hit_correct l lo hh⟩
    | none =>
      have hl : n+1 ≤ C s := by
        by_contra! h
        have eq : n = C s := by omega
        subst n
        simpa [hh] using hit_at_C hy hn l
      obtain ⟨w,hw,hlw,hg⟩ := ih (advance_layer l) hl (by omega)
      exact ⟨w,by rw [search,hh]; exact hw,hlw,hg⟩

/-- On every normalized finite ternary instance, the returned additions have exactly cost C. -/
theorem solve_correct (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    ∃ w, solve s = some w ∧ w.length = C s ∧ FullGuard (replay s w) :=
  search_complete hy hn _ (initial_layer s) (Nat.zero_le _) (by simpa using C_le_cap s hy hn)

theorem solve_optimal (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    {w} (hw : solve s = some w) :
    HZ.Run s w.length (replay s w) ∧ FullGuard (replay s w) ∧
      ∀ (t : State I D) n, HZ.Run s n t → FullGuard t → w.length ≤ n := by
  obtain ⟨v,hv,hl,hg⟩ := solve_correct s hy hn
  obtain rfl := Option.some.inj (hv.symm.trans hw)
  exact ⟨replay_run _ _,hg,fun _ _ r h => hl ▸ least_paid r h⟩

section NumberedRows
variable {m : ℕ}

def solveFixed (s : State (Fin m) D) : Option (List (Gate (Fin m)) × Equiv.Perm (Fin m)) := do
  let w ← solve s
  let e ← finishOrder (replay s w)
  return (w,e)

theorem solveFixed_correct (s : State (Fin m) D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    ∃ w e, solveFixed s = some (w,e) ∧ w.length = C s ∧
      HZ.Run s w.length ((replay s w).permute e) ∧ HZ.Passes ((replay s w).permute e) := by
  obtain ⟨w,hw,hl,hg⟩ := solve_correct s hy hn
  have r := replay_run s w
  obtain ⟨e,he,hp⟩ := finishOrder_correct _ (fullguard_separated _ (r.total_charge.trans hy) hg) hg
  have free := HZ.Run.cons (replay s w) (HZ.Operation.permute e) (HZ.Run.nil _)
  exact ⟨w,e,by simp [solveFixed,hw,he],hl,by simpa [HZ.Operation.cost] using r.trans free,hp⟩

end NumberedRows
end AffineGuard
