import AffineGuard.Quotient

namespace AffineGuard
open Finset Ternary
open OrbitGuard (State Gate replay replay_append replay_run)

variable {I D E : Type*} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]

/-- Length counts paid additions. Permutations and nonzero row scalings stay in one key. -/
inductive Walk (x : Key I) : ℕ → Key I → Prop
  | nil : Walk x 0 x
  | snoc {n y z} : Walk x n y → Edge y z → Walk x (n+1) z

theorem Walk.one {x y : Key I} (e : Edge x y) : Walk x 1 y := Walk.nil.snoc e

theorem Walk.trans {x y z : Key I} {n m} (p : Walk x n y) (q : Walk y m z) :
    Walk x (n+m) z := by
  induction q with
  | nil => exact p
  | snoc _ e ih => exact ih.snoc e

theorem walk_zero {x y : Key I} (p : Walk x 0 y) : x = y := by cases p; rfl

theorem walk_last {x z : Key I} {n} (p : Walk x (n+1) z) :
    ∃ y, Walk x n y ∧ Edge y z := by cases p with | snoc w e => exact ⟨_,w,e⟩

theorem project_run {s t : State I D} {n} (r : HZ.Run s n t) : Walk (key s) n (key t) := by
  induction r with
  | nil => exact Walk.nil
  | cons s op _ ih =>
    cases op with
    | add i j a hij ha =>
      let g : Gate I := ⟨i,j,a,hij,ha⟩
      exact (Walk.one ((edge_from s _).mpr ⟨g,rfl⟩)).trans ih
    | permute e => simpa [HZ.Operation.cost,HZ.Operation.apply,key_permute] using ih
    | scale c hc => simpa [HZ.Operation.cost,HZ.Operation.apply,key_scale s c hc] using ih

/-- Lift a quotient walk to paid instructions on the particular input, ending in the given class. -/
theorem lift_walk {x y : Key I} {n} (p : Walk x n y) (s : State I D) (hs : key s = x) :
    ∃ w : List (Gate I), w.length = n ∧ key (replay s w) = y := by
  induction p with
  | nil => exact ⟨[],rfl,hs⟩
  | snoc _ e ih =>
    obtain ⟨w,hl,hw⟩ := ih
    rw [← hw] at e
    obtain ⟨g,hg⟩ := (edge_from _ _).mp e
    exact ⟨w ++ [g], by simp [hl], by simpa only [replay_append,replay] using hg⟩

def WinningCost (x : Key I) (n : ℕ) : Prop := ∃ y, Walk x n y ∧ Winning y

theorem winningCost_iff_word (s : State I D) (n : ℕ) :
    WinningCost (key s) n ↔ ∃ w : List (Gate I), w.length = n ∧ FullGuard (replay s w) := by
  constructor
  · rintro ⟨y,h,hw⟩
    obtain ⟨w,hl,rfl⟩ := lift_walk h s rfl
    exact ⟨w,hl,(winning_key _).mp hw⟩
  · rintro ⟨w,rfl,hg⟩
    exact ⟨_,project_run (replay_run s w),(winning_key _).mpr hg⟩

theorem winningCost_iff (s : State I D) (n : ℕ) :
    WinningCost (key s) n ↔ ∃ t, HZ.Run s n t ∧ FullGuard t := by
  constructor
  · intro h
    obtain ⟨w,rfl,hg⟩ := (winningCost_iff_word s n).mp h
    exact ⟨_,replay_run s w,hg⟩
  · rintro ⟨t,r,hg⟩
    exact ⟨_, project_run r, (winning_key t).mpr hg⟩

noncomputable def distance (x : Key I) : ℕ := sInf {n | WinningCost x n}

theorem distance_eq_C (s : State I D) : distance (key s) = C s :=
  congrArg sInf (Set.ext (winningCost_iff s))

theorem C_congr {s : State I D} {t : State I E} (h : key s = key t) : C s = C t := by
  rw [← distance_eq_C, ← distance_eq_C, h]

/-- The two presentations may have different parameter dimensions. -/
theorem labeled_cost {s : State I D} {t : State I E} (h : data s = data t) : C s = C t :=
  C_congr (congrArg orbit h)

theorem distance_minimum (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    IsLeast {n | WinningCost (key s) n} (distance (key s)) := by
  refine ⟨?_,fun n h => Nat.sInf_le h⟩
  obtain ⟨t,hr,hg⟩ := C_attained s hy hn
  exact (winningCost_iff s _).mpr ⟨t,distance_eq_C s ▸ hr,hg⟩

theorem fixed_order_iff {m n : ℕ} (s : State (Fin m) D) :
    WinningCost (key s) n ↔ ∃ t, HZ.Run s n t ∧ HZ.Passes t :=
  (winningCost_iff s n).trans (fullguard_run_iff s)

end AffineGuard
