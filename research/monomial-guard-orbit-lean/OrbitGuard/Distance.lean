import OrbitGuard.Moves

namespace OrbitGuard
open Ternary
variable {I D : Type*} [DecidableEq I] [Fintype I] [Fintype D]

/-- The complete-state quotient is finite for any finite numbers of rows and slopes. -/
instance finiteVertex : Finite (Vertex I D) := by
  let encode (s : State I D) := (s.u,s.w,s.b)
  have hi : Function.Injective encode := by rintro ⟨u,w,b⟩ ⟨u',w',b'⟩ h; simpa [encode] using h
  letI : Finite (State I D) := Finite.of_injective _ hi
  apply Finite.of_surjective (vertex : State I D → Vertex I D)
  rintro ⟨_,s,rfl⟩
  exact ⟨s,rfl⟩

inductive Walk (a : Vertex I D) : ℕ → Vertex I D → Prop
  | nil : Walk a 0 a
  | snoc {n b c} : Walk a n b → Edge b c → Walk a (n+1) c

theorem Walk.one {a b : Vertex I D} (e : Edge a b) : Walk a 1 b := Walk.nil.snoc e

theorem Walk.trans {a b c : Vertex I D} {n m} (p : Walk a n b) (q : Walk b m c) :
    Walk a (n+m) c := by
  induction q with
  | nil => exact p
  | snoc _ e ih => exact (ih.snoc e)

theorem walk_zero {a b : Vertex I D} (p : Walk a 0 b) : a = b := by cases p; rfl

theorem walk_last {a c : Vertex I D} {n} (p : Walk a (n+1) c) :
    ∃ b, Walk a n b ∧ Edge b c := by cases p with | snoc w e => exact ⟨_,w,e⟩

theorem project_run {s t : State I D} {n} (r : HZ.Run s n t) : Walk (vertex s) n (vertex t) := by
  induction r with
  | nil => exact Walk.nil
  | cons s op _ ih =>
    cases op with
    | add i j a hij ha =>
      let g : Gate I := ⟨i,j,a,hij,ha⟩
      exact (Walk.one ((edge_from s _).mpr ⟨g,rfl⟩)).trans ih
    | permute e => simpa [HZ.Operation.cost,HZ.Operation.apply,vertex_permute] using ih
    | scale c hc => simpa [HZ.Operation.cost,HZ.Operation.apply,vertex_scale s c hc] using ih

theorem lift_walk {a b : Vertex I D} {n} (p : Walk a n b) (s : State I D) (hs : vertex s = a) :
    ∃ t, HZ.Run s n t ∧ vertex t = b := by
  induction p with
  | nil => exact ⟨s,HZ.Run.nil _,hs⟩
  | snoc _ e ih =>
    obtain ⟨t,hr,ht⟩ := ih
    rw [← ht] at e
    obtain ⟨g,hg⟩ := (edge_from t _).mp e
    exact ⟨_,hr.trans (g.run t),hg⟩

/-- Equality of all exact costs, including zero and paths with interleaved free operations. -/
theorem walk_iff_run (s t : State I D) (n : ℕ) :
    Walk (vertex s) n (vertex t) ↔ HZ.Run s n t := by
  constructor
  · intro w
    obtain ⟨r,hr,hv⟩ := lift_walk w s rfl
    obtain ⟨q,rfl⟩ := (vertex_eq_iff_frame r t).mp hv
    exact hr.trans (q.run r)
  · exact project_run

theorem zero_run_iff (s t : State I D) : HZ.Run s 0 t ↔ vertex s = vertex t := by
  rw [← walk_iff_run]
  exact ⟨walk_zero, fun h => h ▸ Walk.nil⟩

def Winning (v : Vertex I D) : Prop := ∃ s : State I D, vertex s = v ∧ FullGuard s

def WinningCost (a : Vertex I D) (n : ℕ) : Prop := ∃ b, Walk a n b ∧ Winning b

theorem winningCost_iff (s : State I D) (n : ℕ) :
    WinningCost (vertex s) n ↔ ∃ t, HZ.Run s n t ∧ FullGuard t := by
  constructor
  · rintro ⟨_,w,t,rfl,hg⟩
    exact ⟨t,(walk_iff_run s t n).mp w,hg⟩
  · rintro ⟨t,r,hg⟩
    exact ⟨_,project_run r,t,rfl,hg⟩

noncomputable def distance (a : Vertex I D) : ℕ := sInf {n | WinningCost a n}

theorem distance_eq_C (s : State I D) : distance (vertex s) = C s :=
  congrArg sInf (Set.ext (winningCost_iff s))

theorem C_congr (s t : State I D) (h : vertex s = vertex t) : C s = C t := by
  rw [← distance_eq_C,← distance_eq_C,h]

theorem distance_minimum (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    IsLeast {n | WinningCost (vertex s) n} (distance (vertex s)) := by
  refine ⟨?_,fun n h => Nat.sInf_le h⟩
  obtain ⟨t,hr,hg⟩ := C_attained s hy hn
  exact (winningCost_iff s _).mpr ⟨t,distance_eq_C s ▸ hr,hg⟩

omit [DecidableEq I] [Fintype I] in
theorem fixed_order_iff {m n : ℕ} (s : State (Fin m) D) :
    WinningCost (vertex s) n ↔ ∃ t, HZ.Run s n t ∧ HZ.Passes t :=
  (winningCost_iff s n).trans (fullguard_run_iff s)

end OrbitGuard
