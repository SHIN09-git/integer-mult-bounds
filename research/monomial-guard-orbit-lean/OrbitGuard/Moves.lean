import OrbitGuard.Classes

namespace OrbitGuard
open Ternary Finset

/-- A legal paid addition, in the coordinates of the stored representative. -/
structure Gate (I : Type*) where
  dst : I
  src : I
  coeff : F
  distinct : dst ≠ src
  nonzero : coeff ≠ 0
  deriving DecidableEq

def Gate.act [DecidableEq I] (g : Gate I) (s : State I D) : State I D :=
  s.addRow g.dst g.src g.coeff

theorem Gate.run [DecidableEq I] (g : Gate I) (s : State I D) : HZ.Run s 1 (g.act s) :=
  HZ.Run.cons s (.add g.dst g.src g.coeff g.distinct g.nonzero) (HZ.Run.nil _)

def Gate.transport (g : Gate I) (q : Frame I) : Gate I where
  dst := q.perm g.dst
  src := q.perm g.src
  coeff := g.coeff * q.factor g.src / q.factor g.dst
  distinct := q.perm.injective.ne g.distinct
  nonzero := div_ne_zero (mul_ne_zero g.nonzero (q.nonzero _)) (q.nonzero _)

/-- Conjugating a paid addition through a monomial change gives one paid addition. -/
theorem Gate.act_frame [DecidableEq I] (g : Gate I) (q : Frame I) (s : State I D) :
    g.act (q.act s) = q.act ((g.transport q).act s) := by
  apply HZ.State.ext
  · funext k
    by_cases hk : k = g.dst
    · subst k
      simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute]
      field_simp [q.nonzero _]
    · simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute,
            Function.update_of_ne hk,Function.update_of_ne (q.perm.injective.ne hk)]
  · funext k d
    by_cases hk : k = g.src
    · subst k
      simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute]
      field_simp [q.nonzero _]
    · simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute,
            Function.update_of_ne hk,Function.update_of_ne (q.perm.injective.ne hk)]
  · funext k
    by_cases hk : k = g.src
    · subst k
      simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute]
      field_simp [q.nonzero _]
    · simp [act,transport,Frame.act,HZ.State.addRow,HZ.State.scale,HZ.State.permute,
            Function.update_of_ne hk,Function.update_of_ne (q.perm.injective.ne hk)]

variable [DecidableEq I] [Fintype I] [Fintype D]

def Edge (x y : Vertex I D) : Prop :=
  ∃ (s : State I D) (g : Gate I), vertex s = x ∧ vertex (g.act s) = y

theorem edge_from (s : State I D) (y : Vertex I D) :
    Edge (vertex s) y ↔ ∃ g : Gate I, vertex (g.act s) = y := by
  constructor
  · rintro ⟨t,g,ht,hy⟩
    obtain ⟨q,rfl⟩ := (vertex_eq_iff_frame s t).mp ht.symm
    exact ⟨g.transport q, by rw [← vertex_frame q ((g.transport q).act s), ← g.act_frame, hy]⟩
  · rintro ⟨g,h⟩
    exact ⟨s,g,rfl,h⟩

section Enumeration
variable {J : Type*} [Fintype J] [LinearOrder J]

def gates (J : Type*) [Fintype J] [LinearOrder J] : List (Gate J) :=
  let rows := (univ : Finset J).sort (· ≤ ·)
  rows.flatMap fun i => rows.flatMap fun j =>
    if h : i ≠ j then [⟨i,j,1,h,by decide⟩,⟨i,j,-1,h,by decide⟩] else []

theorem mem_gates (g : Gate J) : g ∈ gates J := by
  obtain ⟨i,j,a,h,ha⟩ := g
  unfold gates
  refine List.mem_flatMap.mpr ⟨i,by simp, List.mem_flatMap.mpr ⟨j,by simp,?_⟩⟩
  rw [dif_pos h]
  rcases signs a ha with rfl | rfl <;> simp
end Enumeration

end OrbitGuard
