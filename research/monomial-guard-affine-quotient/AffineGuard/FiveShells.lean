import AffineGuard.FiveEncoding
import Mathlib.Data.Set.Card

namespace AffineGuard.Census
open Finset
open OrbitGuard (vertex Gate)
open OrbitGuard.Examples (five)

/-- Enumerate the 5 · 4 · 2 legal paid additions by their original row labels. -/
def paidGates : List (Gate (Fin 5)) :=
  (List.finRange 5).flatMap fun i => (List.finRange 5).flatMap fun j =>
    if h : i ≠ j then [⟨i,j,1,h,by decide⟩,⟨i,j,-1,h,by decide⟩] else []

private theorem mem_paidGates (g : Gate (Fin 5)) : g ∈ paidGates := by
  obtain ⟨i,j,c,h,hc⟩ := g
  refine List.mem_flatMap.mpr ⟨i,by simp,List.mem_flatMap.mpr ⟨j,by simp,?_⟩⟩
  rw [dif_pos h]
  rcases OrbitGuard.signs c hc with rfl | rfl <;> simp

def successors (c : Code) : Finset Code :=
  (paidGates.map fun g => rowKey (g.act (readCode c))).toFinset

private theorem mem_successors (c d : Code) :
    d ∈ successors c ↔ ∃ g : Gate (Fin 5), rowKey (g.act (readCode c)) = d := by
  simp [successors, mem_paidGates]

/-- The closed ball expands all legal paid additions, including paths through a passing state. -/
def rowBall : ℕ → Finset Code
  | 0 => {rowKey five}
  | n+1 => let prev := rowBall n; prev ∪ prev.biUnion successors

def Within {V : Type*} (walk : ℕ → V → Prop) (n : ℕ) (x : V) : Prop :=
  ∃ j ≤ n, walk j x

abbrev rowWalk := OrbitGuard.Walk (vertex five)
abbrev affineWalk := Walk (key five)

private theorem vertex_read (s : Model) : vertex (readCode (rowKey s)) = vertex s :=
  (rowKey_iff _ _).mp (rowKey_read s)

theorem rowBall_spec (n : ℕ) (c : Code) :
    c ∈ rowBall n ↔ ∃ s : Model, rowKey s = c ∧ Within rowWalk n (vertex s) := by
  induction n generalizing c with
  | zero =>
    constructor
    · intro hc
      obtain rfl : c = rowKey five := by simpa [rowBall] using hc
      exact ⟨five,rfl,0,le_rfl,OrbitGuard.Walk.nil⟩
    · rintro ⟨s,rfl,j,hj,h⟩
      obtain rfl : j = 0 := by omega
      simpa [rowBall] using (rowKey_iff s five).mpr (OrbitGuard.walk_zero h).symm
  | succ n ih =>
    rw [rowBall, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (old | ⟨p,hp,step⟩)
      · obtain ⟨s,rfl,j,hj,w⟩ := (ih _).mp old
        exact ⟨s,rfl,j,Nat.le_succ_of_le hj,w⟩
      · obtain ⟨b,rfl,j,hj,w⟩ := (ih _).mp hp
        obtain ⟨g,rfl⟩ := (mem_successors _ _).mp step
        rw [← vertex_read b] at w
        exact ⟨_,rfl,j+1,Nat.succ_le_succ hj,w.snoc ((OrbitGuard.edge_from _ _).mpr ⟨g,rfl⟩)⟩
    · rintro ⟨s,rfl,j,hj,w⟩
      by_cases old : j ≤ n
      · exact Or.inl ((ih _).mpr ⟨s,rfl,j,old,w⟩)
      · obtain rfl : j = n+1 := by omega
        obtain ⟨v,p,e⟩ := OrbitGuard.walk_last w
        obtain ⟨b,_,rfl⟩ := OrbitGuard.lift_walk p five rfl
        rw [← vertex_read b] at e
        obtain ⟨g,hg⟩ := (OrbitGuard.edge_from _ _).mp e
        exact Or.inr ⟨rowKey b,(ih _).mpr ⟨b,rfl,n,le_rfl,p⟩,
          (mem_successors _ _).mpr ⟨g,(rowKey_iff _ _).mpr hg⟩⟩

/-- Project the whole closed row ball. Two source shells can overlap after projection. -/
def affineBall (n : ℕ) : Finset Code := (rowBall n).image fun l => affineKey (readCode l)

theorem affineBall_spec (n : ℕ) (c : Code) :
    c ∈ affineBall n ↔ ∃ s : Model, affineKey s = c ∧ Within affineWalk n (key s) := by
  constructor
  · intro hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨b,rfl,j,hj,w⟩ := (rowBall_spec _ _).mp hp
    have run := (OrbitGuard.walk_iff_run five b j).mp w
    exact ⟨_,rfl,j,hj,(key_of_vertex (vertex_read b)).symm ▸ project_run run⟩
  · rintro ⟨s,rfl,j,hj,w⟩
    obtain ⟨word,rfl,he⟩ := lift_walk w five rfl
    let b := OrbitGuard.replay five word
    have rowpath := OrbitGuard.project_run (OrbitGuard.replay_run five word)
    refine Finset.mem_image.mpr ⟨rowKey b,(rowBall_spec _ _).mpr ⟨b,rfl,_,hj,rowpath⟩,?_⟩
    exact (affineKey_iff _ _).mpr ((key_of_vertex (vertex_read b)).trans he)

private theorem affineKey_read (s : Model) : affineKey (readCode (affineKey s)) = affineKey s := by
  have hm : affineKey s ∈ variants s := Finset.min'_mem _ _
  obtain ⟨p,_,he⟩ := Finset.mem_image.mp hm
  let t := changeParam s (p.1 : Ternary.F) p.2
  change rowKey t = affineKey s at he
  rw [← he]
  exact ((affineKey_iff _ _).mpr (key_of_vertex (vertex_read t))).trans
    (((affineKey_iff t s).mpr (congrArg orbit (data_change s p.1 p.2 p.1.ne_zero))).trans he.symm)

/-- A closed ball difference counts exactly the vertices whose least paid length is n+1. -/
private theorem count_shell {V : Type*} (v : Model → V) (code : Model → Code)
    (eqv : ∀ s t, code s = code t ↔ v s = v t)
    (restore : ∀ s, code (readCode (code s)) = code s)
    (walk : ℕ → V → Prop) (realized : ∀ j x, walk j x → ∃ s, v s = x)
    (ball : ℕ → Finset Code)
    (spec : ∀ j c, c ∈ ball j ↔ ∃ s, code s = c ∧ Within walk j (v s)) (n : ℕ) :
    {x | walk (n+1) x ∧ ∀ j, walk j x → n+1 ≤ j}.ncard = (ball (n+1) \ ball n).card := by
  let shell := ball (n+1) \ ball n
  have mem (j) (s : Model) : code s ∈ ball j ↔ Within walk j (v s) := by
    constructor
    · intro h
      obtain ⟨t,ht,w⟩ := (spec _ _).mp h
      rwa [← (eqv _ _).mp ht]
    · intro w
      exact (spec _ _).mpr ⟨s,rfl,w⟩
  have rep (c) (hc : c ∈ shell) : code (readCode c) = c := by
    obtain ⟨s,rfl,_⟩ := (spec _ _).mp (Finset.mem_sdiff.mp hc).1
    exact restore s
  have equal : {x | walk (n+1) x ∧ ∀ j, walk j x → n+1 ≤ j} =
      (fun c => v (readCode c)) '' (shell : Set Code) := by
    ext x
    constructor
    · rintro ⟨w,hmin⟩
      obtain ⟨s,rfl⟩ := realized _ _ w
      refine ⟨code s,Finset.mem_sdiff.mpr ⟨(mem _ _).mpr ⟨_,le_rfl,w⟩,?_⟩,(eqv _ _).mp (restore _)⟩
      intro hold
      obtain ⟨j,hj,h⟩ := (mem _ _).mp hold
      have := hmin j h
      omega
    · rintro ⟨c,hc,rfl⟩
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hc
      rw [← rep c hc] at hin hout
      obtain ⟨j,hj,w⟩ := (mem _ _).mp hin
      have low (i) (h : walk i (v (readCode c))) : n+1 ≤ i := by
        by_contra! hi
        exact hout ((mem _ _).mpr ⟨i,by omega,h⟩)
      have eq : j = n+1 := le_antisymm hj (low _ w)
      exact ⟨eq ▸ w,low⟩
  rw [equal,Set.ncard_image_of_injOn,Set.ncard_coe_finset]
  intro c hc d hd he
  exact (rep _ hc).symm.trans (((eqv _ _).mpr he).trans (rep _ hd))

theorem row_shell_card (n : ℕ) :
    {v | OrbitGuard.Nearest (vertex five) (n+1) v}.ncard =
      (rowBall (n+1) \ rowBall n).card :=
  count_shell vertex rowKey rowKey_iff rowKey_read rowWalk
    (fun _ _ w => by obtain ⟨s,_,h⟩ := OrbitGuard.lift_walk w five rfl; exact ⟨s,h⟩)
    rowBall rowBall_spec n

theorem affine_shell_card (n : ℕ) :
    {v | Nearest (key five) (n+1) v}.ncard = (affineBall (n+1) \ affineBall n).card :=
  count_shell key affineKey affineKey_iff affineKey_read affineWalk
    (fun _ _ w => by obtain ⟨a,_,h⟩ := lift_walk w five rfl; exact ⟨_,h⟩)
    affineBall affineBall_spec n

end AffineGuard.Census
