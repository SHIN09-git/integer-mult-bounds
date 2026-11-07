import Ternary.Envelope
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OrbitGuard
open Finset Ternary
abbrev State (I D : Type*) := HZ.State I F (D → F)
abbrev Row (D : Type*) := F × (D → F) × F

def row (s : State I D) (i : I) : Row D := (s.u i,s.w i,s.b i)
def flip (r : Row D) : Row D := (-r.1,-r.2.1,-r.2.2)

@[simp] theorem flip_flip (r : Row D) : flip (flip r) = r := by simp [flip]

def tag [Fintype D] (r : Row D) : Finset (Row D) := {r,flip r}

@[simp] theorem tag_flip [Fintype D] (r : Row D) : tag (flip r) = tag r := by
  simp [tag,Finset.pair_comm]

theorem tag_eq_iff [Fintype D] (r t : Row D) : tag r = tag t ↔ t = r ∨ t = flip r := by
  constructor
  · intro h
    have ht : t ∈ tag r := h ▸ (by simp [tag])
    simpa [tag] using ht
  · rintro (rfl|rfl) <;> simp

def bag [Fintype I] (f : I → A) : Multiset A := ∑ i, {f i}

theorem bag_count [Fintype I] [DecidableEq A] (f : I → A) (v : A) :
    (bag f).count v = Fintype.card {i // f i = v} := by
  rw [bag,Multiset.count_sum',Fintype.card_subtype]
  simp [Multiset.count_singleton,eq_comm]

theorem match_bag [Fintype I] [DecidableEq A] (f g : I → A) (h : bag f = bag g) :
    ∃ e : Equiv.Perm I, ∀ i, f (e i) = g i := by
  classical
  have card (v : A) : Fintype.card {i // g i = v} = Fintype.card {i // f i = v} := by
    rw [← bag_count,← bag_count,h]
  let fibers (v : A) := Fintype.equivOfCardEq (card v)
  exact ⟨Equiv.ofFiberEquiv fibers, Equiv.ofFiberEquiv_map fibers⟩

def signature [Fintype I] [Fintype D] (s : State I D) := bag (fun i => tag (row s i))

/-- Realized signatures contain every row, including its unscaled primal and both dual components. -/
def Vertex (I D : Type*) [Fintype I] [Fintype D] :=
  {k : Multiset (Finset (Row D)) // ∃ s : State I D, signature s = k}

instance [Fintype I] [Fintype D] : DecidableEq (Vertex I D) := fun x y =>
  decidable_of_iff (x.val = y.val) Subtype.ext_iff.symm

def vertex [Fintype I] [Fintype D] (s : State I D) : Vertex I D := ⟨signature s,s,rfl⟩

structure Frame (I : Type*) where
  perm : Equiv.Perm I
  factor : I → F
  nonzero : ∀ i, factor i ≠ 0

def Frame.act (q : Frame I) (s : State I D) : State I D := (s.permute q.perm).scale q.factor

theorem Frame.run [DecidableEq I] (q : Frame I) (s : State I D) : HZ.Run s 0 (q.act s) :=
  HZ.Run.cons s (.permute q.perm) (HZ.Run.cons _ (.scale q.factor q.nonzero) (HZ.Run.nil _))

theorem signs : ∀ a : F, a ≠ 0 → a = 1 ∨ a = -1 := by decide

def changeRow (c : F) (r : Row D) : Row D := (c*r.1,c⁻¹ • r.2.1,c⁻¹*r.2.2)

@[simp] theorem change_one (r : Row D) : changeRow 1 r = r := by simp [changeRow]
@[simp] theorem change_neg (r : Row D) : changeRow (-1) r = flip r := by simp [changeRow,flip]

theorem row_act (q : Frame I) (s : State I D) (i : I) :
    row (q.act s) i = changeRow (q.factor i) (row s (q.perm i)) := rfl

theorem signature_act [Fintype I] [Fintype D] (q : Frame I) (s : State I D) :
    signature (q.act s) = signature s := by
  unfold signature bag
  have h (i : I) : tag (row (q.act s) i) = tag (row s (q.perm i)) := by
    rw [row_act]
    rcases signs _ (q.nonzero i) with e|e <;> rw [e] <;> simp
  simp only [h]
  exact Equiv.sum_comp q.perm (fun i => ({tag (row s i)} : Multiset _))

theorem vertex_frame [Fintype I] [Fintype D] (q : Frame I) (s : State I D) :
    vertex (q.act s) = vertex s := Subtype.ext (signature_act q s)

theorem vertex_eq_iff_frame [Fintype I] [Fintype D] (s t : State I D) :
    vertex s = vertex t ↔ ∃ q : Frame I, q.act s = t := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := match_bag (fun i => tag (row s i)) (fun i => tag (row t i)) (congrArg Subtype.val h)
    let c (i : I) : F := if row (s.permute e) i = row t i then 1 else -1
    have hc (i : I) : c i ≠ 0 := by unfold c; split <;> decide
    let q : Frame I := ⟨e,c,hc⟩
    have hr (i : I) : row (q.act s) i = row t i := by
      rw [row_act]
      change changeRow (if row s (e i) = row t i then 1 else -1) (row s (e i)) = _
      split
      · rename_i heq; simpa using heq
      · rename_i hne
        exact (change_neg _).trans (((tag_eq_iff _ _).mp (he i)).resolve_left (Ne.symm hne)).symm
    exact ⟨q,HZ.State.ext (funext (fun i => congrArg Prod.fst (hr i)))
      (funext (fun i => congrArg (fun r => r.2.1) (hr i)))
      (funext (fun i => congrArg (fun r => r.2.2) (hr i)))⟩
  · rintro ⟨q,rfl⟩
    exact (vertex_frame q s).symm

theorem vertex_permute [Fintype I] [Fintype D] (s : State I D) (e : Equiv.Perm I) :
    vertex (s.permute e) = vertex s := Equiv.sum_comp e (fun i => ({tag (row s i)} : Multiset _)) |> Subtype.ext

theorem vertex_scale [Fintype I] [Fintype D] (s : State I D) (c : I → F) (hc : ∀ i, c i ≠ 0) :
    vertex (s.scale c) = vertex s := vertex_frame ⟨Equiv.refl I,c,hc⟩ s

end OrbitGuard
