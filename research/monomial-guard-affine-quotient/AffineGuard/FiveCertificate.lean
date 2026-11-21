import AffineGuard.FiveShells
import AffineGuard.FiveTable

namespace AffineGuard.Census
open Finset
open OrbitGuard.Examples (five)

section Verify

variable (rowAt affineAt : ℕ → Code) (edgesAt : ℕ → List ℕ) (parentAt : ℕ → ℕ)

def MoveCheck (i : ℕ) : Prop :=
  (paidGates.map fun g => rowKey (g.act (readCode (rowAt i)))) = (edgesAt i).map rowAt

def AffineCheck (i : ℕ) : Prop := affineKey (readCode (rowAt i)) = affineAt i

/-- The first k entries as a set, preserving the mathematical equality on complete five-row codes. -/
def entries (table : ℕ → Code) (k : ℕ) : Finset Code := (range k).image table

/-- Each outgoing index of the old ball lies in the new one. Each new index has a recorded parent. -/
def Coverage (k l : ℕ) : Prop :=
  (∀ i : Fin k, ∀ j ∈ edgesAt i, j < l) ∧
  (∀ j : Fin l, j.val < k ∨ (parentAt j < k ∧ j.val ∈ edgesAt (parentAt j)))

attribute [local irreducible] rowKey affineKey readCode

theorem expand_table {n k l : ℕ} (old : rowBall n = entries rowAt k) (inc : k ≤ l)
    (moves : ∀ i : Fin k, MoveCheck rowAt edgesAt i) (cover : Coverage edgesAt parentAt k l) :
    rowBall (n+1) = entries rowAt l := by
  have neighbors (i : Fin k) (x : Code) :
      x ∈ successors (rowAt i) ↔ ∃ j ∈ edgesAt i, rowAt j = x := by
    have hm := moves i
    unfold MoveCheck at hm
    simp only [successors, hm, List.mem_toFinset, List.mem_map]
  apply Finset.ext
  intro x
  simp only [rowBall, old, Finset.mem_union, Finset.mem_biUnion, entries, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i,hi,rfl⟩ | ⟨_,⟨i,hi,rfl⟩,h⟩)
    · exact ⟨i,lt_of_lt_of_le hi inc,rfl⟩
    · obtain ⟨j,hj,rfl⟩ := (neighbors ⟨i,hi⟩ _).mp h
      exact ⟨j,cover.1 ⟨i,hi⟩ j hj,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    rcases cover.2 ⟨j,hj⟩ with small | ⟨hi,he⟩
    · exact Or.inl ⟨j,small,rfl⟩
    · exact Or.inr ⟨_,⟨_,hi,rfl⟩,(neighbors ⟨_,hi⟩ _).mpr ⟨j,he,rfl⟩⟩

private theorem map_entries (f : Code → Code) {s : Finset Code} {k : ℕ}
    (old : s = entries rowAt k) (h : ∀ i : Fin k, f (rowAt i) = affineAt i) :
    s.image f = entries affineAt k := by
  subst s
  simp only [entries,Finset.image_image]
  exact Finset.image_congr fun i hi => h ⟨i,Finset.mem_range.mp hi⟩

theorem project_table {n k : ℕ} (old : rowBall n = entries rowAt k)
    (values : ∀ i : Fin k, AffineCheck rowAt affineAt i) : affineBall n = entries affineAt k := by
  unfold affineBall
  exact map_entries rowAt affineAt (fun c => affineKey (readCode c)) old values

end Verify

def rowAt (i : ℕ) : Code := Table.rows[i]?.getD []
def affineAt (i : ℕ) : Code := Table.affine[i]?.getD []
def edgesAt (i : ℕ) : List ℕ := Table.edges[i]?.getD []
def parentAt (i : ℕ) : ℕ := Table.parent[i]?.getD 0

end AffineGuard.Census
