import Ternary.Envelope
import Mathlib.Algebra.BigOperators.Pi

namespace AffineGuard.OneParameter
open Finset Ternary

abbrev Pencil (I : Type*) := HZ.State I F (Fin 1 → F)

def slope (s : Pencil I) (i : I) : F := s.charge i 0
def packet (s : Pencil I) (i : I) : F × F := (slope s i, scalar s i)

def Normalized [Fintype I] (s : Pencil I) : Prop := (∑ i, s.charge i) = 0 ∧ (∑ i, scalar s i) = 1

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem packet_total {s t : Pencil I} {n} (r : HZ.Run s n t) :
    ∑ i, packet t i = ∑ i, packet s i := by
  apply Prod.ext
  · simpa [Prod.fst_sum,packet,slope,Finset.sum_apply] using congrFun r.total_charge 0
  · simpa [Prod.snd_sum,packet] using scalar_total r

omit [DecidableEq I] [Fintype I] in
theorem outside_packet {A : Finset I} {s t : Pencil I} (h : HZ.AgreeOutside A s t)
    (i : I) (hi : i ∉ A) : packet t i = packet s i := by
  obtain ⟨u,w,b⟩ := h i hi
  simp [packet,slope,HZ.State.charge,scalar,u,w,b]

/-- Gather a block whose primal entries are nonzero. The pivot receives both block sums. -/
theorem concentrate (s : Pencil I) (B : Finset I) (j : I) (hj : j ∈ B)
    (hu : ∀ i ∈ B, s.u i ≠ 0) :
    ∃ t, HZ.Run s (B.card-1) t ∧ HZ.AgreeOutside B s t ∧
      (∀ i ∈ B, i ≠ j → packet t i = 0) ∧ packet t j = ∑ i ∈ B, packet s i := by
  obtain ⟨t,hr,hU,hW,hB,_,_⟩ := HZ.gather (B.erase j) j s (hu j hj)
    (notMem_erase _ _) (fun i hi => hu i (mem_of_mem_erase hi))
  have out : HZ.AgreeOutside B s t := by
    intro i hi
    have ij : i ≠ j := fun e => hi (e ▸ hj)
    exact ⟨by rw [hU]; simp [hi],hW i ij,hB i ij⟩
  have zero (i) (hi : i ∈ B) (ij : i ≠ j) : packet t i = 0 := by
    simp [packet,slope,HZ.State.charge,scalar,hU,hi,ij]
  refine ⟨t,by simpa [card_erase_of_mem hj] using hr,out,zero,?_⟩
  have total := packet_total hr
  have outside : ∑ i ∈ Bᶜ, packet t i = ∑ i ∈ Bᶜ, packet s i :=
    sum_congr rfl fun i hi => outside_packet out i (mem_compl.mp hi)
  rw [← sum_add_sum_compl B, ← sum_add_sum_compl B (packet s), outside] at total
  have block := add_right_cancel total
  rw [← block]
  symm
  exact Finset.sum_eq_single_of_mem j hj zero

theorem normalize_run {s t : Pencil I} {n} (hs : Normalized s) (r : HZ.Run s n t) :
    Normalized t := ⟨r.total_charge.trans hs.1,(scalar_total r).trans hs.2⟩

end AffineGuard.OneParameter
