import OrbitGuard.Solver
import Mathlib.Data.Fintype.Perm

namespace OrbitGuard
open Ternary Finset
variable {m : ℕ} {D : Type*} [Fintype D]

/-- After separation, every proper prefix minor is determined by its scalar sum. -/
def orderOK (s : State (Fin m) D) (e : Equiv.Perm (Fin m)) : Bool :=
  decide (∀ k : Fin m, (∑ i ∈ HZ.prefixSet m k.val, scalar (s.permute e) i) ≠ 1)

theorem orderOK_iff (s : State (Fin m) D) (hs : HZ.Separated s) (e : Equiv.Perm (Fin m)) :
    orderOK s e = true ↔ HZ.Passes (s.permute e) := by
  have sep : HZ.Separated (s.permute e) := fun i => hs (e i)
  simp only [orderOK,decide_eq_true_eq]
  constructor
  · intro h k hk a
    rw [minor_separated _ sep]
    exact sub_ne_zero.mpr (Ne.symm (h ⟨k,hk⟩))
  · intro h k
    have hp := h k k.isLt 0
    rw [minor_separated _ sep] at hp
    exact Ne.symm (sub_ne_zero.mp hp)

/-- Optional final free permutation in the original numbered-coordinate model. -/
def finishOrder (s : State (Fin m) D) : Option (Equiv.Perm (Fin m)) :=
  (permsOfList (List.finRange m)).find? (orderOK s)

theorem finishOrder_correct (s : State (Fin m) D) (hs : HZ.Separated s) (hg : FullGuard s) :
    ∃ e, finishOrder s = some e ∧ HZ.Passes (s.permute e) := by
  obtain ⟨j,f,hf⟩ := hg
  have eq : j = m := by simpa using Fintype.card_congr f
  subst j
  have hmem : f ∈ permsOfList (List.finRange m) := mem_permsOfList_of_mem (by simp)
  have he : (finishOrder s).isSome := List.find?_isSome.mpr ⟨f,hmem,(orderOK_iff s hs f).mpr hf⟩
  obtain ⟨e,ho⟩ := Option.isSome_iff_exists.mp he
  exact ⟨e,ho,(orderOK_iff s hs e).mp (List.find?_some (p := orderOK s) ho)⟩

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

end OrbitGuard
