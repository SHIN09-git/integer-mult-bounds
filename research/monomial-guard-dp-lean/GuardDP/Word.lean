import HZ.Operations
import Mathlib.Data.Finset.Sort

open Finset
namespace GuardDP

/-- An emitted instruction contains both real row indices and its field coefficient. -/
structure Gate (I K : Type*) where
  target : I
  source : I
  coefficient : K
  deriving Repr, DecidableEq

def Gate.Legal [Zero K] (g : Gate I K) : Prop := g.target ≠ g.source ∧ g.coefficient ≠ 0

abbrev Plan (I : Type*) := List (I × I)

section
variable {I K V : Type*} [DecidableEq I] [Field K] [AddCommGroup V] [Module K V]

def instruction (s : HZ.State I K V) (p : I × I) : Gate I K :=
  ⟨p.1, p.2, -s.u p.1 / s.u p.2⟩

def Gate.act (g : Gate I K) (s : HZ.State I K V) : HZ.State I K V :=
  s.addRow g.target g.source g.coefficient

def execute (s : HZ.State I K V) : List (Gate I K) → HZ.State I K V
  | [] => s
  | g :: gs => execute (g.act s) gs

def runPlan (s : HZ.State I K V) : Plan I → HZ.State I K V
  | [] => s
  | p :: ps => runPlan ((instruction s p).act s) ps

def emit (s : HZ.State I K V) : Plan I → List (Gate I K)
  | [] => []
  | p :: ps => let g := instruction s p; g :: emit (g.act s) ps

def Feasible (s : HZ.State I K V) : Plan I → Prop
  | [] => True
  | p :: ps => (instruction s p).Legal ∧ Feasible ((instruction s p).act s) ps

theorem emit_length (s : HZ.State I K V) (ps : Plan I) : (emit s ps).length = ps.length := by
  induction ps generalizing s <;> simp_all [emit]

theorem execute_emit (s : HZ.State I K V) (ps : Plan I) :
    execute s (emit s ps) = runPlan s ps := by
  induction ps generalizing s <;> simp_all [execute, emit, runPlan]

theorem emit_legal (s : HZ.State I K V) (ps : Plan I) (hf : Feasible s ps) :
    ∀ g ∈ emit s ps, g.Legal := by
  induction ps generalizing s with
  | nil => simp [emit]
  | cons p ps ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hf.1
    · exact ih _ hf.2 _ hg

theorem execute_run (s : HZ.State I K V) (gs : List (Gate I K)) (hl : ∀ g ∈ gs, g.Legal) :
    HZ.Run s gs.length (execute s gs) := by
  induction gs generalizing s with
  | nil => exact .nil s
  | cons g gs ih =>
    obtain ⟨hne, hcoeff⟩ := hl g List.mem_cons_self
    have ht := ih (g.act s) (fun g hg => hl g (List.mem_cons_of_mem _ hg))
    simpa [HZ.Operation.cost, Nat.add_comm] using
      HZ.Run.cons s (.add g.target g.source g.coefficient hne hcoeff) ht

theorem runPlan_append (s : HZ.State I K V) (ps qs : Plan I) :
    runPlan s (ps ++ qs) = runPlan (runPlan s ps) qs := by
  induction ps generalizing s <;> simp_all [runPlan]

theorem feasible_append (s : HZ.State I K V) (ps qs : Plan I) :
    Feasible s (ps ++ qs) ↔ Feasible s ps ∧ Feasible (runPlan s ps) qs := by
  induction ps generalizing s <;> simp_all [Feasible, runPlan, and_assoc]

/-- Gather distinct target rows into a donor whose primal coordinate stays nonzero. -/
theorem gather_spec (j : I) (xs : List I) (s : HZ.State I K V) (hn : xs.Nodup) (hj : j ∉ xs)
    (hd : s.u j ≠ 0) (hu : ∀ i ∈ xs, s.u i ≠ 0) :
    let ps := xs.map (fun i => (i, j))
    Feasible s ps ∧ ∀ k, (runPlan s ps).charge k =
      if k = j then (∑ i ∈ xs.toFinset, s.charge i) + s.charge j
      else if k ∈ xs then 0 else s.charge k := by
  induction xs generalizing s with
  | nil =>
    refine ⟨trivial, ?_⟩
    intro k
    by_cases h : k = j <;> simp_all [runPlan]
  | cons i xs ih =>
    obtain ⟨hi, hnd⟩ := List.nodup_cons.mp hn
    have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self)
    have hj' : j ∉ xs := fun h => hj (List.mem_cons_of_mem _ h)
    let q := (instruction s (i, j)).act s
    obtain ⟨ha, _, hdonor, hzero, hcharge⟩ := HZ.elimination s hji.symm (hu i List.mem_cons_self) hd
    have hu' : ∀ k ∈ xs, q.u k ≠ 0 := by
      intro k hk
      have hki : k ≠ i := fun e => hi (e ▸ hk)
      simpa [q, instruction, Gate.act, HZ.State.addRow, hki] using hu k (List.mem_cons_of_mem _ hk)
    obtain ⟨hf, hout⟩ := ih q hnd hj' (hdonor ▸ hd) hu'
    refine ⟨⟨⟨hji.symm, ha⟩, hf⟩, ?_⟩
    intro k
    simp only [List.map_cons, runPlan]
    rw [hout]
    by_cases hkj : k = j
    · subst k
      have he : ∑ k ∈ xs.toFinset, q.charge k = ∑ k ∈ xs.toFinset, s.charge k := by
        apply sum_congr rfl
        intro k hk
        have hx := List.mem_toFinset.mp hk
        exact HZ.charge_add_outside (i := i) (j := j) s _ (fun e => hi (e ▸ hx)) (fun e => hj' (e ▸ hx))
      change q.charge j = _ at hcharge
      simp [he, hcharge, hi]
      abel
    · by_cases hki : k = i
      · subst k
        simp [hkj, hi, show q.charge i = 0 from hzero]
      · simp [hkj, hki, show q.charge k = s.charge k from HZ.charge_add_outside s _ hki hkj]

/-- Every target touched by the plan initially has scalar carrier row zero. -/
theorem runPlan_preserves_b (s : HZ.State I K V) (ps : Plan I)
    (hb : ∀ p ∈ ps, s.b p.1 = 0) : (runPlan s ps).b = s.b := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have h : ((instruction s p).act s).b = s.b := by
      funext k
      by_cases hk : k = p.2 <;> simp [Gate.act, instruction, HZ.State.addRow, hb p List.mem_cons_self, hk]
    exact (ih _ (by intro q hq; rw [h]; exact hb q (List.mem_cons_of_mem _ hq))).trans h

end

section
variable [LinearOrder I]
/-- Use the least label as the donor and visit the other real labels in order. -/
def blockPlan (B : Finset I) : Plan I :=
  if h : B.Nonempty then ((B.erase (B.min' h)).sort (· ≤ ·)).map (fun i => (i, B.min' h))
  else []

theorem blockPlan_length (B : Finset I) (hb : B.Nonempty) :
    (blockPlan B).length + 1 = B.card := by
  simpa [blockPlan, hb] using card_erase_add_one (B.min'_mem hb)

theorem blockPlan_target (B : Finset I) {p : I × I} (hp : p ∈ blockPlan B) : p.1 ∈ B := by
  by_cases h : B.Nonempty
  · simp only [blockPlan, dif_pos h, List.mem_map, mem_sort] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact mem_of_mem_erase hi
  · simp [blockPlan, h] at hp

variable [Field K] [AddCommGroup V] [Module K V]

theorem blockPlan_spec (B : Finset I) (hb : B.Nonempty) (s : HZ.State I K V)
    (ha : ∀ i ∈ B, s.charge i ≠ 0) :
    Feasible s (blockPlan B) ∧ ∀ k, (runPlan s (blockPlan B)).charge k =
      if k = B.min' hb then ∑ i ∈ B, s.charge i else if k ∈ B then 0 else s.charge k := by
  let j := B.min' hb
  have hj : j ∈ B := B.min'_mem hb
  have hu (i : I) (hi : i ∈ B) : s.u i ≠ 0 := by
    intro hz
    exact ha i hi (by simp [HZ.State.charge, hz])
  obtain ⟨hf, hc⟩ := gather_spec j ((B.erase j).sort (· ≤ ·)) s (sort_nodup ..)
    (by simp) (hu j hj) (by intro i hi; exact hu i (mem_of_mem_erase ((mem_sort _).mp hi)))
  rw [blockPlan, dif_pos hb]
  refine ⟨hf, ?_⟩
  intro k
  change _ = if k = j then _ else _
  rw [hc]
  simp only [sort_toFinset, mem_sort, mem_erase, sum_erase_add _ _ hj]
  by_cases hk : k = j <;> simp [hk]

end
end GuardDP
