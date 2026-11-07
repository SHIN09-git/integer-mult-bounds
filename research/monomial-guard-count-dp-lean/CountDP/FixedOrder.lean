import CountDP.Operations
import GuardDP.Guards

open Finset
namespace CountDP

attribute [local irreducible] zeroGroups realGroups compressed

private theorem before_last {c i : Fin m} {k : ℕ} (hk : k < m) (hi : i ∈ HZ.prefixSet m k) :
    Equiv.swap (GuardDP.lastRow c) c i ≠ c := by
  intro he
  have hlast : Equiv.swap (GuardDP.lastRow c) c (GuardDP.lastRow c) = c := by simp
  have hi' := (Equiv.swap (GuardDP.lastRow c) c).injective (he.trans hlast.symm)
  have hv : i.val < k := (mem_filter.mp hi).2
  rw [hi'] at hv
  change m - 1 < k at hv
  omega

section
variable {K D : Type*} [Field K] [Fintype D] [DecidableEq K]

def anchoredWord (s : HZ.State (Fin m) K (D → K)) (c : Fin m) : GuardDP.FixedWord m K :=
  ⟨separationWord s, some (GuardDP.lastRow c, c)⟩

theorem anchoredWord_optimal (s : HZ.State (Fin m) K (D → K)) (c : Fin m)
    (ha : HZ.Anchored s c) (hs : ∑ i, s.charge i = 0) :
    let w := anchoredWord s c
    (∀ g ∈ w.additions, g.Legal) ∧ HZ.Passes (w.result s) ∧
    w.additions.length = HZ.activeCount s - HZ.partitionCount s ∧
    ∀ n t, HZ.Run s n t → HZ.Passes t → w.additions.length ≤ n := by
  let w := anchoredWord s c
  let t := GuardDP.execute s (separationWord s)
  have opt := separationWord_optimal s hs
  have hc : s.charge c = 0 := by simp [HZ.State.charge, ha.zeroSlope]
  have hb : t.b = s.b := by
    change (GuardDP.execute s (GuardDP.emit s (GuardDP.schedule (zeroGroups s.charge)))).b = s.b
    rw [GuardDP.execute_emit]
    apply GuardDP.runPlan_preserves_b
    intro p hp
    have hm := GuardDP.schedule_target _ hp
    rw [(zero_optimal s.charge hs).full ((Dummy.sum_active _).trans hs)] at hm
    have hp0 : s.charge p.1 ≠ 0 := by simpa [HZ.active] using hm
    exact ha.supported _ (fun he => hp0 (he ▸ hc))
  refine ⟨opt.legal, ?_, opt.length_eq, fun n r hr hp => opt.length_eq ▸
    (HZ.anchored_guard_optimal s c ha hs).2 n r hr hp⟩
  intro k hk a
  have hsep : HZ.Separated (w.result s) := fun i => opt.reaches (w.order i)
  have hz : ∀ i ∈ HZ.prefixSet m k, (w.result s).b i = 0 := by
    intro i hi
    change t.b (Equiv.swap (GuardDP.lastRow c) c i) = 0
    rw [hb]
    exact ha.supported _ (before_last hk hi)
  rw [HZ.separated_minor_one (w.result s) hsep _ hz a]
  exact one_ne_zero
end

section
variable {R : Type*} [Fintype R]

def binaryWord (s : HZ.State (Fin m) Binary.F (R → Binary.F)) : GuardDP.FixedWord m Binary.F :=
  let w := concentrationWord s 1
  let c := (GuardDP.labels (GuardDP.execute s w).charge).head?
  ⟨w, c.map (fun i => (GuardDP.lastRow i, i))⟩

theorem binaryWord_optimal [Nonempty R] (s : HZ.State (Fin m) Binary.F (R → Binary.F))
    (hs : Binary.Normalized s) :
    let w := binaryWord s
    (∀ g ∈ w.additions, g.Legal) ∧ Binary.Passes (w.result s) ∧
    w.additions.length = HZ.activeCount s - Dummy.Zstar s.charge 1 ∧
    ∀ n t, HZ.Run s n t → Binary.Passes t → w.additions.length ≤ n := by
  let w := binaryWord s
  let t := GuardDP.execute s (concentrationWord s 1)
  have opt := concentrationWord_optimal s 1 one_ne_zero hs
  obtain ⟨c, hc⟩ := opt.reaches
  change ∀ i, t.charge i = _ at hc
  have hset : (univ.filter (fun i => t.charge i ≠ 0)) = {c} := by
    ext i
    by_cases h : i = c <;> simp [hc, h]
  have hlabels : GuardDP.labels t.charge = [c] := by simp [GuardDP.labels, hset]
  have horder : w.order = Equiv.swap (GuardDP.lastRow c) c := by
    change (GuardDP.FixedWord.mk _ ((GuardDP.labels t.charge).head?.map _)).order = _
    rw [hlabels]
    rfl
  refine ⟨opt.legal, ?_, opt.length_eq, fun n r hr hp => opt.length_eq ▸
    (Binary.fixed_order_optimal s hs).2 n r hr hp⟩
  intro k hk r
  rw [Binary.principalMinor_eq, Binary.guard_scalar]
  apply sum_eq_zero
  intro i hi
  have hz := hc (w.order i)
  rw [if_neg (horder ▸ before_last hk hi)] at hz
  exact congrFun hz r
end

end CountDP
