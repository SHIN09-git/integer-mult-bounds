import Dummy.Partitions

open Finset
namespace Dummy
variable {I K V : Type*} [DecidableEq I] [Fintype I]
  [Field K] [AddCommGroup V] [Module K V]

/-- A single real coordinate carries the prescribed total. -/
def Concentrated (s : HZ.State I K V) (τ : V) : Prop :=
  ∃ c : I, ∀ i, s.charge i = if i = c then τ else 0

/-- The dummy appears in partitions only. The execution itself is on the original I. -/
theorem execution_partition {s t : HZ.State I K V} {n : ℕ} {τ : V}
    (hr : HZ.Run s n t) (ht : Concentrated t τ) :
    ∃ P : Finpartition (univ : Finset (Option I)), HZ.ZeroSum (augment s.charge τ) P ∧
      Fintype.card (Option I) ≤ n + 1 + P.parts.card := by
  classical
  induction hr with
  | nil s =>
    obtain ⟨c, ht⟩ := ht
    let Q : Finpartition (univ : Finset (Option I)) := ⊥
    have hn : {none} ∈ Q.parts := by simp [Q]
    have hc : {some c} ∈ Q.parts := by simp [Q]
    have hne : ({none} : Finset (Option I)) ≠ {some c} := by simp
    let P := HZ.mergeParts Q {none} {some c} hn hc hne
    have hcard : P.parts.card + 1 = Fintype.card (Option I) := by
      simpa [P, Q] using HZ.mergeParts_card Q {none} {some c} hn hc hne
    refine ⟨P, ?_, by omega⟩
    intro B hB
    rw [HZ.mergeParts_parts] at hB
    rcases mem_insert.mp hB with rfl | hB
    · simp [augment, ht]
    · obtain ⟨hBc, hBn, hBQ⟩ := mem_erase.mp hB |>.imp_right mem_erase.mp
      obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hBQ
      cases i with
      | none => exact False.elim (hBn rfl)
      | some i =>
        have hi : i ≠ c := by intro he; subst i; exact hBc rfl
        simp [augment, ht, hi]
  | @cons s g n t tail ih =>
    obtain ⟨P, hp, hn⟩ := ih ht
    cases g with
    | add i j a hij ha =>
      obtain ⟨Q, hq, hc⟩ := HZ.pullback_pair (augment s.charge τ)
        (augment (s.addRow i j a).charge τ) (i := some i) (j := some j)
        (by simpa using hij)
        (by
          intro k hki hkj
          cases k with
          | none => rfl
          | some k =>
            exact (HZ.charge_add_outside s a (by simpa using hki) (by simpa using hkj)).symm)
        (by simpa using (HZ.charge_add_pair s a hij).symm) P hp
      exact ⟨Q, hq, by simp only [HZ.Operation.cost]; omega⟩
    | permute e =>
      simp only [HZ.Operation.apply] at hp
      have he : augment (s.permute e).charge τ = augment s.charge τ ∘ e.optionCongr := by
        funext i
        cases i <;> rfl
      rw [he] at hp
      exact ⟨HZ.permPartition P e.optionCongr,
        HZ.zeroSum_permPartition (augment s.charge τ) P e.optionCongr hp,
        by simpa [HZ.Operation.cost, HZ.permPartition_card] using hn⟩
    | scale c hc =>
      refine ⟨P, ?_, by simpa [HZ.Operation.cost] using hn⟩
      simp only [HZ.Operation.apply] at hp
      have he : augment (s.scale c).charge τ = augment s.charge τ := by
        funext i
        cases i <;> simp [HZ.charge_scale s c hc]
      simpa [he] using hp

/-- Every legal real-coordinate execution obeys h-Z*, including arbitrary free operations. -/
theorem cost_lower_bound {s t : HZ.State I K V} {n : ℕ} {τ : V}
    (hτ : τ ≠ 0) (hr : HZ.Run s n t) (ht : Concentrated t τ) :
    HZ.activeCount s - Zstar s.charge τ ≤ n := by
  obtain ⟨P, hp, hn⟩ := execution_partition hr ht
  have hh := HZ.active_bound (augment s.charge τ) P hp hn
  rw [active_augment_card s.charge τ hτ] at hh
  change (HZ.active s.charge).card + 1 - Zstar s.charge τ ≤ n + 1 at hh
  change (HZ.active s.charge).card - Zstar s.charge τ ≤ n
  omega

end Dummy

