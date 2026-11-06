import Ternary.Guard

open Finset
namespace Ternary
variable {I D : Type*} [DecidableEq I] [Fintype I] [Fintype D]

/-- The true full-family guard cost, with free final coordinate ordering. -/
noncomputable def C (s : HZ.State I F (D → F)) : ℕ :=
  sInf {n | ∃ t, HZ.Run s n t ∧ FullGuard t}

theorem guard_lower_bound {s t : HZ.State I F (D → F)} {n : ℕ}
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    (hr : HZ.Run s n t) (hg : FullGuard t) : max (S s) (L s) ≤ n := by
  have hyt : ∑ i, t.charge i = 0 := hr.total_charge.trans hy
  have hnt : ∑ i, scalar t i = 1 := (scalar_total hr).trans hn
  have hsep := fullguard_separated t hyt hg
  have hS : S s ≤ n := HZ.cost_lower_bound hr hsep
  have hL : L t = 0 := by
    rcases fullguard_imbalance t hnt hg with he | he <;> simp [L, price, he]
  have hb := (run_price hr).2
  omega

theorem guard_upper_attained (s : HZ.State I F (D → F))
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    ∃ n t, HZ.Run s n t ∧ FullGuard t ∧ n ≤ 2 * S s + L s := by
  obtain ⟨r, hr, hsep, _, _⟩ := HZ.cost_attained s hy
  change HZ.Run s (S s) r at hr
  have hnr : ∑ i, scalar r i = 1 := (scalar_total hr).trans hn
  obtain ⟨t, ht, htsep, hd⟩ := separated_repair r hnr hsep
  refine ⟨S s + L r, t, hr.trans ht, separated_good_fullguard t htsep hd, ?_⟩
  have hb := (run_price hr).1
  omega

theorem C_attained (s : HZ.State I F (D → F))
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    ∃ t, HZ.Run s (C s) t ∧ FullGuard t := by
  obtain ⟨n, t, hr, hg, _⟩ := guard_upper_attained s hy hn
  exact Nat.sInf_mem (show {n | ∃ t, HZ.Run s n t ∧ FullGuard t}.Nonempty from
    ⟨n, t, hr, hg⟩)

/-- The ternary full-flat envelope, with h-Z as S and the signed scalar formula as L. -/
theorem envelope (s : HZ.State I F (D → F))
    (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    max (S s) (L s) ≤ C s ∧ C s ≤ 2 * S s + L s := by
  constructor
  · obtain ⟨t, hr, hg⟩ := C_attained s hy hn
    exact guard_lower_bound hy hn hr hg
  · obtain ⟨n, t, hr, hg, hb⟩ := guard_upper_attained s hy hn
    exact (Nat.sInf_le (show n ∈ {n | ∃ t, HZ.Run s n t ∧ FullGuard t} from ⟨t, hr, hg⟩)).trans hb

omit [DecidableEq I] [Fintype I] in
/-- Existential free ordering has exactly the original fixed-order operational cost. -/
theorem fullguard_run_iff {m n : ℕ} (s : HZ.State (Fin m) F (D → F)) :
    (∃ t, HZ.Run s n t ∧ FullGuard t) ↔ (∃ t, HZ.Run s n t ∧ HZ.Passes t) := by
  constructor
  · rintro ⟨t, hr, j, e, he⟩
    have hj : j = m := by simpa using Fintype.card_congr e
    subst j
    refine ⟨t.permute e, ?_, he⟩
    have hf := HZ.Run.cons t (HZ.Operation.permute e) (HZ.Run.nil (t.permute e))
    simpa [HZ.Operation.cost] using hr.trans hf
  · rintro ⟨t, hr, hp⟩
    exact ⟨t, hr, m, Equiv.refl _, hp⟩

end Ternary
