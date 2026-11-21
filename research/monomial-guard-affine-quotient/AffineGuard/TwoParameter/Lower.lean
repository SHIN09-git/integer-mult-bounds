import AffineGuard.TwoParameter.Upper

namespace AffineGuard.TwoParameter
open Finset Ternary

/-- Linear independence of the two slope columns. -/
def RankTwo (s : Flat I) : Prop :=
  ∀ a b : F, (∀ i, a*s.w i 0+b*s.w i 1=0) → a=0 ∧ b=0

/-- If every nonempty zero-slope block needs at least h rows, a legal run to a
passing state leaves room for at most card(I)/h independent components. -/
theorem component_bound {I : Type*} [DecidableEq I] [Fintype I] (s : Flat I) (hs : Normalized s)
    (h : ℕ) (minSize : ∀ B : Finset I, B.Nonempty → ∑ i ∈ B, slope s i=0 → h ≤ B.card) :
    h*(Fintype.card I - C s) ≤ Fintype.card I := by
  obtain ⟨t,r,g⟩ := C_attained s hs.1 hs.2
  obtain ⟨P,zero,count⟩ := HZ.execution_partition r (fullguard_separated t (r.total_charge.trans hs.1) g)
  have each (B) (hB : B ∈ P.parts) : h ≤ B.card := by
    apply minSize B (P.nonempty_of_mem_parts hB)
    apply Prod.ext
    · simpa [Prod.fst_sum,slope,sum_apply] using congrFun (zero B hB) 0
    · simpa [Prod.snd_sum,slope,sum_apply] using congrFun (zero B hB) 1
  have cap := sum_le_sum each
  rw [sum_const,smul_eq_mul,Nat.mul_comm,P.sum_card_parts,card_univ] at cap
  exact (Nat.mul_le_mul_left h (by omega)).trans cap

def row (x y : F) : Fin 2 → F := ![x,y]

/-- Three exceptional rows followed by n equal slopes. All primal entries are one. -/
def extremal (n : ℕ) : Flat (Fin (n+3)) :=
  ⟨fun _ => 1,
    Fin.cons (row 1 1) (Fin.cons (row (-1) 1) (Fin.cons (row (-(n:F)) 1) (fun _ => row 1 0))),
    Fin.cons 1 (fun _ => 0)⟩

theorem extremal_normalized (n : ℕ) : Normalized (extremal n) := by
  constructor
  · funext d
    fin_cases d <;> simp [extremal,HZ.State.charge,Finset.sum_apply,Fin.sum_univ_succ,row]
    decide
  · simp [extremal,scalar,Fin.sum_univ_succ]

theorem extremal_rank_two (n : ℕ) : RankTwo (extremal n) := by
  intro a b all
  have e : a+b=0 := by simpa [extremal,row] using all 0
  have f : -a+b=0 := by simpa [extremal,row] using all (0 : Fin (n+2)).succ
  have independent : ∀ a b : F, a+b=0 → -a+b=0 → a=0 ∧ b=0 := by decide
  exact independent a b e f

private abbrev Allowed (v : V) := v.2=1 ∨ v=(1,0)

private theorem extremal_slopes (n : ℕ) (i : Fin (n+3)) : Allowed (slope (extremal n) i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Or.inl rfl
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Or.inl rfl
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem extremal_cost (n : ℕ) : C (extremal n)=bound (n+3) := by
  have nz : ∀ v : V, Allowed v → v≠0 := by decide
  have nop : ∀ v w : V, Allowed v → Allowed w → v+w≠0 := by decide
  have sizes (B : Finset (Fin (n+3))) (ne : B.Nonempty) (zero : ∑ i ∈ B, slope (extremal n) i=0) :
      3 ≤ B.card := by
    have pos := ne.card_pos
    by_contra! small
    rcases (show B.card=1 ∨ B.card=2 by omega) with one|two
    · obtain ⟨i,rfl⟩ := card_eq_one.mp one
      exact nz _ (extremal_slopes n i) (by simpa using zero)
    · obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp two
      exact nop _ _ (extremal_slopes n i) (extremal_slopes n j) (by simpa [ij] using zero)
  have lower := component_bound _ (extremal_normalized n) 3 sizes
  have upper := cost_upper _ (extremal_normalized n)
  simp only [Fintype.card_fin,bound] at lower upper ⊢
  omega

def oneRow : Flat (Fin 1) := ⟨fun _ => 1,fun _ => 0,fun _ => 1⟩

theorem oneRow_normalized : Normalized oneRow := by unfold Normalized; decide

def twoRows : Flat (Fin 2) := ⟨fun _ => 1,![row 1 0,row (-1) 0],![1,0]⟩

theorem twoRows_normalized : Normalized twoRows := by unfold Normalized; decide

theorem twoRows_cost : C twoRows=1 := by
  have small : ∀ B : Finset (Fin 2), B.Nonempty → ∑ i ∈ B, slope twoRows i=0 → 2≤B.card := by
    decide
  have lb := component_bound twoRows twoRows_normalized 2 small
  have ub := cost_upper twoRows twoRows_normalized
  simp only [Fintype.card_fin] at lb ub
  change C twoRows ≤ 1 at ub
  omega

end AffineGuard.TwoParameter
