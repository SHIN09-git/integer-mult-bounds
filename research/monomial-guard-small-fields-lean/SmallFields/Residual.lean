import SmallFields.Weights

namespace SmallFields
open Multiset

theorem uniform_blocks {V : Type*} [AddCommGroup V] (v : V) (p : ℕ) (hp : 0 < p)
    (hz : (replicate p v).sum = 0) (n : ℕ) : Blocks (replicate (p*n) v) n := by
  induction n with
  | zero => exact Blocks.empty
  | succ n ih =>
    have hn : replicate p v ≠ 0 := by
      intro he
      have := congrArg Multiset.card he
      simp at this
      omega
    rw [Nat.mul_succ,Nat.add_comm,Multiset.replicate_add]
    exact Blocks.join hn hz ih

theorem two_join {V : Type*} [AddCommGroup V] (u v : V) (a b c d : ℕ) :
    two u v (a+c) (b+d) = two u v a b + two u v c d := by
  simp only [two,Multiset.replicate_add]
  ac_rfl

theorem scale_two {F : Type*} [Field F] (u v : F) (a b : ℕ) :
    (two 1 v a b).map (u*·) = two u (u*v) a b := by simp [two]

/-- Normalize by a nonzero scalar, transporting both the zero-total condition and Z. -/
theorem normalize_two {F : Type*} [Field F] {u : F} (hu : u ≠ 0) (v : F) (a b : ℕ)
    (hz : (two u (u*v) a b).sum = 0) :
    (two 1 v a b).sum = 0 ∧ Z (two u (u*v) a b) = Z (two 1 v a b) := by
  have h := scale_sum u (two 1 v a b)
  rw [scale_two,hz] at h
  have hs := (mul_eq_zero.mp h.symm).resolve_left hu
  exact ⟨hs,scale_two u v a b ▸ Z_scale hu _ hs⟩

theorem three_ones (a : ℕ) (hz : (replicate a (1 : ZMod 3)).sum = 0) :
    Z (replicate a (1 : ZMod 3)) = a/3 := by
  let m := replicate a (1 : ZMod 3)
  have hw : weight (residue (1 : ZMod 3)) m = a := by
    rw [show m = replicate a 1 from rfl,weight_replicate]
    change a*1=a; omega
  have cast := cast_weight (1 : ZMod 3) m
  rw [hw,show m.sum = 0 from hz,mul_zero] at cast
  have hd := (ZMod.natCast_eq_zero_iff a 3).mp cast
  have upper := Z_weight_bound (1 : ZMod 3) m hz (by
    intro v hv; rw [eq_of_mem_replicate hv]; decide)
  rw [hw] at upper
  have low := uniform_blocks (1 : ZMod 3) 3 (by decide) (by decide) (a/3)
  rw [show 3*(a/3) = a by omega] at low
  change Z m = a/3
  have hl : a/3 ≤ Z m := low.le_Z
  omega

def fiveResidual (a b : ℕ) := min ((a+2*b)/5) ((3*a+b)/5)

private theorem weights_five (a b : ℕ) :
    weight (residue (1 : ZMod 5)) (two 1 2 a b) = a+2*b ∧
    weight (residue (3 : ZMod 5)) (two 1 2 a b) = 3*a+b := by
  simp only [two,weight_add,weight_replicate]
  change a*1+b*2 = _ ∧ a*3+b*1 = _
  omega

/-- Strip (1,2,2), which uses five units in each weight. One remaining two
    needs a (1,1,1,2) block; a single remaining type forms blocks of five. -/
theorem five_construct (a b : ℕ) (hd : 5 ∣ a+2*b) :
    Blocks (two (1 : ZMod 5) 2 a b) (fiveResidual a b) := by
  induction a generalizing b with
  | zero =>
    have eq : 5*(b/5)=b := by omega
    have pr := uniform_blocks (2 : ZMod 5) 5 (by decide) (by decide) (b/5)
    rw [eq] at pr
    have sc : fiveResidual 0 b = b/5 := by unfold fiveResidual; omega
    simpa only [two,replicate_zero,zero_add,sc] using pr
  | succ a ih =>
    by_cases h : 2 ≤ b
    · let c := b-2
      have eb : b = 2+c := by dsimp [c]; omega
      have hc : 5 ∣ a+2*c := by omega
      have piece : Blocks (two (1 : ZMod 5) 2 1 2) 1 := Blocks.one (by decide) (by decide)
      have pr := piece.append (ih c hc)
      rw [← two_join] at pr
      have sc : fiveResidual (a+1) b = 1+fiveResidual a c := by unfold fiveResidual; omega
      rw [sc,eb,show a+1=1+a by omega]
      exact pr
    · have bh : b=0 ∨ b=1 := by omega
      rcases bh with rfl|rfl
      · have eq : 5*((a+1)/5) = a+1 := by omega
        have pr := uniform_blocks (1 : ZMod 5) 5 (by decide) (by decide) ((a+1)/5)
        rw [eq] at pr
        have sc : fiveResidual (a+1) 0 = (a+1)/5 := by unfold fiveResidual; omega
        simpa only [two,replicate_zero,add_zero,sc] using pr
      · let n := (a+1-3)/5
        have eq : a+1 = 3+5*n := by dsimp [n]; omega
        have sc : fiveResidual (a+1) 1 = 1+n := by unfold fiveResidual; omega
        have piece : Blocks (two (1 : ZMod 5) 2 3 1) 1 := Blocks.one (by decide) (by decide)
        have rest : Blocks (two (1 : ZMod 5) 2 (5*n) 0) n := by
          simpa only [two,replicate_zero,add_zero] using uniform_blocks (1 : ZMod 5) 5 (by decide) (by decide) n
        have pr := piece.append rest
        rw [← two_join] at pr
        rw [sc,eq]
        exact pr

theorem five_divisibility (a b : ℕ) (hz : (two (1 : ZMod 5) 2 a b).sum = 0) :
    5 ∣ a+2*b ∧ 5 ∣ 3*a+b := by
  obtain ⟨h1,h3⟩ := weights_five a b
  have h (u : ZMod 5) := cast_weight u (two 1 2 a b)
  have c1 := h 1
  have c3 := h 3
  rw [h1,hz,mul_zero] at c1
  rw [h3,hz,mul_zero] at c3
  exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp c1,(ZMod.natCast_eq_zero_iff _ _).mp c3⟩

theorem five_ones_twos (a b : ℕ) (hz : (two (1 : ZMod 5) 2 a b).sum = 0) :
    Z (two (1 : ZMod 5) 2 a b) = fiveResidual a b := by
  let m := two (1 : ZMod 5) 2 a b
  obtain ⟨h1,h3⟩ := weights_five a b
  have low := (five_construct a b (five_divisibility a b hz).1).le_Z
  have support (v : ZMod 5) (hv : v ∈ m) : v=1 ∨ v=2 :=
    (Multiset.mem_add.mp hv).imp eq_of_mem_replicate eq_of_mem_replicate
  have up1 := Z_weight_bound (1 : ZMod 5) m hz (fun v hv => by rcases support v hv with rfl|rfl <;> decide)
  have up3 := Z_weight_bound (3 : ZMod 5) m hz (fun v hv => by rcases support v hv with rfl|rfl <;> decide)
  change weight (residue 1) m = _ at h1
  change weight (residue 3) m = _ at h3
  rw [h1] at up1
  rw [h3] at up3
  apply le_antisymm _ low
  change Z m ≤ min _ _
  omega

end SmallFields
