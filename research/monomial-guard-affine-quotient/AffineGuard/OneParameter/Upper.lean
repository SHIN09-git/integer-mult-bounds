import AffineGuard.OneParameter.Blocks
import AffineGuard.OneParameter.Plane

namespace AffineGuard.OneParameter
open Finset Ternary

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- All slopes on A vanish, and the signed scalar sum on A lies between -k and k. -/
private def Settled (s : Pencil I) (A : Finset I) (k : ℕ) : Prop :=
  (∀ i ∈ A, slope s i = 0) ∧
    -(k : ℤ) ≤ ∑ i ∈ A, lift (scalar s i) ∧ ∑ i ∈ A, lift (scalar s i) ≤ (k : ℤ)

omit [Fintype I] in
private theorem settled_union {s : Pencil I} {A B : Finset I} {k l : ℕ} (hd : Disjoint A B)
    (ha : Settled s A k) (hb : Settled s B l) : Settled s (A ∪ B) (k+l) := by
  refine ⟨fun i hi => (mem_union.mp hi).elim (ha.1 i) (hb.1 i),?_⟩
  rw [sum_union hd]
  obtain ⟨al,au⟩ := ha.2
  obtain ⟨bl,bu⟩ := hb.2
  push_cast
  constructor <;> omega

omit [DecidableEq I] [Fintype I] in
private theorem settled_congr {s t : Pencil I} {A : Finset I} {k : ℕ}
    (h : ∀ i ∈ A, packet t i = packet s i) (hs : Settled s A k) : Settled t A k := by
  refine ⟨fun i hi => (congrArg Prod.fst (h i hi)).trans (hs.1 i hi),?_⟩
  have vals : ∑ i ∈ A, lift (scalar t i) = ∑ i ∈ A, lift (scalar s i) :=
    sum_congr rfl fun i hi => congrArg (fun p : F × F => lift p.2) (h i hi)
  rw [vals]
  exact hs.2

private theorem settle_one (s : Pencil I) (B : Finset I) (hB : B.Nonempty)
    (hu : ∀ i ∈ B, s.u i ≠ 0) (hy : ∑ i ∈ B, slope s i = 0) :
    ∃ t, HZ.Run s (B.card-1) t ∧ HZ.AgreeOutside B s t ∧ Settled t B 1 := by
  obtain ⟨j,hj⟩ := hB
  obtain ⟨t,r,out,z,p⟩ := concentrate s B j hj hu
  have pj : slope t j = 0 := calc
    _ = ∑ i ∈ B, slope s i := by simpa only [Prod.fst_sum,packet] using congrArg Prod.fst p
    _ = 0 := hy
  have vals : ∑ i ∈ B, lift (scalar t i) = lift (scalar t j) :=
    sum_eq_single_of_mem j hj fun i hi ij => by
      have h : scalar t i = 0 := congrArg Prod.snd (z i hi ij)
      rw [h,lift_zero]
  refine ⟨t,r,out,fun i hi => ?_,by simpa only [vals,Nat.cast_one] using lift_bounds (scalar t j)⟩
  by_cases e : i = j
  · exact e ▸ pj
  · exact congrArg Prod.fst (z i hi e)

/-- Make k+1 zero-slope blocks on the given rows, spending one less addition than
the size of each block. Active row labels stay in the same ambient type. -/
private theorem settle_groups (k : ℕ) (s : Pencil I) (A : Finset I)
    (hu : ∀ i ∈ A, s.u i ≠ 0) (hy : ∑ i ∈ A, slope s i = 0) (hn : 3*k < A.card) :
    ∃ t, HZ.Run s (A.card-(k+1)) t ∧ HZ.AgreeOutside A s t ∧ Settled t A (k+1) := by
  induction k generalizing s A with
  | zero => exact settle_one s A (card_pos.mp (by omega)) hu hy
  | succ k ih =>
    obtain ⟨B,sub,ne,sz,hB⟩ := slope_block A (slope s) (by omega)
    obtain ⟨q,r,out,doneB⟩ := settle_one s B ne (fun i hi => hu i (sub hi)) hB
    let D := A \ B
    have sizeD : D.card = A.card-B.card := card_sdiff_of_subset sub
    have yD : ∑ i ∈ D, slope q i = 0 := by
      calc
        _ = ∑ i ∈ D, slope s i := sum_congr rfl fun i hi =>
          congrArg Prod.fst (outside_packet out i (mem_sdiff.mp hi).2)
        _ = 0 := by simpa [D,hB,hy] using (sum_sdiff (f := slope s) sub)
    have uD (i) (hi : i ∈ D) : q.u i ≠ 0 := by
      rw [(out i (mem_sdiff.mp hi).2).1]
      exact hu i (mem_sdiff.mp hi).1
    obtain ⟨t,r',out',doneD⟩ := ih q D uD yD (by omega)
    have neB := ne.card_pos
    have count : B.card-1 + (D.card-(k+1)) = A.card-(k+1+1) := by omega
    refine ⟨t,count ▸ r.trans r',?_,?_⟩
    · intro i hi
      obtain ⟨u,w,b⟩ := out i (fun h => hi (sub h))
      obtain ⟨u',w',b'⟩ := out' i (fun h => hi (mem_sdiff.mp h).1)
      exact ⟨u'.trans u,w'.trans w,b'.trans b⟩
    · have keep := settled_congr (fun i (hi : i ∈ B) => outside_packet out' i
          (fun h => (mem_sdiff.mp h).2 hi)) doneB
      have both := settled_union (show Disjoint D B from sdiff_disjoint) doneD keep
      simpa only [D,sdiff_union_of_subset sub] using both

private theorem finish (s : Pencil I) (A : Finset I) (hs : Normalized s)
    (hu : ∀ i ∈ A, s.u i ≠ 0) (outside : ∀ i ∉ A, packet s i = 0) :
    ∃ n t, HZ.Run s n t ∧ FullGuard t ∧ n ≤ 2*A.card/3 := by
  induction hsize : A.card using Nat.strong_induction_on generalizing A s with
  | h m ih =>
    by_cases large : 9 ≤ m
    · obtain ⟨B,sub,sizeB,zero⟩ := plane_triple A (packet s) (by omega)
      obtain ⟨j,hj⟩ := card_pos.mp (show 0 < B.card by omega)
      obtain ⟨q,r,out,z,p⟩ := concentrate s B j hj (fun i hi => hu i (sub hi))
      have silent (i) (hi : i ∈ B) : packet q i = 0 := by
        by_cases e : i = j
        · exact e ▸ p.trans zero
        · exact z i hi e
      let D := A \ B
      have sizeD : D.card = m-3 := by rw [show D.card = _ from card_sdiff_of_subset sub,hsize,sizeB]
      have uD (i) (hi : i ∈ D) : q.u i ≠ 0 := by
        rw [(out i (mem_sdiff.mp hi).2).1]
        exact hu i (mem_sdiff.mp hi).1
      have zeroD (i) (hi : i ∉ D) : packet q i = 0 := by
        by_cases hb : i ∈ B
        · exact silent i hb
        · exact (outside_packet out i hb).trans (outside i (fun ha => hi (mem_sdiff.mpr ⟨ha,hb⟩)))
      obtain ⟨n,t,r',guard,le⟩ := ih D.card (by omega) q D (normalize_run hs r) uD zeroD rfl
      exact ⟨_,t,r.trans r',guard,by omega⟩
    · have sumA (g : I → F) (h : ∀ i ∉ A, g i = 0) : ∑ i ∈ A, g i = ∑ i, g i :=
        sum_subset (subset_univ _) fun i _ hi => h i hi
      have hy : ∑ i ∈ A, slope s i = 0 := by
        rw [sumA (slope s) (fun i hi => congrArg Prod.fst (outside i hi))]
        simpa [slope,Finset.sum_apply] using congrFun hs.1 0
      have positive : 0 < A.card := by
        by_contra! emp
        have hem : A = ∅ := card_eq_zero.mp (by omega)
        have allzero (i) : scalar s i = 0 := congrArg Prod.snd (outside i (by simp [hem]))
        have bad := hs.2
        simp [allzero] at bad
      let k := (m-1)/3
      obtain ⟨t,r,out,ready⟩ := settle_groups k s A hu hy (by dsimp [k]; omega)
      have tz (i) (hi : i ∉ A) : packet t i = 0 := (outside_packet out i hi).trans (outside i hi)
      have sep : HZ.Separated t := by
        intro i
        funext d
        rw [show d = 0 from Subsingleton.elim _ _]
        by_cases hi : i ∈ A
        · exact ready.1 i hi
        · exact congrArg Prod.fst (tz i hi)
      have imb : (∑ i ∈ A, lift (scalar t i)) = imbalance t :=
        sum_subset (subset_univ _) fun i _ hi => by
          have z : scalar t i = 0 := congrArg Prod.snd (tz i hi)
          rw [z,lift_zero]
      obtain ⟨lo,up⟩ := ready.2
      rw [imb] at lo up
      have mod3 := mod_three (imbalance t) ((cast_imbalance t).trans (normalize_run hs r).2)
      have cap : k+1 ≤ 3 := by dsimp [k]; omega
      exact ⟨_,t,r,separated_good_fullguard t sep (by omega),by dsimp [k]; omega⟩

theorem cost_upper (s : Pencil I) (hs : Normalized s) : C s ≤ 2*Fintype.card I/3 := by
  let A := univ.filter fun i => s.u i ≠ 0
  obtain ⟨n,t,r,g,le⟩ := finish s A hs (fun _ hi => (mem_filter.mp hi).2) (by
    intro i hi
    have z : s.u i = 0 := by simpa [A] using hi
    simp [packet,slope,HZ.State.charge,scalar,z])
  have ca : A.card ≤ Fintype.card I := card_le_univ _
  exact (Nat.sInf_le (show n ∈ {j | ∃ t, HZ.Run s j t ∧ FullGuard t} from ⟨t,r,g⟩)).trans (by omega)

end AffineGuard.OneParameter
