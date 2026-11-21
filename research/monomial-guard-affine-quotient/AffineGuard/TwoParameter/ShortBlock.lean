import AffineGuard.TwoParameter.Geometry

namespace AffineGuard.TwoParameter
open Finset Ternary

private theorem three_same (x : V) : x+x+x=0 := by revert x; decide
private theorem inconsistent_four : ∀ a b c d t : F, t≠0 → a+b+c=t → a+b+d=t →
    a+c+d=t → b+c+d=t → False := by decide
private theorem inconsistent_zero : ∀ a b t : F, t≠0 → a+b=t → a+b+t=t → False := by decide
set_option synthInstance.maxSize 4096 in
private theorem inconsistent_hexagon : ∀ a a' b b' c c' t : F, t≠0 →
    a+a'=t → b+b'=t → c+c'=t → a+b+c'=t → a'+b'+c=t → False := by decide
private theorem inconsistent_cross : ∀ a a' b b' c d t : F, t≠0 →
    a+a'=t → b+b'=t → a'+b'+c=t → a'+b+d=t → c+d+a=t → False := by decide

/-- With twelve rows and nonzero target t, a short zero-slope block has scalar
sum different from t. The remaining scalar total is therefore still nonzero. -/
theorem twelve_block {I : Type*} [DecidableEq I] (A : Finset I) (p : I → V) (b : I → F)
    (t : F) (ht : t≠0) (hn : 12 ≤ A.card) :
    ∃ B ⊆ A, B.Nonempty ∧ B.card ≤ 3 ∧ ∑ i ∈ B, p i = 0 ∧ ∑ i ∈ B, b i ≠ t := by
  classical
  by_contra no
  have forced (B : Finset I) (sub : B ⊆ A) (ne : B.Nonempty) (size : B.card ≤ 3)
      (hp : ∑ i ∈ B, p i = 0) : ∑ i ∈ B, b i = t := by
    by_contra different
    exact no ⟨B,sub,ne,size,hp,different⟩
  have one (i) (hi : i ∈ A) (h : p i = 0) : b i = t := by
    simpa using forced {i} (by simpa) (by simp) (by simp) (by simpa using h)
  have two (i) (hi : i ∈ A) (j) (hj : j ∈ A) (ij : i ≠ j) (h : p i+p j=0) : b i+b j=t := by
    simpa [ij] using forced {i,j} (by simp [insert_subset_iff,hi,hj]) (by simp)
      (by simp [ij]) (by simpa [ij] using h)
  have three (i) (hi : i ∈ A) (j) (hj : j ∈ A) (k) (hk : k ∈ A)
      (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (h : p i+p j+p k=0) : b i+b j+b k=t := by
    simpa [ij,ik,jk,add_assoc] using forced {i,j,k} (by simp [insert_subset_iff,hi,hj,hk]) (by simp)
      (by simp [ij,ik,jk]) (by simpa [ij,ik,jk,add_assoc] using h)
  let P := A.image p
  obtain ⟨i₀,_⟩ := card_pos.mp (show 0<A.card by omega)
  let r (x : V) := if hx : x ∈ P then Classical.choose (mem_image.mp hx) else i₀
  have rep (x : V) (hx : x ∈ P) : r x ∈ A ∧ p (r x)=x := by
    simpa only [r,dif_pos hx] using Classical.choose_spec (mem_image.mp hx)
  let f (x : V) := b (r x)
  have pairAt {x y} (g : Pair P x y) (i : I) (hi : i ∈ A) (pi : p i=x) :
      b i+f y=t := by
    obtain ⟨_,hy,xy,e⟩ := g
    obtain ⟨hj,pj⟩ := rep y hy
    exact two i hi (r y) hj (fun h => xy (pi.symm.trans ((congrArg p h).trans pj))) (by rw [pi,pj,e])
  have tripleAt {x y z} (g : Triple P x y z) (i : I) (hi : i ∈ A) (pi : p i=x) :
      b i+f y+f z=t := by
    obtain ⟨_,hy,hz,xy,xz,yz,e⟩ := g
    obtain ⟨hj,pj⟩ := rep y hy
    obtain ⟨hk,pk⟩ := rep z hz
    exact three i hi (r y) hj (r z) hk (fun h => xy (pi.symm.trans ((congrArg p h).trans pj)))
      (fun h => xz (pi.symm.trans ((congrArg p h).trans pk)))
      (fun h => yz (pj.symm.trans ((congrArg p h).trans pk))) (by rw [pi,pj,pk,e])
  have pair {x y} (g : Pair P x y) : f x+f y=t :=
    pairAt g _ (rep x g.1).1 (rep x g.1).2
  have triple {x y z} (g : Triple P x y z) : f x+f y+f z=t :=
    tripleAt g _ (rep x g.1).1 (rep x g.1).2
  rcases support_geometry P with cap | ⟨x,_,pa,tr⟩ | ⟨x,_,y,_,px,py,rest⟩
  · have bound (x : V) (_ : x ∈ P) : (A.filter (fun i => p i=x)).card ≤ capacity P x := by
      let T := A.filter (fun i => p i=x)
      have mem {i} (hi : i ∈ T) : i ∈ A ∧ p i=x := mem_filter.mp hi
      by_cases z : x=0
      · subst x
        simp only [capacity]
        by_contra! many
        obtain ⟨i,hi,j,hj,ij⟩ := one_lt_card.mp many
        have a := one i (mem hi).1 (mem hi).2
        have b' := one j (mem hj).1 (mem hj).2
        have e := two i (mem hi).1 j (mem hj).1 ij (by rw [(mem hi).2,(mem hj).2,add_zero])
        rw [a,b'] at e
        exact ht (add_right_cancel (show t+t=0+t by simpa using e))
      · by_cases rigid : Rigid P x
        · simp only [capacity,if_neg z,if_pos rigid]
          have constant (i) (hi : i ∈ T) : b i=f x := by
            rcases rigid with pa | ⟨_,_,_,_,tr⟩
            · exact add_right_cancel ((pairAt pa i (mem hi).1 (mem hi).2).trans (pair pa).symm)
            · exact add_right_cancel (add_right_cancel ((tripleAt tr i (mem hi).1 (mem hi).2).trans (triple tr).symm))
          by_contra! many
          obtain ⟨i,hi,j,hj,k,hk,ij,ik,jk⟩ := two_lt_card.mp many
          have e := three i (mem hi).1 j (mem hj).1 k (mem hk).1 ij ik jk
            (by rw [(mem hi).2,(mem hj).2,(mem hk).2,three_same])
          rw [constant i hi,constant j hj,constant k hk] at e
          have zero : ∀ a : F, a+a+a=0 := by decide
          exact ht (e.symm.trans (zero _))
        · simp only [capacity,if_neg z,if_neg rigid]
          by_contra! many
          obtain ⟨U,sub,s4⟩ := exists_subset_card_eq (s := T) (show 4≤T.card from many)
          obtain ⟨i,j,k,l,ij,ik,il,jk,jl,kl,rfl⟩ := card_eq_four.mp s4
          have hi := mem (sub (show i ∈ ({i,j,k,l} : Finset I) by simp))
          have hj := mem (sub (show j ∈ ({i,j,k,l} : Finset I) by simp))
          have hk := mem (sub (show k ∈ ({i,j,k,l} : Finset I) by simp))
          have hl := mem (sub (show l ∈ ({i,j,k,l} : Finset I) by simp))
          exact inconsistent_four _ _ _ _ _ ht
            (three i hi.1 j hj.1 k hk.1 ij ik jk (by rw [hi.2,hj.2,hk.2,three_same]))
            (three i hi.1 j hj.1 l hl.1 ij il jl (by rw [hi.2,hj.2,hl.2,three_same]))
            (three i hi.1 k hk.1 l hl.1 ik il kl (by rw [hi.2,hk.2,hl.2,three_same]))
            (three j hj.1 k hk.1 l hl.1 jk jl kl (by rw [hj.2,hk.2,hl.2,three_same]))
    have count := sum_le_sum bound
    rw [← card_eq_sum_card_image p A] at count
    omega
  · have zero : f 0=t := one _ (rep 0 tr.2.2.1).1 (rep 0 tr.2.2.1).2
    exact inconsistent_zero _ _ _ ht (pair pa) (zero ▸ triple tr)
  · rcases rest with ⟨pc,l,r'⟩ | ⟨l,r',s⟩
    · exact inconsistent_hexagon _ _ _ _ _ _ _ ht (pair px) (pair py) (pair pc) (triple l) (triple r')
    · exact inconsistent_cross _ _ _ _ _ _ _ ht (pair px) (pair py) (triple l) (triple r') (triple s)

end AffineGuard.TwoParameter
