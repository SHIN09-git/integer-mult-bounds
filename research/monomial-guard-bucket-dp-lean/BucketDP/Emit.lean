import BucketDP.Project
import GuardDP.Solver

namespace BucketDP
open GuardDP Finset
variable {I K V : Type*} [DecidableEq I] [Field K] [AddCommGroup V] [Module K V]

/-- Read both original scalar carriers directly. No simulated state-update chain is evaluated. -/
def star (u : I → K) : List I → List (Gate I K)
  | [] => []
  | j::xs => xs.map (fun i => ⟨i,j,-u i / u j⟩)

def word (u : I → K) (gs : List (List I)) := gs.flatMap (star u)

theorem star_eq_emit (u : I → K) (s : HZ.State I K V) (j : I) (xs : List I)
    (hn : (j::xs).Nodup) (hu : ∀ i ∈ j::xs, s.u i = u i) :
    star u (j::xs) = emit s (xs.map (fun i => (i,j))) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    have hji := (List.nodup_cons.mp hn).1
    have hi := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    have hj : j ≠ i := fun e => hji (List.mem_cons.mpr (.inl e))
    have hrest : (j::xs).Nodup := List.nodup_cons.mpr
      ⟨fun h => hji (List.mem_cons_of_mem _ h),(List.nodup_cons.mp (List.nodup_cons.mp hn).2).2⟩
    let q := (instruction s (i,j)).act s
    have hu' (a : I) (ha : a ∈ j::xs) : q.u a = u a := by
      have ne : a ≠ i := by
        rcases List.mem_cons.mp ha with e|hh
        · exact e ▸ hj
        · exact fun e => hi (e ▸ hh)
      have hmem : a ∈ j::i::xs := by
        rcases List.mem_cons.mp ha with e|hh
        · exact List.mem_cons.mpr (.inl e)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh)
      exact (Function.update_of_ne ne ..).trans (hu a hmem)
    change (⟨i,j,-u i/u j⟩ : Gate I K) :: star u (j::xs) = instruction s (i,j) :: emit q _
    rw [ih q hrest hu']
    congr 1
    simp [instruction, hu i (by simp), hu j (by simp)]

private theorem run_out_u (s : HZ.State I K V) (ps : Plan I) (k : I)
    (h : ∀ p ∈ ps, k ≠ p.1) : (runPlan s ps).u k = s.u k := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [runPlan, ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    exact Function.update_of_ne (h p List.mem_cons_self) ..

private theorem execute_append (s : HZ.State I K V) (a b : List (Gate I K)) :
    execute s (a++b) = execute (execute s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons g a ih => exact ih (g.act s)

omit [DecidableEq I] in
theorem word_length (u : I → K) (gs : List (List I)) (hne : ∀ B ∈ gs, B ≠ []) :
    (word u gs).length + gs.length = gs.flatten.length := by
  induction gs with
  | nil => rfl
  | cons B gs ih =>
    have ht := ih (fun C hc => hne C (List.mem_cons_of_mem _ hc))
    cases B with
    | nil => exact False.elim (hne [] List.mem_cons_self rfl)
    | cons j xs =>
      change ((star u (j::xs) ++ word u gs).length) + _ = _
      simp only [star, List.length_append, List.length_map, List.length_cons, List.flatten_cons]
      omega

/-- Besides legality, give the charge on each group pivot and on every other row. -/
theorem word_effect (s : HZ.State I K V) (u : I → K) (gs : List (List I))
    (hn : gs.flatten.Nodup) (ha : ∀ i ∈ gs.flatten, s.charge i ≠ 0)
    (hu : ∀ i ∈ gs.flatten, s.u i = u i) :
    let w := word u gs
    let t := execute s w
    (∀ g ∈ w, g.Legal) ∧
      (∀ j xs, j::xs ∈ gs → t.charge j = ((j::xs).map s.charge).sum ∧ ∀ i ∈ xs, t.charge i = 0) ∧
      ∀ i ∉ gs.flatten, t.charge i = s.charge i := by
  induction gs generalizing s with
  | nil => simp [word, execute]
  | cons B gs ih =>
    cases B with
    | nil => simpa [word, star] using ih s hn ha hu
    | cons j xs =>
      obtain ⟨hb,ht,dis⟩ := List.nodup_append.mp hn
      have memB (i : I) (hi : i ∈ j::xs) : i ∈ ((j::xs)::gs).flatten := List.mem_append_left _ hi
      have memT (i : I) (hi : i ∈ gs.flatten) : i ∈ ((j::xs)::gs).flatten := List.mem_append_right _ hi
      have unz (i : I) (hi : i ∈ j::xs) : s.u i ≠ 0 := fun h => ha i (memB i hi) (by simp [HZ.State.charge,h])
      let ps := xs.map (fun i => (i,j))
      let q := runPlan s ps
      obtain ⟨feas,chg⟩ := gather_spec j xs s (List.nodup_cons.mp hb).2 (List.nodup_cons.mp hb).1
        (unz j List.mem_cons_self) (fun i hi => unz i (List.mem_cons_of_mem _ hi))
      have old (i : I) (hi : i ∉ j::xs) : q.charge i = s.charge i := by
        have hj : i ≠ j := fun e => hi (List.mem_cons.mpr (.inl e))
        have hx : i ∉ xs := fun h => hi (List.mem_cons_of_mem _ h)
        simpa [q,ps,hj,hx] using chg i
      have untouched (i : I) (hi : i ∈ gs.flatten) : i ∉ j::xs := fun hm => dis i hm i hi rfl
      have outside (i : I) (hi : i ∈ gs.flatten) := old i (untouched i hi)
      have uout (i : I) (hi : i ∈ gs.flatten) : q.u i = u i := by
        apply (run_out_u s ps i ?_).trans (hu i (memT i hi))
        intro p hp
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hp
        exact fun e => untouched i hi (List.mem_cons_of_mem _ (e.symm ▸ hx))
      obtain ⟨legal,atB,off⟩ := ih q ht (fun i hi => outside i hi ▸ ha i (memT i hi)) uout
      have eqword := star_eq_emit u s j xs hb (fun i hi => hu i (memB i hi))
      have exe : execute s (star u (j::xs)) = q := by rw [eqword,execute_emit]
      change (∀ g ∈ star u (j::xs) ++ word u gs, g.Legal) ∧ _
      refine ⟨List.forall_mem_append.mpr ⟨eqword ▸ emit_legal _ _ feas,legal⟩, ?_⟩
      let t := execute s (star u (j::xs) ++ word u gs)
      change (∀ k ys, k::ys ∈ (j::xs)::gs → t.charge k = ((k::ys).map s.charge).sum ∧
        ∀ i ∈ ys, t.charge i = 0) ∧ ∀ i ∉ ((j::xs)::gs).flatten, t.charge i = s.charge i
      have et : t = execute q (word u gs) := by dsimp [t]; rw [execute_append,exe]
      rw [et]
      constructor
      · intro k ys hm
        rcases List.mem_cons.mp hm with he | htail
        · injection he with ek eys
          subst k
          subst ys
          have oj := off j (fun h => dis j List.mem_cons_self j h rfl)
          rw [oj, show q.charge j = _ from chg j]
          constructor
          · simp [List.sum_toFinset s.charge (List.nodup_cons.mp hb).2, add_comm]
          · intro i hi
            rw [off i (fun h => dis i (List.mem_cons_of_mem _ hi) i h rfl)]
            have hne : i ≠ j := fun e => (List.nodup_cons.mp hb).1 (e ▸ hi)
            simpa [q,ps,hne,hi] using chg i
        · obtain ⟨hk,hh⟩ := atB k ys htail
          refine ⟨hk.trans ?_,hh⟩
          congr 1
          exact List.map_congr_left (fun i hi => outside i (List.mem_flatten.mpr ⟨_,htail,hi⟩))
      · intro i hi
        have ho : i ∉ gs.flatten := fun h => hi (memT i h)
        exact (off i ho).trans (old i (fun h => hi (memB i h)))

end BucketDP
