import OrbitGuard.Layers

namespace OrbitGuard
open Ternary Finset
variable {I D : Type*} [Fintype I] [LinearOrder I] [Fintype D]

def accepts (s : State I D) : Bool :=
  decide ((∀ i, s.charge i = 0) ∧ (imbalance s = 1 ∨ imbalance s = -2))

omit [LinearOrder I] in
theorem accepts_spec (s : State I D) :
    accepts s = true ↔ HZ.Separated s ∧ (imbalance s = 1 ∨ imbalance s = -2) := by
  simp [accepts,HZ.Separated]

theorem accepts_iff_guard (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    accepts s = true ↔ FullGuard s := (accepts_spec s).trans (fullguard_iff s hy hn).symm

omit [LinearOrder I] in
theorem accepts_congr (s t : State I D) (h : vertex s = vertex t) :
    accepts s = true ↔ accepts t = true := by
  obtain ⟨q,rfl⟩ := (vertex_eq_iff_frame s t).mp h
  have sep : HZ.Separated (q.act s) ↔ HZ.Separated s := by
    simp only [HZ.Separated,Frame.act,HZ.charge_scale _ _ q.nonzero,HZ.charge_permute]
    constructor
    · intro h i; simpa using h (q.perm.symm i)
    · exact fun h i => h (q.perm i)
  rw [accepts_spec,accepts_spec,sep,Frame.act,imbalance_scale _ _ q.nonzero,imbalance_permute]

/-- A computable depth bound. It does not require the partition optimum or C. -/
def cap (s : State I D) : ℕ := 2 * Fintype.card I + L s

theorem C_le_cap (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    C s ≤ cap s := by
  have h : HZ.activeCount s ≤ Fintype.card I := Finset.card_le_univ _
  have hs : S s ≤ HZ.activeCount s := Nat.sub_le _ _
  have he := (envelope s hy hn).2
  unfold cap
  omega

/-- Search a layer before generating its successors, retaining one concrete word per new class. -/
def search (fuel : ℕ) (seen : Finset (Vertex I D)) (front : List (Item I D)) : Option (List (Gate I)) :=
  match front.find? (fun p => accepts p.state) with
  | some p => some p.revWord.reverse
  | none =>
    match fuel with
    | 0 => none
    | k+1 =>
      let next := advance seen front
      search k (remember seen next) next

def solve (s : State I D) : Option (List (Gate I)) :=
  search (cap s) {vertex s} (initial s)

omit [Fintype I] in
theorem least_paid {s t : State I D} {n} (r : HZ.Run s n t) (hg : FullGuard t) : C s ≤ n :=
  Nat.sInf_le (show n ∈ {j | ∃ t, HZ.Run s j t ∧ FullGuard t} from ⟨t,r,hg⟩)

private theorem hit_correct {s : State I D} {n seen front} (l : Layer s n seen front)
    (hn : n ≤ C s) {p : Item I D} (hit : front.find? (fun a => accepts a.state) = some p) :
    p.revWord.reverse.length = C s ∧ FullGuard (replay s p.revWord.reverse) := by
  obtain ⟨hr,hl⟩ := l.valid p (List.mem_of_find?_eq_some hit)
  have good := (accepts_spec p.state).mp (List.find?_some (p := fun a : Item I D => accepts a.state) hit)
  have hg := separated_good_fullguard p.state good.1 good.2
  rw [← hr] at hg
  have hb := least_paid (replay_run s p.revWord.reverse) hg
  simp only [List.length_reverse,hl] at hb ⊢
  exact ⟨Nat.le_antisymm hn hb,hg⟩

private theorem hit_at_C {s : State I D} (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    {seen front} (l : Layer s (C s) seen front) :
    (front.find? fun p => accepts p.state).isSome := by
  obtain ⟨t,r,hg⟩ := C_attained s hy hn
  have near : Nearest (vertex s) (C s) (vertex t) :=
    ⟨project_run r, fun j w => least_paid ((walk_iff_run s t j).mp w) hg⟩
  obtain ⟨p,hp,hkey⟩ := List.mem_map.mp (l.covers _ near)
  have ht := (accepts_iff_guard t (r.total_charge.trans hy) ((scalar_total r).trans hn)).mpr hg
  exact List.find?_isSome.mpr ⟨p,hp,(accepts_congr p.state t hkey).mpr ht⟩

theorem search_complete {s : State I D} (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    (fuel : ℕ) {n seen front} (l : Layer s n seen front) (lo : n ≤ C s) (hi : C s ≤ n+fuel) :
    ∃ w, search fuel seen front = some w ∧ w.length = C s ∧ FullGuard (replay s w) := by
  induction fuel generalizing n seen front with
  | zero =>
    have eq : n = C s := by omega
    subst n
    obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp (hit_at_C hy hn l)
    exact ⟨_,by rw [search,hp],hit_correct l lo hp⟩
  | succ k ih =>
    cases hh : front.find? (fun p => accepts p.state) with
    | some p => exact ⟨_,by rw [search,hh],hit_correct l lo hh⟩
    | none =>
      have hl : n+1 ≤ C s := by
        by_contra! h
        have eq : n = C s := by omega
        subst n
        simpa [hh] using hit_at_C hy hn l
      obtain ⟨w,hw,hlw,hg⟩ := ih (advance_layer l) hl (by omega)
      exact ⟨w,by rw [search,hh]; exact hw,hlw,hg⟩

/-- On every normalized finite ternary instance, the returned additions have exactly cost C. -/
theorem solve_correct (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1) :
    ∃ w, solve s = some w ∧ w.length = C s ∧ FullGuard (replay s w) :=
  search_complete hy hn _ (initial_layer s) (Nat.zero_le _) (by simpa using C_le_cap s hy hn)

theorem solve_optimal (s : State I D) (hy : ∑ i, s.charge i = 0) (hn : ∑ i, scalar s i = 1)
    {w} (hw : solve s = some w) :
    HZ.Run s w.length (replay s w) ∧ FullGuard (replay s w) ∧
      ∀ (t : State I D) n, HZ.Run s n t → FullGuard t → w.length ≤ n := by
  obtain ⟨v,hv,hl,hg⟩ := solve_correct s hy hn
  obtain rfl := Option.some.inj (hv.symm.trans hw)
  exact ⟨replay_run _ _,hg,fun _ _ r h => hl ▸ least_paid r h⟩

end OrbitGuard
