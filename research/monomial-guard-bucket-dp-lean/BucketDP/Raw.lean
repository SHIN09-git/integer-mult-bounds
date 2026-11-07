import BucketDP.Prepare
import GuardDP.Labels
import Mathlib.Data.List.FinRange

namespace BucketDP
open CountDP Finset
variable {K : Type*} [Field K] [DecidableEq K] {m d : ℕ}

/-- Original rows, including zero-charge rows, with directly indexed scalar coordinates. -/
structure Raw (K : Type*) (m d : ℕ) where
  u : Vector K m
  w : Vector (Vector K d) m
  b : Vector K m

def Raw.state (r : Raw K m d) : HZ.State (Fin m) K (Fin d → K) where
  u := r.u.get
  w := fun i => (r.w.get i).get
  b := r.b.get

/-- Returning data forces materialization before coordinates are exposed through get. -/
@[noinline] def pack (f : Fin d → K) : Vector K d := Vector.ofFn f

omit [Field K] [DecidableEq K] in
theorem pack_get (f : Fin d → K) : (pack f).get = f := by
  funext i
  simp [pack, Vector.get]

def compareCoords [DecidableEq F] (v w : Fin d → F) : List (Fin d) → Bool × ℕ
  | [] => (true,0)
  | i::is =>
    if v i = w i then
      let tail := compareCoords v w is
      (tail.1,tail.2+1)
    else (false,1)

theorem compareCoords_spec [DecidableEq F] (v w : Fin d → F) (is : List (Fin d)) :
    ((compareCoords v w is).1 = true ↔ ∀ i ∈ is, v i = w i) ∧ (compareCoords v w is).2 ≤ is.length := by
  induction is with
  | nil => simp [compareCoords]
  | cons i is ih =>
    by_cases h : v i = w i <;> simp [compareCoords,h,ih.1,ih.2]

def denseEq (K : Type*) [DecidableEq K] (d : ℕ) : Equality (Fin d → K) where
  test := fun v w => (compareCoords v w (List.finRange d)).1
  correct := by
    intro v w
    rw [(compareCoords_spec v w _).1]
    simp only [List.mem_finRange, true_implies]
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩

def scanRaw (r : Raw K m d) (is : List (Fin m)) : List (Fin m × (Fin d → K)) :=
  is.filterMap (fun i =>
    let v := pack (r.state.charge i)
    if (denseEq K d).test v.get 0 then none else some (i,v.get))

def activeLabels (r : Raw K m d) :=
  (List.finRange m).filter (fun i => decide (r.state.charge i ≠ 0))

theorem scanRaw_eq (r : Raw K m d) (is : List (Fin m)) :
    scanRaw r is = records r.state.charge (is.filter (fun i => decide (r.state.charge i ≠ 0))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scanRaw, List.filterMap_cons, pack_get] at ih ⊢
    by_cases h : r.state.charge i = 0
    · rw [if_pos (((denseEq K d).correct _ _).mpr h)]
      simpa [h] using ih
    · rw [if_neg (fun he => h (((denseEq K d).correct _ _).mp he))]
      simpa [h, records] using congrArg (List.cons (i,r.state.charge i)) ih

theorem labels_unique (r : Raw K m d) : (activeLabels r).Nodup :=
  (List.nodup_finRange _).filter _

theorem labels_cover (r : Raw K m d) : (activeLabels r).toFinset = HZ.active r.state.charge := by
  ext i; simp [activeLabels,HZ.active]

def tags (ks : List I) := none :: ks.map some

theorem tags_nodup (ks : List I) (hn : ks.Nodup) : (tags ks).Nodup := by
  simp [tags, List.Nodup.map (Option.some_injective _) hn]

theorem tags_set [DecidableEq I] (ks : List I) :
    (tags ks).toFinset = insert none (ks.toFinset.image some) := by
  ext i; cases i <;> simp [tags]

def rawRows (r : Raw K m d) := scanRaw r (List.finRange m)

def augmentedRows (r : Raw K m d) (τ : Fin d → K) : List (Option (Fin m) × (Fin d → K)) :=
  let v := pack (-τ)
  (none,v.get) :: (rawRows r).map (fun (i,v) => (some i,v))

theorem rawRows_eq (r : Raw K m d) : rawRows r = records r.state.charge (activeLabels r) := scanRaw_eq ..

theorem augmentedRows_eq (r : Raw K m d) (τ : Fin d → K) :
    augmentedRows r τ = records (Dummy.augment r.state.charge τ) (tags (activeLabels r)) := by
  simp [augmentedRows,rawRows_eq,pack_get,records,tags,Dummy.augment,List.map_map,Function.comp_def]

end BucketDP
