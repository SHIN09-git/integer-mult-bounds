import BucketDP.Grid
import BucketDP.Blocks

namespace BucketDP
open CountDP StrideDP Finset
variable {I V W : Type*} [AddCommGroup V] [DecidableEq V]

def jumps (A : Arithmetic V W) (a : Array (Cell V W)) : ℕ → ℕ → List (ℕ × Bool)
  | 0, _ => []
  | fuel+1, k =>
    let c := read A a k
    match c.entry.parent with
    | none => []
    | some _ => (k-c.prev,c.entry.cut)::jumps A a fuel c.prev

theorem jumps_correct (A : Arithmetic V W) (xs : List V) (n : V → ℕ) (hd : xs.Nodup)
    (fuel : ℕ) (m : Multiset V) (hf : Fits xs n m) :
    jumps A (runTable A xs n).cells fuel (address n xs m) =
      addressesOf (fun v => stride n v xs) (trace A (runTable A xs n).cells fuel (address n xs m)) := by
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel ih =>
    let c := read A (runTable A xs n).cells (address n xs m)
    have hc := table_ok A xs n hd m hf
    change CellOK _ _ _ _ _ c at hc
    cases he : c.entry.parent with
    | none =>
      simp only [jumps, trace]
      change (match c.entry.parent with | none => [] | some _ => _) = addressesOf _ (match c.entry.parent with | none => [] | some _ => _)
      rw [he]; rfl
    | some v =>
      obtain ⟨hm,hp⟩ := hc.parent v he
      have ht := erase_add_stride xs n m hd (hf.support v hm) hm
      have eq : address n xs m - c.prev = stride n v xs := by omega
      simp only [jumps, trace]
      change (match c.entry.parent with | none => [] | some _ => _) = addressesOf _ (match c.entry.parent with | none => [] | some _ => _)
      rw [he]
      change (address n xs m-c.prev,c.entry.cut)::jumps A (runTable A xs n).cells fuel c.prev =
        (stride n v xs,c.entry.cut)::addressesOf (fun w => stride n w xs) (trace A (runTable A xs n).cells fuel c.prev)
      rw [eq,hp,ih (m.erase v) (hf.erase v)]

structure Recovery (I : Type*) where
  path : Path I
  score : ℕ
  types : ℕ
  states : ℕ
  tests : ℕ
  fillTicks : ℕ
  steps : ℕ
  deriving Repr

/-- The full state is the last address. One array-head update pops each identity. -/
def recover (e : Equality V) (A : Arithmetic V W) (rs : List (I × V)) : Recovery I :=
  let cl := identify e (rs.map Prod.snd)
  let ds := directory e rs cl.keys 1
  let N := volume ds
  let r := fill A (ds.map Prod.fst) N
  let route := jumps A r.cells rs.length (N-1)
  let p := popPath (queues ds N) route
  ⟨p,(read A r.cells (N-1)).entry.score,cl.keys.length,N,cl.comparisons,r.ticks,route.length⟩

variable [DecidableEq I]

omit [AddCommGroup V] [DecidableEq I] in
theorem prepared_keys (e : Equality V) (y : I → V) (ks : List I) :
    (identify e ((records y ks).map Prod.snd)).keys = alphabet y ks := by
  simp [identify_keys, records, alphabet, List.map_map, Function.comp_def]

theorem recovery_correct (e : Equality V) (A : Arithmetic V W) (y : I → V) (ks : List I) (hn : ks.Nodup)
    (hz : ∑ i ∈ ks.toFinset, y i = 0) :
    let r := recover e A (records y ks)
    Partition y ks.toFinset (splitPath r.path).2 r.score ∧
      r.score = HZ.maxBlocks y ks.toFinset ∧ r.steps = ks.length ∧
      (r.path.map Prod.fst).Nodup ∧ (r.path.map Prod.fst).toFinset = ks.toFinset := by
  let xs := alphabet y ks
  let n := capacity y ks
  let m := histogram y ks.toFinset
  let idx := fun v => stride n v xs
  have hd : xs.Nodup := List.nodup_dedup _
  have hf : Fits xs n m := histogram_fits y ks Subset.rfl
  have pos (v : V) (hv : v ∈ xs) := capacity_pos y ks hv
  have haddr : slots n xs - 1 = address n xs m := by
    have := full_address n xs m (fun _ _ => rfl)
    omega
  have hcard : m.card = ks.length := by rw [histogram_card, List.toFinset_card_of_nodup hn]
  let a := (runTable A xs n).cells
  let k := address n xs m
  let cp := backtrack (lookup xs n (table xs n)) m.card m
  have ht := backtrack_correct xs n hd m hf
  change Follows m cp ∧ cuts cp = D xs n m at ht
  have route : jumps A a ks.length k = addressesOf idx cp := by
    rw [← hcard, jumps_correct A xs n hd m.card m hf, trace_eq_backtrack A xs n hd m.card m hf]
  let q := queues (directory e (records y ks) xs 1) (slots n xs)
  let lp := popPath q (addressesOf idx cp)
  have hp := popPath_correct y ks hn xs idx (stride_unique n xs pos) cp ks.toFinset q Subset.rfl
    (fun i hi => List.mem_dedup.mpr (List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩)) (queues_ready e y ks hn) ht.1
  obtain ⟨hmap,hnd,hset⟩ := hp
  have cert := partition_of_trace y ks.toFinset lp cp hmap hnd hset ht.1 ((histogram_sum _ _).trans hz)
  have he : (read A a k).entry.score = D xs n m := congrArg Entry.score (table_ok A xs n hd m hf).entry
  have hl : cp.length = ks.length := by
    have := congrArg Multiset.card (Follows.contents m cp ht.1)
    simpa [hcard] using this
  let P := fun (score : ℕ) (route : List (ℕ × Bool)) =>
    let out := popPath q route
    Partition y ks.toFinset (splitPath out).2 score ∧ score = HZ.maxBlocks y ks.toFinset ∧
      route.length = ks.length ∧ (out.map Prod.fst).Nodup ∧ (out.map Prod.fst).toFinset = ks.toFinset
  dsimp only [recover]
  rw [prepared_keys, axes_eq e y ks hn, volume_eq e y ks hn, show (records y ks).length = ks.length by simp [records]]
  change P (read A a (slots n xs-1)).entry.score (jumps A a ks.length (slots n xs-1))
  rw [haddr]
  change P (read A a k).entry.score (jumps A a ks.length k)
  rw [route,he]
  refine ⟨ht.2 ▸ cert, fullScore_eq_maxBlocks y ks hz, ?_, hnd, hset⟩
  simpa [addressesOf, relabel] using hl

end BucketDP
