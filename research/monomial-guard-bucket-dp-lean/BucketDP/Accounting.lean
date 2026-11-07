import BucketDP.Visits
import BucketDP.Solver

namespace BucketDP
open CountDP StrideDP GuardDP

/-- Loop counts and sizes of the actual buffers. Observing them is a proof-side
    operation; clients call separate/concentrate without traversing buffers for a report. -/
structure Events where
  rows : ℕ
  dim : ℕ
  retained : ℕ
  types : ℕ
  cells : ℕ
  comparisons : ℕ
  identifyCoords : ℕ
  bucketCoords : ℕ
  bucketTests : ℕ
  bucketNodes : ℕ
  heads : ℕ
  fillTicks : ℕ
  tableWords : ℕ
  jumps : ℕ
  pops : ℕ
  groups : ℕ
  realNodes : ℕ
  gates : ℕ
  deriving Repr

variable {I J K : Type*} [Field K] [DecidableEq K] {m d : ℕ}

def observe (m : ℕ) (rs : List (J × (Fin d → K))) (a : Answer J I K) : Events :=
  let e := denseEq K d
  let xs := (identify e (rs.map Prod.snd)).keys
  let ds := directory e rs xs 1
  let N := volume ds
  let A := dense K d
  ⟨m,d,rs.length,a.recovered.types,a.recovered.states,a.recovered.tests,identifyCoords (rs.map Prod.snd),bucketCoords rs xs,bucketVisits e rs xs,
   (ds.map (fun p => p.2.length)).sum,(queues ds N).size,a.recovered.fillTicks,
   tableWords A (fill A (ds.map Prod.fst) N).cells,a.recovered.steps,
   a.recovered.path.length,a.groups.length,a.groups.flatten.length,a.gates.length⟩

def zeroEvents (r : Raw K m d) := observe m (rawRows r) (separate r)
def targetEvents (r : Raw K m d) (τ : Fin d → K) := observe m (augmentedRows r τ) (concentrate r τ)

structure Limits (e : Events) : Prop where
  retained_lt : e.retained < e.cells
  types_lt : e.types < e.cells
  box : e.retained * e.types ≤ 2*e.cells
  comparisons : e.comparisons ≤ e.retained*e.types
  identCoords : e.identifyCoords ≤ e.dim*e.comparisons
  buildCoords : e.bucketCoords ≤ e.dim*e.bucketTests
  visit : e.bucketTests = e.types*e.retained
  nodes : e.bucketNodes = e.retained
  slots : e.heads = e.cells+1
  fill : e.fillTicks ≤ 48*((1+e.types+e.dim)*e.cells)
  table : e.tableWords ≤ 16*((1+e.dim)*e.cells)
  jumps : e.jumps ≤ e.retained
  pops : e.pops ≤ e.jumps
  groups : e.groups ≤ e.pops
  realNodes : e.realNodes ≤ e.pops

theorem observe_limits [DecidableEq J] (m : ℕ) (y : J → Fin d → K) (ks : List J) (hn : ks.Nodup)
    (gs : List (List I)) (ws : List (Gate I K))
    (hg : gs.length ≤ (recover (denseEq K d) (dense K d) (records y ks)).path.length)
    (hr : gs.flatten.length ≤ (recover (denseEq K d) (dense K d) (records y ks)).path.length) :
    Limits (observe m (records y ks) ⟨recover (denseEq K d) (dense K d) (records y ks),gs,ws⟩) := by
  let e := denseEq K d
  let A := dense K d
  let rs := records y ks
  let xs := alphabet y ks
  let n := capacity y ks
  let N := slots n xs
  let ds := directory e rs xs 1
  let a := fill A (layout n xs 1) N
  let route := jumps A a.cells ks.length (N-1)
  let p := popPath (queues ds N) route
  have len : rs.length = ks.length := by simp [rs,records]
  have ek : (identify e (rs.map Prod.snd)).keys = xs := prepared_keys ..
  have en : volume ds = N := volume_eq e y ks hn xs 1
  have ea : ds.map Prod.fst = layout n xs 1 := axes_eq e y ks hn xs 1
  have sum : (xs.map n).sum = ks.length := sum_capacities y ks hn
  have ⟨bh,bt,bp⟩ := box_bounds xs n (fun _ hv => capacity_pos y ks hv)
  rw [sum] at bh bp
  have bw : ks.length*xs.length ≤ 2*N := by
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm xs.length] at bp
    omega
  have cmp := identify_bound e (rs.map Prod.snd)
  rw [ek,List.length_map,len] at cmp
  have ci := identifyCoords_le (rs.map Prod.snd)
  have cb := bucketCoords_le rs xs
  have v := bucketVisits_eq e rs xs
  rw [len] at v
  have nd : (ds.map (fun h => h.2.length)).sum = ks.length := (dir_nodes e y ks hn xs 1).trans sum
  have hd : (queues ds N).size = N+1 := by simp [queues]
  have f : a.ticks ≤ 48*((1+xs.length+d)*N) := by
    simpa only [layout_length] using fill_time_bound A (dense_costs d) (layout n xs 1) N (slots_pos _ _)
  have sp : tableWords A a.cells ≤ 16*((1+d)*N) := fill_space_bound A (dense_costs _) _ _ (slots_pos _ _)
  have j : route.length ≤ ks.length := jumps_length ..
  have pp : p.length ≤ route.length := pop_length ..
  have rp : (recover e A rs).path = p := by
    change popPath (queues (directory e rs (identify e (rs.map Prod.snd)).keys 1) _) _ = _
    rw [ek]
    change popPath (queues ds (volume ds)) (jumps A (fill A (ds.map Prod.fst) (volume ds)).cells rs.length _) = _
    rw [en,ea,len]
  change gs.length ≤ (recover e A rs).path.length at hg
  change gs.flatten.length ≤ (recover e A rs).path.length at hr
  rw [rp] at hg hr
  change Limits (observe m rs ⟨recover e A rs,gs,ws⟩)
  unfold observe
  change Limits ⟨m,d,rs.length,_,_,_,_,_,bucketVisits e rs (identify e (rs.map Prod.snd)).keys,_,_,_,_,_,_,_,_,_⟩
  dsimp only [recover]
  rw [ek]
  change Limits ⟨m,d,rs.length,xs.length,volume ds,_,_,_,bucketVisits e rs xs,_,_,_,_,_,_,_,_,_⟩
  rw [en,ea,len]
  exact ⟨(by change ks.length < N; change 1+ks.length ≤ N at bh; omega),
    (by change xs.length < N; change 1+xs.length ≤ N at bt; omega),bw,cmp,ci,cb,v,nd,hd,f,sp,j,pp,hg,hr⟩

omit [Field K] [DecidableEq K] in
theorem group_count_le (p : Path I) : (splitPath p).2.length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    obtain ⟨i,b⟩ := z
    cases b <;> simp [splitPath] <;> omega

theorem zero_limits (r : Raw K m d) : Limits (zeroEvents r) := by
  unfold zeroEvents separate
  rw [rawRows_eq]
  apply observe_limits _ _ _ (labels_unique _) _ _ (group_count_le _) (split_length _)

theorem target_limits (r : Raw K m d) (τ : Fin d → K) : Limits (targetEvents r τ) := by
  unfold targetEvents concentrate
  rw [augmentedRows_eq]
  apply observe_limits _ _ _ (tags_nodup _ (labels_unique _))
  · simpa only [List.length_map] using group_count_le _
  · rw [real_flat]
    exact (List.length_filterMap_le _ _).trans (split_length _)

end BucketDP
