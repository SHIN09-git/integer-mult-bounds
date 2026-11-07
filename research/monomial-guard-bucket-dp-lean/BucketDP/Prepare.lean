import StrideDP.Grid
import StrideDP.Machine
import CountDP.Score

namespace BucketDP
open CountDP StrideDP

/-- Deterministic equality oracle for raw charge types. The dense implementation
    below compares individual coordinates, without hashing. -/
structure Equality (V : Type*) where
  test : V → V → Bool
  correct : ∀ v w, test v w = true ↔ v = w

structure Classes (V : Type*) where
  keys : List V
  comparisons : ℕ

def probe (e : Equality V) (v : V) : List V → Bool × ℕ
  | [] => (false,0)
  | w::ws => if e.test v w then (true,1) else
    let r := probe e v ws
    (r.1,1+r.2)

theorem probe_spec (e : Equality V) (v : V) (ws : List V) :
    ((probe e v ws).1 = true ↔ v ∈ ws) ∧ (probe e v ws).2 ≤ ws.length := by
  induction ws with
  | nil => simp [probe]
  | cons w ws ih =>
    simp only [probe, List.length_cons, List.mem_cons]
    split
    · rename_i h
      simp [(e.correct _ _).mp h]
    · rename_i h
      have hn : v ≠ w := fun he => h ((e.correct _ _).mpr he)
      simp only [hn, false_or, ih.1, true_and]
      omega

def identify (e : Equality V) : List V → Classes V
  | [] => ⟨[],0⟩
  | v::vs =>
    let r := identify e vs
    let p := probe e v r.keys
    ⟨if p.1 then r.keys else v::r.keys, r.comparisons + p.2⟩

theorem identify_keys [DecidableEq V] (e : Equality V) (vs : List V) :
    (identify e vs).keys = vs.dedup := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [identify, ih, List.dedup_cons']
    split <;> rename_i h
    · simp [(probe_spec e v vs.dedup).1.mp h]
    · have hn : v ∉ vs := fun hmem => h ((probe_spec e v vs.dedup).1.mpr (List.mem_dedup.mpr hmem))
      simp [hn]

theorem identify_bound (e : Equality V) (vs : List V) :
    (identify e vs).comparisons ≤ vs.length * (identify e vs).keys.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hp := (probe_spec e v (identify e vs).keys).2
    simp only [identify, List.length_cons, Nat.succ_mul]
    split
    · omega
    · simp only [List.length_cons, Nat.mul_succ]
      omega

/-- Each comparison inspects one input record, emitting only matching labels. -/
def scanBucket (e : Equality V) (v : V) : List (I × V) → List I × ℕ
  | [] => ([],0)
  | (i,w)::rs =>
    let tail := scanBucket e v rs
    (if e.test w v then i::tail.1 else tail.1, tail.2+1)

def collect (e : Equality V) (rs : List (I × V)) (v : V) := (scanBucket e v rs).1

theorem scanBucket_visits (e : Equality V) (v : V) (rs : List (I × V)) :
    (scanBucket e v rs).2 = rs.length := by
  induction rs with
  | nil => rfl
  | cons p rs ih => cases p; simp [scanBucket,ih]

def directory (e : Equality V) (rs : List (I × V)) : List V → ℕ → List (Axis V × List I)
  | [], _ => []
  | v::vs, s =>
    let labels := collect e rs v
    let b := labels.length + 1
    (⟨v,b,s⟩,labels) :: directory e rs vs (s*b)

def volume : List (Axis V × List I) → ℕ
  | [] => 1
  | a::as => a.1.radix * volume as

def findQueue (k : ℕ) : List (Axis V × List I) → List I
  | [] => []
  | (a,ids)::rest => if k = a.offset then ids else findQueue k rest

/-- Install one head pointer per axis into the reserved stride-addressed array. -/
def install (a : Array (List I)) : List (Axis V × List I) → Array (List I)
  | [] => a
  | h::ds => (install a ds).setIfInBounds h.1.offset h.2

def queues (ds : List (Axis V × List I)) (N : ℕ) : Array (List I) :=
  install (Array.replicate (N+1) []) ds

@[simp] theorem install_size (a : Array (List I)) (ds : List (Axis V × List I)) :
    (install a ds).size = a.size := by
  induction ds with
  | nil => rfl
  | cons h ds ih => simp [install,ih]

theorem queues_get (ds : List (Axis V × List I)) (N k : ℕ) (hk : k < N+1) :
    ((queues ds N)[k]?).getD [] = findQueue k ds := by
  induction ds with
  | nil => simp [queues, install, findQueue, hk]
  | cons h ds ih =>
    obtain ⟨a,ids⟩ := h
    by_cases he : k = a.offset
    · subst k
      simp [queues, install, Array.setIfInBounds, hk, findQueue]
    · by_cases h : a.offset < N+1 <;>
        simpa [queues,install,Array.setIfInBounds,findQueue,he,Ne.symm he,h] using ih

@[simp] theorem dir_length (e : Equality V) (rs : List (I × V)) (xs : List V) (s : ℕ) :
    (directory e rs xs s).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons _ _ ih => simp [directory, ih]

variable [DecidableEq I] [DecidableEq V]

def records (y : I → V) (keys : List I) := keys.map (fun i => (i,y i))

omit [DecidableEq I] in
theorem collect_records (e : Equality V) (y : I → V) (keys : List I) (v : V) :
    collect e (records y keys) v = keys.filter (fun i => decide (y i = v)) := by
  induction keys with
  | nil => rfl
  | cons i ks ih =>
    change (if e.test (y i) v then i::collect e (records y ks) v else collect e (records y ks) v) = _
    by_cases h : y i = v
    · rw [if_pos ((e.correct _ _).mpr h)]
      simp [h, ih]
    · rw [if_neg (fun hp => h ((e.correct _ _).mp hp))]
      simp [h, ih]

theorem collect_count (e : Equality V) (y : I → V) (keys : List I) (hn : keys.Nodup) (v : V) :
    (collect e (records y keys) v).length = capacity y keys v := by
  rw [collect_records, capacity, histogram, List.toFinset_val, List.dedup_eq_self.mpr hn]
  rw [Multiset.map_coe, Multiset.coe_count]
  rw [List.count_eq_length_filter, List.filter_map, List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp

theorem axes_eq (e : Equality V) (y : I → V) (keys : List I) (hn : keys.Nodup) (xs : List V) (s : ℕ) :
    (directory e (records y keys) xs s).map Prod.fst = layout (capacity y keys) xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [directory, layout, collect_count e y keys hn, ih]

theorem volume_eq (e : Equality V) (y : I → V) (keys : List I) (hn : keys.Nodup) (xs : List V) (s : ℕ) :
    volume (directory e (records y keys) xs s) = slots (capacity y keys) xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [directory, volume, slots, collect_count e y keys hn, ih]

end BucketDP
