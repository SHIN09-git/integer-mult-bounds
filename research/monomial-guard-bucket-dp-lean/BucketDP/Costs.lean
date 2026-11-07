import BucketDP.Accounting
import Mathlib.Analysis.Asymptotics.Defs

namespace BucketDP

/-- One evaluation of -u[i]/u[j] for every non-pivot in the actual groups. -/
def divisions (gs : List (List I)) : ℕ := (gs.map (fun b => b.tail.length)).sum

theorem divisions_eq [Field K] (u : I → K) (gs : List (List I)) :
    divisions gs = (word u gs).length := by
  induction gs with
  | nil => rfl
  | cons b gs ih => cases b <;> simp [divisions,word,star] at ih ⊢ <;> omega

namespace Events

def inputScale (e : Events) := (e.rows+1)*(1+e.dim)
def gridScale (e : Events) := (1+e.dim)*e.cells
def fillScale (e : Events) := (1+e.types+e.dim)*e.cells
def timeScale (e : Events) := e.inputScale+e.fillScale+e.gates
def spaceScale (e : Events) := e.inputScale+e.gridScale+e.gates

/-- A charged execution on the word RAM. A dense comparison is charged its full
    coordinate allowance, including generating indices; early exit can reduce work.
    The two extra passes that tag/project rows are allowed in either variant. -/
def sumTime (e : Events) := 24*e.inputScale
def rawTime (e : Events) := 32*e.inputScale
def identifyTime (e : Events) := 12*(1+e.retained) + 12*((1+e.dim)*e.comparisons) + 8*e.identifyCoords
def directoryTime (e : Events) := 12*(1+e.retained+e.types+e.bucketNodes+e.heads)
    + 12*((1+e.dim)*e.bucketTests) + 8*e.bucketCoords
def traceTime (e : Events) := 20*(1+e.jumps+e.pops+e.groups+e.realNodes)
def emitTime (e : Events) := 8*(1+e.groups+e.realNodes)+16*e.gates
def time (e : Events) := e.sumTime+e.rawTime+e.identifyTime+e.directoryTime+e.fillTicks+e.traceTime+e.emitTime

/-- Occupancy in words. Count raw buffers and the directory throughout; take the
    maximum of transient phases. The final table, output witness and recursive
    frames are allowed to coexist. Updated arrays use a single mutable owner. -/
def resident (e : Events) := 24*e.inputScale + 12*(1+e.retained+e.types) + 4*e.bucketNodes + e.heads
def prepScratch (e : Events) := 12*(1+e.retained+e.types+e.dim)
def fillScratch (e : Events) := 16*(1+e.types+e.dim)
def traceScratch (e : Events) := 16*(1+e.jumps+e.pops+e.groups+e.realNodes)+8*e.gates
def space (e : Events) := e.resident + max e.prepScratch (e.tableWords + max e.fillScratch e.traceScratch)

end Events
open Events

theorem resources_le (e : Events) (h : Limits e) :
    e.time ≤ 384*e.timeScale ∧ e.space ≤ 192*e.spaceScale := by
  obtain ⟨hh,ht,hb,hc,hi,hk,hv,hn,ha,hf,hs,hj,hp,hg,hr⟩ := h
  have base : 1 ≤ e.cells := by omega
  have gN : e.cells ≤ e.gridScale := Nat.le_mul_of_pos_left _ (by omega : 0 < 1+e.dim)
  have gd : 1+e.dim ≤ e.gridScale := Nat.le_mul_of_pos_right _ base
  have gf : e.gridScale ≤ e.fillScale := Nat.mul_le_mul_right _ (by omega)
  have bound : (1+e.dim)*(e.retained*e.types) ≤ 2*e.gridScale := by
    calc
      _ ≤ (1+e.dim)*(2*e.cells) := Nat.mul_le_mul_left _ hb
      _ = _ := by simp only [gridScale,Nat.mul_left_comm]
  have cmp : (1+e.dim)*e.comparisons ≤ 2*e.gridScale := (Nat.mul_le_mul_left _ hc).trans bound
  have test : (1+e.dim)*e.bucketTests ≤ 2*e.gridScale := by
    rw [hv,Nat.mul_comm e.types]; exact bound
  have ci : e.identifyCoords ≤ 2*e.gridScale := hi.trans ((Nat.mul_le_mul_right _ (by omega : e.dim ≤ 1+e.dim)).trans cmp)
  have cb : e.bucketCoords ≤ 2*e.gridScale := hk.trans ((Nat.mul_le_mul_right _ (by omega : e.dim ≤ 1+e.dim)).trans test)
  change e.fillTicks ≤ 48*e.fillScale at hf
  change e.tableWords ≤ 16*e.gridScale at hs
  constructor
  · unfold time timeScale sumTime rawTime identifyTime directoryTime traceTime emitTime
    omega
  · have a : e.prepScratch ≤ 48*e.gridScale := by unfold prepScratch; omega
    have b : e.fillScratch ≤ 48*e.gridScale := by unfold fillScratch; omega
    have c : e.traceScratch ≤ 80*e.gridScale+8*e.gates := by unfold traceScratch; omega
    have v : max e.fillScratch e.traceScratch ≤ 80*e.gridScale+8*e.gates := max_le (by omega) c
    have w : max e.prepScratch (e.tableWords+max e.fillScratch e.traceScratch) ≤ 96*e.gridScale+8*e.gates :=
      max_le (by omega) (by omega)
    unfold space resident spaceScale
    omega

theorem zero_resources [Field K] [DecidableEq K] (r : Raw K m d) :
    (zeroEvents r).time ≤ 384*(zeroEvents r).timeScale ∧
    (zeroEvents r).space ≤ 192*(zeroEvents r).spaceScale := resources_le _ (zero_limits r)

theorem target_resources [Field K] [DecidableEq K] (r : Raw K m d) (τ : Fin d → K) :
    (targetEvents r τ).time ≤ 384*(targetEvents r τ).timeScale ∧
    (targetEvents r τ).space ≤ 192*(targetEvents r τ).spaceScale := resources_le _ (target_limits r τ)

open Asymptotics Filter

private theorem big_of_nat {ι : Type*} (l : Filter ι) (f g : ι → ℕ) (c : ℕ) (h : ∀ i, f i ≤ c*g i) :
    (fun i => (f i : ℝ)) =O[l] (fun i => (g i : ℝ)) := by
  apply IsBigO.of_bound (c : ℝ)
  apply Filter.Eventually.of_forall
  intro i
  simp only [Real.norm_natCast]
  exact_mod_cast h i

def Bounds {ι : Type*} (l : Filter ι) (s : ι → Events) : Prop :=
  ((fun i => ((s i).time : ℝ)) =O[l] (fun i => ((s i).timeScale : ℝ))) ∧
  ((fun i => ((s i).space : ℝ)) =O[l] (fun i => ((s i).spaceScale : ℝ)))

theorem bounds_of_limits {ι : Type*} (l : Filter ι) (s : ι → Events) (h : ∀ i, Limits (s i)) : Bounds l s :=
  ⟨big_of_nat _ _ _ 384 (fun i => (resources_le _ (h i)).1),
   big_of_nat _ _ _ 192 (fun i => (resources_le _ (h i)).2)⟩

/-- Both the number of physical rows and the charge dimension may vary with the input. -/
theorem zero_bigO {ι K : Type*} [Field K] [DecidableEq K] (l : Filter ι) {m d : ι → ℕ}
    (r : (i : ι) → Raw K (m i) (d i)) : Bounds l (fun i => zeroEvents (r i)) :=
  bounds_of_limits _ _ (fun i => zero_limits (r i))

theorem target_bigO {ι K : Type*} [Field K] [DecidableEq K] (l : Filter ι) {m d : ι → ℕ}
    (r : (i : ι) → Raw K (m i) (d i)) (τ : (i : ι) → Fin (d i) → K) :
    Bounds l (fun i => targetEvents (r i) (τ i)) :=
  bounds_of_limits _ _ (fun i => target_limits (r i) (τ i))

end BucketDP
