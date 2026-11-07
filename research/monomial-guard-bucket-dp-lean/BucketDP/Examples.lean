import BucketDP.EndToEnd
import CountDP.Examples

namespace BucketDP.Examples
open GuardDP

def scalarRaw {m : ℕ} (s : HZ.State (Fin m) (ZMod 5) (ZMod 5)) : Raw (ZMod 5) m 1 :=
  ⟨Vector.ofFn s.u,Vector.ofFn (fun i => Vector.replicate 1 (s.w i)),Vector.ofFn s.b⟩

def toRaw {K : Type*} [Field K] (s : HZ.State (Fin m) K (Fin d → K)) : Raw K m d :=
  ⟨Vector.ofFn s.u,Vector.ofFn (fun i => Vector.ofFn (s.w i)),Vector.ofFn s.b⟩

def five := scalarRaw GuardDP.Examples.five
def repeated := scalarRaw CountDP.Examples.repeated
def collision := scalarRaw GuardDP.Examples.targeted

def profileOK (e : Events) : Bool :=
  decide (e.time ≤ 384*e.timeScale ∧ e.space ≤ 192*e.spaceScale ∧
    e.bucketTests = e.types*e.retained ∧ e.bucketNodes = e.retained ∧ e.heads = e.cells+1 ∧
    e.tableWords = 3+(10+3*e.dim)*e.cells ∧ e.identifyCoords ≤ e.dim*e.comparisons ∧
    e.bucketCoords ≤ e.dim*e.bucketTests)

def zeroRun (r : Raw (ZMod 5) m 1) (z n : ℕ) : Bool :=
  match solve r with
  | .inr _ => false
  | .inl a =>
    let e := zeroEvents r
    let ids := a.recovered.path.map Prod.fst
    a.recovered.score == z && e.cells == n && a.gates.length == m-z &&
      divisions a.groups == a.gates.length && profileOK e &&
      (List.finRange m).all (fun i => ids.count i == 1 && (execute r.state a.gates).charge i == 0)

def collisionRun : Bool :=
  match solve collision with
  | .inl _ => false
  | .inr a =>
    let e := targetEvents collision (total collision)
    let ids := a.recovered.path.map Prod.fst
    let after := execute collision.state a.gates
    let hit : Fin 5 := 1
    let inactive : Fin 5 := 4
    profileOK e && (e.rows,e.retained,e.types,e.cells,e.gates) == (5,5,3,18,2) &&
      a.recovered.score == 2 && collision.state.charge hit == -total collision &&
      ids.count none == 1 && ids.count (some hit) == 1 && a.groups.flatten.count hit == 1 &&
      ids.count (some inactive) == 0 && a.groups.flatten.count inactive == 0 &&
      (List.finRange 5).all (fun i => (a.groups.flatten.count i) == if i == inactive then 0 else 1) &&
      ((List.finRange 5).map after.charge).filter (· != 0) == [total collision] &&
      (divisions a.groups == 2) && a.gates.any (fun g => g.coefficient != 1 && g.coefficient != -1)

def binaryRun : Bool :=
  let r := toRaw GuardDP.Examples.binary
  match solve r with
  | .inl _ => false
  | .inr a =>
    a.gates.length == 2 && profileOK (solutionEvents r) &&
      ((List.finRange 5).map (execute r.state a.gates).charge).filter (· != 0) == [total r]

def emptyRaw (m d : ℕ) : Raw (ZMod 5) m d :=
  ⟨Vector.replicate m 0,Vector.replicate m (Vector.replicate d 1),Vector.replicate m 0⟩

def emptyRun (m d : ℕ) : Bool :=
  let r := emptyRaw m d
  let e := solutionEvents r
  match solve r with
  | .inr _ => false
  | .inl a => profileOK e && (e.rows,e.retained,e.cells,e.gates) == (m,0,1,0) &&
      a.recovered.path.isEmpty && decide (24*((m+1)*(1+d)) ≤ e.time)

def oneRun : Bool :=
  let r := scalarRaw GuardDP.Examples.singleton
  match solve r with
  | .inl _ => false
  | .inr a => a.gates.isEmpty && a.groups.flatten == [0] && a.recovered.steps == 2 && profileOK (solutionEvents r)

def earlyExit : Bool :=
  let v : Fin 3 → ZMod 5 := ![0,1,2]
  let w : Fin 3 → ZMod 5 := ![2,1,2]
  coords v w == 1 && coords v v == 3 && probeCoords v [w,v] == 4

def checks : List (String × Bool) :=
  [("8 distinct row identities, 64 cells, execute 4 minimum additions", zeroRun five 4 64),
   ("two types of 20 each, 441 cells, execute 20 minimum additions", zeroRun repeated 20 441),
   ("same-charge dummy and real row, zero row, non-unit coefficient", collisionRun),
   ("two dense coordinates and concentrated output", binaryRun),
   ("25 inactive physical rows, one table cell", emptyRun 25 3),
   ("zero-row and zero-dimensional inputs", emptyRun 0 2 && emptyRun 7 0),
   ("single real carrier plus dummy, no emitted addition", oneRun),
   ("dense comparison exits on first difference and counts coordinates", earlyExit)]

#guard checks.all Prod.snd

end BucketDP.Examples
