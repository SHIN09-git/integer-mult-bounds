import StrideDP.Witness
import StrideDP.Dense
import StrideDP.Cost
import CountDP.Examples

namespace StrideDP.Examples
open CountDP
open GuardDP.Examples (five targeted binary emptyState singleton)

def allCells {V W : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Arithmetic V W) (xs : List V) (n : V → ℕ) : Bool :=
  let a := (runTable A xs n).cells
  let ref := table xs n
  (List.range (slots n xs)).all fun k =>
    let m := unpack n xs k
    let c := read A a k
    c.entry == readAt ref k && A.denote c.total == m.sum &&
      (match c.entry.parent with
        | none => m == 0
        | some v => decide (v ∈ m ∧ c.prev < k) && c.prev == address n xs (m.erase v))

def stats {V W : Type*} [AddCommGroup V] [DecidableEq V] (A : Arithmetic V W) (xs : List V) (n : V → ℕ) :=
  let r := runTable A xs n
  (r.cells.size, r.reads, r.ticks, tableWords A r.cells)

def fiveStats :=
  let y := five.charge
  let keys := GuardDP.labels y
  stats (scalar _) (alphabet y keys) (capacity y keys)

def repeatedStats :=
  let y := CountDP.Examples.repeated.charge
  let keys := GuardDP.labels y
  stats (scalar _) (alphabet y keys) (capacity y keys)

def fiveAll :=
  let y := five.charge
  let keys := GuardDP.labels y
  allCells (scalar _) (alphabet y keys) (capacity y keys)

def collide :=
  let keys := GuardDP.augmentedKeys targeted.charge
  let y := Dummy.augment targeted.charge 1
  let gs := groups (scalar _) y keys keys.toFinset
  let word := StrideDP.concentrationWord (scalar _) targeted 1
  (allCells (scalar _) (alphabet y keys) (capacity y keys) &&
    decide (y none = y (some 1)) && gs.any (fun b => decide (none ∈ b ∧ some 1 ∈ b)) &&
    word.length == 2 && ((List.finRange 5).map (GuardDP.execute targeted word).charge).filter (· != 0) == [1])

def denseBinary :=
  let keys := GuardDP.augmentedKeys binary.charge
  let y := Dummy.augment binary.charge 1
  let A := dense Binary.F 2
  let word := StrideDP.concentrationWord A binary 1
  allCells A (alphabet y keys) (capacity y keys) && word.length == 2 &&
    ((List.finRange 5).map (GuardDP.execute binary word).charge).filter (· != 0) == [1]

def zeroDim :=
  let A := dense (ZMod 5) 0
  let v : Fin 0 → ZMod 5 := 0
  let r := runTable A [v] (fun _ => 2)
  stats A [] (fun _ => 0) == (1, 0, 17, 13) && allCells A [v] (fun _ => 2) &&
    r.reads == 2 && (read A r.cells 2).entry.score == 2

def radixOne :=
  let xs : List (ZMod 5) := [0,1]
  let n := fun (v : ZMod 5) => if v = 0 then 0 else 2
  let r := runTable (scalar _) xs n
  allCells (scalar _) xs n && r.cells.size == 3 && r.reads == 2 && (read (scalar _) r.cells 2).prev == 1

def checks : List (String × Bool) :=
  let word := StrideDP.separationWord (scalar _) five
  let large := CountDP.Examples.repeated
  let many := StrideDP.separationWord (scalar _) large
  [("all 64 cells, ties and cached sums", fiveAll && fiveStats == (64,160,4476,643)),
   ("zero target: execute four real additions", word.length == 4 &&
     (List.finRange 8).all (fun i => (GuardDP.execute five word).charge i == 0)),
   ("441 cells, exact edge count and twenty optimal additions", repeatedStats == (441,840,22949,4413) &&
     many.length == 20 && (List.finRange 40).all (fun i => (GuardDP.execute large many).charge i == 0)),
   ("virtual charge coincides with a real charge", collide),
   ("two-coordinate dense cache and real operation replay", denseBinary),
   ("empty alphabet and zero-dimensional charges", zeroDim),
   ("radix-one axis interleaved with live digits", radixOne),
   ("empty real input and one real carrier", (StrideDP.separationWord (scalar _) emptyState).isEmpty &&
     (StrideDP.concentrationWord (scalar _) singleton 1).isEmpty)]

#guard checks.all Prod.snd

end StrideDP.Examples
