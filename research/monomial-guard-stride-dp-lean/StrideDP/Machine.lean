import CountDP.Table

namespace StrideDP
open CountDP

/-- A packed cache. The second component of each arithmetic operation counts word operations. -/
structure Arithmetic (V W : Type*) [AddCommGroup V] [DecidableEq V] where
  zero : W
  initWork : ℕ
  addType : V → W → W × ℕ
  isZero : W → Bool × ℕ
  denote : W → V
  payloadWords : W → ℕ
  zero_ok : denote zero = 0
  add_ok : ∀ v w, denote (addType v w).1 = v + denote w
  test_ok : ∀ w, (isZero w).1 = decide (denote w = 0)

/-- Bounds for a particular representation in a word RAM with unit coordinate operations. -/
structure WordCosts {V W : Type*} [AddCommGroup V] [DecidableEq V] (A : Arithmetic V W) (d : ℕ) : Prop where
  init : A.initWork ≤ 5 * (1 + d)
  add : ∀ v w, (A.addType v w).2 ≤ 10 * (1 + d)
  test : ∀ w, (A.isZero w).2 ≤ 5 * (1 + d)
  words : ∀ w, A.payloadWords w ≤ 4 * (1 + d)

structure Axis (V : Type*) where
  key : V
  radix : ℕ
  offset : ℕ
  deriving Repr

def layout (n : V → ℕ) : List V → ℕ → List (Axis V)
  | [], _ => []
  | v :: vs, s => ⟨v, n v + 1, s⟩ :: layout n vs (s * (n v + 1))

@[simp] theorem layout_length (n : V → ℕ) (xs : List V) (s : ℕ) :
    (layout n xs s).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons _ _ ih => simp [layout, ih]

structure Cell (V W : Type*) where
  entry : Entry V
  prev : ℕ
  total : W
  deriving Repr

structure Candidate (V W : Type*) where
  key : V
  prev : ℕ
  cell : Cell V W

def prefer (x : Candidate V W) : Option (Candidate V W) → Option (Candidate V W)
  | none => some x
  | some y => if y.cell.entry.score ≤ x.cell.entry.score then some x else some y

structure Search (V W : Type*) where
  winner : Option (Candidate V W)
  ticks : ℕ
  reads : ℕ

/-- One quotient and remainder per axis. The positive-digit arm issues one array read.
    Both arms retain a reference to the best cell, with the first type winning ties. -/
def scan (get : ℕ → Cell V W) (k : ℕ) : List (Axis V) → ℕ → Search V W
  | [], _ => ⟨none, 1, 0⟩
  | a :: axes, q =>
    let r := scan get k axes (q / a.radix)
    if q % a.radix = 0 then ⟨r.winner, 6 + r.ticks, r.reads⟩ else
      let p := k - a.offset
      ⟨prefer ⟨a.key, p, get p⟩ r.winner, 16 + r.ticks, 1 + r.reads⟩

variable {V W : Type*} [AddCommGroup V] [DecidableEq V]

def blank (A : Arithmetic V W) : Cell V W := ⟨emptyEntry, 0, A.zero⟩
def read (A : Arithmetic V W) (a : Array (Cell V W)) (k : ℕ) := a[k]?.getD (blank A)

/-- Charge addition and the zero test are performed only after the winning row is known. -/
def finish (A : Arithmetic V W) : Option (Candidate V W) → Cell V W × ℕ
  | none => (blank A, 3)
  | some w =>
    let z := A.addType w.key w.cell.total
    let b := A.isZero z.1
    (⟨⟨w.cell.entry.score + (if b.1 then 1 else 0), some w.key, b.1⟩, w.prev, z.1⟩,
      9 + z.2 + b.2)

structure Run (V W : Type*) where
  cells : Array (Cell V W)
  ticks : ℕ
  reads : ℕ

def initial (A : Arithmetic V W) (N : ℕ) : Run V W :=
  ⟨Array.emptyWithCapacity N, N + A.initWork + 3, 0⟩

def step (A : Arithmetic V W) (axes : List (Axis V)) (r : Run V W) : Run V W :=
  let k := r.cells.size
  let probe := scan (read A r.cells) k axes k
  let result := finish A probe.winner
  ⟨r.cells.push result.1, r.ticks + probe.ticks + result.2 + 8, r.reads + probe.reads⟩

/-- Executable increasing-address fill into a single preallocated array. -/
def loop (A : Arithmetic V W) (axes : List (Axis V)) : ℕ → Run V W → Run V W
  | 0, r => r
  | j+1, r => loop A axes j (step A axes r)

def fill (A : Arithmetic V W) (axes : List (Axis V)) (N : ℕ) :=
  loop A axes N (initial A N)

/-- Iteration in proof order, equal to the tail-recursive executable loop. -/
def built (A : Arithmetic V W) (axes : List (Axis V)) (N : ℕ) : ℕ → Run V W
  | 0 => initial A N
  | j+1 => step A axes (built A axes N j)

theorem loop_built (A : Arithmetic V W) (axes : List (Axis V)) (N i j : ℕ) :
    loop A axes j (built A axes N i) = built A axes N (i+j) := by
  induction j generalizing i with
  | zero => rfl
  | succ j ih =>
    change loop A axes j (built A axes N (i+1)) = _
    rw [ih, Nat.succ_add, Nat.add_succ]

theorem fill_eq_built (A : Arithmetic V W) (axes : List (Axis V)) (N : ℕ) :
    fill A axes N = built A axes N N := by simpa [fill, built] using loop_built A axes N 0 N

@[simp] theorem built_size (A : Arithmetic V W) (axes : List (Axis V)) (N k : ℕ) :
    (built A axes N k).cells.size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [built, step, Array.size_push] using congrArg Nat.succ ih

end StrideDP
