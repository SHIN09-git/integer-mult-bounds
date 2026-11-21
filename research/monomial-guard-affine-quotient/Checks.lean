import AffineGuard

open Ternary
open OrbitGuard (State replay)
open OrbitGuard.Examples (normalized directPass rawWithin tinyCases reordered pair triple twoSlopes)
open AffineGuard

private def check (label : String) (result : Bool) : IO Unit := do
  unless result do throw (IO.userError label)
  IO.println ("PASS " ++ label)

private def checkWord (s : State (Fin m) (Fin d)) (expected : ℕ) : Bool :=
  normalized s && match AffineGuard.solveFixed s with
    | none => false
    | some (word, order) => word.length == expected && directPass ((replay s word).permute order)

private def checkTiny (s : State (Fin 2) (Fin 1)) : Bool :=
  match AffineGuard.solve s with
  | none => false
  | some word => rawWithin s word.length && (List.range word.length).all (fun j => !rawWithin s j)
    && (directPass (replay s word) || directPass ((replay s word).permute (Equiv.swap 0 1)))

def main : IO Unit := do
  let left := Examples.leftEndpoint
  let right := Examples.rightEndpoint
  check "translated presentations share an affine key and have different free row orbits"
    (key left == key right && OrbitGuard.vertex left != OrbitGuard.vertex right)
  check "equal keys across one and two parameter coordinates" (key left == key Examples.redundant)
  check "zero additions with a necessary final free swap" (!directPass reordered && checkWord reordered 0)
  check "one paid addition" (checkWord pair 1)
  check "two paid additions with one parameter" (checkWord triple 2)
  check "two paid additions with two independent parameters" (checkWord twoSlopes 2)
  check "all 72 normalized two-row one-parameter inputs versus exhaustive labeled words"
    (tinyCases.length == 72 && tinyCases.all checkTiny)
  check "three instructions replay on the original five labels in the identity order"
    (Examples.fiveWord.length == 3 && directPass (replay OrbitGuard.Examples.five Examples.fiveWord))
  let old₂ := Census.rowBall 2
  let old₃ := Census.rowBall 3
  let new₂ := Census.affineBall 2
  let new₃ := Census.affineBall 3
  check "five-row complete-row closed balls 47 and 213, shell 166"
    (old₂.card == 47 && old₃.card == 213 && (old₃ \ old₂).card == 166)
  let shifts₂ := Census.translationBall 2
  let shifts₃ := Census.translationBall 3
  check "five-row translation-only closed balls 47 and 173, shell 126"
    (shifts₂.card == 47 && shifts₃.card == 173 && (shifts₃ \ shifts₂).card == 126)
  check "five-row affine-image closed balls 42 and 122, shell 80"
    (new₂.card == 42 && new₃.card == 122 && (new₃ \ new₂).card == 80)
