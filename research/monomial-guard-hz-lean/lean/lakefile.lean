import Lake
open Lake DSL

package integerMultHZ where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib HZ where
  roots := #[`HZ, `ProofCheck]
