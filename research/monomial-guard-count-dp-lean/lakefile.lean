import Lake
open Lake DSL

package integerMultCountDP where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require integerMultDP from ".." / "monomial-guard-dp-lean"

@[default_target]
lean_lib CountDP where
  roots := #[`CountDP, `CountProofCheck]
