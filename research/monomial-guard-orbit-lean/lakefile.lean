import Lake
open Lake DSL

package integerMultOrbitGuard where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require integerMultTernary from ".." / "monomial-guard-ternary-lean"

@[default_target]
lean_lib OrbitGuard where
  roots := #[`OrbitGuard, `OrbitProofCheck]
