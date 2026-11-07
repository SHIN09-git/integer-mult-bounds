import Lake
open Lake DSL

package integerMultSmallFields where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require integerMultCountDP from ".." / "monomial-guard-count-dp-lean"

@[default_target]
lean_lib SmallFields where
  roots := #[`SmallFields, `SmallFieldsProofCheck]
