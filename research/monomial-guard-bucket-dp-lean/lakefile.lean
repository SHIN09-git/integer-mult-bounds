import Lake
open Lake DSL

package integerMultBucketDP where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require integerMultStrideDP from ".." / "monomial-guard-stride-dp-lean"

@[default_target]
lean_lib BucketDP where
  roots := #[`BucketDP, `BucketProofCheck]
