import Lake
open Lake DSL

package affineGuardQuotient where
  moreLeanArgs := #["-DwarningAsError=true"]

require integerMultOrbitGuard from ".." / "monomial-guard-orbit-lean"

@[default_target]
lean_lib AffineGuard
