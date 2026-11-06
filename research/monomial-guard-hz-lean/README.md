# Lean proof of the h − Z optimal row-addition theorem

This package formalizes the separation-distance theorem and its anchored
full-family proper-minor consequence from [PR #6712](https://github.com/CrocSwap/integer-mult-bounds/pull/6712),
at source commit `03caa7f6cb5bd21c834024e9d81f6b43eb325b91`.
The source package remains unchanged. The Lean development, its original
verification records and its source reference are retained byte for byte in
[`lean/`](lean/).

[中文证明说明](lean/README.md) · [Main theorem](lean/HZ/Optimality.lean) ·
[Full-minor result](lean/HZ/Guards.lean) · [Verification receipt](lean/verification/RESULT.json) ·
[Standalone proof package](IntegerMult-HZ-Lean-20261107.zip)

## Proven result

For a finite labeled coordinate set over any field, let the vector charges be
`y_i = u_i • w_i` and assume their total is zero. Let `h` count the initially
nonzero charges and `Z` be the largest number of nonempty zero-sum blocks
partitioning those labeled charges. Then the least number of paid elementary
row additions making every charge zero is exactly **h − Z**.

An addition updates `u_i += a*u_j`, `w_j -= a*w_i` and `b_j -= a*b_i`, with
distinct coordinates and a nonzero coefficient. It costs one. Permutations and
nonzero diagonal scalings cost zero and may occur anywhere in the execution.
Initially zero coordinates remain available as helpers throughout the proof.

- `HZ.cost_lower_bound` covers every successful legal execution.
- `HZ.cost_attained` constructs an execution with exactly h − Z paid additions.
- `HZ.minimumCost_eq` proves the literal minimum-cost equality.
- `HZ.anchored_guard_optimal` gives the same exact cost for all original proper
  prefix minors under the anchored-carrier and full-parameter-family hypotheses.
- The two five-element-field examples have proven exact minima 2 and 3.

The declaration of the minimum-cost equality explicitly assumes initial total
charge zero. The full determinant is not a tested proper prefix minor.

## Verification and reproduction

The public runner completed on Windows on 2026-11-07 using Lean 4.24.0:

- Compilation passed with warnings treated as errors.
- All 22 audited key declarations use only the allowed standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
- No proof placeholders, new axioms or `native_decide` are used.
- Official lean4checker replayed `ProofCheck` and all its imported declarations
  into a fresh environment; it exited successfully after about 651 seconds.

The checker uses the same Lean kernel, not a second kernel implementation.
These are retained local verification records; no hosted replay is claimed.
See the [full reproduction instructions](lean/README.md#复现),
[pinned toolchain](lean/reference/TOOLCHAIN.json),
[file manifest](lean/MANIFEST.json) and [archive checksum](ARCHIVE.json).
The Lean sources and dependency/configuration files in this publication match
all 12 SHA-256 entries in the successful verification receipt.

Run from the `lean` directory, with Lean 4.24.0 and PowerShell 7 installed:

```text
pwsh -NoProfile -File ./prepare.ps1
git clone --branch v4.24.0 https://github.com/leanprover/lean4checker.git .verification-tools/lean4checker
git -C .verification-tools/lean4checker checkout --detach da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
lake -d .verification-tools/lean4checker build lean4checker
pwsh -NoProfile -File ./verify.ps1 -CheckerExe ./.verification-tools/lean4checker/.lake/build/bin/lean4checker
```

On Windows, append `.exe` to the final checker path. The replay requires its
declared Lean environment and takes several minutes; it is not registered in
the repository's generic Python-only package runner.

## Scope, credit and open next questions

This formalizes the general separation theorem and its anchored full-family
consequence. It does not formalize the later binary-dummy formula, ternary
envelope, orbit counts, NP-completeness, dynamic-programming complexity or an
integer-multiplication complexity exponent.

Prepared by SHIN09-git with substantial OpenAI Codex assistance. The original
monomial-header work, ToikY, Nick Petalas, classical zero-sum debt-partition
literature, and standard row-operation/determinant identities retain their
attribution in [NOTICE](lean/NOTICE) and the [source notice](lean/reference/NOTICE).
Original-text-to-Lean correspondence was checked during this AI-assisted work;
external human review or upstream scientific acceptance is not claimed.
Apache-2.0; the upstream repository and dependency licenses remain applicable.

**Open next questions**

1. Independently review the correspondence between the original theorem and the
   Lean operation model. Start with `State.addRow`, `Operation`, `Passes` and
   `Anchored`; this would review the specification beyond kernel correctness.
   No missing source files block that review.
2. Formalize the binary-family dummy-charge formula. Start by extending the
   lower-bound partition argument to a designated final charge, while keeping
   the dummy outside the actual coordinate set. That extension is not yet
   proved in this package and needs its own explicit specification.
