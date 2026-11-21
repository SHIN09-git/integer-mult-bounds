# An affine-image quotient for ternary guard search

[双语短稿 / Bilingual note (PDF)](paper/affine_quotient.pdf) · [LaTeX source](paper/main.tex) · [Lean proofs](AffineGuard) · [Exact census](verify.py)

For a normalized state $(u,W,b)$ over $\mathbb F_3$, the dual column $z=b+Wa$ runs over an affine set. Keeping $u$ and that set preserves which operation words make every proper leading principal minor of $I-uz^\top$ nonzero in one common row order. The search may also quotient by free row permutations and sign changes. A breadth-first search that retains one reachable, labeled representative per class recovers a shortest sequence of additions on the original input.

In the predecessor's five-row example, the old row quotient has 166 classes at distance exactly three from the start. Adding parameter translations gives 126. Allowing all six affine changes of the single parameter gives 80. Each search returns a three-addition witness that passes in the original row order.

## Lean formalization

Lean 4.24.0 proves the following against the predecessor's definitions of legal operations, literal principal minors and paid cost $C$. The row set and both parameter sets may have arbitrary finite sizes.

| Result | Lean declaration |
| --- | --- |
| Equal labeled affine data give the same answer for each operation word and each specified final order, even across parameter dimensions. Surjective affine reparametrizations preserve the data. | [word_order_iff, data_reparam](AffineGuard/Image.lean) |
| Every paid edge can be executed from any representative of its signed affine class. Success is constant on a class. | [edge_from, winning_key](AffineGuard/Quotient.lean) |
| At every paid length, a quotient walk to a successful class is equivalent to an actual successful execution. Its minimum on normalized inputs is attained and equals $C$. | [lift_walk, winningCost_iff_word, distance_eq_C, distance_minimum](AffineGuard/Distance.lean) |
| The breadth-first solver retains one word per newly reached class. On normalized inputs it returns a shortest word on the original labels and a final free permutation that passes every proper prefix. | [advance_nodup, solve_optimal, solveFixed_correct](AffineGuard/Search.lean) |
| The five-row example has optimal cost three. Its explicit word passes in the original order. The two translated states in Section 2 share a key and have no zero-cost execution between them. | [five_distance, five_passes, endpoint_example](AffineGuard/Examples.lean) |
| In the five-row example the complete-row graph has exactly 166 vertices at minimum distance three. The affine-image graph has exactly 80. | [five_three_shells, five_ball_counts](AffineGuard/FiveCounts.lean) |

The general Lean solver enumerates the affine points and their signed row frames. For the five-row count, Lean proves that sorting the five signed row codes preserves exactly the predecessor's row classes. Taking the least such code over the six invertible affine changes of the parameter preserves exactly the affine-image classes, including constant affine families. [Equivalence of the two encodings](AffineGuard/FiveEncoding.lean)

### The five-row count

| Classes counted from the five-row start | At most two additions | At most three additions | Minimum exactly three |
| --- | ---: | ---: | ---: |
| Complete rows modulo free row operations | 47 | 213 | 166 |
| Primal column and dual affine image modulo free row operations | 42 | 122 | 80 |

The proof projects each complete closed ball to the affine quotient before taking the difference. This excludes a class whenever any representative reaches it in at most two additions. Lean identifies each resulting finite count with the cardinality of the set of vertices satisfying the original graph's minimum-distance predicate. [Closed-ball semantics and exact shells](AffineGuard/FiveShells.lean)

The certificate lists the 40 legal paid additions from each of the 47 complete-row classes within two steps. Lean recomputes the resulting 1,880 target codes, checks a parent for each newly listed class, and computes the affine code for each of the 213 representatives. The numerical theorem uses ordinary kernel reduction. Run `lake build AffineGuard.FiveCounts` in this directory to check it. Python can regenerate the witness table. [Certificate verifier](AffineGuard/FiveCertificate.lean) · [Witness table](AffineGuard/FiveTable.lean) · [Generator](generate_shell_certificate.py)

With this package and both adjacent predecessor packages from the same branch, run the following commands in this directory. Lake reads the pinned mathlib revision from the manifest. A matching mathlib binary cache can be fetched with `lake exe cache get` before building.

~~~sh
lake build AffineGuard
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true --run Checks.lean
lake env lean4checker --fresh -v AffineGuard.FiveCounts
~~~

The final command uses the official Lean 4.24.0 checker on the command path. Its target imports the solver, all general proofs and the concrete example theorems. The executable checks include all 72 normalized two-row, one-parameter inputs and replay each returned word. [Checker source](https://github.com/leanprover/lean4checker/tree/da26eb05e9959402afcb9bd6dfe5dc4f700f70d6) · [Verification record](verification/RESULT.json) · [Axiom audit](Audit.lean) · [Executable checks](Checks.lean)

## Reproduce the finite checks

From this directory, run the following command with Python 3. The published results were checked with CPython 3.12.10 and the standard library.

~~~sh
python -I -B verify.py
python -B generate_shell_certificate.py --check
~~~

The script compares each quotient with a labeled 0–1 search on all 2,106 normalized three-row, one-parameter inputs. The reference search applies dense primal and inverse-transpose matrices and evaluates the literal prefix determinants. The script also reproduces all five-row shells through depth three, replays the recovered instructions, and checks a homogeneous row-space key against point enumeration for all 819 two-row presentations with zero, one, or two parameters.

The PDF contains three pages in each language. From the paper directory, two XeLaTeX passes on [the source](paper/main.tex) build the manuscript.

## Sources and scope

The [original orbit construction](https://github.com/SHIN09-git/integer-mult-bounds/blob/03caa7f6cb5bd21c834024e9d81f6b43eb325b91/research/monomial-guard-settlement/ORBITS.md) and the [complete-row Lean search](https://github.com/SHIN09-git/integer-mult-bounds/blob/5703e56d6eb4b4f0a83af8c23a5d1dddd0b5474f/research/monomial-guard-orbit-lean/README.md) are due to SHIN09-git's research project. Nick Petalas's [charge-only criterion](https://github.com/CrocSwap/integer-mult-bounds/pull/6793) treats the sublevels through two paid additions. This note proves an all-depth statement for equality of the full affine images, measured by distance to the successful set. The endpoint example in Section 2 explains why a prescribed labeled target requires a different test. This package was prepared with OpenAI Codex assistance.

The Lean code reuses the predecessor's legal gates, physical replay, list deduplication and final-order finder. Its breadth-first layer and fuel inductions adapt the predecessor proofs to affine-image classes. [Predecessor source and attribution](../monomial-guard-orbit-lean/NOTICE)

## Open next questions

For several parameters, when does the smaller search offset the cost of computing the affine key? A comparison of homogeneous row reduction with point enumeration on the same inputs would measure this trade-off.
