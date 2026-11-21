# An affine-image quotient for ternary guard search

[双语短稿 / Bilingual note (PDF)](paper/affine_quotient.pdf) · [LaTeX source](paper/main.tex) · [Exact verifier](verify.py)

For a normalized state $(u,W,b)$ over $\mathbb F_3$, the dual column $z=b+Wa$ runs over an affine set. Keeping $u$ and that set preserves which operation words make every proper leading principal minor of $I-uz^\top$ nonzero in one common row order. The search may also quotient by free row permutations and sign changes. A breadth-first search that retains one reachable, labeled representative per class recovers a shortest sequence of additions on the original input.

In the predecessor's five-row example, the old row quotient has 166 classes at distance exactly three from the start. Adding parameter translations gives 126. Allowing all six affine changes of the single parameter gives 80. Each search returns a three-addition witness that passes in the original row order.

## Reproduce the finite checks

From this directory, run the following command with Python 3. The published results were checked with CPython 3.12.10 and the standard library.

~~~sh
python -I -B verify.py
~~~

The script compares each quotient with a labeled 0–1 search on all 2,106 normalized three-row, one-parameter inputs. The reference search applies dense primal and inverse-transpose matrices and evaluates the literal prefix determinants. The script also reproduces all five-row shells through depth three, replays the recovered instructions, and checks a homogeneous row-space key against point enumeration for all 819 two-row presentations with zero, one, or two parameters.

The PDF contains three pages in each language. From the paper directory, two XeLaTeX passes on [the source](paper/main.tex) build the manuscript.

## Sources and scope

The [original orbit construction](https://github.com/SHIN09-git/integer-mult-bounds/blob/03caa7f6cb5bd21c834024e9d81f6b43eb325b91/research/monomial-guard-settlement/ORBITS.md) and the [complete-row Lean search](https://github.com/SHIN09-git/integer-mult-bounds/blob/5703e56d6eb4b4f0a83af8c23a5d1dddd0b5474f/research/monomial-guard-orbit-lean/README.md) are due to SHIN09-git's research project. Nick Petalas's [charge-only criterion](https://github.com/CrocSwap/integer-mult-bounds/pull/6793) treats the sublevels through two paid additions. This note proves an all-depth statement for equality of the full affine images, measured by distance to the successful set. The endpoint example in Section 2 explains why a prescribed labeled target requires a different test. This package was prepared with OpenAI Codex assistance.

## Open next questions

Can the affine-image path-lifting theorem and witness recovery be formalized against the predecessor Lean model? For several parameters, when does avoiding duplicate states outweigh the cost of computing the new key? The program measures graph sizes and exact distances.
