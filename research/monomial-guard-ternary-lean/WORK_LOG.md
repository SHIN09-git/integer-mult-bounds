# Ternary full-family price envelope

User task: formalize max(S,L) <= C <= 2S+L and attain both endpoints for every
prescribed pair S=r, L=n of nonnegative integers.

Source: PR 6712, commit 03caa7f6cb5bd21c834024e9d81f6b43eb325b91,
research/monomial-guard-settlement/GAP.md and families.py.
Reuse the completed h-Z Lean development without changing its proven sources.

Scope: the true full proper-prefix-minor distance for ternary full affine
families, with free permutations/scalings and paid legal elementary additions.
Separate proof obligations: signed scalar price and ordering; general envelope;
parameterized lower endpoint; parameterized upper endpoint (including its lower
bound against arbitrary mixed executions); zero-parameter cases.

2026-11-07: All nine new Ternary modules compiled with warnings as errors.
The default build imports the full development through TernaryProofCheck.
The source scan and 40 transitive axiom reports passed; only propext,
Classical.choice and Quot.sound occur in those reports. Seven inherited HZ
sources match the prior verification receipt byte for byte.

Main declarations: Ternary.envelope and Ternary.sharp_endpoints. Supporting
declarations include the literal principal-minor bridge, an actual cost-attaining
execution for each family, and the stronger weight lower bound for arbitrary
mixed executions with zero helpers retained. Both parameters range over all
natural numbers, including zero.

Construction variation: one helper with u=0,b=0,w=1 is retained for every r,
whereas the source only adds one when r=0. The exact lower bound permits its use.
No claim about smallest dimensions or prices between the endpoints is made.

The public verification script completed a fresh replay of TernaryProofCheck
and all imported dependencies. PASS: compilation, source audit, transitive axiom checks and fresh kernel replay all succeeded.


Final evidence is saved in verification/RESULT.json and verification/SUMMARY.json.
The dependency revisions and reference-file correspondence were separately checked.
The standalone archive is prepared only after every receipt input still matches.
