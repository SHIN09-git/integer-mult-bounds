# Dummy-charge optimality and binary arbitrary-family formalization

Authorized task: prove the h-Z_* concentration optimum with no operations on the
dummy, derive the exact binary arbitrary-family guard cost, and publish this
development together with the already verified ternary envelope and endpoints.

Pinned mathematical source: PROOF.md at
03caa7f6cb5bd21c834024e9d81f6b43eb325b91, PR 6712.
Inherited HZ sources must remain byte-for-byte unchanged.

The dummy will occur only in a charge function on Option I used for finite
partitions. Every State and Run in the operational theorem remains on I.
No actual augmented operational workspace is introduced.


Completed: Dummy.minimumCost_eq and Binary.cost_eq_h_sub_Zstar, including
arbitrary legal interleavings, all real zero helpers, and the literal fixed-order
principal-minor optimum. No State or Run has an extra dummy coordinate.

Validation PASS: six new modules, warning-as-error compilation, source scan,
28 transitive axiom reports, seven unchanged HZ sources and fresh kernel replay
of DummyProofCheck including all imports. Inputs stayed unchanged during replay.
Final evidence is saved in verification/RESULT.json and SUMMARY.json.

Publication scope: the two new proof packages are added on an isolated branch
based on b87752d. The prior h-Z package and original PR 6712 files remain frozen.
This is formalization of the pinned statements, not a new multiplication exponent.