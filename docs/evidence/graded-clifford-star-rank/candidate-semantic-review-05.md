# Candidate source-semantic review 05: contract scope

Reviewer: /root/graded_unroll_intake.

Scope: independent read-only comparison of the updated mathematical contract
with the six current owner sources. No mathematical or contract edits,
Lean/Lake execution, tests, or GitHub operations were performed by this reviewer.
This report is the only new review artifact.

## Exact document and source identities

Checkout: /workspace/scratch/9009f3c86480/graded-unroll-extension.

Reviewed contract:
docs/GRADED_CLIFFORD_STAR_RANK_CONTRACT.md.

- Initial document SHA-256, before three precision corrections:
  6631367385ea4d877369f0f965d43d9ef6e855809bb2888593bfd50db9b2a694
- Corrected document SHA-256, read in full and accepted at source scope:
  **256e26af7e0d8093a7d214d7584ca7608e8d674a2d3eb857ee2228251316f98c**

The corrected document was compared against these owner identities:

| Owner | SHA-256 |
|---|---|
| lean/InfoGeometry/Clifford/Cl11GradedAdjoint.lean | 3cfd3f3ba84d1696edde9c07940161948d96c0ecd4f05316af1de5a9de2f72f2 |
| lean/InfoGeometry/Clifford/GradedTensorCutRank.lean | 7d72537012ee6e289fc1c06bc49c100ed89215e88760633c4caad122b80c2174 |
| lean/InfoGeometry/Clifford/Cl11UntwistCutRank.lean | e66706561dae1b754528be595d9b9d5b40f25890fdc4c767cc9d03fb9e8081f5 |
| lean/InfoGeometry/LinearAlgebra/FiniteRealAnticommutation.lean | 6ff63798bde7ae22a89d4b58c95d492207b26e81bba7f039a23fe5a831f23cff |
| lean/InfoGeometry/Clifford/GradedUnrollingCounterexamples.lean | 11a8334a63215c5f443c14821042915259cd8e059ca88b0ff06e3d62cbdd52b2 |
| lean/InfoGeometry/Clifford/Cl11GradedProjectorDefects.lean | e201293de9f1bb81c22a6d468dcb1f60591409d25e8a945f03c33e37d769bc20 |

The earlier source reviews supply the owner context at the listed unchanged
hashes. The concrete-counterexample proof diff was also inspected: it reverses
the diagonal-negation equality in the appropriate direction and exposes the
diagonal block product before taking an entry. It does not change the theorem
types, carrier, or mathematical assumptions.

## Closed documentation issues

| Initial issue | Corrected statement | Status |
|---|---|---|
| The displayed controlled-map involutivity did not explicitly require θ² = id. | Both θ and T are now explicitly real linear involutions before the parity projections and equations are stated. | Closed at source scope |
| Fixed-total-parity rank invariance was worded for an arbitrary controlled map. | It is now restricted to the Clifford twist whose left involution preserves parity; the document explicitly excludes a parity-changing arbitrary left involution. | Closed at source scope |
| The final dependency paragraph connected the native head equivalence to the projector calculations. | It now sends that equivalence to adjoint transport and the one-head rank bridge, while the projector branch uses weighted Clifford relations and the existing Jordan–Wigner algebra representation. | Closed at source scope |

The second qualification is mathematically necessary. With even/odd basis
vectors e₀,e₁ and f₀,f₁, an odd left involution swapping e₀,e₁ sends the
homogeneous-even tensor e₀⊗f₀ + e₁⊗f₁ under the corresponding controlled map
to e₀⊗(f₀+f₁), changing rank from two to one. That counterexample does not
apply to right multiplication by the even Clifford volume, which preserves
left parity.

## Factual scope after the corrections

**No remaining misleading mathematical scope statement was found in the
corrected document at the listed snapshots.**

The source provenance is accurate: exact length, SHA, no terminal newline,
and the unfinished D2 cutoff are retained without inventing a continuation.

The adjoint section correctly distinguishes the transported algebraic
anti-involution from Mathlib's canonical Clifford star. It identifies the
additional coefficient star/parity premise only for the compatibility
theorems and does not infer positivity, norm, or completion.

The rank section uses the genuine canonical contraction range, finite left
dimension, and unrestricted right dimension. Its finite right-tail estimate
explicitly requires both relevant right factors to be finite-dimensional.
The actual coordinate application is restricted to one Clifford head and
does not silently promote the general controlled-map bound to every cut of
an arbitrary-length train.

The dimension section concerns actual finite real representation dimension.
The separate M₃(M₂(ℝ)) witness is correctly described as acting on six real
coordinates. It does not invalidate the finite-real obstruction.

The projector section preserves the native weighted Cl(3,3) carrier, the
ordered word identities, the normalized −1/32 scaling defect, and the −1/8
idempotence readouts. Its explanation correctly distinguishes the algebra
representation from the nonmultiplicative entry-evaluation function.

The explicitly unproved extensions remain clearly separated: arbitrary-length
graded-terminal unrolling, every TT cut, TT existence/minimality, homogeneous
rank equality, sharpness, the integral lattice-index theorem, and analytic
positivity. Their presence in the source audit is not represented as a new
kernel-checked theorem in this PR.

## Execution and acceptance boundary

The document explicitly calls the six owners proof candidates, records the
initial actual CI failure, and requires a fresh exact-revision run before
kernel acceptance. It keeps exact-source compilation, owned-declaration axiom
auditing, semantic review, and integration/root gates separate.

This closes the three reported documentation issues only at source-semantic
scope. It does not change the recorded initial CI failure, authenticate a new
remote run, or establish a current successful compilation/axiom audit.
