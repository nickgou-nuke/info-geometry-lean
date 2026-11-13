# Candidate source-semantic review 04

Reviewer: /root/graded_unroll_intake.

Scope: read-only review of the narrow adjoint/rank repairs and the integrated
site-projection noncommutativity result. No mathematical owner edits,
Lean/Lake execution, tests, or GitHub operations were performed by this reviewer.

## Exact reviewed snapshots

All owner paths are under
/workspace/scratch/9009f3c86480/graded-unroll-extension.

| Owner | SHA-256 |
|---|---|
| lean/InfoGeometry/Clifford/Cl11GradedAdjoint.lean | 3cfd3f3ba84d1696edde9c07940161948d96c0ecd4f05316af1de5a9de2f72f2 |
| lean/InfoGeometry/Clifford/GradedTensorCutRank.lean | 7d72537012ee6e289fc1c06bc49c100ed89215e88760633c4caad122b80c2174 |
| lean/InfoGeometry/Clifford/Cl11GradedProjectorDefects.lean | e201293de9f1bb81c22a6d468dcb1f60591409d25e8a945f03c33e37d769bc20 |

The files and the repair diff from 347f02a57 to e77105c1a were inspected.
The previous reviews remain historical records at their own hashes.

## Verdict

**No mathematical or source-semantic blocker found in these snapshots.**
This verdict concerns source meaning, carrier, and hypotheses only.
It does not establish that the repairs compile.

## Adjoint repair

The added include hStar makes

\[
\theta(\operatorname{star}a)=\operatorname{star}(\theta a)
\]

an actual retained premise of tensorAdjoint_parity and
tensorAdjoint_tmul_homogeneous. This was already a required premise of the
audited mathematical contract; its formal retention corrects an elaboration
gap rather than importing the desired conclusion as an assumption.

The four explicit parity-case goals use exponents 0,0,0,1. They preserve the
same Koszul formula and the same native graded tensor carrier. The basic
transported anti-involution remains independent of hStar; only the
coefficient-parity compatibility statements require that hypothesis.

The additional head noncommutativity witness uses the actual two native
Clifford generators and their faithful matrix images. No coefficient
commutativity, positivity structure, or replacement global star instance
has been introduced.

## Rank repair

The cutRank_zero proof now explicitly maps zero to the zero contraction,
identifies its range with the bottom submodule, and takes its zero finrank.
Its statement and carrier are unchanged.

The finite operator-tail proof constructs the finite-dimensional instance
for U ⊗ B from the already declared finite-dimensional U and B. It does not
assume a finite arbitrary right factor elsewhere, nor does it insert a
commutative coefficient hypothesis. The general infinite-right-factor rank
inequalities retain their earlier scope.

The import changes and explicit instance are implementation-level
dependencies whose successful elaboration remains an execution question.
The revised parityTwist_involutive docstring accurately describes the two
involutive component maps.

## Projector noncommutativity

siteProjections_noncommuting assumes commutation temporarily and applies the
valid result that a product of commuting idempotents is idempotent. The two
site idempotence facts and the proved identification of their ordered product
with pairProjection then contradict pairProjection_not_idempotent.

This proves noncommutativity of the actual site projections in the native
weighted Cl(3,3) carrier. It uses the previously established nonzero defect,
not an assumed noncommutativity conclusion or a scalar replacement.

## Initial execution failure remains separate

The following preserved local CI evidence was read:

- [Initial status](sandbox:/workspace/scratch/9009f3c86480/candidates/graded_unroll/qa/run-43417741663-status.json)
- [Initial kernel log](sandbox:/workspace/scratch/9009f3c86480/candidates/graded_unroll/qa/run-43417741663-kernel.log)

Their SHA-256 values are respectively:

- 387bc422a191a547f8d4f3f589bb6b64c9dc85b025b6bd739c1328e8a9755f46
- c2744f33466b9f8cf379d6075a5fcd8973a1bc2c91ecf8806f20091849bcedd7

The preserved status records an actual failed initial closure check at revision
c0e50c0408a2c00e1ed88ef4793f5200eeb20b05, tree
f07a52f2bebf3c2079dc55b1900a0608c548cfc6. Adjoint, cut-rank, and concrete
counterexample owners failed; the finite-real-anticommutation owner returned
zero. The status explicitly records that no declaration axiom audit was
performed.

The log shows unknown hStar, parity rewrite failures, an unresolved rank-zero
goal, a missing finite tensor-product instance, and separate concrete
counterexample proof errors. This is execution evidence of failure, distinct
from the earlier source-semantic assessments of the intended mathematics.

The current review neither erases that failure nor certifies that the fixes
compiled. Successful exact-source compilation and owned-declaration axiom
auditing of the repaired snapshots remain required. This reviewer inspected
the preserved local files and did not independently reauthenticate their
remote provenance.
