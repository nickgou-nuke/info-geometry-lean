# Candidate source-semantic review 09: direct Jordan–Wigner entry equalities

Reviewer: /root/graded_unroll_intake.

Scope: independent source-only differential review. No mathematical owner
edits, Lean/Lake execution, tests, or GitHub operations were performed by
this reviewer. This report is an audit artifact, not a kernel certificate.

## Exact snapshots

Candidate:
/workspace/scratch/9009f3c86480/candidates/graded_unroll/projector_entry/Cl11GradedProjectorDefects.lean

- Candidate SHA-256:
  **c464904edc97f6b0187a47bef83ac2ad9fb4addc6527ba7394f39e3e1038b309**.
- Candidate length: 352 lines.
- Previous reviewed projector SHA-256:
  78e26a1729dc7cd2147a3419e0ef9611869a6cf7c421d9505ac493be9203033b.
- That exact prior snapshot was recovered read-only from local commit
  aa1d6bcca896829df467866f4768fe591e90b0ce in graded-unroll-extension.
- The complete diff against that snapshot was inspected.

The original intake remains the 24,406-byte attachment with SHA-256
f21693468fc1ff3ff5ed07361d18f0f65c8461a090ac2ce8c6d7f480f1ce17c4.
This review changes none of the original claim boundaries recorded in
source-intake-audit.md or the public projector contract.

## Verdict

**No source-semantic blocker found.**

The candidate adds one private carrier abbreviation and three private
entry equalities. It replaces broad unfolding in the three vacuum readout
proofs with those equalities. No existing public declaration statement,
Clifford generator, ordered product, normalization, representation, vacuum
coordinate, or reported defect value changes.

The new equalities are written with proof rfl. Their mathematical statements
match the inspected recursive definitions. This review does not certify
that Lean accepts those proof terms or that the final normalization closes.

## Carrier and recursive-definition check

Binary3 is the left-associated product
((Fin 1 × Fin 2) × Fin 2) × Fin 2. This is the explicit carrier obtained
from TowerMatrix.Idx 3, including the original one-dimensional seed. It
does not quotient, project, or replace the eight-dimensional spinor module.

The inspected source definitions say:

- TowerMatrix.Idx starts at Fin 1 and appends Fin 2 on the right.
- TowerMatrix.kronPow starts at the seed identity and appends its atom on
  the right.
- jwStringWithBase appends identity after a previously indexed site; at
  the final indexed site it uses globalChirality followed by the local atom.
- jwCreation and jwAnnihilation use the two existing Witt atoms.
- jwMajoranaPlus is the matrix sum of those two strings.

Consequently, with U and V the existing creation and annihilation atoms
and Γ the existing gamma_chiral_base, the actual three positive strings are:

| Site | Creation summand | Annihilation summand |
| --- | --- | --- |
| 0 | ((I_seed ⊗ U) ⊗ I₂) ⊗ I₂ | ((I_seed ⊗ V) ⊗ I₂) ⊗ I₂ |
| 1 | ((I_seed ⊗ Γ) ⊗ U) ⊗ I₂ | ((I_seed ⊗ Γ) ⊗ V) ⊗ I₂ |
| 2 | ((I_seed ⊗ Γ) ⊗ Γ) ⊗ U | ((I_seed ⊗ Γ) ⊗ Γ) ⊗ V |

The right-hand sides of jwMajoranaPlus_three_zero_apply,
jwMajoranaPlus_three_one_apply, and jwMajoranaPlus_three_two_apply are
exactly the scalar entry expansions of these Kronecker expressions.
They retain the left association, seed identity, zero/one/two preceding
chirality atoms, and both creation/annihilation summands. The equalities
quantify over arbitrary row and column indices, not just a diagonal entry.

The gamma convention remains the repository convention Γ = gamma_0_base *
gamma_1_base. No chirality sign is substituted or reversed.

## Genuine matrix products and the separating readout

The three revised readout proofs first use Matrix.mul_apply and
Matrix.add_apply. They therefore retain the actual sums over intermediate
matrix indices. Only the entries of individual positive generators are
then rewritten by the new equalities. Subsequent finite normalization uses
the existing atom entries, identities, product-index sums, and Fin sums.

In particular, this proof structure does not replace a product's diagonal
entry by the product of diagonal entries. The scalar products appearing
inside the new lemmas are Kronecker-entry products; they are not a claimed
multiplicative property of the vacuum readout.

An independent hand check agrees with the three retained readout values:
each positive generator flips its own binary coordinate, while preceding
chirality factors are diagonal. Every nonempty product involving distinct
sites therefore has zero all-zero-to-all-zero matrix entry. Expanding the
pair and triple words leaves their identity term with entry 1. The middle
word always includes the site-1 flip, so its entry is 0.

The representation remains jwCliffordRepresentation 3 on the actual
weighted Clifford quotient. Nonzero source defects are still inferred by
applying a separating entry function to a proposed equality with zero.
Neither injectivity of the representation nor multiplicativity of the
entry function is assumed.

The existing consequences remain unchanged:

- The three-factor unnormalized scaling defect has entry −2.
- The ordinary pair and triple idempotence defects have entry −1/8.
- The proposed three-factor quarter-scaling defect has entry −1/32.
- The noncommuting site-projection conclusion follows from the same
  non-idempotent ordered product.

## Definition sources inspected

All four files below were read from the implementation checkout at
/workspace/scratch/9009f3c86480/graded-unroll-extension/lean/InfoGeometry/Clifford.

| File | SHA-256 |
| --- | --- |
| Cl11JordanWignerCARBridge.lean | 9f4acef0cb295e8936c2285b3dbf3b4d6cdb0576a28636db252ffa91a0a1c00d |
| Cl11TensorTower.lean | 1e08191d55b0c7827239332bcc9ba68b97d2c2004772d485ab0b19e2c00dc9ea |
| TowerMatrix.lean | 3489868cb323fad6ea3aed08cae00729cae4ec8f36e6da4ca42c460aa892876b |
| Cl11Matrix.lean | c95d89d20b10271d66e9cbe1632f04d57b817f118d92867b5121c55d7c4f7f85 |

## Execution boundary

The parent reports that the preceding approach failed during global
matrix-wrapper normalization. That execution result was not independently
reauthenticated during this review. The new strategy addresses proof
elaboration and normalization without weakening the mathematical contract.

No success is inferred from the use of rfl, the unchanged numerical values,
or the source-semantic verdict. Exact-source compilation of this candidate
and the subsequent owned-declaration axiom audit remain separate gates.
