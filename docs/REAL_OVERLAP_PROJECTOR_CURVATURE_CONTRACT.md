# Real overlap chirality and projector-curvature traces

## Frozen intake

Nathaniel Craig, *A gauge-invariant measure for lattice chiral fermions*,
arXiv:2610.09093v1, 6 October 2026, user-supplied 126-page PDF.
SHA256: `45c8d3eaecb57f220a444192220464af64f00e3a15cab1d50c4719f62e934382`.
The original attachment is retained unchanged. Equations below refer to the
paper's printed page numbers, which differ from PDF page indices by three.

Target repository: `nickgou-nuke/info-geometry-lean`. New-paper ancestry is
main `08c34e03f610b452e03422037949196dc7d92d6d`, independent of pending PR393.

## Intent and exact boundary

Compile the finite noncommutative operator identities used in the paper into
native Lean/Mathlib, reusing the repository's real phase, idempotent, chiral
curvature, and matrix-realification owners. Public geometric readouts use
real matrices and an internal square-minus-one phase operator. Compatibility
with the conventional complex notation is a proved bridge through the
existing faithful realification, not an unproved replacement of scalar i.

The internal phase has square -1 and is distinct from a Krein fundamental
symmetry with square +1. Krein self-adjointness alone does not give the
positive-Hilbert spectral hypotheses used in the paper.

This work does not construct an overlap sign operator from functional
calculus, prove a spectral gap, construct a lattice gauge field, solve Kato's
transport ODE, or reconstruct a fermion integration measure.

## Source-linked claim ledger

| Source | Finite target | Status before generation |
| --- | --- | --- |
| (1.3)--(1.7), pp2--3; (2.6)--(2.9), p11 | Dimensionless overlap d=1+gamma*sigma from two involutions; Ginsparg--Wilson relation, modified chirality -sigma, mixed chiral projector intertwining | Locally provable ring/real-endomorphism identities |
| (4.15), p19 | Tangent equation and Kato generator | Existing `Core.IdempotentTangent`; reuse, no new ODE claim |
| Lemma5.1, p23 | Trace of three projector-tangent operators vanishes | Locally provable algebraic ingredient of curvature closure |
| (8.6), p40 | trace(P[X,[G,P]])=trace(GX) | Locally provable for cyclic additive trace, P²=P, PX+XP=X |
| (4.19), p20; §8.3, p41 | Internal-phase curvature readout, complement sign, realification normalization | Finite real matrix target with explicit commutation conditions |
| Existing Cl(3) real pseudoscalar | A concrete nonzero curvature readout using realPhaseAxis and realSigma1/2/3 | Finite 4-dimensional noncommutative example; no new carrier |
| Lemma5.1 full conclusion | Exterior transgression and determinant holonomy ratio | Open analytic/geometric debt |
| Theorem4.1, pp21--22; §§7--11 | Uniform locality, anomaly cancellation, convergence, global loop integrability, gauge-invariant measure and Standard Model specialization | Open debt, not implied by finite identities |

## Owners and carriers

- `Cartan.Involution`: native `Module.End` projectors `Pplus` and `Pminus`.
- `Core.IdempotentTangent`: actual first-order idempotent equation,
  off-diagonal decomposition and double-commutator reconstruction.
- `OperatorAlgebra.PeirceCompressionCurvature`: two tangents have an even
  product; ordered Gram compression; naturality of projector curvature.
- `Clifford.ChiralProjectorBerryCurvature`: existing coefficient
  `projectorCurvature P X Y = P * (X*Y-Y*X) * P`.
- `Quantum.Realification`: arbitrary finite-index faithful ring homomorphism,
  real internal phase, trace normalization and exact commutant/range theorem.
- `Clifford.GullDoranPseudoscalarBridge`: existing real 4x4 Cl(3) generators
  and their pseudoscalar.
- Native `Matrix.traceAddMonoidHom`, `Matrix.trace_mul_comm`, and native
  subalgebra centralizers where needed; no custom trace axiom or carrier.

The generic trace theorem uses an explicit cyclic additive functional;
finite real matrix consumers instantiate it with the actual matrix trace.
The phase-weighted readout is not a positive or normalized state. Its
cyclicity requires phase-compatible operators, and the half factor accounts
for the doubling in the established realification.

## Dependency order and acceptance

The two involution laws imply overlap chirality and then projector
intertwining. Separately, the existing tangent equation and ordered even
product theorem imply triple-tangent trace cancellation. Cyclicity and the
existing double-commutator reconstruction imply the gauge moment identity.
The actual realification map fixes the phase-readout sign and normalization.
The existing real Cl(3) operators supply a nonzero instance.

No edge from these algebraic statements to a global integration measure is
asserted. Generation, independent source audit, source QA, native compilation,
owned-declaration axiom audit, and root integration are recorded separately.
Allowed foundational axioms are propext, Classical.choice, and Quot.sound.
Pins and maintained verification implementations remain unchanged.
