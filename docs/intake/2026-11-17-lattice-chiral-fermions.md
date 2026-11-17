# Frozen intake: lattice chiral fermions and real projector-curvature algebra

## Source identity

- Author: Nathaniel Craig.
- Title: *A gauge-invariant measure for lattice chiral fermions*.
- Version: arXiv:2610.09093v1 [hep-lat], 6 October 2026.
- Version URL: [arXiv:2610.09093v1](https://arxiv.org/abs/2610.09093v1).
- Version PDF URL: [version 1 PDF](https://arxiv.org/pdf/2610.09093v1).
- Received source: user attachment `2610.09093v1(1).pdf`, 126 PDF pages.
- Attachment SHA-256:
  `45c8d3eaecb57f220a444192220464af64f00e3a15cab1d50c4719f62e934382`.

The attachment is preserved unchanged. This record indexes and paraphrases
the portions selected for formalization; it does not replace the paper or
reproduce its complete text. Page references below are the paper's printed
pages. For the cited body pages, the one-based PDF page number is the printed
page plus three. The version URLs identify the supplied source; no later
revision or independent external report is used as verification evidence.

The implementation base is `nickgou-nuke/info-geometry-lean` main
`08c34e03f610b452e03422037949196dc7d92d6d`. The
[theorem contract](../REAL_OVERLAP_PROJECTOR_CURVATURE_CONTRACT.md) fixes the
scope, and the [source review](../REAL_OVERLAP_PROJECTOR_CURVATURE_REVIEW.md)
records exact candidate hashes and subsequent validation status.

## Intake boundary

The paper states a construction of a smooth gauge-invariant overlap-fermion
measure with locality and global integrability properties. This PR selects
finite algebraic ingredients from that argument. The paper's statement is
source provenance, not a theorem established by the new Lean files.

The operator algebra remains noncommutative. Public new phase readouts and
the concrete witness use real matrices; the conventional complex expression
is compared by the repository's existing faithful realification. The internal
phase `J² = -1` is distinguished from a Krein fundamental symmetry `K² = +1`.
No substitution of one square law for the other, or spectral theorem based
solely on Krein self-adjointness, is part of the intake normalization.

## Source-linked causal claim ledger

The status “source-reviewed candidate” means that complete candidate proofs
have passed independent mathematical/source/API review. It does not mean that
Lean compilation or the native axiom audit has run successfully.

| ID | Source or existing premise | Exact selected claim and causal inputs | Disposition |
| --- | --- | --- | --- |
| O1 | Equations (1.3)--(1.5), printed pp2--3 / PDF pp5--6 | For arbitrary associative-ring involutions `gamma` and `sigma`, define dimensionless `d = 1 + gamma*sigma`; derive `gamma*(1-d) = -sigma` and the modified square law. The lattice spacing is absorbed into `d`. | Source-reviewed candidate: `OverlapChirality` |
| O2 | Equation (1.4), p2; O1 | Derive Ginsparg--Wilson with ordered products. More generally, under `gamma² = 1`, modified chirality squares to one iff the Ginsparg--Wilson defect vanishes. | Source-reviewed candidate |
| O3 | Equations (1.6)--(1.7), p3; O2 and existing Cartan projectors | Derive `d*hat_gamma = -gamma*d`, then both mixed projector intertwinings on `Module.End ℝ V`. Preserve the native kernel and identify zero-mode chirality. | Source-reviewed candidate; no sign functional calculus |
| T0 | Equation (4.15), p19 / PDF p22; existing `Core.IdempotentTangent` | Reuse `p*x+x*p=x`, its off-diagonal corners, and the exact double-commutator generator. | Existing owner reused; no duplicate Kato-generator construction |
| T1 | Lemma 5.1 proof, p23 / PDF p26; T0, even product of two tangents, cyclic additive trace | An ordered triple of projector tangents is tangent and has trace zero. | Source-reviewed candidate: `PeirceCurvatureTrace`; finite ingredient of closure only |
| T2 | Equation (8.6), p40 / PDF p43; T0 and cyclic trace | `τ(F(p,x,[g,p])) = τ(g*x)` for `p²=p` and `p*x+x*p=x`; `F` remains the existing sandwiched coefficient. | Source-reviewed candidate; no differentiation of gauge covariance asserted |
| T3 | Equation (4.19), p20 / PDF p23; idempotence and cyclic trace | Remove the final projector under the trace; complementing `p` and negating both insertions reverses the trace. | Source-reviewed candidate |
| R1 | Native matrix trace and `Subalgebra.centralizer ℝ {J}` | Construct `κ_J(T) = (1/2) Tr_R(J*T)` as a cyclic additive functional on the phase centralizer. Feed that actual functional into T1--T3. | Source-reviewed candidate: `RealChiralCurvature`; no cyclicity on arbitrary real matrices |
| R2 | Existing `Quantum.Realification`; R1 | The native faithful matrix embedding and its trace law give `κ_internalJ(realify T) = -Im(Tr_C T)`. Exact commutant reconstruction covers every real matrix centralizing `internalJ`. | Source-reviewed candidate; faithful matrix map, not faithful scalar readout |
| R3 | Equation (4.19), p20; existing curvature naturality and skew-adjointness; R2 and T3 | For self-adjoint `p,x,y` and idempotent `p`, realified curvature has exactly the scalar readout represented by `i Tr_C(p[x,y])`. The pure-imaginary trace condition is derived. | Source-reviewed candidate; no new differential-form object |
| W1 | Existing Gull--Doran real Cl(3) matrices; R1 | On `Fin 4`, use `J=realPhaseAxis`, `P=(1/2)(1+realSigma3)`, `X=realSigma1`, `Y=realSigma2`. Prove phase compatibility, self-adjoint tangency, full `F=2JP`, and `κ_J(F)=-2`. | Source-reviewed candidate: `RealChiralCurvatureExample`; actual four-dimensional witness |
| A1 | Full Lemma 5.1, pp22--24 / PDF pp25--27 | Construct the projector-family differential forms and comparison integral; prove `db=Omega_1-Omega_0` and the determinant-holonomy ratio on the cylinder. | Open debt |
| A2 | Equations (4.15)--(4.17), pp19--20; Theorem 4.1, pp21--22; sections 7--11 | Solve transport, prove all-loop integrability, locality and convergence, reconstruct a gauge-invariant fermion measure, and specialize the required gauge representations. | Open debt |

These edges express proof dependencies. O1--O3 and T0--T3 are distinct finite
branches. No edge is asserted from overlap algebra alone to a differentiable
projector family, or from triple-trace cancellation alone to A1 or A2.

## Existing-owner search and decisions

The bounded source survey covered relevant declarations, alternate names,
imports and consumers in `lean/`, `src/`, and `proofs/`. Searches for
Ginsparg--Wilson, overlap Dirac operators and modified chirality did not locate
an owner for the selected two-involution construction. This is a bounded
search result, not an exhaustive absence theorem about the repository.

The source inspection did locate the following reusable constructions:

- `Cartan/Involution.lean`: native `Module.End` `Pplus` and `Pminus` with
  idempotence, complementarity and involution actions. The new mixed
  intertwining uses these definitions.
- `Core/IdempotentTangent.lean`: `tangent_iff_diagonal_corners_zero`,
  `tangent_eq_double_commutator`, and
  `tangent_iff_adjoint_square_eq_self` supply the actual tangent algebra.
- `OperatorAlgebra/PeirceCompressionCurvature.lean`:
  `tangent_product_commutes`, ordered compression, adjoint compatibility and
  native ring-homomorphism naturality of the existing curvature.
- `Clifford/ChiralProjectorBerryCurvature.lean`: the ring-level coefficient
  `p * (x*y-y*x) * p`; its arguments are operator data, not constructed
  Fréchet derivatives of a family.
- `Quantum/Realification.lean`: arbitrary finite-index `realify`, injectivity,
  `realifyRingHom`, `trace_realify`, `internalJ`, and exact image/centralizer
  reconstruction. These fix the half normalization and the negative sign.
- `Clifford/GullDoranPseudoscalarBridge.lean`: the existing real 4-by-4 phase
  and Pauli matrices, their square and anticommutation laws, and
  `real_pseudoscalar_eq_phaseAxis`.

The larger
`Canonical/VietaIKKTLaxBerryDarkMatterTemperleyLiebHodgePoset.lean` also contains
`kato_adiabatic_berry_transport`, an algebraic commutator/corner theorem. Its
name does not make it an ODE existence or uniqueness theorem, and this PR
reuses the smaller tangent owner instead of introducing another generator API.

Two inspected geometric names do not discharge the missing family geometry:
`Volume/DeterminantBundle.lean` uses the scalar model `DeterminantLine V := ℝ`,
and `Canonical/RealBerryRotorBridge.lean` stores `regularizedStokesLimit` as an
input field of its bridge data. Neither inspected declaration constructs the
paper's varying relative determinant line and global comparison theorem.
This observation is confined to those declarations.

## Remaining obligations for the full paper

1. Construct the Wilson/overlap operator on an actual finite lattice and its
   representation space. Supply the relevant positive-Hilbert adjoint,
   admissible-field domain, uniform spectral gap, sign functional calculus,
   and regularity of the spectral projectors.
2. Differentiate the actual projector family on a fixed carrier. Relate its
   derivatives to the algebraic tangents, solve Kato's transport ODE with
   initial condition and piecewise-smooth compatibility, and prove the
   corresponding transport identities.
3. Construct the determinant line from actual exterior powers of the
   projector ranges, its relative reference factor, local trivializations,
   connection and determinant holonomy. A matrix trace identity supplies
   none of this data by itself.
4. Construct and integrate the differential forms. Establish the exterior
   derivative, parameter-integral compatibility and cylinder Stokes theorem
   needed for the full transgression and phase ratio in Lemma 5.1.
5. Prove the uniform locality, differentiability, interpolation-gap and
   convergence estimates for the refinement construction. Derive the anomaly
   identities for the intended gauge representations and preserve all
   relevant endpoint identifications.
6. Establish full integrability for every closed admissible loop, including
   noncontractible loops, and perform the measure reconstruction. Equality
   of local curvature does not by itself establish this global condition.

The four reviewed candidates target a selected finite operator layer of the
paper. A global fermion measure, the stated Standard Model construction, and
any continuum-limit consequence remain outside their finite theorem targets.
