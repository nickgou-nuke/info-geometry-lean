# CAR, finite Majorana chains, and the coefficient-kernel criterion

## Ground-truth theorem contract

Inspected base: e49fa4c75b05d7ddb6c7da2f1ff798d67370a6ab.

Reuse the full owner sources, not substitute inverse, Clifford, or Pfaffian predicates:

- Canonical.SuperchargeCARCCRBridge: concrete doubled-real creation/annihilation and spectral projections.
- Quantum.MajoranaPfaffianNaturalClosure: explicit real matrix units, complexified self-adjoint Majoranas.
- Canonical.KitaevChainMajoranaZeroModes: IsMajoranaBasis, kitaevSweetSpotHamiltonian, and the one-bond commutator lemma.
- Canonical.ProjectivePfaffianDeterminantCounts: PfaffianKernel. Its square law is a structure field, not a general combinatorial Pfaffian theorem.
- Canonical.KreinMajoranaZeroModeBlock: conditional determinant/Pfaffian bridge for an explicitly modeled polarized block.
- Canonical.MajoranaPfaffian4: actual signed matching polynomial and proved square law for a general four-by-four skew matrix.

## New maps and assertions

The coefficient space is Fin(2N) -> real; the operator algebra is a nontrivial real algebra A. For the existing IsMajoranaBasis predicate define G(v)=sum_i v_i gamma_i and K(w)=1/4 sum_ij w_ij gamma_i gamma_j.

CAR implies {gamma_i,G(v)}=2 v_i 1 and therefore G is injective. For skew w, prove [K(w),G(v)]=G(w v). It follows that [K(w),G(v)]=0 iff w v=0. This equivalence concerns linear Majorana fields, not arbitrary members of the full Hamiltonian commutant.

For an existing PfaffianKernel P, use the supplied square law and native Matrix.exists_mulVec_eq_zero_iff to obtain P.pfaffian=0 iff there is a nonzero conserved linear Majorana field. This is a conditional general statement; it does not manufacture a Pfaffian witness by naming a square root.

The finite-chain boundary theorem extends the existing one-bond lemma to the entire sweet-spot sum, for either endpoint and a coefficient commuting with that endpoint. Centrality is necessary because the owner accepts its coefficient as an arbitrary ring element.

The explicit witness uses two sites (four Majoranas) on the full complex four-dimensional spin space. The second-site generators carry the parity string. All cross-site CAR and adjoint identities are checked. The concrete doubled-real creation matrix is the upper matrix unit, named annihilationR by the separate natural-closure owner; the coordinate transport states this naming exchange explicitly.

For all six real couplings, instantiate PfaffianKernel with the existing signed matching polynomial af-be+cd and its proved determinant identity. At the open-chain sweet spot the only coupling is w_12=2t, w_21=-2t. The coefficient matrix, its quadratic generator, and the existing two-site chain operator are proved equal under the fixed normalization, with explicit endpoint kernel vectors.

K(w) is the real-skew quadratic generator. In a complex star algebra, the Hermitian physical Hamiltonian uses i K(w); multiplication by a central nonzero i does not change its commutant. No topological sign invariant, stability theorem, bulk gap, or infinite-chain limit is inferred from a vanishing finite-chain Pfaffian.

The polarized-block adapter upgrades the existing determinant-zero criterion to existence of a nonzero coefficient kernel vector, retaining the model map and square-law witness. Its named zeroModeProjector is a chiral projector, not automatically the kernel projector of a separately chosen Hamiltonian.

## Attached notes

The two supplied notes motivate square-zero pairs, active support, and grading. The present task uses the normalized concrete CAR pair: ab+ba=1 and an actual adjoint relation. A general MP pair has only active-support normalization; its reciprocal need not be its adjoint. The attachments' full-ambient grading and centrality claims are not assumptions of this bridge. No extra uniform self-adjointness claim is made for oblique Drazin shells.

## Validation

The dedicated scoped checker compiles all three new modules and their exact transitive repository source closure against the recorded Lean toolchain and pinned Mathlib revision. It audits every named new definition/theorem and rejects any nonfoundational axiom footprint. The workflow result at the checked source commit is the verification evidence. This document alone is not a successful-build claim.

Local command, run sequentially under the repository build lock:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.MajoranaLinearKernel \
  InfoGeometry.Canonical.CARMajoranaFiniteBridge \
  InfoGeometry.Canonical.KreinMajoranaKernelCriterion
```
