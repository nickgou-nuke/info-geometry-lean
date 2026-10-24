# Complex-time closed-strip bound: source-only candidate

G-A candidate; uncompiled and requiring independent AA and serial QA. No live
owner edits, builds, tests, dependency edits, budget changes, or transparency changes.

## Contract

On the existing arbitrary complex CStarAlgebra A, take G:selfAdjoint A,
φ:A→L[ℂ]ℂ, X,Y:A and β:ℝ with 0≤β. Prove

    ∃ M:ℝ, 0≤M ∧ ∀ z:ℂ, 0≤z.im → z.im≤β →
      ‖φ (Y * alpha (G:A) z X)‖ ≤ M.

The β=0 case is included. No positivity, normalization, faithfulness or traciality
of φ is needed. Self-adjointness of G is used for real-time norm preservation.
No new carrier, state, orbit definition, or certificate structure is introduced.

## Five focused lemmas

1. continuous_alpha_imaginary: continuity follows from alpha_analyticAt at every
   complex point and composition with s↦I*s.
2. norm_alpha_ofReal: alpha_ofReal_eq_unitary plus StarAlgEquiv.norm_map.
3. norm_alpha_eq_imaginary: z=re(z)+I*im(z), alpha_add, real norm preservation.
4. exists_norm_alpha_le_closedStrip: compactness of [0,β] bounds the continuous
   imaginary-axis orbit norm. Its bound is nonnegative since 0 belongs to [0,β].
   The preceding exact norm identity transfers this to every real part.
5. exists_scalar_alpha_le_closedStrip: operator norm and submultiplicativity give
   M=‖φ‖*(‖Y‖*C). Both the bound and its nonnegativity are derived.

## Source grounding and dependency

Pending substrate imported EXACTLY as scratch.ComplexTimeConjugation20261024:
source SHA256 4ecde7738ff3de4f67bf2131e84c0a7ed624c4af9ba135938e6bb8950e4ddd29,
contract SHA256 428ed393758b005a0403d7503c733498d78b175110199afdc61d97ccb90add85.
Consumes alpha, alpha_analyticAt, alpha_ofReal_eq_unitary and alpha_add.
Parent can change the import on promotion after dependency acceptance; no
copy of the exponential substrate or unitary readback is included here.

Pinned Mathlib source read:
- Analysis/Analytic/Basic.lean: AnalyticAt.continuousAt.
- Analysis/Complex/Basic.lean: Complex.continuous_ofReal.
- Analysis/CStarAlgebra/Spectrum.lean: StarAlgEquiv.norm_map (complex CStar).
- Topology/Order/Compact.lean: IsCompact.bddAbove_image, continuous image bound.
- Analysis/Normed/Operator/Basic.lean: ContinuousLinearMap.le_opNorm.

Bounded repo search of OperatorAlgebra and Canonical strip/alpha bounds included
Canonical/BoundedModularKMSBridge: it consumes an analytic KMS certificate and
explicitly does not prove a strip theorem. This candidate derives this particular
bound on the actual exponential orbit; it makes no repo-wide novelty claim.

## Consumer boundary

A later consumer must instantiate the actual representedCStarClosure, its native
self-adjoint represented generator and the continuous linear vacuum functional,
with their exact existing instances. This candidate does not establish that
specialization, a scalar KMS boundary identity, a state positivity theorem,
faithfulness, an unbounded generator, or a growing-family construction.
Entire analyticity is already derived in the pending substrate; boundedness
here is independently derived from compactness and real unitary isometry.

No kernel acceptance is claimed. The author cannot supply independent AA for
this candidate. Parent owns promotion after separate AA and locked QA.
