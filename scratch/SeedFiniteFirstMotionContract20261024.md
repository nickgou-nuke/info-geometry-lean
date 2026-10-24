# Finite-first actual seed motion: source-grounded next contract

Research only. No implementation/build/live edits, no budget or transparency
changes. v12 terminal status now reports terminal_lock_released/exit1; compile
/tmp/qa-a-motion-v12-ob2yd729/compile.log fails154:2 isDefEq1M at obtaining the
generic represented witness. Accepted alignment dependency rebuilt successfully.
This precedes using the action equality; do not repeat the same existential
specialization with another final rewrite.

## Existing finite carrier, not a replacement model

Canonical.CantorBernoulliCStarMatrixTraceState.CStarMatrixStage k is EXACTLY
CStarMatrix (Fin(2^k)) (Fin(2^k)) Complex (:38). Use the existing
CStarMatrix.ofMatrixStarAlgEquiv e : MatrixStage k ≃⋆ₐ[Complex] CStarMatrixStage k.
Do not install a new operator norm/CStar instance on raw MatrixStage.
Let J be the ACTUAL seedStageHom H hH beta and F=J.comp e.symm.toStarAlgHom.
This is a local expression for the existing seed representation in native stage
coordinates, not a new represented carrier or a replacement flow.

## Three small obligations, in order

1. Finite motion first. For H,x:MatrixStage k and H*x-x*H≠0, prove
   exists t:Real,
     complexExponentialConjugationPath (e H) (e x) t ≠ e x
   in CStarMatrixStage k. Transfer the commutator with e.injective and map_mul/
   map_sub. Reuse v11/v12 exists_complexExponentialConjugationPath_ne, whose
   native foundation is ModularFlowExponentialGenerator.
   hasDerivAt_complexExponentialConjugationPath_zero (:52).
   Crucially this theorem contains NO Gibbs family, represented closure, or beta.
   The tilt witness stays the existing entry01 calculation 2*(h:Complex)≠0.

2. Pointwise naturality. For a continuous complex algebra/star-algebra hom F
   between the actual CStar algebras, prove at fixed H,x,t:
     F(complexExponentialConjugationPath H x t)
       = complexExponentialConjugationPath (F H) (F x) t.
   Reuse NormedSpace.map_exp (Mathlib Analysis/Normed/Algebra/Exponential:579),
   twice, map_mul/map_neg/map_smul. It requires Continuous F; do NOT assume
   continuity of an arbitrary ring hom. For the actual F, continuity can be
   derived from its linear map with finite-dimensional domain using native
   LinearMap.continuous_of_finiteDimensional; transfer finite-dimensionality
   through e if its CStarMatrix instance is not automatically available.
   Inspect exact required scalar restriction (Complex -> Real/rat exp API)
   when authoring; no analytic theorem or continuity field is to be postulated.
   Existing repo precedents: Lie.DerivationExponentialRepresentation.
   continuousAlgHom_map_exp uses NormedSpace.map_exp for bounded endomorphisms;
   Canonical.TomitaTakesaki.involutiveConjugation_exp does likewise. Their
   specialized domains do not justify copying a replacement carrier here.

   Then obtain an OWNER-SPECIFIC pointwise equality on the actual seed:
     F(complexExponentialConjugationPath (e H) (e x) t)
       = seedRealTimeAut H hH beta t (J x).
   Use e.symm_apply_apply, the earlier generic expUnitary/path normalization,
   and accepted whole-action/congr_fun alignment. Native seedRealTimeAut uses
   positive exp(i*t*J H), consistent with the finite path. This is a genuine
   representation naturality lemma, not assumed intertwining.
   It remains a possible dependent-elaboration bottleneck; isolate its first
   failure. Do not assert that finite-first automatically fixes normalization.

3. Take the FINITE witness t from1. If the actual native action fixed J x,
   pointwise equality2 gives F(finitePath t)=J x=F(e x). Native
   FiniteSeedRepresentationFaithfulness.seedStageHom_injective and e.symm.injective
   yield finitePath t=e x, contradiction. No existential theorem whose target
   is a generic represented closure is instantiated. Work with one t and one
   equality through the actual hom. Derive F injectivity from the accepted
   theorem, not a new faithfulness assumption or duplicate simple-ring proof.

## Final target, unchanged

For EVERY h,beta:Real with h≠0, let J=seedStageHom (k:=1) (h•tilt2)
(tiltHamiltonian_isHermitian h) beta. Conclude exists t:Real,
seedRealTimeAut (h•tilt2) ... beta t (J switch2) ≠ J switch2.
The finite path is only a witness construction. The final observable and action
remain the actual represented seed flow. No selected state, beta≠0 condition,
all-nonzero-time claim, alternate carrier, or replacement dynamics.

## Narrow handoff

First author finite motion and generic map-path naturality separately from the
concrete seed pointwise application. Reuse generic analytic helpers rather than
repeat derivative calculations. Only after the pointwise native bridge checks
should the final existential wrapper be attempted. Preserve all older files.
Budgets stay1M/500k baseline. Parent controls independent AA/serialized QA.
