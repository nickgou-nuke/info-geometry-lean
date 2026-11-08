/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.MobiusClassification
import InfoGeometry.Canonical.MoebiusKleinStatisticalZornSynthesis
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import InfoGeometry.OperatorAlgebra.MobiusClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysKleinActionBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset
import InfoGeometry.SuperGrassmannian.GradedGraphTransition
import InfoGeometry.SuperGrassmannian.MoebiusSuperGrassmannianCPT
import InfoGeometry.SuperGrassmannian.SuperGrassmannianMoebiusQuotient
import InfoGeometry.SuperGrassmannian.UnorientedSuperGrassmannianCPT
import InfoGeometry.SuperGrassmannian.BerezinianSheafStiefelWhitney
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import InfoGeometry.Supergeometry.BerezinianDecomposition
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Topology.KleinRealOperatorDescent
import InfoGeometry.External.Auto.SquashingOperator
import InfoGeometry.External.Auto.BiquaternionMobiusSquashing
import InfoGeometry.Canonical.ZornVectorMatrixMobiusAction
import InfoGeometry.Canonical.DrazinSupergradedWeyl
import InfoGeometry.Canonical.GLSupermatrixGradedLie
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import InfoGeometry.Canonical.Z3TrialityCapstone
import InfoGeometry.Canonical.OperatorBerezinianCore
import InfoGeometry.Canonical.SuperdeterminantBerezinianBridge
import InfoGeometry.Canonical.BerezinianSuperBarrierBridge
import InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge
import InfoGeometry.Canonical.RelativeModularBerezinianBridge
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.Canonical.IntensiveLogDetPositivityTension

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.MoebiusTetraktysKleinBerezinianWeylPoset
Role: Canonical 6-Stage Causal Poset (`𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`) unifying the
  repository's preexisting owners for:
  1. `𝔐₁` (`M1_PlanarToOperatorRingMoebiusLift`): Planar `SL(2, ℂ)` Möbius trace-squared
     classification, projective trace-determinant invariance, failure of raw single-sheet
     determinant sign under projective `i`-scaling (`determinant_sign_not_projective_invariant`),
     and lift to the noncommutative ring of operators (`operatorMobiusAction`),
  2. `𝔐₂` (`M2_TetraktysOrientationCharacterization`): Tetraktys orientation characterization
     (`1 - (2 : ℤ) • P = -invS P` is the orientation-reversing grading involution, not a single-sheet
     positive-cone perturbation), Klein-four sandwich action (`peirceKleinHom`,
     `tetraktys_sandwich_channels_are_peirce_klein_action`), and polarization-swapping
     Möbius anticommutation (`moebius_anticommutes_polarization`, `moebius_symplectic_anti_invariance`),
  3. `𝔐₃` (`M3_KleinBottleOperatorAlgebraQuotientGluing`): Quotienting and gluing the two sides
     like a Klein bottle to construct the non-oriented topological space out of the algebra of
     operators (`AssociatedOperatorAlgebra`, `operator_algebra_quotient_packet`, and
     unipotent Klein edge-transition closure `twisted_edge_transition_cocycle_and_klein_quotient_bridge`),
  4. `𝔐₄` (`M4_GroupMoebiusSquashingAndCayleyWeylTransform`): Classifying transformations via
     Möbius operators acting on groups (`modularBoostSL2_add`), holographic/Cayley squashing of
     operators (`squash_at_defect`, `exp_of_squash`, `cayley_biquaternion_closure`,
     `mobius_biquaternion_closure`), and Peirce nilpotent conjugation (`conjPlus`, `conjMinus`),
  5. `𝔐₅` (`M5_BerezinianSuperdeterminantAndGradedPotential`): Potentials and Berezinian
     superdeterminant after orientation and Klein-bottle gluing (`opNoncommBerezinian`,
     `superdeterminantBerezinian`, `canonicalBerezinian_pos`, `oddReflection_berezinian`,
     `superBerezinianBarrier_eq_bosonic_sub_fermionic`, and `operatorMassieu` = `log Ber`),
  6. `𝔐₆` (`M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure`): Weyl gauge invariance of
     two-sheet relative determinant character (`determinantCharacter_gaugeRescale`), strict
     positivity of two-sheet relative volume (`relativeVolumeScale_pos`), additive logarithmic
     potential chain rule (`logRelativeVolumePotential_mulTransport`), graded supertrace
     Weyl scale extraction (`total_deformation_superTrace`), and the dimension-independent
     operator-norm / intensive-trace cubic bound.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.MoebiusTetraktysKleinBerezinianWeylPoset

open Matrix
open scoped Matrix CStarAlgebra MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset
open InfoGeometry.SuperGrassmannian.MoebiusQuotient
open InfoGeometry.SuperGrassmannian.WeylBerezinian
open KleinBrillouinBase KleinBottleOrbitQuotient
open InfoGeometry.Topology.KleinRealOperatorDescent
open SquashingOperator
open BiquaternionMobiusSquashing
open InfoGeometry.Canonical.MoebiusKleinStatisticalZornSynthesis
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.SuperdeterminantBerezinianBridge
open InfoGeometry.Canonical.BerezinianSuperBarrierBridge
open InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge
open InfoGeometry.Canonical.SouriauConformalKKT
open InfoGeometry.Canonical.CartanBerezinianCore
open InfoGeometry.Canonical.WeylGaugeOperatorLift
open InfoGeometry.Canonical.IntensiveLogDetPositivityTension
open InfoGeometry.Analysis.PositiveMatrixDikin

/-! ===========================================================================
    Section 0: The 6-Stage Causal Poset (`𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`)
    =========================================================================== -/

/-- The 6-stage causal poset ordering the repository's operator Möbius, Tetraktys orientation,
Klein-bottle operator-algebra quotient, operator squashing, Berezinian super-potential,
and Weyl-gauge volume architecture. -/
inductive MoebiusKleinBerezinianWeylStage : Type
  | M1_PlanarToOperatorRingMoebiusLift
  | M2_TetraktysOrientationCharacterization
  | M3_KleinBottleOperatorAlgebraQuotientGluing
  | M4_GroupMoebiusSquashingAndCayleyWeylTransform
  | M5_BerezinianSuperdeterminantAndGradedPotential
  | M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure
  deriving DecidableEq, Repr, Inhabited

namespace MoebiusKleinBerezinianWeylStage

/-- Strictly monotone integer rank `0..5` witnessing the causal ordering `𝔐₁ ≺ ⋯ ≺ 𝔐₆`. -/
def rank : MoebiusKleinBerezinianWeylStage → ℕ
  | .M1_PlanarToOperatorRingMoebiusLift => 0
  | .M2_TetraktysOrientationCharacterization => 1
  | .M3_KleinBottleOperatorAlgebraQuotientGluing => 2
  | .M4_GroupMoebiusSquashingAndCayleyWeylTransform => 3
  | .M5_BerezinianSuperdeterminantAndGradedPotential => 4
  | .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure => 5

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> revert h <;> decide

instance instLinearOrderMoebiusKleinBerezinianWeylStage :
    LinearOrder MoebiusKleinBerezinianWeylStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edges of the 6-stage Möbius–Tetraktys–Klein–Berezinian–Weyl poset. -/
def causalEdge : MoebiusKleinBerezinianWeylStage → MoebiusKleinBerezinianWeylStage → Prop
  | .M1_PlanarToOperatorRingMoebiusLift, .M2_TetraktysOrientationCharacterization => True
  | .M2_TetraktysOrientationCharacterization, .M3_KleinBottleOperatorAlgebraQuotientGluing => True
  | .M3_KleinBottleOperatorAlgebraQuotientGluing, .M4_GroupMoebiusSquashingAndCayleyWeylTransform => True
  | .M4_GroupMoebiusSquashingAndCayleyWeylTransform, .M5_BerezinianSuperdeterminantAndGradedPotential => True
  | .M5_BerezinianSuperdeterminantAndGradedPotential, .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_strict_rank_mono {a b : MoebiusKleinBerezinianWeylStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem causalEdge_irrefl (a : MoebiusKleinBerezinianWeylStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : MoebiusKleinBerezinianWeylStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : MoebiusKleinBerezinianWeylStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

theorem strict_six_stage_chain :
    MoebiusKleinBerezinianWeylStage.M1_PlanarToOperatorRingMoebiusLift <
      .M2_TetraktysOrientationCharacterization ∧
    MoebiusKleinBerezinianWeylStage.M2_TetraktysOrientationCharacterization <
      .M3_KleinBottleOperatorAlgebraQuotientGluing ∧
    MoebiusKleinBerezinianWeylStage.M3_KleinBottleOperatorAlgebraQuotientGluing <
      .M4_GroupMoebiusSquashingAndCayleyWeylTransform ∧
    MoebiusKleinBerezinianWeylStage.M4_GroupMoebiusSquashingAndCayleyWeylTransform <
      .M5_BerezinianSuperdeterminantAndGradedPotential ∧
    MoebiusKleinBerezinianWeylStage.M5_BerezinianSuperdeterminantAndGradedPotential <
      .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end MoebiusKleinBerezinianWeylStage

/-! ===========================================================================
    Section 1: Stage `𝔐₁` — Planar Möbius Classification Lifted to the Ring of
    Operators & Projective Failure of Naive Determinant Sign
    =========================================================================== -/

/-- **Stage `𝔐₁` Theorem (`stage_M1_planar_to_operator_ring_moebius_lift`)**:
Reuses `MobiusClassification.lean`, `MoebiusKleinStatisticalZornSynthesis.lean`, and
`OperatorMobiusAction.lean`:
1. Planar `SL(2, ℂ)` transformations are disjointly classified by `traceSq`: parabolic is
   neither elliptic nor hyperbolic, and elliptic is never hyperbolic,
2. Projective scaling by `Complex.I` preserves the planar Möbius transformation while reversing
   the ordinary determinant sign (`Matrix.det (matrixScale Complex.I A_m) = -Matrix.det A_m`),
   whereas `projectiveTraceInvariant` is invariant under all nonzero projective rescalings,
3. Lifted to any noncommutative operator ring `A`, `operatorMobiusAction` satisfies the exact
   matrix-composition law `operatorMobiusAction (g * h) v = operatorMobiusAction g (operatorMobiusAction h v)`,
   its carrier `OperatorMatrix A` is noncommutative (`mobiusForwardUnit * mobiusBackwardUnit ≠ ...`),
   and `thermalBogoliubovMatrix` acts on operator pairs as `thermalAnnihilator` and `thermalCreator`. -/
theorem stage_M1_planar_to_operator_ring_moebius_lift
    {M_par M_ell : InfoGeometry.SL2C}
    (h_par : InfoGeometry.IsParabolic M_par)
    (h_ell : InfoGeometry.IsElliptic M_ell)
    (c : ℂ) (hc : c ≠ 0) (A_m : Mat2C) (z : ℂ)
    {A : Type*} [Ring A] [Algebra ℂ A] [Nontrivial A]
    (g h : OperatorMatrix A) (v : OperatorPair A)
    (a_op d_op c_op b_op : A) (u_bog v_bog : ℂ) :
    (¬ InfoGeometry.IsElliptic M_par ∧
     ¬ InfoGeometry.IsHyperbolic M_par ∧
     ¬ InfoGeometry.IsHyperbolic M_ell) ∧
    (projectiveTraceInvariant (matrixScale c A_m) = projectiveTraceInvariant A_m ∧
     matrixMobiusAction (matrixScale Complex.I A_m) z = matrixMobiusAction A_m z ∧
     Matrix.det (matrixScale Complex.I A_m) = -Matrix.det A_m) ∧
    (operatorMobiusAction (g * h) v = operatorMobiusAction g (operatorMobiusAction h v) ∧
     operatorMobiusAction (1 : OperatorMatrix A) v = v ∧
     mobiusForwardUnit (A := A) * mobiusBackwardUnit (A := A) ≠
       mobiusBackwardUnit (A := A) * mobiusForwardUnit (A := A) ∧
     operatorMobiusAction (thermalBogoliubovMatrix (A := A) u_bog v_bog) ![a_op, d_op] 0 =
       thermalAnnihilator a_op d_op u_bog v_bog ∧
     operatorMobiusAction (thermalBogoliubovMatrix (A := A) u_bog v_bog) ![b_op, c_op] 1 =
       thermalCreator c_op b_op u_bog v_bog) :=
  ⟨⟨InfoGeometry.not_elliptic_of_parabolic h_par,
    InfoGeometry.not_hyperbolic_of_parabolic h_par,
    InfoGeometry.not_hyperbolic_of_elliptic h_ell⟩,
   ⟨projectiveTraceInvariant_matrixScale c hc A_m,
    (determinant_sign_not_projective_invariant A_m z).1,
    (determinant_sign_not_projective_invariant A_m z).2⟩,
   ⟨operatorMobiusAction_mul g h v,
    operatorMobiusAction_one v,
    operatorMatrix_noncommutative (A := A),
    thermalAnnihilator_eq_operatorMobiusAction a_op d_op u_bog v_bog,
    thermalCreator_eq_operatorMobiusAction c_op b_op u_bog v_bog⟩⟩

/-! ===========================================================================
    Section 2: Stage `𝔐₂` — Tetraktys as the Tool for Characterizing Orientation
    (`1 - 2P = -invS P`) & Klein-Four Sandwich Channels
    =========================================================================== -/

/-- **Stage `𝔐₂` Theorem (`stage_M2_tetraktys_orientation_characterization`)**:
Reuses `Tetraktys.lean`, `TetraktysKleinActionBridge.lean`, and `SuperGrassmannianMoebiusQuotient.lean`:
1. In any ring `B` with idempotent `P * P = P`, the operator `1 - (2 : ℤ) • P` is **not** a
   positive-cone perturbation: it is `-invS P = (1 - P) - P`, the **Tetraktys orientation-reversing
   grading involution** satisfying `(1 - (2 : ℤ) • P) * (1 - (2 : ℤ) • P) = 1` and
   `(1 - (2 : ℤ) • P) * X * (1 - (2 : ℤ) • P) = parityConjRingEquiv hP X`,
2. On the unit-horizon locus `genV P A C = 1`, the four Tetraktys sandwich channels
   `(grpId, grpPhi, grpJ, grpSig)` are the four automorphisms of the Klein-four group action
   `peirceKleinHom hP A C hV`,
3. On the `2 × 2` polarization carrier `K_mat = diag(1, -1)`, the Möbius sheet swap `M_mat`
   anticommutes with `K_mat` (`M_mat * K_mat + K_mat * M_mat = 0`), preserves the neutral metric
   `g_mat`, and reverses the symplectic orientation (`M_matᵀ * omega_mat * M_mat = -omega_mat`). -/
theorem stage_M2_tetraktys_orientation_characterization
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C = 1) (X : B)
    {R : Type*} [CommRing R] :
    ((1 : B) - (2 : ℤ) • P = -invS P ∧
     ((1 : B) - (2 : ℤ) • P) * ((1 : B) - (2 : ℤ) • P) = 1 ∧
     ((1 : B) - (2 : ℤ) • P) * X * ((1 : B) - (2 : ℤ) • P) = parityConjRingEquiv hP X) ∧
    (grpId P A C X = X ∧
     grpPhi P A C X = phiUnitSquareEquiv hP A C hV X ∧
     grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) ∧
     grpSig P A C X = parityConjRingEquiv hP X) ∧
    (M_mat (R := R) * K_mat + K_mat * M_mat = 0 ∧
     (M_mat (R := R)).transpose * g_mat * M_mat = g_mat ∧
     (M_mat (R := R)).transpose * omega_mat * M_mat = -omega_mat) := by
  have hInvNeg : (1 : B) - (2 : ℤ) • P = -invS P := by
    peirce_nf hP
  have hInvSq : ((1 : B) - (2 : ℤ) • P) * ((1 : B) - (2 : ℤ) • P) = 1 := by
    peirce_nf hP
  have hParity :
      ((1 : B) - (2 : ℤ) • P) * X * ((1 : B) - (2 : ℤ) • P) = parityConjRingEquiv hP X := by
    change ((1 : B) - (2 : ℤ) • P) * X * ((1 : B) - (2 : ℤ) • P) = invS P * X * invS P
    rw [hInvNeg]
    noncomm_ring
  exact ⟨⟨hInvNeg, hInvSq, hParity⟩,
         tetraktys_sandwich_channels_are_peirce_klein_action hP A C hV X,
         ⟨moebius_anticommutes_polarization (R := R),
          moebius_metric_isometry (R := R),
          moebius_symplectic_anti_invariance (R := R)⟩⟩

/-! ===========================================================================
    Section 3: Stage `𝔐₃` — Quotienting & Gluing the Different Sides Like a
    Klein Bottle out of the Algebra of Operators
    =========================================================================== -/

/-- **Stage `𝔐₃` Theorem (`stage_M3_klein_bottle_operator_algebra_quotient_gluing`)**:
Reuses `KleinBottleOrbitQuotient.lean`, `KleinRealOperatorDescent.lean`, and
`NonCommutativeKMSStripKleinMonodromyPoset.lean`:
1. The topological orbit quotient `KleinBrillouinQuotient = Quotient glideSetoid` glues the
   Brillouin torus by `torusGlide` (`quotientMap (torusGlide k) = quotientMap k`), with surjective
   continuous quotient map `quotientMap : BrillouinTorus → KleinBrillouinQuotient` and linear
   isomorphism `fieldEquiv : (KleinBrillouinQuotient → V) ≃ₗ[ℝ] invariantFields` descending
   operators to the Klein quotient (`quotientOperator_apply`),
2. In any star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent `P`, the KMS-to-critical-strip
   bijection, period-two winding monodromy `monodromyIter (2 * k) P X = X`, and unipotent Klein
   quotient edge-transition closure `edgeTransition P (1 + conePlus P A) (1 - conePlus P A) (edgeTransition ... X) = X`
   glue the two Peirce sheets with exact period-2 closure. -/
theorem stage_M3_klein_bottle_operator_algebra_quotient_gluing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (field : KleinBrillouinQuotient → V) (pt : BrillouinTorus)
    {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (S_kms X_crit B_im A C X : B) (n k : ℕ) :
    ((Function.Surjective quotientMap ∧
      Continuous quotientMap ∧
      Topology.IsQuotientMap quotientMap ∧
      (∀ p_torus, quotientMap (torusGlide p_torus) = quotientMap p_torus)) ∧
     (fieldEquiv (V := V) field).1 pt = field (quotientMap pt)) ∧
    (kmsToCrit P (critToKms P X_crit) = X_crit ∧
     critToKms P (kmsToCrit P S_kms) = S_kms ∧
     monodromyIter (2 * k) P X = X ∧
     logisticOpPlus P A C + logisticOpMinus P A C = 1 ∧
     edgeTransition P (1 + conePlus P A) (1 - conePlus P A)
       (edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X) := by
  rcases stage_D35_kms_strip_klein_monodromy_logistic_and_edge_bridge_master_synthesis
      (P := P) (S_kms := S_kms) (X_crit := X_crit) (B_im := B_im) (A := A) (C := C) (X := X)
      hP hPsym n k with
    ⟨_, hKms1, hKms2, _, _, hMonEven, _, hLogSum, _, _, _, hEdge⟩
  exact ⟨⟨klein_orbit_quotient_packet, fieldEquiv_apply field pt⟩,
         ⟨hKms1, hKms2, hMonEven, hLogSum, hEdge⟩⟩

/-! ===========================================================================
    Section 4: Stage `𝔐₄` — Classifying Transformations via Möbius Operators
    Acting on Groups, Squashing of Operators, & Unipotent Conjugation
    =========================================================================== -/

/-- **Stage `𝔐₄` Theorem (`stage_M4_group_moebius_squashing_and_unipotent_conjugation`)**:
Reuses `SquashingOperator.lean`, `BiquaternionMobiusSquashing.lean`,
`ZornVectorMatrixMobiusAction.lean`, and `PeirceSpine/Unipotent.lean`:
1. The holographic squashing operator `squash D = tanh D` vanishes at the topological defect
   (`squash 0 = 0`), and the Cayley squashing transform `κ = expCayleySquash E = (E - 1)/(E + 1)`
   reconstructs `E = (1 + κ)/(1 - κ)` and closes the Pauli-biquaternion subalgebra `Xab a b = aI + bσ₁`
   under both Cayley squashing and general Möbius transformations `(pX + qI)(rX + tI)⁻¹`,
2. The modular boost group `modularBoostSL2 : ℝ → SL(2, ℝ)` satisfies the group law
   `modularBoostSL2 (s + t) = modularBoostSL2 s * modularBoostSL2 t` and acts by affine Möbius
   scaling `mobiusAffine (modularBoostMatrix s) x = exp(2s) * x`,
3. On any operator ring `B` with idempotent `P * P = P`, the unipotent Peirce shears `conjPlus P A`
   form an additive one-parameter group (`conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X`)
   preserving the horizon mass operator `genV P A₁ C₁`. -/
theorem stage_M4_group_moebius_squashing_and_unipotent_conjugation
    {E_param κ : ℂ} (hE : E_param + 1 ≠ 0) (hκ : κ = expCayleySquash E_param) (hden : 1 - κ ≠ 0)
    (p_m q_m r_m t_m a_m b_m : ℂ) (h_mob : (r_m * a_m + t_m) ^ 2 - (r_m * b_m) ^ 2 ≠ 0)
    (s_boost t_boost x_aff : ℝ)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A₁ A₂ C₁ X : B) :
    (squash 0 = 0 ∧
     E_param = (1 + κ) / (1 - κ) ∧
     (p_m • Xab a_m b_m + q_m • (1 : M2C)) * invPauli (r_m * a_m + t_m) (r_m * b_m) =
       Xab (mobiusAlpha p_m q_m r_m t_m a_m b_m) (mobiusBeta p_m q_m r_m t_m a_m b_m)) ∧
    (InfoGeometry.Canonical.modularBoostSL2 (s_boost + t_boost) =
       InfoGeometry.Canonical.modularBoostSL2 s_boost *
         InfoGeometry.Canonical.modularBoostSL2 t_boost ∧
     InfoGeometry.Canonical.mobiusAffine (InfoGeometry.Canonical.modularBoostMatrix s_boost) x_aff =
       Real.exp (2 * s_boost) * x_aff) ∧
    (conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X ∧
     conjPlus P A₁ (genV P A₁ C₁) = genV P A₁ C₁) :=
  ⟨⟨squash_at_defect,
    exp_of_squash hE hκ hden,
    mobius_biquaternion_closure p_m q_m r_m t_m a_m b_m h_mob⟩,
   ⟨InfoGeometry.Canonical.modularBoostSL2_add s_boost t_boost,
    InfoGeometry.Canonical.modularBoost_mobius_affine s_boost x_aff⟩,
   ⟨(archetype_A12_nilpotent_conjugation_group hP A₁ A₂ C₁ C₁ X).2.2.2.2.2.2.1,
    (archetype_A14_unipotent_tetraktys_action hP A₁ C₁).1⟩⟩

/-! ===========================================================================
    Section 5: Stage `𝔐₅` — Potentials, Berezinian Superdeterminant, &
    Graded Boson/Fermion Barrier Split after Orientation Gluing
    =========================================================================== -/

/-- **Stage `𝔐₅` Theorem (`stage_M5_berezinian_superdeterminant_and_graded_potential`)**:
Reuses `OperatorBerezinianCore.lean`, `SuperdeterminantBerezinianBridge.lean`,
`BerezinianSuperBarrierBridge.lean`, and `OperatorPartitionSupervolumeBridge.lean`:
1. The noncommutative operator Berezinian `opNoncommBerezinian u Δ = u * Δ⁻¹` is inverted by
   `opNoncommBerezinianInv u Δ = Δ * u⁻¹`, and `superdeterminantBerezinian a 0 0 d_inv = a * d_inv`,
2. On a two-sheet block carrier `(A_blk, D_blk)`, the Berezinian `canonicalBerezinian A_blk D_blk = det A_blk / det D_blk`:
   - Detects the odd orientation reflection `oddReflectionOdd = -1` with sign `-1`
     (`canonicalBerezinian oddReflectionEven oddReflectionOdd = -1`),
   - Is strictly positive (`0 < canonicalBerezinian A_blk D_blk`) when both sheets have positive
     determinant (`0 < det A_blk`, `0 < det D_blk`),
   - Splits the graded logarithmic potential into bosonic minus fermionic barriers:
     `superBerezinianBarrier A_blk D_blk = bosonicDetBarrier A_blk - bosonicDetBarrier D_blk`,
     vanishing at balanced determinant weight `det A_blk = det D_blk`,
3. When the operatorial Souriau partition equals `generalizedBerezinianScale S`, the operatorial
   Massieu potential is the logarithm of the Berezinian supervolume scale. -/
theorem stage_M5_berezinian_superdeterminant_and_graded_potential
    {A_ring : Type*} [Ring A_ring] (u Δ : A_ringˣ)
    {R : Type*} [CommRing R] (a_sdet d_inv : R)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A_blk D_blk : Block ι) (hA_pos : 0 < Matrix.det A_blk) (hD_pos : 0 < Matrix.det D_blk)
    {α : Type _} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    (C_ctx : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (S_adm : SchurAdmissibleTransport (E := H))
    (hPart : C_ctx.operatorPartition = generalizedBerezinianScale (E := H) S_adm) :
    (opNoncommBerezinian u Δ * opNoncommBerezinianInv u Δ = 1 ∧
     superdeterminantBerezinian a_sdet 0 0 d_inv = a_sdet * d_inv) ∧
    (canonicalBerezinian oddReflectionEven oddReflectionOdd = -1 ∧
     0 < canonicalBerezinian A_blk D_blk ∧
     superBerezinianBarrier A_blk D_blk =
       bosonicDetBarrier A_blk - bosonicDetBarrier D_blk ∧
     superBerezinianBarrier A_blk A_blk = 0) ∧
    (C_ctx.operatorMassieu = Real.log (generalizedBerezinianScale (E := H) S_adm)) := by
  have hBerInv : opNoncommBerezinian u Δ * opNoncommBerezinianInv u Δ = 1 := by
    simp only [opNoncommBerezinian, opNoncommBerezinianInv]
    calc
      (u : A_ring) * (↑Δ⁻¹ : A_ring) * ((Δ : A_ring) * (↑u⁻¹ : A_ring))
        = (u : A_ring) * ((↑Δ⁻¹ : A_ring) * (Δ : A_ring)) * (↑u⁻¹ : A_ring) := by noncomm_ring
      _ = (u : A_ring) * 1 * (↑u⁻¹ : A_ring) := by rw [Units.inv_mul]
      _ = (u : A_ring) * (↑u⁻¹ : A_ring) := by rw [mul_one]
      _ = 1 := Units.mul_inv u
  have hA_ne : Matrix.det A_blk ≠ 0 := ne_of_gt hA_pos
  have hD_ne : Matrix.det D_blk ≠ 0 := ne_of_gt hD_pos
  exact ⟨⟨hBerInv, superdeterminant_diagonal a_sdet d_inv⟩,
         ⟨oddReflection_berezinian,
          canonicalBerezinian_pos hA_pos hD_pos,
          superBerezinianBarrier_eq_bosonic_sub_fermionic A_blk D_blk hA_ne hD_ne,
          superBerezinianBarrier_zero_of_det_eq A_blk A_blk rfl hA_ne⟩,
         ConformalGibbsSouriauOperatorContext.operatorMassieu_eq_log_generalizedBerezinianScale_of_operatorPartition_eq_generalizedBerezinianScale
           C_ctx S_adm hPart⟩

/-! ===========================================================================
    Section 6: Stage `𝔐₆` — Weyl Gauge Invariance, Two-Sheet Relative Volume
    Positivity, & Operator-Norm / Intensive-Trace Cubic Closure
    =========================================================================== -/

/-- **Stage `𝔐₆` Theorem (`stage_M6_weyl_gauge_two_sheet_volume_and_intensive_operator_closure`)**:
Reuses `WeylBerezinianDeformation.lean`, `WeylGaugeOperatorLift.lean`, and
`IntensiveLogDetPositivityTension.lean`:
1. On the `2 × 2` operator deformation triad `(scaleOperator, chiralOperator, volumeOperator)`,
   the graded supertrace `superTrace` vanishes on the chiral and volume modes and extracts the
   exact Weyl scale difference `superTrace (scaleOperator p q σ + chiralOperator k₁ k₂ + volumeOperator a) = (p - q) * σ`,
2. On the lifted two-sheet operator carrier `LiftedSheetAut (E := E)`:
   - Common Weyl gauge rescaling `(w.trans g.plus, w.trans g.minus)` leaves both
     `determinantCharacter` and `relativeVolumeScale` strictly invariant,
   - The relative volume scale is strictly positive (`0 < relativeVolumeScale g_aut`),
   - The logarithmic relative-volume potential satisfies the exact additive transport chain rule
     `logRelativeVolumePotential (mulTransport g_aut h_aut) = logRelativeVolumePotential g_aut + logRelativeVolumePotential h_aut`,
3. On any strictly positive base point `P_mat : Matrix nMat nMat ℂ` and self-adjoint variation `H_mat`,
   the intensive third directional derivative is bounded by `2 ‖normalizedVariation P_mat H_mat‖`
   times the intensive second directional derivative without any dimension factor. -/
theorem stage_M6_weyl_gauge_two_sheet_volume_and_intensive_operator_closure
    {R : Type*} [CommRing R] (p_w q_w σ_w k₁ k₂ a_vol : R)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (w_gauge : E ≃L[ℝ] E) (g_aut h_aut : LiftedSheetAut (E := E))
    {nMat : Type*} [Fintype nMat] [DecidableEq nMat]
    {P_mat H_mat : Matrix nMat nMat ℂ}
    (hP_mat : IsStrictlyPositive P_mat) (hH_mat : IsSelfAdjoint H_mat) :
    (superTrace (scaleOperator p_w q_w σ_w + chiralOperator k₁ k₂ + volumeOperator a_vol) =
       (p_w - q_w) * σ_w ∧
     superTrace (chiralOperator (R := R) k₁ k₂ * chiralOperator (R := R) k₁ k₂) = 0) ∧
    (LiftedSheetAut.determinantCharacter { plus := w_gauge.trans g_aut.plus, minus := w_gauge.trans g_aut.minus } =
       LiftedSheetAut.determinantCharacter g_aut ∧
     LiftedSheetAut.relativeVolumeScale { plus := w_gauge.trans g_aut.plus, minus := w_gauge.trans g_aut.minus } =
       LiftedSheetAut.relativeVolumeScale g_aut ∧
     0 < LiftedSheetAut.relativeVolumeScale g_aut ∧
     LiftedSheetAut.logRelativeVolumePotential (LiftedSheetAut.mulTransport g_aut h_aut) =
       LiftedSheetAut.logRelativeVolumePotential g_aut +
         LiftedSheetAut.logRelativeVolumePotential h_aut) ∧
    (|deriv (deriv (deriv (fun s : ℝ => intensiveNegLogDet nMat (P_mat + s • H_mat)))) 0| ≤
      2 * ‖normalizedVariation P_mat H_mat‖ *
        deriv (deriv (fun s : ℝ => intensiveNegLogDet nMat (P_mat + s • H_mat))) 0) :=
  ⟨⟨total_deformation_superTrace p_w q_w σ_w k₁ k₂ a_vol,
    superTrace_chiral_square k₁ k₂⟩,
   ⟨LiftedSheetAut.determinantCharacter_gaugeRescale w_gauge g_aut,
    LiftedSheetAut.relativeVolumeScale_gaugeRescale w_gauge g_aut,
    LiftedSheetAut.relativeVolumeScale_pos g_aut,
    LiftedSheetAut.logRelativeVolumePotential_mulTransport g_aut h_aut⟩,
   abs_third_deriv_intensiveNegLogDet_le_two_opNorm_mul_second_deriv hP_mat hH_mat⟩

/-! ===========================================================================
    Section 7: Supergrading Across All Six Stages (`ℤ₂` Koszul, `gl(m|n)` Peirce
    Supermatrix, `ℤ₃` Ternary Grassmann, Unoriented CPT & Stiefel–Whitney
    Crosscap, Super-LU Berezinian, & Inductive-Colimit Hodge Gram Positivity)
    =========================================================================== -/

section SupergradingAcrossAllSixStages

open InfoGeometry.SuperGrassmannian.GradedGraphChart
open InfoGeometry.SuperGrassmannian.GradedGraphTransition
open InfoGeometry.SuperGrassmannian.MoebiusReflection
open InfoGeometry.SuperGrassmannian.ModularCPT
open InfoGeometry.SuperGrassmannian.BerezinianSheaf
open InfoGeometry.Supergeometry.Berezinian
open InfoGeometry.Canonical.DrazinSupergradedWeyl
open InfoGeometry.Canonical.GLSupermatrixGradedLie
open InfoGeometry.Canonical.CattoGurseyBlockGrading
open InfoGeometry.Canonical.Z3TrialityCapstone
open InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
open InfoGeometry.Canonical.RelativeModularBerezinianBridge
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- **Stage `𝔐₁` Supergrading (`stage_M1_supergraded_graph_transition_and_osp_reflection`)**:
Reuses `GradedGraphTransition.lean` and `MoebiusSuperGrassmannianCPT.lean`:
1. Over any (possibly noncommutative) ring `A` and commutative grading base `k`, any even
   block operators `(a, b, c, d, f)` induce an even fractional Möbius graph transition
   `PreservesDegree GU GW ((c + d.comp f).comp u.symm.toLinearMap)` without assuming an
   extra inverse-grading axiom (`preservesDegree_symm`),
2. On the `2|1` `osp(1|2)` supermatrix carrier `M₃ R = Matrix (Fin 3) (Fin 3) R`, the Möbius
   reflection `tau = J * Gamma` satisfies `tau * tau = 1`, intertwines the parity-aware
   `superBracket p q`, reverses the Cartan generator `tau * H_gen R * tau = -H_gen R`,
   preserves `supertrace`, and flips the energy sign in `ospPairingElement ε Δ`. -/
theorem stage_M1_supergraded_graph_transition_and_osp_reflection
    {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
    [AddCommGroup U] [Module A U] [Module k U]
    [AddCommGroup W] [Module A W] [Module k W]
    (GU : ι → Submodule k U) (GW : ι → Submodule k W)
    [DirectSum.Decomposition GU]
    (a_tr : Module.End A U) (b_tr : W →ₗ[A] U)
    (c_tr : U →ₗ[A] W) (d_tr : Module.End A W) (f_tr : U →ₗ[A] W)
    (ha : PreservesDegree GU GU a_tr) (hb : PreservesDegree GW GU b_tr)
    (hc : PreservesDegree GU GW c_tr) (hd : PreservesDegree GW GW d_tr)
    (hf : PreservesDegree GU GW f_tr)
    (u_tr : U ≃ₗ[A] U) (hu : u_tr.toLinearMap = a_tr + b_tr.comp f_tr)
    {R : Type*} [CommRing R] (p_b q_b : Bool) (X_m Y_m : M₃ R) (ε_osp Δ_osp : ℝ) :
    PreservesDegree GU GW ((c_tr + d_tr.comp f_tr).comp u_tr.symm.toLinearMap) ∧
    (tau (R := R) * tau = 1 ∧
     tau (R := R) * InfoGeometry.Algebra.SupergradedBracket.superBracket p_b q_b X_m Y_m * tau =
       InfoGeometry.Algebra.SupergradedBracket.superBracket p_b q_b
         (tau * X_m * tau) (tau * Y_m * tau) ∧
     tau (R := R) * InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen R * tau =
       -InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen R ∧
     InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace (tau (R := R) * X_m * tau) =
       InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X_m ∧
     tau (R := ℝ) *
         InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement ε_osp Δ_osp * tau =
       InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge.ospPairingElement (-ε_osp) Δ_osp) :=
  ⟨fractional_preservesDegree GU GW a_tr b_tr c_tr d_tr f_tr ha hb hc hd hf u_tr hu,
   ⟨tau_sq (R := R),
    tau_conj_superBracket p_b q_b X_m Y_m,
    tau_conj_H (R := R),
    supertrace_tau_invariant X_m,
    tau_intertwines_ospPairingElement ε_osp Δ_osp⟩⟩

/-- **Stage `𝔐₂` Supergrading (`stage_M2_peirce_supergrading_koszul_gl_and_z3_triality`)**:
Reuses `GLSupermatrixGradedLie.lean`, `CattoGurseyBlockGrading.lean`, and `Z3TrialityCapstone.lean`:
1. On `SuperMatrix m n R = Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R`, the native Peirce
   projections `even firstSupport` and `odd firstSupport` coincide with the block-even and
   block-odd decompositions, each directed odd block squares to zero, and on the hadronic
   `6|21` color supermatrix carrier `supertrace (1 : SuperMatrix 6 21 R) = -15`,
2. Homogeneous supermatrices obey Koszul-signed supertrace cyclicity
   `supertrace (X * Y) = Parity.sign R p q * supertrace (Y * X)`, vanishing supertrace on all
   homogeneous supercommutators `supertrace (superbracket p q X Y) = 0`, and the universal
   graded super-Jacobi identity `graded_super_jacobi`,
3. On the `ℤ₃` ternary Grassmann lane, the quantum plane (`ω³ = 1`, `θ₁³ = 0`, `θ₂³ = 0`,
   `θ₁ θ₂ = ω θ₂ θ₁`), `ℤ₃`-graded Leibniz cubic differential (`d³ = 0`), and tripotent
   `O³ = O` three-sector projector resolution (`P_vac + P_up + P_down = 1`) hold. -/
theorem stage_M2_peirce_supergrading_koszul_gl_and_z3_triality
    {m n : ℕ} {R : Type*} [CommRing R]
    (H X Y Z : SuperMatrix m n R) (pX pY pZ : Parity)
    (hX : IsHomogeneous pX X) (hY : IsHomogeneous pY Y)
    {A_z3 : Type*} [MonoidWithZero A_z3] (P_z3 : Z3QuantumPlane A_z3)
    {B_z3 : Type*} [Zero B_z3] [Add B_z3] [Mul B_z3]
    (D_z3 : Z3DifferentialCalculus B_z3) (x_z3 y_z3 : B_z3)
    {Vspace : Type*} [AddCommGroup Vspace] [Module ℝ Vspace]
    (O_tri : InfoGeometry.Algebra.OSp12.Op Vspace) (hO3 : O_tri ^ 3 = O_tri) :
    (InfoGeometry.Core.PeirceGrading.even firstSupport H = evenMatrix (blockA H) (blockD H) ∧
     InfoGeometry.Core.PeirceGrading.odd firstSupport H = oddMatrix (blockB H) (blockC H) ∧
     (oddMatrix (blockB H) 0 : SuperMatrix m n R) ^ 2 = 0 ∧
     (oddMatrix 0 (blockC H) : SuperMatrix m n R) ^ 2 = 0 ∧
     GLSupermatrixGradedLie.supertrace (1 : SuperMatrix 6 21 R) = -15) ∧
    (GLSupermatrixGradedLie.supertrace (X * Y) =
       Parity.sign R pX pY * GLSupermatrixGradedLie.supertrace (Y * X) ∧
     GLSupermatrixGradedLie.supertrace (superbracket pX pY X Y) = 0 ∧
     Parity.sign (SuperMatrix m n R) pX pZ *
         ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
       Parity.sign (SuperMatrix m n R) pY pX *
         ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
       Parity.sign (SuperMatrix m n R) pZ pY *
         ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0) ∧
    ((P_z3.omega ^ 3 = 1 ∧ P_z3.theta1 ^ 3 = 0 ∧ P_z3.theta2 ^ 3 = 0 ∧
      P_z3.theta1 * P_z3.theta2 = P_z3.omega * (P_z3.theta2 * P_z3.theta1)) ∧
     (D_z3.d (D_z3.d (D_z3.d x_z3)) = 0 ∧
      D_z3.d (x_z3 * y_z3) =
        D_z3.d x_z3 * y_z3 + D_z3.omegaPow (D_z3.degree x_z3) * (x_z3 * D_z3.d y_z3)) ∧
     InfoGeometry.Algebra.OSp12.projVac O_tri +
       InfoGeometry.Algebra.OSp12.projUp O_tri +
       InfoGeometry.Algebra.OSp12.projDown O_tri = 1 ∧
     InfoGeometry.Algebra.OSp12.projUp O_tri * InfoGeometry.Algebra.OSp12.projDown O_tri = 0) := by
  have hPeirce := peirce_components H
  have hSq := directed_blocks_square_zero H
  have hTri := hadjiivanov_tripotent_projector_packet O_tri hO3
  exact ⟨⟨hPeirce.1, hPeirce.2, hSq.1, hSq.2, supertrace_identity_6_21 (R := R)⟩,
         ⟨supertrace_mul_graded pX pY X Y hX hY,
          supertrace_superbracket_eq_zero pX pY X Y hX hY,
          gl_graded_super_jacobi pX pY pZ X Y Z⟩,
         ⟨z3_quantum_plane_substrate_packet P_z3,
          z3_grassmann_differential_substrate_packet D_z3 x_z3 y_z3,
          hTri.2.2.2.1, hTri.2.2.2.2.2⟩⟩

/-- **Stage `𝔐₃` Supergrading (`stage_M3_unoriented_super_grassmannian_cpt_and_crosscap`)**:
Reuses `UnorientedSuperGrassmannianCPT.lean` and `BerezinianSheafStiefelWhitney.lean`:
1. On the doubled primal/vacuum carrier `DoubledCarrier E = E × E`, the modular CPT operator
   satisfies `CPT_op (CPT_op z) = (-z.1, -z.2)`, reverses the split Krein metric
   (`kreinForm pairing (CPT_op z₁) (CPT_op z₂) = -kreinForm pairing z₁ z₂`), preserves the
   symplectic form (`symplecticForm pairing (CPT_op z₁) (CPT_op z₂) = symplecticForm pairing z₁ z₂`),
   and the Möbius twist `moebiusTwist = P_op ∘ₗ C_op` satisfies `moebiusTwist (moebiusTwist z) = z`
   while anticommuting with the para-complex polarization `paraK`:
   `moebiusTwist (paraK z) = -(paraK (moebiusTwist z))`,
2. On the unoriented super-Grassmannian crosscap `Gr(n|q; 2n|2q)/ℤ₂`, the Berezinian transition
   Jacobian sign at the identity satisfies `(-1 : ℤ) ^ ((gradedParity n q) ^ 2) = cechCocycleSign n q`,
   and the Berezinian sheaf is orientable (`w₁ = 0`) iff `cechCocycleSign n q = 1` and a
   non-orientable crosscap (`w₁ = 1`) iff `cechCocycleSign n q = -1`. -/
theorem stage_M3_unoriented_super_grassmannian_cpt_and_crosscap
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (z z₁ z₂ : DoubledCarrier E)
    (n_ber q_ber : ℕ) :
    (CPT_op (CPT_op z) = (-z.1, -z.2) ∧
     moebiusTwist (moebiusTwist z) = z ∧
     moebiusTwist (paraK z) = -(paraK (moebiusTwist z)) ∧
     InfoGeometry.SuperGrassmannian.ModularCPT.kreinForm pairing (CPT_op z₁) (CPT_op z₂) =
       -InfoGeometry.SuperGrassmannian.ModularCPT.kreinForm pairing z₁ z₂ ∧
     InfoGeometry.SuperGrassmannian.ModularCPT.symplecticForm pairing (CPT_op z₁) (CPT_op z₂) =
       InfoGeometry.SuperGrassmannian.ModularCPT.symplecticForm pairing z₁ z₂) ∧
    ((-1 : ℤ) ^ ((gradedParity n_ber q_ber) ^ 2) = cechCocycleSign n_ber q_ber ∧
     (IsOrientableBerezinianSheaf n_ber q_ber ↔ cechCocycleSign n_ber q_ber = 1) ∧
     (IsCrosscapNonOrientable n_ber q_ber ↔ cechCocycleSign n_ber q_ber = -1) ∧
     (IsOrientableBerezinianSheaf n_ber q_ber ∨ IsCrosscapNonOrientable n_ber q_ber) ∧
     ¬ (IsOrientableBerezinianSheaf n_ber q_ber ∧ IsCrosscapNonOrientable n_ber q_ber)) :=
  ⟨⟨CPT_sq_neg z,
    moebiusTwist_involutive z,
    moebius_anticommutes_paraK z,
    kreinForm_cpt_anti_invariant pairing z₁ z₂,
    symplecticForm_cpt_invariant pairing z₁ z₂⟩,
   ⟨berezinian_parity_square_law n_ber q_ber,
    orientable_iff_cocycle_one n_ber q_ber,
    crosscap_iff_cocycle_neg_one n_ber q_ber,
    orientable_or_crosscap n_ber q_ber,
    not_orientable_and_crosscap n_ber q_ber⟩⟩

/-- **Stage `𝔐₄` Supergrading (`stage_M4_super_lu_factorization_and_drazin_weyl_projector`)**:
Reuses `Supergeometry/BerezinianDecomposition.lean` and `DrazinSupergradedWeyl.lean`:
1. Every `2 × 2` supermatrix `M : Matrix (Fin 2) (Fin 2) R` with invertible lower-right block
   `M 1 1 * invD = 1` admits the exact Super-LU trifactor decomposition
   `factorL M invD * factorH M invD * factorR M invD = M`, with unipotent shear composition
   `!![1, x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1]` and balanced `(1|1)` projective
   scaling invariance `berezinian (c • M) (inv_c * invD) = berezinian M invD`,
2. For any scaled projector `P_obs * P_obs = λ • P_obs` (`λ ≠ 0`), `(λ⁻¹ * λ⁻¹) • P_obs`
   acts as its two-sided Drazin Weyl inverse (`P_obs * ((λ⁻¹ * λ⁻¹) • P_obs) = λ⁻¹ • P_obs`). -/
theorem stage_M4_super_lu_factorization_and_drazin_weyl_projector
    {R : Type*} [CommRing R]
    (M_lu : Matrix (Fin 2) (Fin 2) R) (invD c_sc inv_c x_sh y_sh : R)
    (hD : M_lu 1 1 * invD = 1) (hc_sc : c_sc * inv_c = 1)
    {Obs : Type*} [Semiring Obs] [Algebra ℂ Obs]
    (P_obs : Obs) (lam : ℂ) (hlam : lam ≠ 0) (hP_obs : P_obs * P_obs = lam • P_obs) :
    (factorL M_lu invD * factorH M_lu invD * factorR M_lu invD = M_lu ∧
     (!![1, x_sh; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, y_sh; 0, 1] =
       !![1, x_sh + y_sh; 0, 1] ∧
     berezinian (c_sc • M_lu) (inv_c * invD) = berezinian M_lu invD) ∧
    (P_obs * ((lam⁻¹ * lam⁻¹) • P_obs) = lam⁻¹ • P_obs ∧
     ((lam⁻¹ * lam⁻¹) • P_obs) * P_obs = lam⁻¹ • P_obs) :=
  ⟨⟨super_lu_factorization M_lu invD hD,
    unipotent_group_mul x_sh y_sh,
    berezinian_scaling_balanced M_lu invD c_sc inv_c hc_sc⟩,
   scaledProjector_candidate_mul P_obs lam hlam hP_obs⟩

/-- **Stage `𝔐₅` & `𝔐₆` Supergrading
(`stage_M5_M6_relative_modular_berezinian_and_colimit_gram_positivity`)**:
Reuses `RelativeModularBerezinianBridge.lean` and `PeirceTetraktysColimitCoercivity.lean`:
1. Realizing the plus/minus modular operators on `Fin n → ℝ` as the doubled-sheet equivalence
   `relativeModularRestrictedSheetEquiv qPlus q0Plus qMinus q0Minus` identifies its restricted
   volume scale with `relativeModularBerezinianShadow` and its negative log with
   `relativeModularSupervolumePotential`, while its concrete Krein Hessian lift on doubled
   real Hestenes coordinates evaluates to `splitB11` and `splitQ11`,
2. For any self-adjoint element `P_lim : Limit` (`star P_lim = P_lim`) in the inductive colimit
   `Cl11TensorTowerLimit.Limit`, both the Peirce Tetraktys quadratic coupling
   `genV P_lim A_lim (star A_lim)` and the two-sheeted quadratic coupling
   `CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling P_lim A_lim (star A_lim)` equal the
   symmetric Gram sum `conePlus P_lim A_lim * star (conePlus P_lim A_lim) +
   star (conePlus P_lim A_lim) * conePlus P_lim A_lim`. -/
theorem stage_M5_M6_relative_modular_berezinian_and_colimit_gram_positivity
    {n_mod : ℕ} [Nonempty (Fin n_mod)]
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n_mod))
    (x_h ξ_h y_h η_h : ℝ)
    {P_lim : Limit} (hPs_lim : star P_lim = P_lim) (A_lim : Limit) :
    (RestrictedSheetEquiv.restrictedVolumeScale (E := (Fin n_mod → ℝ))
       (relativeModularRestrictedSheetEquiv (n := n_mod) qPlus q0Plus qMinus q0Minus) =
       relativeModularBerezinianShadow (n := n_mod) qPlus q0Plus qMinus q0Minus ∧
     -Real.log
       (RestrictedSheetEquiv.restrictedVolumeScale (E := (Fin n_mod → ℝ))
         (relativeModularRestrictedSheetEquiv (n := n_mod) qPlus q0Plus qMinus q0Minus)) =
       relativeModularSupervolumePotential (n := n_mod) qPlus q0Plus qMinus q0Minus ∧
     inner ℝ
       (relativeModularSupervolumeKreinHessian
         (n := n_mod) (E := ℝ) qPlus q0Plus qMinus q0Minus
         (InfoGeometry.Krein.to_doubled x_h ξ_h))
       (InfoGeometry.Krein.to_doubled y_h η_h) =
       InfoGeometry.Clifford.splitB11 (x_h, ξ_h) (y_h, η_h)) ∧
    (genV P_lim A_lim (star A_lim) =
       conePlus P_lim A_lim * star (conePlus P_lim A_lim) +
         star (conePlus P_lim A_lim) * conePlus P_lim A_lim ∧
     CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling P_lim A_lim (star A_lim) =
       CanonicalTwoSheetedInductiveColimit.opZig P_lim A_lim *
           star (CanonicalTwoSheetedInductiveColimit.opZig P_lim A_lim) +
         star (CanonicalTwoSheetedInductiveColimit.opZig P_lim A_lim) *
           CanonicalTwoSheetedInductiveColimit.opZig P_lim A_lim) :=
  ⟨⟨relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
      (n := n_mod) qPlus q0Plus qMinus q0Minus,
    neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential
      (n := n_mod) qPlus q0Plus qMinus q0Minus,
    (relativeModularSupervolume_Hestenes_realDoubled_packet
      (n := n_mod) qPlus q0Plus qMinus q0Minus x_h ξ_h y_h η_h).2.1⟩,
   ⟨genV_eq_conePlus_hodge_coefficient hPs_lim A_lim,
    opQuadraticCoupling_eq_opZig_gram hPs_lim A_lim⟩⟩

end SupergradingAcrossAllSixStages

/-! ===========================================================================
    Section 8: Master 6-Stage Coagulation (`𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`)
    =========================================================================== -/

/-- **Master Möbius–Tetraktys–Klein–Berezinian–Weyl Synthesis
(`moebius_tetraktys_klein_berezinian_weyl_master_synthesis`)**:
Coagulates the complete 6-stage causal poset (`𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`) from the
repository's preexisting owners:
1. Strict causal chain and acyclicity of `MoebiusKleinBerezinianWeylStage`,
2. Planar Möbius classification lifted to noncommutative operator rings (`operatorMobiusAction_mul`,
   `operatorMatrix_noncommutative`) and projective failure of raw determinant sign
   (`determinant_sign_not_projective_invariant`),
3. Tetraktys orientation characterization (`1 - (2 : ℤ) • P = -invS P`) and Klein-four sandwich
   action (`tetraktys_sandwich_channels_are_peirce_klein_action`),
4. Klein-bottle operator-algebra quotient (`operator_algebra_quotient_packet`) and period-2
   unipotent edge-transition gluing (`edgeTransition`),
5. Group Möbius boost action (`modularBoostSL2_add`) and Cayley/Möbius squashing closure on
   biquaternions (`mobius_biquaternion_closure`),
6. Berezinian superdeterminant positivity (`canonicalBerezinian_pos`), odd-reflection sign (`-1`),
   and graded boson/fermion barrier split (`superBerezinianBarrier_eq_bosonic_sub_fermionic`),
7. Weyl-gauge invariance (`relativeVolumeScale_gaugeRescale`), two-sheet relative volume positivity
   (`relativeVolumeScale_pos`), additive log-potential chain rule (`logRelativeVolumePotential_mulTransport`),
   and dimension-independent operator-norm / intensive-trace cubic bound. -/
theorem moebius_tetraktys_klein_berezinian_weyl_master_synthesis
    (A_m : Mat2C) (z : ℂ)
    {A_op : Type*} [Ring A_op] [Nontrivial A_op]
    (g_op h_op : OperatorMatrix A_op) (v_op : OperatorPair A_op)
    {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (A C X : B) (hV : genV P A C = 1)
    (pt_torus : BrillouinTorus)
    (p_m q_m r_m t_m a_m b_m : ℂ) (h_mob : (r_m * a_m + t_m) ^ 2 - (r_m * b_m) ^ 2 ≠ 0)
    (s_boost t_boost : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A_blk D_blk : Block ι) (hA_pos : 0 < Matrix.det A_blk) (hD_pos : 0 < Matrix.det D_blk)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (w_gauge : E ≃L[ℝ] E) (g_aut h_aut : LiftedSheetAut (E := E))
    {nMat : Type*} [Fintype nMat] [DecidableEq nMat]
    {P_mat H_mat : Matrix nMat nMat ℂ}
    (hP_mat : IsStrictlyPositive P_mat) (hH_mat : IsSelfAdjoint H_mat) :
    -- (0) Strict 6-stage causal chain and acyclicity
    ((∀ s : MoebiusKleinBerezinianWeylStage,
        ¬ Relation.TransGen MoebiusKleinBerezinianWeylStage.causalEdge s s) ∧
     MoebiusKleinBerezinianWeylStage.M1_PlanarToOperatorRingMoebiusLift <
       .M2_TetraktysOrientationCharacterization ∧
     MoebiusKleinBerezinianWeylStage.M2_TetraktysOrientationCharacterization <
       .M3_KleinBottleOperatorAlgebraQuotientGluing ∧
     MoebiusKleinBerezinianWeylStage.M3_KleinBottleOperatorAlgebraQuotientGluing <
       .M4_GroupMoebiusSquashingAndCayleyWeylTransform ∧
     MoebiusKleinBerezinianWeylStage.M4_GroupMoebiusSquashingAndCayleyWeylTransform <
       .M5_BerezinianSuperdeterminantAndGradedPotential ∧
     MoebiusKleinBerezinianWeylStage.M5_BerezinianSuperdeterminantAndGradedPotential <
       .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure) ∧
    -- (1) Stage 𝔐₁: Projective determinant sign flip & operator-ring Möbius action
    (matrixMobiusAction (matrixScale Complex.I A_m) z = matrixMobiusAction A_m z ∧
     Matrix.det (matrixScale Complex.I A_m) = -Matrix.det A_m ∧
     operatorMobiusAction (g_op * h_op) v_op =
       operatorMobiusAction g_op (operatorMobiusAction h_op v_op) ∧
     mobiusForwardUnit (A := A_op) * mobiusBackwardUnit (A := A_op) ≠
       mobiusBackwardUnit (A := A_op) * mobiusForwardUnit (A := A_op)) ∧
    -- (2) Stage 𝔐₂: Tetraktys orientation involution `1 - 2P = -invS P` & Klein-four action
    ((1 : B) - (2 : ℤ) • P = -invS P ∧
     grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) ∧
     grpSig P A C X = parityConjRingEquiv hP X) ∧
    -- (3) Stage 𝔐₃: Klein-bottle orbit quotient & period-2 unipotent edge gluing
    (Function.Surjective quotientMap ∧
     Topology.IsQuotientMap quotientMap ∧
     quotientMap (torusGlide pt_torus) = quotientMap pt_torus ∧
     edgeTransition P (1 + conePlus P A) (1 - conePlus P A)
       (edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X) ∧
    -- (4) Stage 𝔐₄: Group Möbius boost & biquaternion squashing/Möbius closure
    (squash 0 = 0 ∧
     InfoGeometry.Canonical.modularBoostSL2 (s_boost + t_boost) =
       InfoGeometry.Canonical.modularBoostSL2 s_boost *
         InfoGeometry.Canonical.modularBoostSL2 t_boost ∧
     (p_m • Xab a_m b_m + q_m • (1 : M2C)) * invPauli (r_m * a_m + t_m) (r_m * b_m) =
       Xab (mobiusAlpha p_m q_m r_m t_m a_m b_m) (mobiusBeta p_m q_m r_m t_m a_m b_m)) ∧
    -- (5) Stage 𝔐₅: Berezinian superdeterminant positivity, odd reflection sign, & barrier split
    (canonicalBerezinian oddReflectionEven oddReflectionOdd = -1 ∧
     0 < canonicalBerezinian A_blk D_blk ∧
     superBerezinianBarrier A_blk D_blk =
       bosonicDetBarrier A_blk - bosonicDetBarrier D_blk) ∧
    -- (6) Stage 𝔐₆: Weyl-gauge relative volume positivity, additive log-potential, & intensive cubic bound
    (LiftedSheetAut.relativeVolumeScale { plus := w_gauge.trans g_aut.plus, minus := w_gauge.trans g_aut.minus } =
       LiftedSheetAut.relativeVolumeScale g_aut ∧
     0 < LiftedSheetAut.relativeVolumeScale g_aut ∧
     LiftedSheetAut.logRelativeVolumePotential (LiftedSheetAut.mulTransport g_aut h_aut) =
       LiftedSheetAut.logRelativeVolumePotential g_aut +
         LiftedSheetAut.logRelativeVolumePotential h_aut ∧
     |deriv (deriv (deriv (fun s : ℝ => intensiveNegLogDet nMat (P_mat + s • H_mat)))) 0| ≤
       2 * ‖normalizedVariation P_mat H_mat‖ *
         deriv (deriv (fun s : ℝ => intensiveNegLogDet nMat (P_mat + s • H_mat))) 0) := by
  have hInvNeg : (1 : B) - (2 : ℤ) • P = -invS P := by peirce_nf hP
  have hTet := tetraktys_sandwich_channels_are_peirce_klein_action hP A C hV X
  have hEdge :=
    (twisted_edge_transition_cocycle_and_klein_quotient_bridge
      hP (1 + conePlus P A) (1 - conePlus P A) (1 + conePlus P A) (1 - conePlus P A) A X).2.2.2
  have hA_ne : Matrix.det A_blk ≠ 0 := ne_of_gt hA_pos
  have hD_ne : Matrix.det D_blk ≠ 0 := ne_of_gt hD_pos
  exact ⟨⟨MoebiusKleinBerezinianWeylStage.causalEdge_acyclic,
          MoebiusKleinBerezinianWeylStage.strict_six_stage_chain.1,
          MoebiusKleinBerezinianWeylStage.strict_six_stage_chain.2.1,
          MoebiusKleinBerezinianWeylStage.strict_six_stage_chain.2.2.1,
          MoebiusKleinBerezinianWeylStage.strict_six_stage_chain.2.2.2.1,
          MoebiusKleinBerezinianWeylStage.strict_six_stage_chain.2.2.2.2⟩,
         ⟨(determinant_sign_not_projective_invariant A_m z).1,
          (determinant_sign_not_projective_invariant A_m z).2,
          operatorMobiusAction_mul g_op h_op v_op,
          operatorMatrix_noncommutative (A := A_op)⟩,
         ⟨hInvNeg, hTet.2.2.1, hTet.2.2.2⟩,
         ⟨quotientMap_surjective, quotientMap_isQuotient, quotientMap_glide pt_torus, hEdge⟩,
         ⟨squash_at_defect,
          InfoGeometry.Canonical.modularBoostSL2_add s_boost t_boost,
          mobius_biquaternion_closure p_m q_m r_m t_m a_m b_m h_mob⟩,
         ⟨oddReflection_berezinian,
          canonicalBerezinian_pos hA_pos hD_pos,
          superBerezinianBarrier_eq_bosonic_sub_fermionic A_blk D_blk hA_ne hD_ne⟩,
         ⟨LiftedSheetAut.relativeVolumeScale_gaugeRescale w_gauge g_aut,
          LiftedSheetAut.relativeVolumeScale_pos g_aut,
          LiftedSheetAut.logRelativeVolumePotential_mulTransport g_aut h_aut,
          abs_third_deriv_intensiveNegLogDet_le_two_opNorm_mul_second_deriv hP_mat hH_mat⟩⟩

/-- **Supergraded Möbius–Tetraktys–Klein–Berezinian–Weyl Master Synthesis
(`supergraded_moebius_tetraktys_klein_berezinian_weyl_master_synthesis`)**:
Unifies the `ℤ₂` and `ℤ₃` supergrading structure across all six stages (`𝔐₁ ≺ ⋯ ≺ 𝔐₆`):
1. `𝔐₁`: `2|1` `osp(1|2)` Möbius reflection `tau * tau = 1`, parity-superbracket covariance,
   and `supertrace` invariance,
2. `𝔐₂`: Native `gl(m|n)` Peirce block grading, `gl(6|21)` identity supertrace `-15`,
   Koszul-signed supertrace cyclicity, universal graded super-Jacobi, and `ℤ₃` quantum plane,
3. `𝔐₃`: Unoriented Super-Grassmannian CPT (`CPT² = -id`, `moebiusTwist ∘ paraK = -paraK ∘ moebiusTwist`)
   and Stiefel–Whitney crosscap dichotomy (`IsOrientableBerezinianSheaf n q ∨ IsCrosscapNonOrientable n q`),
4. `𝔐₄`: Noncommutative `2 × 2` Super-LU factorization `factorL M invD * factorH M invD * factorR M invD = M`
   and balanced `(1|1)` Berezinian scaling invariance,
5. `𝔐₅`–`𝔐₆`: Relative modular Berezinian supervolume identity and inductive-colimit Peirce–Hodge
   symmetric Gram decomposition `genV P_lim A_lim (star A_lim) = N₊ N₊* + N₊* N₊`. -/
theorem supergraded_moebius_tetraktys_klein_berezinian_weyl_master_synthesis
    {m n : ℕ} {R : Type*} [CommRing R]
    (X_m3 : InfoGeometry.SuperGrassmannian.MoebiusReflection.M₃ R)
    (H_gl X_gl Y_gl Z_gl : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix m n R)
    (pX pY pZ : InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity)
    (hX : InfoGeometry.Canonical.GLSupermatrixGradedLie.IsHomogeneous pX X_gl)
    (hY : InfoGeometry.Canonical.GLSupermatrixGradedLie.IsHomogeneous pY Y_gl)
    {A_z3 : Type*} [MonoidWithZero A_z3]
    (P_z3 : InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus.Z3QuantumPlane A_z3)
    {E_cpt : Type*} [AddCommGroup E_cpt] [Module ℝ E_cpt]
    (z_cpt : InfoGeometry.SuperGrassmannian.ModularCPT.DoubledCarrier E_cpt)
    (n_ber q_ber : ℕ)
    (M_lu : Matrix (Fin 2) (Fin 2) R) (invD c_sc inv_c : R)
    (hD : M_lu 1 1 * invD = 1) (hc_sc : c_sc * inv_c = 1)
    {n_mod : ℕ} [Nonempty (Fin n_mod)]
    (qPlus q0Plus qMinus q0Minus : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n_mod))
    {P_lim : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit}
    (hPs_lim : star P_lim = P_lim)
    (A_lim : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    -- (1) Stage 𝔐₁ Supergrading: 2|1 osp(1|2) reflection & supertrace invariance
    (InfoGeometry.SuperGrassmannian.MoebiusReflection.tau (R := R) *
       InfoGeometry.SuperGrassmannian.MoebiusReflection.tau = 1 ∧
     InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace
       (InfoGeometry.SuperGrassmannian.MoebiusReflection.tau (R := R) * X_m3 *
         InfoGeometry.SuperGrassmannian.MoebiusReflection.tau) =
       InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X_m3) ∧
    -- (2) Stage 𝔐₂ Supergrading: gl(m|n) Peirce grading, gl(6|21) supertrace -15, Koszul cyclicity, & Z₃ plane
    (InfoGeometry.Core.PeirceGrading.even
       InfoGeometry.Canonical.CattoGurseyBlockGrading.firstSupport H_gl =
       InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.blockA H_gl)
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.blockD H_gl) ∧
     InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
       (1 : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix 6 21 R) = -15 ∧
     InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace (X_gl * Y_gl) =
       InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity.sign R pX pY *
         InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace (Y_gl * X_gl) ∧
     InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity.sign
       (InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix m n R) pX pZ *
       InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pX (pY + pZ) X_gl
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pY pZ Y_gl Z_gl) +
     InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity.sign
       (InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix m n R) pY pX *
       InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pY (pZ + pX) Y_gl
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pZ pX Z_gl X_gl) +
     InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity.sign
       (InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix m n R) pZ pY *
       InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pZ (pX + pY) Z_gl
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.ringSuperbracket pX pY X_gl Y_gl) = 0 ∧
     P_z3.omega ^ 3 = 1 ∧ P_z3.theta1 * P_z3.theta2 = P_z3.omega * (P_z3.theta2 * P_z3.theta1)) ∧
    -- (3) Stage 𝔐₃ Supergrading: Unoriented CPT twist & Stiefel–Whitney crosscap dichotomy
    (InfoGeometry.SuperGrassmannian.ModularCPT.CPT_op
       (InfoGeometry.SuperGrassmannian.ModularCPT.CPT_op z_cpt) = (-z_cpt.1, -z_cpt.2) ∧
     InfoGeometry.SuperGrassmannian.ModularCPT.moebiusTwist
       (InfoGeometry.SuperGrassmannian.ModularCPT.paraK z_cpt) =
       -(InfoGeometry.SuperGrassmannian.ModularCPT.paraK
           (InfoGeometry.SuperGrassmannian.ModularCPT.moebiusTwist z_cpt)) ∧
     (InfoGeometry.SuperGrassmannian.BerezinianSheaf.IsOrientableBerezinianSheaf n_ber q_ber ∨
      InfoGeometry.SuperGrassmannian.BerezinianSheaf.IsCrosscapNonOrientable n_ber q_ber) ∧
     ¬ (InfoGeometry.SuperGrassmannian.BerezinianSheaf.IsOrientableBerezinianSheaf n_ber q_ber ∧
        InfoGeometry.SuperGrassmannian.BerezinianSheaf.IsCrosscapNonOrientable n_ber q_ber)) ∧
    -- (4) Stage 𝔐₄ Supergrading: Super-LU factorization & balanced (1|1) Berezinian scaling
    (InfoGeometry.Supergeometry.Berezinian.factorL M_lu invD *
       InfoGeometry.Supergeometry.Berezinian.factorH M_lu invD *
       InfoGeometry.Supergeometry.Berezinian.factorR M_lu invD = M_lu ∧
     InfoGeometry.Supergeometry.Berezinian.berezinian (c_sc • M_lu) (inv_c * invD) =
       InfoGeometry.Supergeometry.Berezinian.berezinian M_lu invD) ∧
    -- (5) Stage 𝔐₅–𝔐₆ Supergrading: Relative modular Berezinian & colimit Hodge Gram positivity
    (InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeScale
       (E := (Fin n_mod → ℝ))
       (InfoGeometry.Canonical.RelativeModularBerezinianBridge.relativeModularRestrictedSheetEquiv
         (n := n_mod) qPlus q0Plus qMinus q0Minus) =
       InfoGeometry.Canonical.RelativeModularOperator.relativeModularBerezinianShadow
         (n := n_mod) qPlus q0Plus qMinus q0Minus ∧
     genV P_lim A_lim (star A_lim) =
       conePlus P_lim A_lim * star (conePlus P_lim A_lim) +
         star (conePlus P_lim A_lim) * conePlus P_lim A_lim) := by
  have hZ3 := InfoGeometry.Canonical.Z3TrialityCapstone.z3_quantum_plane_substrate_packet P_z3
  exact ⟨⟨InfoGeometry.SuperGrassmannian.MoebiusReflection.tau_sq (R := R),
          InfoGeometry.SuperGrassmannian.MoebiusReflection.supertrace_tau_invariant X_m3⟩,
         ⟨(InfoGeometry.Canonical.CattoGurseyBlockGrading.peirce_components H_gl).1,
          InfoGeometry.Canonical.CattoGurseyBlockGrading.supertrace_identity_6_21 (R := R),
          InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace_mul_graded pX pY X_gl Y_gl hX hY,
          InfoGeometry.Canonical.GLSupermatrixGradedLie.gl_graded_super_jacobi pX pY pZ X_gl Y_gl Z_gl,
          hZ3.1, hZ3.2.2.2⟩,
         ⟨InfoGeometry.SuperGrassmannian.ModularCPT.CPT_sq_neg z_cpt,
          InfoGeometry.SuperGrassmannian.ModularCPT.moebius_anticommutes_paraK z_cpt,
          InfoGeometry.SuperGrassmannian.BerezinianSheaf.orientable_or_crosscap n_ber q_ber,
          InfoGeometry.SuperGrassmannian.BerezinianSheaf.not_orientable_and_crosscap n_ber q_ber⟩,
         ⟨InfoGeometry.Supergeometry.Berezinian.super_lu_factorization M_lu invD hD,
          InfoGeometry.Supergeometry.Berezinian.berezinian_scaling_balanced M_lu invD c_sc inv_c hc_sc⟩,
         ⟨InfoGeometry.Canonical.RelativeModularBerezinianBridge.relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
            (n := n_mod) qPlus q0Plus qMinus q0Minus,
          InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity.genV_eq_conePlus_hodge_coefficient
            hPs_lim A_lim⟩⟩

end InfoGeometry.Canonical.MoebiusTetraktysKleinBerezinianWeylPoset
