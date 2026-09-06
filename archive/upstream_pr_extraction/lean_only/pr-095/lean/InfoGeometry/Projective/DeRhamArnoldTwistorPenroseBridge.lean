import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Projective.ArnoldRelations
import InfoGeometry.Projective.TwistorAmplituhedronBoundary
import InfoGeometry.Projective.PenroseSpinTilingConfig
import InfoGeometry.Geometry.PauliParavectorBridge

/-!
# de Rham / Arnold / Twistor / Penrose finite bridge

This file does not claim a global equivalence theorem. It packages the finite
owner readouts that already exist in the codebase:

* logarithmic de Rham monodromy on the Klein-quadric complement;
* Arnold three-edge mixed-relation vanishing in quotient form;
* twistor null-incidence exclusion for non-null pairs/triples;
* the rank-32 Penrose spin-tiling arithmetic readout.

The purpose is to keep the bridge explicit and theorem-honest.
-/

namespace InfoGeometry.Projective.DeRhamArnoldTwistorPenroseBridge

open scoped BigOperators
open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Projective.ArnoldRelations
open InfoGeometry.Projective.TwistorAmplituhedronBoundary
open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Geometry.PauliParavectorBridge

theorem circleIntegral_grothendieck_dlog_readout (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), grothendieck_dlog z) =
      (2 * Real.pi * Complex.I : ℂ) := by
  exact circleIntegral_grothendieck_dlog R hR

theorem grothendieck_dlog_winding_readout (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), grothendieck_dlog z)) =
      (1 : ℂ) := by
  exact grothendieckTomitaWilsonBridge n R hR

theorem arnold_mixed_relation_kernel_readout
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {A : Type*} [Semiring A]
    (w12 w23 w31 : ArnoldExterior R M) (φ : ArnoldExterior R M →+* A)
    (hKer : arnoldMixedRelation R M w12 w23 w31 ∈ RingHom.ker φ) :
    φ (arnoldMixedRelation R M w12 w23 w31) = 0 := by
  exact arnold_mixed_relation_vanishes_under_kernel_membership
    (R := R) (M := M) (A := A) w12 w23 w31 φ hKer

theorem triple_nonnull_pairwise_common_twistor_exclusion
    (X₁ X₂ X₃ : InfoGeometry.Clifford.Soldering.Vec22)
    (hTriple : TripleNonNull X₁ X₂ X₃) :
    (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
      InfoGeometry.Twistor.Incidence.Incident Z X₁ ∧
      InfoGeometry.Twistor.Incidence.Incident Z X₂ ∧ Z.2 ≠ 0) ∧
    (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
      InfoGeometry.Twistor.Incidence.Incident Z X₂ ∧
      InfoGeometry.Twistor.Incidence.Incident Z X₃ ∧ Z.2 ≠ 0) ∧
    (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
      InfoGeometry.Twistor.Incidence.Incident Z X₃ ∧
      InfoGeometry.Twistor.Incidence.Incident Z X₁ ∧ Z.2 ≠ 0) := by
  exact triple_nonnull_excludes_pairwise_common_twistors X₁ X₂ X₃ hTriple

theorem pauliMatrix_determinant_readout (v : Minkowski4) :
    Matrix.det (pauliMatrix v) = ((v.q : ℝ) : ℂ) := by
  exact det_pauliMatrix v

end InfoGeometry.Projective.DeRhamArnoldTwistorPenroseBridge
