import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

theorem finite_bridge_packet :
  (∀ (R : ℝ) (hR : 0 < R),
    (∮ z in C((0 : ℂ), R), grothendieck_dlog z) =
      (2 * Real.pi * Complex.I : ℂ)) ∧
  (∀ (R : ℝ) (hR : 0 < R) (n : ℤ),
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), grothendieck_dlog z)) =
      (1 : ℂ)) ∧
  (∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {A : Type*} [Semiring A]
    (w12 w23 w31 : ArnoldExterior R M) (φ : ArnoldExterior R M →+* A),
    arnoldMixedRelation R M w12 w23 w31 ∈ RingHom.ker φ →
      φ (arnoldMixedRelation R M w12 w23 w31) = 0) ∧
  (∀ (X₁ X₂ X₃ : InfoGeometry.Clifford.Soldering.Vec22),
    TripleNonNull X₁ X₂ X₃ →
      (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
        InfoGeometry.Twistor.Incidence.Incident Z X₁ ∧
        InfoGeometry.Twistor.Incidence.Incident Z X₂ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
        InfoGeometry.Twistor.Incidence.Incident Z X₂ ∧
        InfoGeometry.Twistor.Incidence.Incident Z X₃ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : InfoGeometry.Twistor.Incidence.Twistor,
        InfoGeometry.Twistor.Incidence.Incident Z X₃ ∧
        InfoGeometry.Twistor.Incidence.Incident Z X₁ ∧ Z.2 ≠ 0)) ∧
  (∀ v : Minkowski4,
    Matrix.det (pauliMatrix v) = ((v.q : ℝ) : ℂ)) := by
  refine ⟨?residue, ?winding, ?arnold, ?twistor, ?determinantCarrier⟩
  · intro R hR
    exact circleIntegral_grothendieck_dlog R hR
  · intro R hR n
    exact grothendieckTomitaWilsonBridge n R hR
  · intro R _ M _ _ A _ w12 w23 w31 φ hKer
    exact arnold_mixed_relation_vanishes_under_kernel_membership
      (R := R) (M := M) (A := A) w12 w23 w31 φ hKer
  · intro X₁ X₂ X₃ hTriple
    exact triple_nonnull_excludes_pairwise_common_twistors X₁ X₂ X₃ hTriple
  · intro v
    exact det_pauliMatrix v

end InfoGeometry.Projective.DeRhamArnoldTwistorPenroseBridge
