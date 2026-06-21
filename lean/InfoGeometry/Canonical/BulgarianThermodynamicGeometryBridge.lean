import InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket
import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

/-!
# Bulgarian Thermodynamic Geometry Bridge

Concrete bridge from the multilingual Bulgarian theorem packet into existing
finite Souriau owner surfaces.

This module does two bounded things only:

* packages the Fisher/Hessian/covariance family against the already-owned
  finite Souriau response matrix;
* packages the entropy-production/second-law family against the already-owned
  finite Onsager entropy-production theorem.

It does not claim the full analytic Gibbs-Souriau integral story.
-/

namespace InfoGeometry.Canonical.BulgarianThermodynamicGeometryBridge

open InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket
open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.GrandCanonical

variable {α : Type _}

abbrev BulgarianFiniteMoment := ℝ × ℝ
abbrev BulgarianFiniteObservable := Fin 2
abbrev BulgarianFiniteForce := ℝ × ℝ

/-- Finite pair of conjugate thermodynamic readouts in the Bulgarian packet lane. -/
@[rep_depth thermo]
noncomputable def finiteThermodynamicMoment
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : BulgarianFiniteMoment :=
  (souriauMeanShift M T, souriauMeanNumber M T)

/-- Matrix-entry Fisher/covariance readout at a finite Souriau parameter. -/
@[rep_depth thermo]
noncomputable def finiteFisherCovarianceEntry
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (i j : BulgarianFiniteObservable) : ℝ :=
  souriauFisherMetricMatrix M T i j

/--
Concrete Bulgarian family-A interface realized by the finite Souriau response
matrix and its covariance/Hessian projection theorems.
-/
@[rep_depth thermo]
noncomputable def familyAInterfaceOfSouriau
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det) :
    InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianFamilyAInterface
      GeometricTemperature BulgarianFiniteMoment BulgarianFiniteObservable where
  potential := souriauMassieuPotential M
  moment := finiteThermodynamicMoment M
  fisherMetric := fun T₁ T₂ =>
    souriauEntropyProduction M T₁ T₂.beta T₂.mu
  covarianceMetric := finiteFisherCovarianceEntry M T
  firstDerivativeEncodesMoments :=
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
        -souriauMeanShift M T
      ∧ deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
        T.beta * souriauMeanNumber M T
  fisherEqMassieuHessian :=
    (souriauFisherResponseMatrix M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muMu =
        T.beta ^ (2 : ℕ) * varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
  covarianceRealizesFisher :=
    finiteFisherCovarianceEntry M T 0 0 =
        (souriauFisherResponseMatrix M T).betaBeta
      ∧ finiteFisherCovarianceEntry M T 0 1 =
        (souriauFisherResponseMatrix M T).betaMu
      ∧ finiteFisherCovarianceEntry M T 1 0 =
        (souriauFisherResponseMatrix M T).muBeta
      ∧ finiteFisherCovarianceEntry M T 1 1 =
        (souriauFisherResponseMatrix M T).muMu
  fisherSymmetric := (souriauFisherResponseMatrix M T).Symmetric
  fisherNonnegative := (souriauFisherResponseMatrix M T).PositiveSemidefinite

/--
Concrete Bulgarian family-D interface realized by finite Souriau Onsager entropy
production and the finite Fisher response whose `2 × 2` response-matrix
determinant gate is nonnegative.  This is not the `det(exp A)` H¹
volume-cocycle determinant.
-/
@[rep_depth thermo]
noncomputable def familyDInterfaceOfSouriau
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det) :
    InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianFamilyDInterface
      BulgarianFiniteForce where
  entropyProduction := fun x => souriauEntropyProduction M T x.1 x.2
  quadraticFormRealization :=
    ∀ x : BulgarianFiniteForce,
      (fun y => souriauEntropyProduction M T y.1 y.2) x =
        souriauEntropyProduction M T x.1 x.2
  nonnegative :=
    ∀ x : BulgarianFiniteForce,
      0 ≤ souriauEntropyProduction M T x.1 x.2
  vanishesAtEquilibrium :=
    souriauEntropyProduction M T 0 0 = 0

/--
Family-A bridge theorem: the Bulgarian packet's Fisher/Hessian layer is owned
by the finite Souriau translator packet plus the finite response-matrix
determinant gate.
-/
@[rep_depth thermo]
theorem familyA_bridge_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det) :
    let A := familyAInterfaceOfSouriau M T hdet
    A.fisherSymmetric ∧ A.fisherNonnegative := by
  refine ⟨?_, ?_⟩
  · exact souriauFisherResponseMatrix_symmetric M T
  · exact souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg M T hdet

/-- Family-D bridge theorem: the Bulgarian entropy-production layer is realized
by the finite Souriau Onsager second-law theorem. -/
@[rep_depth thermo]
theorem familyD_bridge_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det)
    (x : BulgarianFiniteForce) :
    let D := familyDInterfaceOfSouriau M T hdet
    0 ≤ D.entropyProduction x := by
  exact souriauEntropyProduction_nonneg_of_det_nonneg M T hdet x.1 x.2

end InfoGeometry.Canonical.BulgarianThermodynamicGeometryBridge
