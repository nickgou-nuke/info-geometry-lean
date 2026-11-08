/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorFrechetDerivationJet
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport

/-!
# Continuous Fréchet–Leibniz realization of a CE connection

An existing continuous Leibniz derivation and the inner derivation generated
by a CE connection value combine to give a continuous covariant derivation.
Its curvature commutator agrees with the native CE curvature. The CE complex
and the exterior algebra of scalar forms remain distinct carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.FrechetCECovariantConnection

open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetDerivationJet.FrechetBridge
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra.DerivationLieLane

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The adjoint covariant action of a continuous derivation direction. -/
def covariantFrechet
    (Γ : OneForm (realDerivationsLane A)) (D : FrechetOperatorDerivation ℝ A) :
    FrechetOperatorDerivation ℝ A where
  toContinuousLinearMap := D.toContinuousLinearMap +
    (FrechetOperatorDerivation.ofInner (Γ (toRealDerivation D))).toContinuousLinearMap
  leibniz := by
    intro a b
    change D (a * b) + FrechetOperatorDerivation.ofInner (Γ (toRealDerivation D)) (a * b) = _
    rw [D.leibniz, (FrechetOperatorDerivation.ofInner _).leibniz]
    simp only [add_apply]
    noncomm_ring

@[simp] theorem covariantFrechet_apply
    (Γ : OneForm (realDerivationsLane A)) (D : FrechetOperatorDerivation ℝ A) (a : A) :
    covariantFrechet Γ D a = D a + Γ (toRealDerivation D) * a -
      a * Γ (toRealDerivation D) := by
  change D a + (Γ (toRealDerivation D) * a - a * Γ (toRealDerivation D)) = _
  abel

/-- The continuous construction agrees pointwise with the native CE
covariant derivation, on a Fréchet derivation direction. -/
theorem covariantFrechet_eq_ce
    (Γ : OneForm (realDerivationsLane A)) (D : FrechetOperatorDerivation ℝ A) (a : A) :
    covariantFrechet Γ D a =
      covariantDerivative (realDerivationsLane A) Γ (toRealDerivation D) a := by
  rw [covariantFrechet_apply]
  rfl

/-- The continuous covariant operator is its own Fréchet derivative at each
point, and satisfies the noncommutative Leibniz rule. -/
theorem covariantFrechet_differentiable_leibniz
    (Γ : OneForm (realDerivationsLane A)) (D : FrechetOperatorDerivation ℝ A)
    (x a b : A) :
    HasFDerivAt (covariantFrechet Γ D : A → A)
      (covariantFrechet Γ D).toContinuousLinearMap x ∧
    covariantFrechet Γ D (a * b) =
      covariantFrechet Γ D a * b + a * covariantFrechet Γ D b :=
  ⟨(covariantFrechet Γ D).hasFDerivAt x, (covariantFrechet Γ D).leibniz a b⟩

/-- The commutator defect of the continuous covariant derivations is the
inner action of the native CE curvature. -/
theorem covariantFrechet_curvature
    (Γ : OneForm (realDerivationsLane A))
    (D E : FrechetOperatorDerivation ℝ A) (a : A) :
    covariantFrechet Γ D (covariantFrechet Γ E a) -
      covariantFrechet Γ E (covariantFrechet Γ D a) -
      covariantFrechet Γ (FrechetOperatorDerivation.commutator D E) a =
    connectionCurvature (realDerivationsLane A) Γ (toRealDerivation D) (toRealDerivation E) * a -
      a * connectionCurvature (realDerivationsLane A) Γ (toRealDerivation D) (toRealDerivation E) := by
  simp only [covariantFrechet_eq_ce, toRealDerivation_commutator]
  exact covariantDerivative_commutator (realDerivationsLane A) Γ
    (toRealDerivation D) (toRealDerivation E) a

/-- Gauge covariance holds for the continuous Fréchet realization on every
operator, including the inhomogeneous term in the transformed connection. -/
theorem covariantFrechet_gauge_intertwine
    (Γ : OneForm (realDerivationsLane A)) (u : Aˣ)
    (D : FrechetOperatorDerivation ℝ A) (a : A) :
    covariantFrechet (gaugeOneForm (realDerivationsLane A) Γ u) D
        (InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u a) =
      InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u (covariantFrechet Γ D a) := by
  simp only [covariantFrechet_eq_ce]
  exact covariantDerivative_gaugeOneForm (realDerivationsLane A) Γ u (toRealDerivation D) a

end InfoGeometry.Canonical.FrechetCECovariantConnection

end
