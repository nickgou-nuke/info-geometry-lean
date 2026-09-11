import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus.PolarizationProjectors

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 2. Deterministic and projective Jones layers -/

/--
A deterministic Jones datum.

This is the coherent single-operator layer.
-/
structure DeterministicJonesDatum
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Boundary/Jones operator. -/
  R : Op

  /-- Abstract adjoint backend. -/
  adj : Op → Op

  /-- Deterministic state action. -/
  action : Op → Op

  /-- The action is `rho ↦ R rho R†`. -/
  action_eq_jones :
    ∀ rho : Op,
      action rho =
        PolarizationProjectorPair.jonesAction adj R rho

/--
A projective Jones datum.

This represents ray-level action where global nonzero scalar factors are
discarded.  Brewster reflection becomes projector-like at this layer.
-/
structure ProjectiveJonesDatum
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Boundary operator. -/
  R : Op

  /-- Projective equivalence predicate. -/
  projectivelyEquivalent : Op → Op → Prop

  /-- The projective equivalence is reflexive. -/
  projective_refl :
    ∀ x : Op, projectivelyEquivalent x x

namespace ProjectiveJonesDatum

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (J : ProjectiveJonesDatum Op)

/-- Re-export reflexivity of projective equivalence. -/
theorem refl
    (x : Op) :
    J.projectivelyEquivalent x x :=
  J.projective_refl x

end ProjectiveJonesDatum

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
