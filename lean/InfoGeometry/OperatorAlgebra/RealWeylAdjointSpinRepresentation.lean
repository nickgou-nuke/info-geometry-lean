import InfoGeometry.Canonical.HestenesSpinAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Adjoint right multiplier and the two Weyl spin representations

For a Hermitian Pauli four-vector the Lorentz action is

`X |-> g X g^dagger`.

Thus the right *multiplier* is literally `g^dagger`.  The right-handed spinor
representation, however, must be a homomorphism and is therefore
`g |-> (g^{-1})^dagger`.  Confusing these two statements reverses the group
multiplication order.  This file formalizes both and proves the distinction.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation

open Matrix
open InfoGeometry.Canonical.HestenesSpinAction

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev WeylSpinor := Fin 2 → ℂ
abbrev WeylPair := WeylSpinor × WeylSpinor

/-- Right multiplier in the Hermitian-vector congruence action. -/
def rightAdjointMultiplier (g : SL2C) : Mat2C :=
  star (g : Mat2C)

/-- The vector action uses the literal relation `g_R = g_L^dagger` at the
level of left and right matrix multiplication. -/
theorem spinAction_eq_left_mul_rightAdjoint
    (g : SL2C) (X : Mat2C) :
    spinAction g X = (g : Mat2C) * X * rightAdjointMultiplier g := rfl

/-- Dagger is an antihomomorphism, so right multipliers reverse products. -/
theorem rightAdjointMultiplier_mul_reverse
    (g h : SL2C) :
    rightAdjointMultiplier (g * h) =
      rightAdjointMultiplier h * rightAdjointMultiplier g := by
  simp [rightAdjointMultiplier, Matrix.star_mul]

/-- The genuine right-handed Weyl representation is inverse-adjoint. -/
def rightWeyl (g : SL2C) : SL2C :=
  ⟨star (((g⁻¹ : SL2C) : Mat2C)), by
    change Matrix.det ((((g⁻¹ : SL2C) : Mat2C)ᴴ)) = 1
    rw [Matrix.det_conjTranspose]
    rw [(g⁻¹).prop]
    exact map_one (starRingEnd ℂ)⟩

@[simp] theorem rightWeyl_coe (g : SL2C) :
    ((rightWeyl g : SL2C) : Mat2C) =
      star (((g⁻¹ : SL2C) : Mat2C)) := rfl

@[simp] theorem rightWeyl_one :
    rightWeyl (1 : SL2C) = 1 := by
  apply Subtype.ext
  simp [rightWeyl]

/-- Inverse followed by dagger reverses twice and is a homomorphism. -/
theorem rightWeyl_mul (g h : SL2C) :
    rightWeyl (g * h) = rightWeyl g * rightWeyl h := by
  apply Subtype.ext
  simp [rightWeyl, Matrix.star_mul]

/-- Bundled right-handed Weyl representation. -/
def rightWeylRepresentation : SL2C →* SL2C where
  toFun := rightWeyl
  map_one' := rightWeyl_one
  map_mul' := rightWeyl_mul

/-- Left-handed defining representation. -/
def leftWeylRepresentation : SL2C →* SL2C :=
  MonoidHom.id SL2C

/-- The two real-Lorentz-related complex Weyl factors. -/
def chiralSpinPair (g : SL2C) : SL2C × SL2C :=
  (leftWeylRepresentation g, rightWeylRepresentation g)

@[simp] theorem chiralSpinPair_left (g : SL2C) :
    (chiralSpinPair g).1 = g := rfl

@[simp] theorem chiralSpinPair_right (g : SL2C) :
    (chiralSpinPair g).2 = rightWeyl g := rfl

/-- Matrix action on a Weyl spinor. -/
def matrixSpinAction (M : Mat2C) (psi : WeylSpinor) : WeylSpinor :=
  M.mulVec psi

/-- Paired left/right Weyl spinor action. -/
def actWeylPair (g : SL2C) (psi : WeylPair) : WeylPair :=
  (matrixSpinAction (g : Mat2C) psi.1,
    matrixSpinAction (rightWeyl g : Mat2C) psi.2)

@[simp] theorem actWeylPair_one (psi : WeylPair) :
    actWeylPair 1 psi = psi := by
  rcases psi with ⟨psiL, psiR⟩
  apply Prod.ext <;>
    simp [actWeylPair, matrixSpinAction]

/-- The two Weyl actions compose in the same group order. -/
theorem actWeylPair_mul (g h : SL2C) (psi : WeylPair) :
    actWeylPair (g * h) psi = actWeylPair g (actWeylPair h psi) := by
  rcases psi with ⟨psiL, psiR⟩
  apply Prod.ext
  · simp [actWeylPair, matrixSpinAction, Matrix.mulVec_mulVec]
  · change matrixSpinAction ((rightWeyl (g * h) : SL2C) : Mat2C) psiR =
        matrixSpinAction ((rightWeyl g : SL2C) : Mat2C)
          (matrixSpinAction ((rightWeyl h : SL2C) : Mat2C) psiR)
    rw [rightWeyl_mul]
    simp [matrixSpinAction, Matrix.mulVec_mulVec]

/-- The congruence action preserves Hermitian matrices. -/
theorem spinAction_preserves_hermitian
    (g : SL2C) (X : Mat2C) (hX : star X = X) :
    star (spinAction g X) = spinAction g X := by
  simp [spinAction, Matrix.star_mul, hX, mul_assoc]

/-- The already-owned determinant theorem and the new adjoint-factor theorem
form the finite real Lorentz-spin packet. -/
theorem real_weyl_spin_packet
    (g : SL2C) (X : Mat2C) (hX : star X = X) :
    spinAction g X = (g : Mat2C) * X * rightAdjointMultiplier g ∧
      Matrix.det (spinAction g X) = Matrix.det X ∧
      star (spinAction g X) = spinAction g X := by
  exact ⟨spinAction_eq_left_mul_rightAdjoint g X,
    spinAction_preserves_det g X,
    spinAction_preserves_hermitian g X hX⟩

end InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
