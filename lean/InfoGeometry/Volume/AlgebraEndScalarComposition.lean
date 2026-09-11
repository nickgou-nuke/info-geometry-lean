import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scalar laws for explicit endomorphism composition

The ambient `AlgebraEnd` multiplication instance need not expose the scalar
tower laws needed by ring automation.  This owner keeps composition explicit
and proves only the two linearity lemmas needed by commutator calculations.
-/

namespace InfoGeometry.Volume.AlgebraEndScalarComposition

universe u

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

abbrev AlgebraEnd (H : Type u) [AddCommGroup H] [Module ℝ H] := H →ₗ[ℝ] H

def compose (A B : AlgebraEnd H) : AlgebraEnd H := A.comp B

theorem compose_assoc (A B C : AlgebraEnd H) :
    compose (compose A B) C = compose A (compose B C) := by
  ext x
  rfl

theorem compose_smul_right (A B : AlgebraEnd H) (r : ℝ) :
    compose A (r • B) = r • compose A B := by
  ext x
  simp [compose]

theorem compose_smul_left (A B : AlgebraEnd H) (r : ℝ) :
    compose (r • A) B = r • compose A B := by
  ext x
  simp [compose]

def commutator (A B : AlgebraEnd H) : AlgebraEnd H :=
  compose A B - compose B A

theorem commutator_self_smul (A : AlgebraEnd H) (r : ℝ) :
    commutator A (r • A) = 0 := by
  unfold commutator
  rw [compose_smul_right, compose_smul_left]
  exact sub_self _

theorem commutator_antisymm (A B : AlgebraEnd H) :
    commutator A B = -(commutator B A) := by
  unfold commutator
  ext x
  simp [compose]

theorem commutator_self (A : AlgebraEnd H) :
    commutator A A = 0 := by
  unfold commutator
  exact sub_self _

theorem commutator_jacobi (A B C : AlgebraEnd H) :
    commutator A (commutator B C) +
        commutator B (commutator C A) +
        commutator C (commutator A B) = 0 := by
  ext x
  simp [commutator, compose]
  abel

theorem commutator_leibniz (A B C : AlgebraEnd H) :
    commutator A (compose B C) =
      compose (commutator A B) C + compose B (commutator A C) := by
  ext x
  simp [commutator, compose]

theorem commutator_add_right (A B C : AlgebraEnd H) :
    commutator A (B + C) = commutator A B + commutator A C := by
  unfold commutator
  ext x
  simp [compose]
  abel

theorem commutator_add_left (A B C : AlgebraEnd H) :
    commutator (A + B) C = commutator A C + commutator B C := by
  unfold commutator
  ext x
  simp [compose]
  abel

theorem commutator_smul_right (A B : AlgebraEnd H) (r : ℝ) :
    commutator A (r • B) = r • commutator A B := by
  unfold commutator
  rw [compose_smul_right, compose_smul_left]
  rw [smul_sub]

def innerDerivation (A : AlgebraEnd H) : AlgebraEnd H →ₗ[ℝ] AlgebraEnd H where
  toFun B := commutator A B
  map_add' B C := commutator_add_right A B C
  map_smul' r B := commutator_smul_right A B r

@[simp] theorem innerDerivation_apply (A B : AlgebraEnd H) :
    innerDerivation A B = commutator A B :=
  rfl

theorem innerDerivation_self_zero (A : AlgebraEnd H) :
    innerDerivation A A = 0 := by
  exact commutator_self A

theorem innerDerivation_leibniz (A B C : AlgebraEnd H) :
    innerDerivation A (compose B C) =
      compose (innerDerivation A B) C + compose B (innerDerivation A C) := by
  exact commutator_leibniz A B C

end InfoGeometry.Volume.AlgebraEndScalarComposition
