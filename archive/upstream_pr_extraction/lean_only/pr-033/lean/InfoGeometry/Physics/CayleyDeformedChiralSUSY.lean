import InfoGeometry.Physics.ChiralSUSYBlockFactorization
import InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet

/-!
# Cayley-deformed chiral SUSY comparison

This owner compares two products of the same chiral data:

* ordinary matrix multiplication, whose square is the SUSY partner
  Hamiltonian;
* the polarized Cayley product, whose same-sheet vector channel is the
  oriented cross-product transfer and whose mixed channel is scalar.

The coefficients are finite algebraic parameters.  Differential operators,
curvature, Cuntz shifts, and Fredholm indices can be supplied later through
these parameters; this file does not assert analytic domain or index facts.
-/

namespace InfoGeometry.Physics.CayleyDeformedChiralSUSY

open InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet
open InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet.ChiralAmplitude

structure Data (R : Type*) where
  plusFactor : R
  minusFactor : R
  plusVector : Vec3 R
  minusVector : Vec3 R

variable {R : Type*} [CommRing R]

def qPlus (D : Data R) : ChiralBlock R :=
  chiralQPlus D.plusFactor

def qMinus (D : Data R) : ChiralBlock R :=
  chiralQMinus D.minusFactor

def dirac (D : Data R) : ChiralBlock R :=
  chiralDirac D.plusFactor D.minusFactor

def hSUSY (D : Data R) : ChiralBlock R :=
  chiralSUSYHamiltonian D.plusFactor D.minusFactor

def plusSpin (D : Data R) : ChiralAmplitude R :=
  plusTriplet D.plusVector

def minusSpin (D : Data R) : ChiralAmplitude R :=
  minusTriplet D.minusVector

theorem qPlus_sq (D : Data R) : qPlus D * qPlus D = 0 := by
  exact chiralQPlus_sq D.plusFactor

theorem qMinus_sq (D : Data R) : qMinus D * qMinus D = 0 := by
  exact chiralQMinus_sq D.minusFactor

/-- The ordinary product sees the symmetric SUSY/Hamiltonian channel. -/
theorem ordinary_product_is_hSUSY (D : Data R) :
    dirac D * dirac D = hSUSY D := by
  exact chiralDirac_sq_eq_susyHamiltonian D.plusFactor D.minusFactor

/-- The same-sheet Cayley product transfers the oriented vector channel. -/
theorem cayley_plus_spin_transfer (D : Data R) :
    star (plusSpin D) (plusSpin D) = minusTriplet (cross D.plusVector D.plusVector) := by
  exact plus_plus D.plusVector D.plusVector

/-- The opposite-sheet Cayley product is the scalar contraction channel. -/
theorem cayley_mixed_spin_scalar (D : Data R) :
    star (plusSpin D) (minusSpin D) = plusPole (-dot D.plusVector D.minusVector) := by
  exact plus_minus D.plusVector D.minusVector

/-- A compact packet exposing the two complementary products. -/
theorem two_product_packet (D : Data R) :
    qPlus D * qPlus D = 0 ∧
      qMinus D * qMinus D = 0 ∧
      dirac D * dirac D = hSUSY D ∧
      star (plusSpin D) (plusSpin D) =
        minusTriplet (cross D.plusVector D.plusVector) ∧
      star (plusSpin D) (minusSpin D) =
        plusPole (-dot D.plusVector D.minusVector) := by
  exact ⟨qPlus_sq D, qMinus_sq D, ordinary_product_is_hSUSY D,
    cayley_plus_spin_transfer D, cayley_mixed_spin_scalar D⟩

end InfoGeometry.Physics.CayleyDeformedChiralSUSY
