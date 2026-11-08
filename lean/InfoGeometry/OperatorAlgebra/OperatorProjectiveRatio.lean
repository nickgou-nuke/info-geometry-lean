import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.InnerConjugation

/-!
# Noncommutative operator ratios

The ratio of two invertible operators is represented by right division.  This
is an internal ring-valued construction; no commutative or scalar projective
space is used.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Ring A]

def rightOperatorRatio (x y : Aˣ) : A :=
  (y : A) * (↑(x⁻¹) : A)

theorem RingHom.map_rightOperatorRatio
    {B : Type*} [Ring B] (φ : A →+* B) (x y : Aˣ) :
    φ (rightOperatorRatio x y) =
      rightOperatorRatio (Units.map φ x) (Units.map φ y) := by
  simp [rightOperatorRatio, Units.coe_map, Units.coe_map_inv]

theorem innerConjugation_map_rightOperatorRatio
    (u x y : Aˣ) :
    innerConjugation u (rightOperatorRatio x y) =
      rightOperatorRatio
        (Units.map (innerConjugationRingEquiv u).toMonoidHom x)
        (Units.map (innerConjugationRingEquiv u).toMonoidHom y) := by
  simp [rightOperatorRatio, innerConjugation, innerConjugationRingEquiv,
    Units.coe_map, Units.coe_map_inv, mul_assoc]

theorem innerConjugationNat_map_rightOperatorRatio
    (u x y : Aˣ) (n : ℕ) :
    innerConjugationNat u n (rightOperatorRatio x y) =
      rightOperatorRatio
        (Units.map (innerConjugationNat u n).toMonoidHom x)
        (Units.map (innerConjugationNat u n).toMonoidHom y) := by
  simp [innerConjugationNat, innerConjugation_map_rightOperatorRatio]

end

end InfoGeometry.OperatorAlgebra
