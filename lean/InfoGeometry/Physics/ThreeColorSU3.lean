import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Canonical.CyclotomicCliffordPauliQutrit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The special unitary three-colour group

`SU3` is the determinant-one subgroup of Mathlib's native unitary group on
`3 × 3` complex matrices.  The ambient group is therefore associative and its
inverse is supplied by `Unitary`; no matrix subtype with a hand-written group
instance is introduced.

The qutrit cyclotomic phase remains in its canonical owner.  This file only
bundles the genuine special-unitary carrier and its elementary structural
properties.
-/

namespace InfoGeometry.Physics.ThreeColorSU3

open Matrix

abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev U3C := unitary M3C

def SU3 : Subgroup U3C where
  carrier := {U | (U : M3C).det = 1}
  one_mem' := by simp [Matrix.det_one]
  mul_mem' {U V} hU hV := by
    change Matrix.det ((U : M3C) * (V : M3C)) = 1
    rw [Matrix.det_mul, hU, hV, one_mul]
  inv_mem' {U} hU := by
    change Matrix.det (↑((U : U3C)⁻¹) : M3C) = 1
    have hmat : (U : M3C) * (↑((U : U3C)⁻¹) : M3C) = 1 := by
      rw [show (U : U3C)⁻¹ = star (U : U3C) from
        (Unitary.star_eq_inv (U : U3C)).symm]
      exact Unitary.coe_mul_star_self (U : U3C)
    have hdet : (U : M3C).det *
        ((↑((U : U3C)⁻¹) : M3C).det) = 1 := by
      rw [← Matrix.det_mul, hmat, Matrix.det_one]
    rw [hU, one_mul] at hdet
    exact hdet

abbrev Element := SU3

@[simp] theorem det_eq_one (U : Element) :
    ((U : U3C) : M3C).det = 1 := U.property

theorem is_unitary (U : Element) :
    ((U : U3C) : M3C) ∈ unitary M3C := (U : U3C).property

theorem subgroup_carrier_iff (U : U3C) :
    U ∈ SU3 ↔ (U : M3C).det = 1 := Iff.rfl

end InfoGeometry.Physics.ThreeColorSU3
