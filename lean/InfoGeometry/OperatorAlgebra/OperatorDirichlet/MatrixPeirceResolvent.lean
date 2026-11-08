/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CharacteristicResolvent
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Resolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors

/-!
# Finite-matrix resolvents for Peirce odd operators

The Peirce factorizations `(1 - Φ)(1 + Φ) = 1 - V` and
`(1 - J)(1 + J) = 1 + V` convert nonzero determinant conditions on the
operator-valued factors `1 ± V` into resolvents for `Φ` and `J` at `1`.
Determinants only certify matrix inverses; the operators are not diagonalized
and are not assumed to commute.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.CharacteristicResolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem scalar_eq_algebraMap (z : ℂ) :
    Matrix.scalar ι z = algebraMap ℂ (Matrix ι ι ℂ) z := by
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal]

/-- Determinant form of the characteristic factorization for `Φ² = V`. -/
theorem peircePhi_char_value_det_factorization
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) (z : ℂ) :
    (algebraMap ℂ (Matrix ι ι ℂ) z - genPhi P A C).det *
        (algebraMap ℂ (Matrix ι ι ℂ) z + genPhi P A C).det =
      (algebraMap ℂ (Matrix ι ι ℂ) (z * z) - genV P A C).det := by
  have hΦSq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
  calc
    _ = ((algebraMap ℂ (Matrix ι ι ℂ) z - genPhi P A C) *
        (algebraMap ℂ (Matrix ι ι ℂ) z + genPhi P A C)).det := by
      rw [Matrix.det_mul]
    _ = _ := congrArg Matrix.det (charPoly_factor hΦSq z)

/-- Determinant form of the characteristic factorization for `J² = -V`. -/
theorem peirceJ_char_value_det_factorization
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) (z : ℂ) :
    (algebraMap ℂ (Matrix ι ι ℂ) z - genJ P A C).det *
        (algebraMap ℂ (Matrix ι ι ℂ) z + genJ P A C).det =
      (algebraMap ℂ (Matrix ι ι ℂ) (z * z) + genV P A C).det := by
  have hJSq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.1
  have hfactor :
      (algebraMap ℂ (Matrix ι ι ℂ) z - genJ P A C) *
          (algebraMap ℂ (Matrix ι ι ℂ) z + genJ P A C) =
        algebraMap ℂ (Matrix ι ι ℂ) (z * z) + genV P A C := by
    simpa only [sub_neg_eq_add] using charPoly_factor hJSq z
  calc
    _ = ((algebraMap ℂ (Matrix ι ι ℂ) z - genJ P A C) *
        (algebraMap ℂ (Matrix ι ι ℂ) z + genJ P A C)).det := by
      rw [Matrix.det_mul]
    _ = _ := congrArg Matrix.det hfactor

/-- At an arbitrary complex spectral value `z`, a nonzero determinant of
`z² I - V` certifies the two-sided resolvent of `Φ`. -/
theorem peircePhi_resolvent_of_mass_char_value_det_ne_zero
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) (z : ℂ)
    (hdet :
      (algebraMap ℂ (Matrix ι ι ℂ) (z * z) - genV P A C).det ≠ 0) :
    (Matrix.scalar ι z - genPhi P A C) *
        CharacteristicResolvent.resolvent (genPhi P A C) z = 1 ∧
      CharacteristicResolvent.resolvent (genPhi P A C) z *
        (Matrix.scalar ι z - genPhi P A C) = 1 := by
  have hdetMul := peircePhi_char_value_det_factorization P A C hP z
  have hleft :
      (algebraMap ℂ (Matrix ι ι ℂ) z - genPhi P A C).det ≠ 0 := by
    intro hz
    apply hdet
    rw [← hdetMul, hz, zero_mul]
  have hchar : (genPhi P A C).charpoly.eval z ≠ 0 := by
    have hleft' : (Matrix.scalar ι z - genPhi P A C).det ≠ 0 := by
      rw [scalar_eq_algebraMap (ι := ι) z]
      exact hleft
    simpa only [Matrix.eval_charpoly] using hleft'
  exact ⟨difference_mul_resolvent _ _ hchar,
    resolvent_mul_difference _ _ hchar⟩

/-- At an arbitrary complex spectral value `z`, a nonzero determinant of
`z² I + V` certifies the two-sided resolvent of `J`. -/
theorem peirceJ_resolvent_of_mass_char_value_det_ne_zero
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) (z : ℂ)
    (hdet :
      (algebraMap ℂ (Matrix ι ι ℂ) (z * z) + genV P A C).det ≠ 0) :
    (Matrix.scalar ι z - genJ P A C) *
        CharacteristicResolvent.resolvent (genJ P A C) z = 1 ∧
      CharacteristicResolvent.resolvent (genJ P A C) z *
        (Matrix.scalar ι z - genJ P A C) = 1 := by
  have hdetMul := peirceJ_char_value_det_factorization P A C hP z
  have hleft :
      (algebraMap ℂ (Matrix ι ι ℂ) z - genJ P A C).det ≠ 0 := by
    intro hz
    apply hdet
    rw [← hdetMul, hz, zero_mul]
  have hchar : (genJ P A C).charpoly.eval z ≠ 0 := by
    have hleft' : (Matrix.scalar ι z - genJ P A C).det ≠ 0 := by
      rw [scalar_eq_algebraMap (ι := ι) z]
      exact hleft
    simpa only [Matrix.eval_charpoly] using hleft'
  exact ⟨difference_mul_resolvent _ _ hchar,
    resolvent_mul_difference _ _ hchar⟩

/-- If the operator `1 - V` has nonzero determinant, then `1 - Φ` has a
two-sided matrix inverse. The inverse is the finite-matrix resolvent of `Φ`
at spectral value `1`. -/
theorem peircePhi_resolvent_of_mass_det_ne_zero
    (P A C : Matrix ι ι ℂ) (hP : P * P = P)
    (hdet : (1 - genV P A C).det ≠ 0) :
    (1 - genPhi P A C) * CharacteristicResolvent.resolvent (genPhi P A C) 1 = 1 ∧
      CharacteristicResolvent.resolvent (genPhi P A C) 1 * (1 - genPhi P A C) = 1 := by
  have hdet' :
      (algebraMap ℂ (Matrix ι ι ℂ) ((1 : ℂ) * 1) - genV P A C).det ≠ 0 := by
    simpa using hdet
  simpa using peircePhi_resolvent_of_mass_char_value_det_ne_zero
    P A C hP 1 hdet'

/-- If the operator `1 + V` has nonzero determinant, then `1 - J` has a
two-sided matrix inverse, given by the resolvent of `J` at spectral value `1`.
-/
theorem peirceJ_resolvent_of_partition_det_ne_zero
    (P A C : Matrix ι ι ℂ) (hP : P * P = P)
    (hdet : (1 + genV P A C).det ≠ 0) :
    (1 - genJ P A C) * CharacteristicResolvent.resolvent (genJ P A C) 1 = 1 ∧
      CharacteristicResolvent.resolvent (genJ P A C) 1 * (1 - genJ P A C) = 1 := by
  have hdet' :
      (algebraMap ℂ (Matrix ι ι ℂ) ((1 : ℂ) * 1) + genV P A C).det ≠ 0 := by
    simpa using hdet
  simpa using peirceJ_resolvent_of_mass_char_value_det_ne_zero
    P A C hP 1 hdet'

/-- The chiral determinant product equals the product of the two mass
characteristic determinants. This is the finite-matrix form of the chiral
factor identity, with no analytic Euler-product interpretation. -/
theorem chiral_factor_determinant_product
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) :
    (1 - genSig P A C).det * (1 + genSig P A C).det =
      (1 - genV P A C).det * (1 + genV P A C).det := by
  have hfactor :
      (1 - genSig P A C) * (1 + genSig P A C) =
        (1 - genV P A C) * (1 + genV P A C) := by
    simpa [chiralFactor, chiralConjugateFactor, zetaFactor, zetaPlusFactor] using
      (chiral_factor_product hP A C).1
  calc
    _ = ((1 - genSig P A C) * (1 + genSig P A C)).det := by rw [Matrix.det_mul]
    _ = ((1 - genV P A C) * (1 + genV P A C)).det := congrArg Matrix.det hfactor
    _ = _ := by rw [Matrix.det_mul]

/-- If both finite chiral characteristic factors have nonzero determinant,
then the `Φ` and `J` resolvents at `1` exist. The bridge is the finite matrix
determinant consequence of `(1-Σ)(1+Σ)=(1-V)(1+V)`; no analytic Euler
product is involved. -/
theorem chiral_factor_determinants_imply_peirce_resolvents
    (P A C : Matrix ι ι ℂ) (hP : P * P = P)
    (hminus : (1 - genSig P A C).det ≠ 0)
    (hplus : (1 + genSig P A C).det ≠ 0) :
    ((1 - genPhi P A C) * CharacteristicResolvent.resolvent (genPhi P A C) 1 = 1 ∧
      CharacteristicResolvent.resolvent (genPhi P A C) 1 * (1 - genPhi P A C) = 1) ∧
    ((1 - genJ P A C) * CharacteristicResolvent.resolvent (genJ P A C) 1 = 1 ∧
      CharacteristicResolvent.resolvent (genJ P A C) 1 * (1 - genJ P A C) = 1) := by
  have hdetProduct := chiral_factor_determinant_product P A C hP
  have hdetPair := mul_ne_zero hminus hplus
  have hmassMinus : (1 - genV P A C).det ≠ 0 := by
    intro hz
    apply hdetPair
    rw [hdetProduct, hz, zero_mul]
  have hmassPlus : (1 + genV P A C).det ≠ 0 := by
    intro hz
    apply hdetPair
    rw [hdetProduct, hz, mul_zero]
  exact ⟨peircePhi_resolvent_of_mass_det_ne_zero P A C hP hmassMinus,
    peirceJ_resolvent_of_partition_det_ne_zero P A C hP hmassPlus⟩

end InfoGeometry.OperatorAlgebra.OperatorDirichlet

end
