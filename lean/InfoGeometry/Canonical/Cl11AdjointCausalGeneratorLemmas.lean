import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Mixed products in the finite `Cl(1,1)` adjoint representation

This owner records the remaining mixed products of the three normalized
Clifford units.  They are consequences of the unit identities in the
adjoint-representation owner, not a new group or carrier.
-/

namespace InfoGeometry.Canonical.Cl11AdjointCausalGeneratorLemmas

open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation

theorem adjointAlgHom_gamma_causal :
    adjointAlgHom gammaUnit * adjointAlgHom causalUnit =
      adjointAlgHom bivectorUnit := by
  have hunit : gammaUnit * causalUnit = bivectorUnit := by
    rw [causalUnit_eq_gamma_mul_bivector, ← mul_assoc, gammaUnit_sq]
    simp
  rw [← adjointAlgHom.map_mul, hunit]

theorem adjointAlgHom_causal_gamma :
    adjointAlgHom causalUnit * adjointAlgHom gammaUnit =
      adjointAlgHom bivectorUnit := by
  have hunit : causalUnit * gammaUnit = -bivectorUnit := by
    apply Units.ext
    change InfoGeometry.Clifford.Cl11Matrix.Eminus *
        InfoGeometry.Clifford.Cl11Matrix.Eplus =
      (-InfoGeometry.Clifford.Cl11Matrix.J1 : Mat2)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Clifford.Cl11Matrix.Eminus,
        InfoGeometry.Clifford.Cl11Matrix.Eplus,
        InfoGeometry.Clifford.Cl11Matrix.J1, Matrix.mul_apply, Matrix.vecMul,
        Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  rw [← adjointAlgHom.map_mul, hunit, adjointAlgHom_neg_unit]

theorem adjointAlgHom_causal_bivector :
    adjointAlgHom causalUnit * adjointAlgHom bivectorUnit =
      adjointAlgHom gammaUnit := by
  rw [← adjointAlgHom.map_mul, causalUnit_eq_gamma_mul_bivector]
  simp only [map_mul]
  rw [mul_assoc, adjointAlgHom_bivector_sq]
  have hrefl : (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) = 1 := by
    apply AlgEquiv.ext
    intro A
    rfl
  simp [hrefl]

theorem adjointAlgHom_bivector_causal :
    adjointAlgHom bivectorUnit * adjointAlgHom causalUnit =
      adjointAlgHom gammaUnit := by
  rw [← adjointAlgHom_gamma_bivector]
  rw [← mul_assoc, adjointAlgHom_bivector_gamma]
  exact adjointAlgHom_causal_bivector

end InfoGeometry.Canonical.Cl11AdjointCausalGeneratorLemmas
