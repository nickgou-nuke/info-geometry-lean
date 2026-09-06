import Mathlib
import InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

noncomputable section

namespace InfoGeometry.Clifford

open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
open InfoGeometry.Clifford.STAOperators
open InfoGeometry.Clifford.CrawfordDiracBispinorDensities

theorem concrete_loxodromic_projector_plus_mul_minus :
    ((1 / 2 : ℂ) •
        ((1 : ChiralGrandCanonicalLoxodromicRotor.Operator) -
          Complex.I • (boostAxis * phaseAxis))) *
      ((1 / 2 : ℂ) •
        ((1 : ChiralGrandCanonicalLoxodromicRotor.Operator) +
          Complex.I • (boostAxis * phaseAxis))) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostAxis, phaseAxis, staSigma3, staPhaseBivector, gamma0,
      gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

end InfoGeometry.Clifford
