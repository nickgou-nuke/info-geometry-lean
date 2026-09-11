import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbert

def finiteCombinedDirac {n : Type*} [Fintype n]
    (h b : Matrix n n ℝ) : Matrix n n ℝ := h + b

theorem finiteCombinedDirac_square_of_anticommute
    {n : Type*} [Fintype n]
    (h b : Matrix n n ℝ)
    (hanti : h * b = -(b * h)) :
    finiteCombinedDirac h b * finiteCombinedDirac h b = h * h + b * b := by
  unfold finiteCombinedDirac
  rw [add_mul, mul_add, hanti]
  noncomm_ring

theorem finiteCombinedDirac_square_zero_of_nilpotent
    {n : Type*} [Fintype n]
    (h b : Matrix n n ℝ)
    (hanti : h * b = -(b * h))
    (hh : h * h = 0)
    (hb : b * b = 0) :
    finiteCombinedDirac h b * finiteCombinedDirac h b = 0 := by
  rw [finiteCombinedDirac_square_of_anticommute h b hanti, hh, hb, add_zero]

/-! ## 2. Real Majorana--Berry--Keating operator problem -/

/--
Finite-cutoff real Majorana--Berry--Keating operator problem.

This names the combined operator

`D_Λ = H_BK ⊗ 1 + ρ ⊗ Q_Λ`

without pretending to construct its analytic closure.  The square law is
separate property data; it depends on the anticommutation of `ρ` with the real
Berry--Keating block and on the Dirac-square law for `Q_Λ`.
-/
structure RealMajoranaBerryKeatingProblem
    (Carrier Operator Mode Cutoff : Type) where
  carrier : Carrier
  cutoff : Cutoff
  realBerryKeatingBlock : Operator
  chiralityRho : Operator
  majoranaDiracCutoff : Operator
  combinedDirac : Operator
  modeEnergyCoefficient : Mode → ℝ

namespace RealMajoranaBerryKeatingProblem

end RealMajoranaBerryKeatingProblem

end InfoGeometry.Arithmetic.MajoranaPolyaHilbert
