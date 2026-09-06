import proofs.HestenesLoxodromicRotor

/-!
# Loxodromic bivector Casimirs

The finite Pauli realization certifies the scalar and pseudoscalar parts of
`B(η,θ) = η K + θ (I K)`.  The grade-language interpretation is deferred to
a genuine real Clifford carrier.
-/

noncomputable section
namespace HestenesLoxodromicCasimirs

open TwoSheetThreeColorWeyl
open HestenesPhaseBoostRotors

abbrev Sheet := M2C

def loxodromicGenerator (η θ : ℂ) : Sheet := η • K + θ • IK

def scalarCasimir (η θ : ℂ) : ℂ := η ^ 2 - θ ^ 2
def pseudoscalarCasimir (η θ : ℂ) : ℂ := 2 * η * θ

theorem loxodromicGenerator_sq (η θ : ℂ) :
    loxodromicGenerator η θ * loxodromicGenerator η θ =
      scalarCasimir η θ • (1 : Sheet) +
        (Complex.I * pseudoscalarCasimir η θ) • (1 : Sheet) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [loxodromicGenerator, scalarCasimir, pseudoscalarCasimir,
      IK, K, sheetGamma, sheetPlus, sheetMinus, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    rw [hI] <;>
    ring

theorem loxodromicGenerator_sq_scalar_part (η θ : ℂ) :
    scalarCasimir η θ = η ^ 2 - θ ^ 2 := rfl

theorem loxodromicGenerator_sq_pseudoscalar_part (η θ : ℂ) :
    pseudoscalarCasimir η θ = 2 * η * θ := rfl

theorem pure_boost_casimir (η : ℂ) :
    scalarCasimir η 0 = η ^ 2 ∧ pseudoscalarCasimir η 0 = 0 := by
  simp [scalarCasimir, pseudoscalarCasimir]

theorem pure_rotation_casimir (θ : ℂ) :
    scalarCasimir 0 θ = -θ ^ 2 ∧ pseudoscalarCasimir 0 θ = 0 := by
  simp [scalarCasimir, pseudoscalarCasimir]

end HestenesLoxodromicCasimirs
end noncomputable section
