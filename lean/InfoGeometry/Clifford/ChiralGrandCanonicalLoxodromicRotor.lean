import InfoGeometry.Clifford.STAOperators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete commuting boost--rotation rotors

This owner uses the existing real-valued STA matrix generators.  The boost axis
and the spatial phase bivector are concrete noncommutative `4 × 4` operators;
their commutation is proved from the displayed Dirac matrices, not assumed.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

open InfoGeometry.Clifford.STAOperators
open InfoGeometry.Clifford.CrawfordDiracBispinorDensities

abbrev Operator := DiracMatrix

def boostAxis : Operator := staSigma3

def phaseAxis : Operator := staPhaseBivector

theorem boostAxis_sq : boostAxis * boostAxis = 1 := by
  exact staSigma3_mul_self

theorem phaseAxis_sq : phaseAxis * phaseAxis = -1 := by
  exact staPhaseBivector_mul_self

theorem boostAxis_phaseAxis_commute :
    boostAxis * phaseAxis = phaseAxis * boostAxis := by
  unfold boostAxis phaseAxis staSigma3 staPhaseBivector
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

def boostRotor (η : ℝ) : Operator :=
  Real.cosh η • (1 : Operator) + Real.sinh η • boostAxis

def phaseRotor (θ : ℝ) : Operator :=
  Real.cos θ • (1 : Operator) + Real.sin θ • phaseAxis

theorem boostRotor_mul_neg (η : ℝ) :
    boostRotor η * boostRotor (-η) = 1 := by
  calc
    boostRotor η * boostRotor (-η) =
        (Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η) •
          (1 : Operator) := by
            unfold boostRotor
            simp [Real.cosh_neg, Real.sinh_neg, add_mul, mul_add, boostAxis_sq]
            module
    _ = 1 := by
      rw [show Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η = 1 by
        simpa [pow_two] using Real.cosh_sq_sub_sinh_sq η]
      simp

theorem boostRotor_neg_mul (η : ℝ) :
    boostRotor (-η) * boostRotor η = 1 := by
  simpa only [neg_neg] using boostRotor_mul_neg (-η)

theorem phaseRotor_mul_neg (θ : ℝ) :
    phaseRotor θ * phaseRotor (-θ) = 1 := by
  calc
    phaseRotor θ * phaseRotor (-θ) =
        (Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ) •
          (1 : Operator) := by
            unfold phaseRotor
            simp [Real.cos_neg, Real.sin_neg, add_mul, mul_add, phaseAxis_sq]
            module
    _ = 1 := by
      rw [show Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 by
        simpa [pow_two] using Real.cos_sq_add_sin_sq θ]
      simp

theorem phaseRotor_neg_mul (θ : ℝ) :
    phaseRotor (-θ) * phaseRotor θ = 1 := by
  simpa only [neg_neg] using phaseRotor_mul_neg (-θ)

theorem boostRotor_phaseRotor_commute (η θ : ℝ) :
    boostRotor η * phaseRotor θ = phaseRotor θ * boostRotor η := by
  unfold boostRotor phaseRotor
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add,
    one_mul, mul_one]
  rw [boostAxis_phaseAxis_commute]
  module

def loxodromicRotor (η θ : ℝ) : Operator :=
  boostRotor η * phaseRotor θ

theorem loxodromicRotor_mul_neg (η θ : ℝ) :
    loxodromicRotor η θ * loxodromicRotor (-η) (-θ) = 1 := by
  unfold loxodromicRotor
  calc
    (boostRotor η * phaseRotor θ) *
        (boostRotor (-η) * phaseRotor (-θ)) =
        boostRotor η * ((phaseRotor θ * boostRotor (-η)) * phaseRotor (-θ)) := by
          simp [Matrix.mul_assoc]
    _ = boostRotor η * ((boostRotor (-η) * phaseRotor θ) * phaseRotor (-θ)) := by
          rw [← boostRotor_phaseRotor_commute (-η) θ]
    _ = (boostRotor η * boostRotor (-η)) *
        (phaseRotor θ * phaseRotor (-θ)) := by
          simp [Matrix.mul_assoc]
    _ = 1 := by rw [boostRotor_mul_neg, phaseRotor_mul_neg]; simp

theorem loxodromicRotor_neg_mul (η θ : ℝ) :
    loxodromicRotor (-η) (-θ) * loxodromicRotor η θ = 1 := by
  unfold loxodromicRotor
  calc
    (boostRotor (-η) * phaseRotor (-θ)) *
        (boostRotor η * phaseRotor θ) =
        boostRotor (-η) * ((phaseRotor (-θ) * boostRotor η) * phaseRotor θ) := by
          simp [Matrix.mul_assoc]
    _ = boostRotor (-η) * ((boostRotor η * phaseRotor (-θ)) * phaseRotor θ) := by
          rw [← boostRotor_phaseRotor_commute η (-θ)]
    _ = (boostRotor (-η) * boostRotor η) *
        (phaseRotor (-θ) * phaseRotor θ) := by
          simp [Matrix.mul_assoc]
    _ = 1 := by rw [boostRotor_neg_mul, phaseRotor_neg_mul]; simp

/-! ## Inner operator geometry -/

/-- The Erlangen action of the concrete loxodromic rotor on STA operators. -/
def loxodromicConjugation (η θ : ℝ) (ψ : Operator) : Operator :=
  loxodromicRotor η θ * ψ * loxodromicRotor (-η) (-θ)

theorem loxodromicConjugation_one (η θ : ℝ) :
    loxodromicConjugation η θ 1 = 1 := by
  unfold loxodromicConjugation
  rw [mul_one, loxodromicRotor_mul_neg]

theorem loxodromicConjugation_mul (η θ : ℝ) (ψ χ : Operator) :
    loxodromicConjugation η θ (ψ * χ) =
      loxodromicConjugation η θ ψ * loxodromicConjugation η θ χ := by
  unfold loxodromicConjugation
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (loxodromicRotor (-η) (-θ))
    (loxodromicRotor η θ)]
  rw [loxodromicRotor_neg_mul]
  simp only [one_mul]

theorem loxodromicConjugation_inverse (η θ : ℝ) (ψ : Operator) :
    loxodromicConjugation (-η) (-θ) (loxodromicConjugation η θ ψ) = ψ := by
  unfold loxodromicConjugation
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (loxodromicRotor (-η) (-θ))
    (loxodromicRotor η θ)]
  rw [loxodromicRotor_neg_mul, loxodromicRotor_mul_neg]
  simp only [one_mul, mul_one]

end InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
