import Mathlib.Tactic
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
import InfoGeometry.Physics.PauliLubanskiFiniteBridge
import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Finite spin-half Pauli--Lubanski operator

This file specializes the repository's already-owned finite Pauli--Lubanski
3+1 decomposition to the two Weyl spin-half representations.

The construction is entirely finite:

* rotations are `sigma_i / 2`;
* left/right boosts are `-i sigma_i / 2` and `+i sigma_i / 2`;
* momentum is the existing real `PauliParavector`;
* both chiral sectors satisfy `W^2 = -(3/4) Q(P) I_2`;
* the resulting scalar matrix is transported through the existing
  associative `OperatorZornMatrix.ofMatrix`.

The massless proportionality `W^mu = helicity * P^mu` is stated only on
explicit helicity eigenspinors.  It is not an equality of the full matrices.
No unbounded position or momentum operator is introduced.
-/

noncomputable section

namespace InfoGeometry.Bridge.OperatorPauliLubanskiLift

open Matrix
open scoped Matrix
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

abbrev PauliBlock := QuaternionicPauliDiracSoldering.PauliBlock
abbrev WeylSpinor := QuaternionicPauliDiracSoldering.WeylSpinor

/-- Spatial Pauli contraction `p dot sigma`. -/
def momentumDotSigma (P : PauliParavector) : PauliBlock :=
  (P.px : ℂ) • sigma1 + (P.py : ℂ) • sigma2 + (P.pz : ℂ) • sigma3

/-- Spatial cross product `p cross sigma`, in the order fixed by the
repository's finite Pauli--Lubanski owner. -/
def momentumCrossSigma (P : PauliParavector) : Fin 3 → PauliBlock
  | 0 => (P.py : ℂ) • sigma3 - (P.pz : ℂ) • sigma2
  | 1 => (P.pz : ℂ) • sigma1 - (P.px : ℂ) • sigma3
  | 2 => (P.px : ℂ) • sigma2 - (P.py : ℂ) • sigma1

/-- Left-handed spin-half Pauli--Lubanski matrices:
`W^0 = (p dot sigma)/2` and
`W^j = (E sigma_j - i (p cross sigma)_j)/2`. -/
def pauliLubanskiLeft (P : PauliParavector) : Fin 4 → PauliBlock
  | 0 => (1 / 2 : ℂ) • momentumDotSigma P
  | 1 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma1 - Complex.I • momentumCrossSigma P 0)
  | 2 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma2 - Complex.I • momentumCrossSigma P 1)
  | 3 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma3 - Complex.I • momentumCrossSigma P 2)

/-- Right-handed spin-half Pauli--Lubanski matrices, with the opposite boost
sign. -/
def pauliLubanskiRight (P : PauliParavector) : Fin 4 → PauliBlock
  | 0 => (1 / 2 : ℂ) • momentumDotSigma P
  | 1 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma1 + Complex.I • momentumCrossSigma P 0)
  | 2 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma2 + Complex.I • momentumCrossSigma P 1)
  | 3 => (1 / 2 : ℂ) •
      ((P.energy : ℂ) • sigma3 + Complex.I • momentumCrossSigma P 2)

/-- Minkowski contraction of momentum with a matrix-valued four-vector. -/
def momentumContraction
    (P : PauliParavector) (W : Fin 4 → PauliBlock) : PauliBlock :=
  (P.energy : ℂ) • W 0 -
    (P.px : ℂ) • W 1 -
    (P.py : ℂ) • W 2 -
    (P.pz : ℂ) • W 3

/-- Minkowski square of a matrix-valued four-vector. -/
def minkowskiMatrixSq (W : Fin 4 → PauliBlock) : PauliBlock :=
  W 0 * W 0 - W 1 * W 1 - W 2 * W 2 - W 3 * W 3

/-- Correct Pauli cross-product rearrangement for the conventions in this
file:
`-i (p cross sigma)_j = (p dot sigma) sigma_j - p_j I`. -/
theorem minus_i_cross_eq_dot_mul_sigma_sub
    (P : PauliParavector) (j : Fin 3) :
    (-Complex.I) • momentumCrossSigma P j =
      momentumDotSigma P *
          (match j with | 0 => sigma1 | 1 => sigma2 | 2 => sigma3) -
        ((match j with | 0 => P.px | 1 => P.py | 2 => P.pz : ℝ) : ℂ) •
          (1 : PauliBlock) := by
  fin_cases j
  all_goals
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [momentumCrossSigma, momentumDotSigma, sigma1, sigma2, sigma3,
        sigma1C, sigma2C, sigma3C, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- The left-handed Pauli--Lubanski vector is momentum-transverse. -/
theorem pauliLubanskiLeft_momentum_orthogonal (P : PauliParavector) :
    momentumContraction P (pauliLubanskiLeft P) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumContraction, pauliLubanskiLeft, momentumCrossSigma,
      momentumDotSigma, sigma1, sigma2, sigma3,
      sigma1C, sigma2C, sigma3C] <;>
    ring

/-- The right-handed Pauli--Lubanski vector is momentum-transverse. -/
theorem pauliLubanskiRight_momentum_orthogonal (P : PauliParavector) :
    momentumContraction P (pauliLubanskiRight P) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumContraction, pauliLubanskiRight, momentumCrossSigma,
      momentumDotSigma, sigma1, sigma2, sigma3,
      sigma1C, sigma2C, sigma3C] <;>
    ring

/-- Spin-half Casimir matrix `S^2 = 3/4 I_2`. -/
def spinHalfCasimir : PauliBlock :=
  (3 / 4 : ℂ) • (1 : PauliBlock)

theorem spinHalfCasimir_eq_three_quarters :
    spinHalfCasimir = (3 / 4 : ℂ) • (1 : PauliBlock) :=
  rfl

/-- Left-handed quadratic Pauli--Lubanski Casimir. -/
theorem pauliLubanskiLeft_sq_eq_mass_spin_casimir
    (P : PauliParavector) :
    minkowskiMatrixSq (pauliLubanskiLeft P) =
      -(P.minkowskiNormSq : ℂ) • spinHalfCasimir := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMatrixSq, pauliLubanskiLeft, momentumCrossSigma,
      momentumDotSigma, spinHalfCasimir, PauliParavector.minkowskiNormSq,
      sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- Right-handed quadratic Pauli--Lubanski Casimir. -/
theorem pauliLubanskiRight_sq_eq_mass_spin_casimir
    (P : PauliParavector) :
    minkowskiMatrixSq (pauliLubanskiRight P) =
      -(P.minkowskiNormSq : ℂ) • spinHalfCasimir := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMatrixSq, pauliLubanskiRight, momentumCrossSigma,
      momentumDotSigma, spinHalfCasimir, PauliParavector.minkowskiNormSq,
      sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- Numerical form `W^2 = -(3/4) Q(P) I_2`. -/
theorem pauliLubanskiLeft_sq_eq_three_quarters
    (P : PauliParavector) :
    minkowskiMatrixSq (pauliLubanskiLeft P) =
      ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) •
        (1 : PauliBlock) := by
  rw [pauliLubanskiLeft_sq_eq_mass_spin_casimir]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfCasimir, Matrix.one_apply] <;>
    ring

/-- A null momentum has null Pauli--Lubanski norm in the finite spin-half
symbol representation. -/
theorem pauliLubanski_null_norm
    (P : PauliParavector) (hP : P.minkowskiNormSq = 0) :
    minkowskiMatrixSq (pauliLubanskiLeft P) = 0 ∧
    minkowskiMatrixSq (pauliLubanskiRight P) = 0 := by
  constructor
  · rw [pauliLubanskiLeft_sq_eq_mass_spin_casimir, hP]
    simp
  · rw [pauliLubanskiRight_sq_eq_mass_spin_casimir, hP]
    simp

/-- Standard future null momentum along the positive third axis. -/
def northNullMomentum (E : ℝ) : PauliParavector where
  energy := E
  px := 0
  py := 0
  pz := E

theorem northNullMomentum_isNull (E : ℝ) :
    (northNullMomentum E).minkowskiNormSq = 0 := by
  simp [northNullMomentum, PauliParavector.minkowskiNormSq]

def momentumComponent (P : PauliParavector) : Fin 4 → ℂ
  | 0 => P.energy
  | 1 => P.px
  | 2 => P.py
  | 3 => P.pz

def positiveHelicitySpinor : WeylSpinor := ![1, 0]
def negativeHelicitySpinor : WeylSpinor := ![0, 1]

/-- On the positive-helicity eigenspinor of a standard null momentum,
the left-handed matrices obey `W^mu psi = +(1/2) P^mu psi`. -/
theorem left_null_positive_helicity
    (E : ℝ) (μ : Fin 4) :
    pauliLubanskiLeft (northNullMomentum E) μ *ᵥ positiveHelicitySpinor =
      ((1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) •
        positiveHelicitySpinor := by
  fin_cases μ
  all_goals
    ext i
    fin_cases i <;>
      simp [pauliLubanskiLeft, northNullMomentum, momentumComponent,
        positiveHelicitySpinor, momentumCrossSigma, momentumDotSigma,
        sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring

/-- On the negative-helicity eigenspinor of a standard null momentum,
the right-handed matrices obey `W^mu psi = -(1/2) P^mu psi`. -/
theorem right_null_negative_helicity
    (E : ℝ) (μ : Fin 4) :
    pauliLubanskiRight (northNullMomentum E) μ *ᵥ negativeHelicitySpinor =
      (-(1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) •
        negativeHelicitySpinor := by
  fin_cases μ
  all_goals
    ext i
    fin_cases i <;>
      simp [pauliLubanskiRight, northNullMomentum, momentumComponent,
        negativeHelicitySpinor, momentumCrossSigma, momentumDotSigma,
        sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring

/-- Existing associative operator-Zorn transport of the left Casimir matrix. -/
def zornPauliLubanskiSq (P : PauliParavector) :
    InfoGeometry.Physics.OperatorZornMatrix ℂ :=
  InfoGeometry.Physics.OperatorZornMatrix.ofMatrix
    (minkowskiMatrixSq (pauliLubanskiLeft P))

/-- The transported operator-Zorn readout is scalar-diagonal. -/
theorem toMatrix_zornPauliLubanskiSq
    (P : PauliParavector) :
    InfoGeometry.Physics.OperatorZornMatrix.toMatrix
        (zornPauliLubanskiSq P) =
      ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) •
        (1 : PauliBlock) := by
  simp [zornPauliLubanskiSq,
    pauliLubanskiLeft_sq_eq_three_quarters]

/-- Both Zorn diagonal rails carry the same Poincare spin Casimir and both
off-diagonal rails vanish. -/
theorem zornPauliLubanski_coordinate_packet
    (P : PauliParavector) :
    (zornPauliLubanskiSq P).n_plus_op =
        ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) ∧
    (zornPauliLubanskiSq P).n_minus_op =
        ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) ∧
    (zornPauliLubanskiSq P).sigma_plus_op = 0 ∧
    (zornPauliLubanskiSq P).sigma_minus_op = 0 := by
  have h := toMatrix_zornPauliLubanskiSq P
  constructor
  · simpa [InfoGeometry.Physics.OperatorZornMatrix.toMatrix] using
      congrFun (congrFun h 0) 0
  constructor
  · simpa [InfoGeometry.Physics.OperatorZornMatrix.toMatrix] using
      congrFun (congrFun h 1) 1
  constructor
  · simpa [InfoGeometry.Physics.OperatorZornMatrix.toMatrix] using
      congrFun (congrFun h 0) 1
  · simpa [InfoGeometry.Physics.OperatorZornMatrix.toMatrix] using
      congrFun (congrFun h 1) 0

end InfoGeometry.Bridge.OperatorPauliLubanskiLift
