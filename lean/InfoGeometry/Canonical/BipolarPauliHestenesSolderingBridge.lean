import InfoGeometry.Canonical.BipolarCartanLorentzBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import Mathlib.Tactic

/-!
# Bipolar Cartan action on the native Pauli--Hestenes carrier

The repository already owns two representations of the same finite algebraic
operation:

* `BipolarCartanLorentzBridge.CartanCoordinates` records the four diagonal
  Cartan weights abstractly;
* `PauliHestenesSpinMomentum.PauliParavector.pauliMatrix` is the canonical
  Hermitian `2 × 2` representative of a real Minkowski paravector.

This file proves that conjugation by the bipolar half-log lift acts on the four
matrix entries with exactly those abstract weights. Thus the phrases
"light-cone dilation" and "circular transverse phase" become a theorem about
one concrete matrix action rather than two parallel descriptions.

The two Cartan coefficients are independent over `ℝ` but dependent over `ℂ`:
`Kcirc = i Kboost`. The corresponding statement is proved directly on the
matrix carrier. No Clifford-algebra isomorphism, global spin-group
classification, gauge dynamics, or physical momentum interpretation is added.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Physics.ChiralCausalCone
open scoped Matrix

abbrev Matrix2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
/-- The native Pauli/Hestenes paravector as the repository-owned Hermitian
soldering carrier. -/
def pauliHermitian (P : PauliParavector) : HermitianMat2 :=
  minkowskiSoldering P.energy P.px P.py P.pz

/-- The two native Pauli matrix owners agree entrywise. -/
theorem pauliHermitian_mat (P : PauliParavector) :
    (pauliHermitian P).mat = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliHermitian, minkowskiSoldering,
      PauliParavector.pauliMatrix] <;> ring

/-- Turn the abstract four-weight carrier into its `2 × 2` matrix. -/
def matrixOfCartanCoordinates (X : CartanCoordinates) : Matrix2C :=
  !![X.plus, X.transversePlus;
     X.transverseMinus, X.minus]

/-- Light-cone/circular coordinates of a real Pauli paravector. -/
def pauliCartanCoordinates (P : PauliParavector) : CartanCoordinates where
  plus := ((P.energy + P.pz : ℝ) : ℂ)
  minus := ((P.energy - P.pz : ℝ) : ℂ)
  transversePlus := (P.px : ℂ) - Complex.I * (P.py : ℂ)
  transverseMinus := (P.px : ℂ) + Complex.I * (P.py : ℂ)

private lemma star_div_two (z : ℂ) :
    (starRingEnd ℂ) (z / 2) = (starRingEnd ℂ z) / 2 := by
  rw [map_div₀]
  simp only [starRingEnd_apply, star_ofNat]

/-- The four Cartan coordinates reconstruct the canonical Pauli matrix. -/
theorem matrixOf_pauliCartanCoordinates (P : PauliParavector) :
    matrixOfCartanCoordinates (pauliCartanCoordinates P) = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfCartanCoordinates, pauliCartanCoordinates,
      PauliParavector.pauliMatrix]

/-- Positive half-weight times its conjugate is the noncompact weight `e^η`. -/
theorem plusWeight_mul_conj_plusWeight (s : ℂ) :
    plusWeight s * (starRingEnd ℂ) (plusWeight s) =
      Complex.exp (eta s : ℂ) := by
  have harg :
      bipolarLog s / 2 + (starRingEnd ℂ) (bipolarLog s / 2) =
        (eta s : ℂ) := by
    rw [bipolarLog_split]
    rw [star_div_two]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [plusWeight, ← Complex.exp_conj, ← Complex.exp_add, harg]

/-- Negative half-weight times its conjugate is the reciprocal noncompact
weight `e⁻η`. -/
theorem minusWeight_mul_conj_minusWeight (s : ℂ) :
    minusWeight s * (starRingEnd ℂ) (minusWeight s) =
      Complex.exp (-(eta s : ℂ)) := by
  have harg :
      -bipolarLog s / 2 + (starRingEnd ℂ) (-bipolarLog s / 2) =
        -(eta s : ℂ) := by
    rw [bipolarLog_split]
    rw [star_div_two]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [minusWeight, ← Complex.exp_conj, ← Complex.exp_add, harg]

/-- Mixed half-weights give the positive compact character `e^{iθ}`. -/
theorem plusWeight_mul_conj_minusWeight (s : ℂ) :
    plusWeight s * (starRingEnd ℂ) (minusWeight s) =
      Complex.exp (Complex.I * (theta s : ℂ)) := by
  have harg :
      bipolarLog s / 2 + (starRingEnd ℂ) (-bipolarLog s / 2) =
        Complex.I * (theta s : ℂ) := by
    rw [bipolarLog_split]
    rw [star_div_two]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [plusWeight, minusWeight, ← Complex.exp_conj,
    ← Complex.exp_add, harg]

/-- Reversed mixed half-weights give the negative compact character
`e^{-iθ}`. -/
theorem minusWeight_mul_conj_plusWeight (s : ℂ) :
    minusWeight s * (starRingEnd ℂ) (plusWeight s) =
      Complex.exp (-Complex.I * (theta s : ℂ)) := by
  have harg :
      -bipolarLog s / 2 + (starRingEnd ℂ) (bipolarLog s / 2) =
        -Complex.I * (theta s : ℂ) := by
    rw [bipolarLog_split]
    rw [star_div_two]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [minusWeight, plusWeight, ← Complex.exp_conj,
    ← Complex.exp_add, harg]

/-- Diagonal positive weight acting on an arbitrary matrix entry. -/
theorem plusWeight_mul_entry_mul_conj_plusWeight
    (s z : ℂ) :
    plusWeight s * z * (starRingEnd ℂ) (plusWeight s) =
      Complex.exp (eta s : ℂ) * z := by
  calc
    plusWeight s * z * (starRingEnd ℂ) (plusWeight s) =
        (plusWeight s * (starRingEnd ℂ) (plusWeight s)) * z := by ring
    _ = Complex.exp (eta s : ℂ) * z := by
      rw [plusWeight_mul_conj_plusWeight]

/-- Diagonal negative weight acting on an arbitrary matrix entry. -/
theorem minusWeight_mul_entry_mul_conj_minusWeight
    (s z : ℂ) :
    minusWeight s * z * (starRingEnd ℂ) (minusWeight s) =
      Complex.exp (-(eta s : ℂ)) * z := by
  calc
    minusWeight s * z * (starRingEnd ℂ) (minusWeight s) =
        (minusWeight s * (starRingEnd ℂ) (minusWeight s)) * z := by ring
    _ = Complex.exp (-(eta s : ℂ)) * z := by
      rw [minusWeight_mul_conj_minusWeight]

/-- Positive circular weight acting on an off-diagonal matrix entry. -/
theorem plusWeight_mul_entry_mul_conj_minusWeight
    (s z : ℂ) :
    plusWeight s * z * (starRingEnd ℂ) (minusWeight s) =
      Complex.exp (Complex.I * (theta s : ℂ)) * z := by
  calc
    plusWeight s * z * (starRingEnd ℂ) (minusWeight s) =
        (plusWeight s * (starRingEnd ℂ) (minusWeight s)) * z := by ring
    _ = Complex.exp (Complex.I * (theta s : ℂ)) * z := by
      rw [plusWeight_mul_conj_minusWeight]

/-- Negative circular weight acting on the opposite off-diagonal entry. -/
theorem minusWeight_mul_entry_mul_conj_plusWeight
    (s z : ℂ) :
    minusWeight s * z * (starRingEnd ℂ) (plusWeight s) =
      Complex.exp (-Complex.I * (theta s : ℂ)) * z := by
  calc
    minusWeight s * z * (starRingEnd ℂ) (plusWeight s) =
        (minusWeight s * (starRingEnd ℂ) (plusWeight s)) * z := by ring
    _ = Complex.exp (-Complex.I * (theta s : ℂ)) * z := by
      rw [minusWeight_mul_conj_plusWeight]

/-- Conjugation by the half-log lift realizes the abstract four-coordinate
Cartan action exactly. -/
theorem halfLogLift_conjugation_matrixOfCartanCoordinates
    (s : ℂ) (X : CartanCoordinates) :
    halfLogLift s * matrixOfCartanCoordinates X * Matrix.conjTranspose (halfLogLift s) =
      matrixOfCartanCoordinates (bipolarCoordinateAction s X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, matrixOfCartanCoordinates,
      bipolarCoordinateAction, cartanCoordinateAction,
      Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose, Matrix.transpose_apply,
      plusWeight_mul_entry_mul_conj_plusWeight,
      minusWeight_mul_entry_mul_conj_minusWeight,
      plusWeight_mul_entry_mul_conj_minusWeight,
      minusWeight_mul_entry_mul_conj_plusWeight]

/-- Native Pauli/Hestenes specialization of the exact Cartan weight action. -/
theorem bipolarSolderingAction_pauliMatrix
    (s : ℂ) (P : PauliParavector) :
    (bipolarSolderingAction s (pauliHermitian P)).mat =
      matrixOfCartanCoordinates
        (bipolarCoordinateAction s (pauliCartanCoordinates P)) := by
  change
    halfLogLift s * (pauliHermitian P).mat * Matrix.conjTranspose (halfLogLift s) = _
  rw [pauliHermitian_mat, ← matrixOf_pauliCartanCoordinates]
  exact halfLogLift_conjugation_matrixOfCartanCoordinates
    s (pauliCartanCoordinates P)

/-- The determinant of the transformed Pauli matrix is the original Minkowski
quadratic form. -/
theorem bipolarSolderingAction_pauli_det
    (s : ℂ) (P : PauliParavector) :
    Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
      (P.minkowskiNormSq : ℂ) := by
  rw [bipolarSolderingAction_det, pauliHermitian_mat,
    PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]

/-- The two named Cartan directions are linearly independent over `ℝ`, expressed
without imposing an additional bundled realification on the matrix algebra. -/
theorem Kboost_Kcirc_real_relation
    (a b : ℝ)
    (h : (a : ℂ) • Kboost + (b : ℂ) • Kcirc = 0) :
    a = 0 ∧ b = 0 := by
  have h00 := congrArg (fun M : Matrix2C => M 0 0) h
  have hscalar :
      (a : ℂ) * (1 / 2 : ℂ) +
        (b : ℂ) * (Complex.I / 2) = 0 := by
    simpa [Kboost, Kcirc, σ3c, Matrix.add_apply,
      Matrix.smul_apply] using h00
  have hre := congrArg Complex.re hscalar
  have him := congrArg Complex.im hscalar
  norm_num at hre him
  exact ⟨by linarith, by linarith⟩

/-- Correct scalar-field packet: real independence together with complex
rank-one dependence. -/
theorem cartan_real_complex_rank_packet :
    Kcirc = Complex.I • Kboost ∧
      ∀ a b : ℝ,
        (a : ℂ) • Kboost + (b : ℂ) • Kcirc = 0 →
          a = 0 ∧ b = 0 := by
  exact ⟨Kcirc_eq_I_smul_Kboost,
    fun a b h => Kboost_Kcirc_real_relation a b h⟩

/-- Compact Pauli/Hestenes soldering packet. -/
theorem bipolar_pauli_hestenes_soldering_packet
    (s : ℂ) (P : PauliParavector) :
    (pauliHermitian P).mat = P.pauliMatrix ∧
      (bipolarSolderingAction s (pauliHermitian P)).mat =
        matrixOfCartanCoordinates
          (bipolarCoordinateAction s (pauliCartanCoordinates P)) ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        (P.minkowskiNormSq : ℂ) := by
  exact ⟨pauliHermitian_mat P,
    bipolarSolderingAction_pauliMatrix s P,
    bipolarSolderingAction_pauli_det s P⟩

end InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
