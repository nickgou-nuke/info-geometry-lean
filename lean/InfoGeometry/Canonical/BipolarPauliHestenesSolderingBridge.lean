import InfoGeometry.Canonical.BipolarCartanLorentzBridge
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
matrix entries with exactly those abstract weights.  Thus the phrases
"light-cone dilation" and "circular transverse phase" become a theorem about
one concrete matrix action rather than two parallel descriptions.

The two Cartan coefficients are independent over `ℝ` but dependent over `ℂ`:
`Kcirc = i Kboost`.  The corresponding statement is proved directly on the
matrix carrier.  No Clifford-algebra isomorphism, global spin-group
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

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev PauliVector := PauliParavector

/-- The native Pauli/Hestenes paravector as the repository-owned Hermitian
soldering carrier. -/
def pauliHermitian (P : PauliVector) : HermitianMat2 :=
  minkowskiSoldering P.energy P.px P.py P.pz

/-- The two native Pauli matrix owners agree entrywise. -/
theorem pauliHermitian_mat (P : PauliVector) :
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
def pauliCartanCoordinates (P : PauliVector) : CartanCoordinates where
  plus := ((P.energy + P.pz : ℝ) : ℂ)
  minus := ((P.energy - P.pz : ℝ) : ℂ)
  transversePlus := (P.px : ℂ) - Complex.I * (P.py : ℂ)
  transverseMinus := (P.px : ℂ) + Complex.I * (P.py : ℂ)

/-- The four Cartan coordinates reconstruct the canonical Pauli matrix. -/
theorem matrixOf_pauliCartanCoordinates (P : PauliVector) :
    matrixOfCartanCoordinates (pauliCartanCoordinates P) = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfCartanCoordinates, pauliCartanCoordinates,
      PauliParavector.pauliMatrix]

/-- Positive half-weight times its conjugate is the noncompact weight `e^η`. -/
theorem plusWeight_mul_conj_plusWeight (s : ℂ) :
    plusWeight s * Complex.conj (plusWeight s) =
      Complex.exp (eta s : ℂ) := by
  have harg :
      bipolarLog s / 2 + Complex.conj (bipolarLog s / 2) =
        (eta s : ℂ) := by
    rw [bipolarLog_split]
    apply Complex.ext <;> simp <;> ring
  rw [plusWeight, ← Complex.exp_conj, ← Complex.exp_add, harg]

/-- Negative half-weight times its conjugate is the reciprocal noncompact
weight `e⁻η`. -/
theorem minusWeight_mul_conj_minusWeight (s : ℂ) :
    minusWeight s * Complex.conj (minusWeight s) =
      Complex.exp (-(eta s : ℂ)) := by
  have harg :
      -bipolarLog s / 2 + Complex.conj (-bipolarLog s / 2) =
        -(eta s : ℂ) := by
    rw [bipolarLog_split]
    apply Complex.ext <;> simp <;> ring
  rw [minusWeight, ← Complex.exp_conj, ← Complex.exp_add, harg]

/-- Mixed half-weights give the positive compact character `e^{iθ}`. -/
theorem plusWeight_mul_conj_minusWeight (s : ℂ) :
    plusWeight s * Complex.conj (minusWeight s) =
      Complex.exp (Complex.I * (theta s : ℂ)) := by
  have harg :
      bipolarLog s / 2 + Complex.conj (-bipolarLog s / 2) =
        Complex.I * (theta s : ℂ) := by
    rw [bipolarLog_split]
    apply Complex.ext <;> simp <;> ring
  rw [plusWeight, minusWeight, ← Complex.exp_conj,
    ← Complex.exp_add, harg]

/-- Reversed mixed half-weights give the negative compact character
`e^{-iθ}`. -/
theorem minusWeight_mul_conj_plusWeight (s : ℂ) :
    minusWeight s * Complex.conj (plusWeight s) =
      Complex.exp (-Complex.I * (theta s : ℂ)) := by
  have harg :
      -bipolarLog s / 2 + Complex.conj (bipolarLog s / 2) =
        -Complex.I * (theta s : ℂ) := by
    rw [bipolarLog_split]
    apply Complex.ext <;> simp <;> ring
  rw [minusWeight, plusWeight, ← Complex.exp_conj,
    ← Complex.exp_add, harg]

/-- Conjugation by the half-log lift realizes the abstract four-coordinate
Cartan action exactly. -/
theorem halfLogLift_conjugation_matrixOfCartanCoordinates
    (s : ℂ) (X : CartanCoordinates) :
    halfLogLift s * matrixOfCartanCoordinates X * (halfLogLift s)ᴴ =
      matrixOfCartanCoordinates (bipolarCoordinateAction s X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, matrixOfCartanCoordinates,
      bipolarCoordinateAction, cartanCoordinateAction,
      Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose, Matrix.transpose_apply,
      plusWeight_mul_conj_plusWeight,
      minusWeight_mul_conj_minusWeight,
      plusWeight_mul_conj_minusWeight,
      minusWeight_mul_conj_plusWeight] <;> ring

/-- Native Pauli/Hestenes specialization of the exact Cartan weight action. -/
theorem bipolarSolderingAction_pauliMatrix
    (s : ℂ) (P : PauliVector) :
    (bipolarSolderingAction s (pauliHermitian P)).mat =
      matrixOfCartanCoordinates
        (bipolarCoordinateAction s (pauliCartanCoordinates P)) := by
  change
    halfLogLift s * (pauliHermitian P).mat * (halfLogLift s)ᴴ = _
  rw [pauliHermitian_mat, ← matrixOf_pauliCartanCoordinates]
  exact halfLogLift_conjugation_matrixOfCartanCoordinates
    s (pauliCartanCoordinates P)

/-- The determinant of the transformed Pauli matrix is the original Minkowski
quadratic form. -/
theorem bipolarSolderingAction_pauli_det
    (s : ℂ) (P : PauliVector) :
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
    (s : ℂ) (P : PauliVector) :
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
