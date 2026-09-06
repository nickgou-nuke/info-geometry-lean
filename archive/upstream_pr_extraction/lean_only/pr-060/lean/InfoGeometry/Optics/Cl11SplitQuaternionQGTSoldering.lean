import InfoGeometry.Clifford.Cl11CoordinateAlgebra
import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge
import InfoGeometry.Optics.OperatorQGTBogoliubovPauliSoldering

/-!
# `Cl(1,1)` / split-quaternion / operator-QGT soldering

This file identifies the finite coordinate `Cl(1,1)` owner with the existing
real split-quaternion matrix packet and then transports that identification to
the operator-valued QGT soldering action.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorQGTBogoliubovPauliSoldering
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Unified

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/--
The causal Pauli vector of a `Cl(1,1)` coordinate packet.  The bivector sign
records `e₁e₂ ↦ sqJ * sqI = -sqK`.
-/
def cl11PauliVector (q : Cl11) : Vec22 :=
  (q.s, -q.e12, q.e1, q.e2)

/-- The corresponding real split-quaternion matrix representation. -/
def cl11SplitQuaternionMatrix (q : Cl11) : Matrix (Fin 2) (Fin 2) ℝ :=
  splitQ q.s q.e2 q.e1 (-q.e12)

@[simp] theorem cl11SplitQuaternionMatrix_eq_soldering
    (q : Cl11) :
    cl11SplitQuaternionMatrix q = soldering (cl11PauliVector q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11SplitQuaternionMatrix, cl11PauliVector, splitQ_eq_matrix,
      soldering, sigma0, sigma1, sigma3, epsilon] <;> ring

/-- The coordinate representation respects the full `Cl(1,1)` product. -/
theorem cl11SplitQuaternionMatrix_mul (q r : Cl11) :
    cl11SplitQuaternionMatrix (q * r) =
      cl11SplitQuaternionMatrix q * cl11SplitQuaternionMatrix r := by
  change cl11SplitQuaternionMatrix
      (InfoGeometry.Clifford.Cl11CoordinateAlgebra.mul q r) =
    cl11SplitQuaternionMatrix q * cl11SplitQuaternionMatrix r
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11SplitQuaternionMatrix, splitQ_eq_matrix,
      InfoGeometry.Clifford.Cl11CoordinateAlgebra.mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The split-quaternion matrix representation is faithful. -/
theorem cl11SplitQuaternionMatrix_injective :
    Function.Injective cl11SplitQuaternionMatrix := by
  intro q r h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun h (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  simp [cl11SplitQuaternionMatrix, splitQ_eq_matrix] at h00 h01 h10 h11
  ext <;> dsimp <;> linarith

/-- Matrix adjugation on the split-quaternion packet. -/
def splitQuaternionMatrixConjugate
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 1 1, -A 0 1; -A 1 0, A 0 0]

/-- Clifford conjugation is exactly split-quaternion matrix conjugation. -/
theorem cl11SplitQuaternionMatrix_cliffordConjugate (q : Cl11) :
    cl11SplitQuaternionMatrix (cliffordConjugate q) =
      splitQuaternionMatrixConjugate (cl11SplitQuaternionMatrix q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11SplitQuaternionMatrix, splitQuaternionMatrixConjugate,
      splitQ_eq_matrix, cliffordConjugate_apply] <;> ring

/-- The causal quadratic form is the `Cl(1,1)` split norm. -/
@[simp] theorem q22_cl11PauliVector (q : Cl11) :
    q22 (cl11PauliVector q) = splitNorm q := by
  simp [cl11PauliVector, splitNorm]
  ring

/-- The matrix determinant is the same split norm. -/
theorem det2_cl11SplitQuaternionMatrix (q : Cl11) :
    det2 (cl11SplitQuaternionMatrix q) = splitNorm q := by
  rw [cl11SplitQuaternionMatrix_eq_soldering]
  simpa [Matrix.det_fin_two, det2] using det_soldering_eq_q22 (cl11PauliVector q)

/-! ## Native split-octonion fixed-colour realization -/

/-- A `Cl(1,1)` packet embedded in one associative colour plane of the native Zorn carrier. -/
def cl11FixedColorSplitOctonion (i : Fin 3) (q : Cl11) : Native :=
  fixedColorReadout i (cl11SplitQuaternionMatrix q)

/-- The fixed-colour split-octonion realization preserves multiplication. -/
theorem cl11FixedColorSplitOctonion_mul (i : Fin 3) (q r : Cl11) :
    cl11FixedColorSplitOctonion i (q * r) =
      cl11FixedColorSplitOctonion i q * cl11FixedColorSplitOctonion i r := by
  unfold cl11FixedColorSplitOctonion
  rw [cl11SplitQuaternionMatrix_mul, fixedColorReadout_mul]

/-- Every selected colour plane gives a faithful `Cl(1,1)` realization. -/
theorem cl11FixedColorSplitOctonion_injective (i : Fin 3) :
    Function.Injective (cl11FixedColorSplitOctonion i) :=
  (fixedColorReadout_injective i).comp cl11SplitQuaternionMatrix_injective

/-- The `Cl(1,1)` coordinate packet as an operator-valued QGT four-vector. -/
def cl11QGTFourVector (q : Cl11) : QGTFourVector W :=
  pauliQGTFourVector (W := W) (cl11PauliVector q)

/--
The QGT soldering action of a `Cl(1,1)` coordinate is exactly the scalar
extension of its split-quaternion matrix representation.
-/
theorem QGTSoldering_cl11QGTFourVector (q : Cl11) :
    QGTSoldering (cl11QGTFourVector (W := W) q) =
      matrixAction
        (complexifyMatrix (W := W) (cl11SplitQuaternionMatrix q)) := by
  rw [cl11QGTFourVector, QGTSoldering_pauliQGTFourVector,
    complexifiedPauliFrameAction, complexifiedPauliFrame,
    cl11SplitQuaternionMatrix_eq_soldering]

end InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering
