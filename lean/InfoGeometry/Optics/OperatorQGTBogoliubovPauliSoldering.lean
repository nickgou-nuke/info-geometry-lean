import InfoGeometry.Optics.OperatorQGTSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorBogoliubovPauliBridge

/-!
# Operator QGT / Bogoliubov--Pauli soldering identification

The real Pauli soldering owner and the operator-valued causal soldering owner
are the same construction after scalar extension.  The circular coordinate is
sent to `i y`; the factors `∓ i` in causal reconstruction then recover the
real split-quaternion off-diagonal signs `x ± y`.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTBogoliubovPauliSoldering

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Unified

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW := Module.End ℂ W

/-- Real scalar multiplication, regarded as an internal complex-linear operator. -/
def realScalarOperator (r : ℝ) : EndW (W := W) :=
  algebraMap ℝ (EndW (W := W)) r

/--
The `(t,z,x,y)` split-signature Pauli coordinates in causal operator order
`(scalar, exchange, circular, chiral) = (t,x,i y,z)`.
-/
def pauliCausalFourVector (v : Vec22) : OperatorFourVector W :=
  ![realScalarOperator (W := W) v.1,
    realScalarOperator (W := W) v.2.2.1,
    Complex.I • realScalarOperator (W := W) v.2.2.2,
    realScalarOperator (W := W) v.2.1]

@[simp] theorem pauliCausalFourVector_zero :
    pauliCausalFourVector (W := W) 0 = 0 := by
  funext i
  fin_cases i <;> simp [pauliCausalFourVector, realScalarOperator]

/--
Native matrix identification: real Pauli soldering followed by scalar
extension is exactly causal operator soldering.
-/
theorem operatorSoldering_pauliCausalFourVector
    (v : Vec22) :
    operatorSoldering (pauliCausalFourVector (W := W) v) =
      complexifiedPauliFrame (W := W) v := by
  rcases v with ⟨t, z, x, y⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCausalFourVector, realScalarOperator,
      complexifiedPauliFrame, complexifyMatrix,
      InfoGeometry.Physics.BogoliubovPauliSolderedFrame.pauliTetradSoldering,
      soldering, sigma0, sigma1, sigma3, epsilon,
      operatorSoldering_apply, smul_smul, sub_eq_add_neg]

/-- The corresponding endomorphisms of the doubled internal carrier agree. -/
theorem operatorSolderingAction_pauliCausalFourVector
    (v : Vec22) :
    operatorSolderingAction (pauliCausalFourVector (W := W) v) =
      complexifiedPauliFrameAction (W := W) v := by
  rw [operatorSolderingAction, complexifiedPauliFrameAction,
    operatorSoldering_pauliCausalFourVector]

/-- The real Pauli frame as a purely symmetric operator-valued QGT channel. -/
def pauliQGTFourVector (v : Vec22) : QGTFourVector W where
  symmetricBKM := pauliCausalFourVector (W := W) v
  antisymmetricBerry := 0

@[simp] theorem pauliQGTFourVector_totalOperator
    (v : Vec22) :
    (pauliQGTFourVector (W := W) v).totalOperator =
      pauliCausalFourVector (W := W) v := by
  funext i
  simp [pauliQGTFourVector, QGTFourVector.totalOperator]

/--
The QGT soldering of the symmetric real Pauli channel is exactly the
scalar-extended Bogoliubov--Pauli frame acting on the doubled carrier.
-/
theorem QGTSoldering_pauliQGTFourVector
    (v : Vec22) :
    QGTSoldering (pauliQGTFourVector (W := W) v) =
      complexifiedPauliFrameAction (W := W) v := by
  rw [QGTSoldering, pauliQGTFourVector_totalOperator,
    operatorSolderingAction_pauliCausalFourVector]

end InfoGeometry.Optics.OperatorQGTBogoliubovPauliSoldering
