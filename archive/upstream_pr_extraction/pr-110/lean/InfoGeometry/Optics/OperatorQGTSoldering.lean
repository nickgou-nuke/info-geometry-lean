import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability

/-!
# QGT operator soldering

The symmetric BKM channel and antisymmetric Berry channel are packaged as a
single operator-valued four-vector and soldered through the existing causal
operator reconstruction.  This owner introduces no second curvature or
matrix-algebra definition.
-/

noncomputable section

namespace InfoGeometry.Unified

open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Quantum.GeometricQuantumTensor
open SouriauOnsagerBKM

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

structure QGTFourVector (W : Type*) [AddCommGroup W] [Module ℂ W] where
  symmetricBKM : OperatorFourVector W
  antisymmetricBerry : OperatorFourVector W

def QGTFourVector.totalOperator (Q : QGTFourVector W) : OperatorFourVector W :=
  fun i => Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i

def QGTSoldering (Q : QGTFourVector W) : Module.End ℂ (Fin 2 → W) :=
  operatorSolderingAction Q.totalOperator

@[simp] theorem QGTFourVector.totalOperator_apply
    (Q : QGTFourVector W) (i : Fin 4) :
    Q.totalOperator i =
      Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i :=
  rfl

@[simp] theorem QGTSoldering_apply
    (Q : QGTFourVector W) (ψ : Fin 2 → W) (i : Fin 2) :
    QGTSoldering Q ψ i =
      ∑ j : Fin 2, operatorSoldering Q.totalOperator i j (ψ j) := by
  exact operatorSolderingAction_apply Q.totalOperator ψ i

theorem QGTSoldering_eq_operatorSolderingAction
    (Q : QGTFourVector W) :
    QGTSoldering Q = operatorSolderingAction Q.totalOperator :=
  rfl

/-- Vanishing of the soldered action is exactly vanishing of the combined
operator four-vector.  No commutativity of its entries is assumed. -/
theorem QGTSoldering_eq_zero_iff
    (Q : QGTFourVector W) :
    QGTSoldering Q = 0 ↔ Q.totalOperator = 0 := by
  exact operatorSolderingAction_eq_zero_iff Q.totalOperator

/-! ## Genuine finite BKM operator channel -/

section BKM

variable {n : ℕ}

/--
The Kubo--Mori modular interpolation itself, retained as a noncommutative
operator-valued four-vector.  Unlike a scalar metric readout, every entry is
the actual operator `ρ^s A ρ^(1-s)` on the finite Hilbert carrier.
-/
def bkmInterpolationFourVector
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    OperatorFourVector (FiniteHilbertSpace n) :=
  fun i => (D.modularInterpolation (parameter i) (observable i)).toLinearMap

@[simp] theorem bkmInterpolationFourVector_apply
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (i : Fin 4) :
    bkmInterpolationFourVector D parameter observable i =
      (D.modularInterpolation (parameter i) (observable i)).toLinearMap :=
  rfl

@[simp] theorem bkmInterpolationFourVector_zero
    (D : FaithfulDensityOperator n) (parameter : Fin 4 → ℝ) :
    bkmInterpolationFourVector D parameter
      (0 : Fin 4 → FiniteOperatorAlgebra n) = 0 := by
  funext i
  simp [bkmInterpolationFourVector,
    FaithfulDensityOperator.modularInterpolation]

/-- Package a genuine BKM interpolation channel together with an independently
typed phase/Berry operator channel on the same finite Hilbert carrier. -/
def QGTFourVector.ofBKMInterpolation
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryChannel : OperatorFourVector (FiniteHilbertSpace n)) :
    QGTFourVector (FiniteHilbertSpace n) where
  symmetricBKM := bkmInterpolationFourVector D parameter observable
  antisymmetricBerry := berryChannel

@[simp] theorem QGTFourVector.ofBKMInterpolation_totalOperator_apply
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryChannel : OperatorFourVector (FiniteHilbertSpace n))
    (i : Fin 4) :
    (QGTFourVector.ofBKMInterpolation D parameter observable berryChannel).totalOperator i =
      (D.modularInterpolation (parameter i) (observable i)).toLinearMap +
        Complex.I • berryChannel i :=
  rfl

end BKM

section IntegratedBKM

variable {n : ℕ}

/-- Four integrated operator-valued Kubo--Mori transforms. -/
def bkmTransformFourVector
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    OperatorFourVector (FiniteHilbertSpace n) :=
  fun i => (D.kuboMoriTransform (observable i)).toLinearMap

/-- The same four-vector exhibited as evaluation of the integrated
complex-linear Kubo--Mori superoperator. -/
def bkmLinearTransformFourVector
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    OperatorFourVector (FiniteHilbertSpace n) :=
  fun i => (D.kuboMoriTransformLinear h_rpow (observable i)).toLinearMap

/-- Four-vector obtained by evaluating the bounded Kubo--Mori superoperator
in each observable channel. -/
def bkmContinuousTransformFourVector
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    OperatorFourVector (FiniteHilbertSpace n) :=
  fun i => (D.kuboMoriTransformCLM h_rpow (observable i)).toLinearMap

theorem bkmContinuousTransformFourVector_eq
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    bkmContinuousTransformFourVector D h_rpow observable =
      bkmTransformFourVector D observable := by
  rfl

theorem bkmLinearTransformFourVector_eq
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    bkmLinearTransformFourVector D h_rpow observable =
      bkmTransformFourVector D observable := by
  rfl

@[simp] theorem bkmLinearTransformFourVector_add
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (observable₁ observable₂ : Fin 4 → FiniteOperatorAlgebra n) :
    bkmLinearTransformFourVector D h_rpow (observable₁ + observable₂) =
      bkmLinearTransformFourVector D h_rpow observable₁ +
        bkmLinearTransformFourVector D h_rpow observable₂ := by
  funext i
  change
    (D.kuboMoriTransformLinear h_rpow
      ((observable₁ + observable₂) i)).toLinearMap =
      (D.kuboMoriTransformLinear h_rpow (observable₁ i)).toLinearMap +
        (D.kuboMoriTransformLinear h_rpow (observable₂ i)).toLinearMap
  rw [Pi.add_apply, map_add]
  rfl

@[simp] theorem bkmLinearTransformFourVector_smul
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (c : ℂ)
    (observable : Fin 4 → FiniteOperatorAlgebra n) :
    bkmLinearTransformFourVector D h_rpow (c • observable) =
      c • bkmLinearTransformFourVector D h_rpow observable := by
  funext i
  change
    (D.kuboMoriTransformLinear h_rpow ((c • observable) i)).toLinearMap =
      c • (D.kuboMoriTransformLinear h_rpow (observable i)).toLinearMap
  rw [Pi.smul_apply, map_smul]
  rfl

@[simp] theorem bkmTransformFourVector_apply
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (i : Fin 4) :
    bkmTransformFourVector D observable i =
      (D.kuboMoriTransform (observable i)).toLinearMap :=
  rfl

/-- Package the integrated BKM transform with a phase/Berry operator channel. -/
def QGTFourVector.ofBKMTransform
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryChannel : OperatorFourVector (FiniteHilbertSpace n)) :
    QGTFourVector (FiniteHilbertSpace n) where
  symmetricBKM := bkmTransformFourVector D observable
  antisymmetricBerry := berryChannel

@[simp] theorem QGTFourVector.ofBKMTransform_totalOperator_apply
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryChannel : OperatorFourVector (FiniteHilbertSpace n))
    (i : Fin 4) :
    (QGTFourVector.ofBKMTransform D observable berryChannel).totalOperator i =
      (D.kuboMoriTransform (observable i)).toLinearMap +
        Complex.I • berryChannel i :=
  rfl

end IntegratedBKM

/-! ## Evaluated Berry two-form channel -/

section Berry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- A complex scalar acts as a central endomorphism of the internal carrier. -/
def centralOperator (z : ℂ) : Module.End ℂ W :=
  z • LinearMap.id

@[simp] theorem centralOperator_apply (z : ℂ) (w : W) :
    centralOperator (W := W) z w = z • w := by
  simp [centralOperator]

/--
Evaluate the genuine operatorial Berry 2-form in four tangent slots and lift
the resulting real values to central complex operators.  This is deliberately
named a readout lift: it does not pretend that a real bilinear form is already
a complex-linear endomorphism.
-/
noncomputable def berryReadoutFourVector
    (operator : Fin 4 → EndH)
    (left right : Fin 4 → H₂) : OperatorFourVector W :=
  fun i =>
    centralOperator (W := W)
      ((berryOfOperator (E := E) (operator i) (left i) (right i) : ℝ) : ℂ)

@[simp] theorem berryReadoutFourVector_apply
    (operator : Fin 4 → EndH)
    (left right : Fin 4 → H₂)
    (i : Fin 4) :
    berryReadoutFourVector (W := W) operator left right i =
      centralOperator (W := W)
        ((metricOfOperator (E := E) (operator i)
          (InfoGeometry.Canonical.TomitaTakesaki.clockAxis (left i)) (right i) : ℝ) : ℂ) := by
  rfl

@[simp] theorem berryReadoutFourVector_zero_operator
    (left right : Fin 4 → H₂) :
    berryReadoutFourVector (W := W) (0 : Fin 4 → EndH) left right = 0 := by
  funext i
  simp [berryReadoutFourVector, centralOperator, berryOfOperator_apply]

end Berry

/-! ## Combined BKM/Berry soldering -/

section Combined

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Typed constructor joining the genuine noncommutative Kubo--Mori interpolation
with evaluated operatorial Berry curvature on the same final internal carrier.
The BKM entries remain arbitrary finite operators; only the real Berry
bilinear-form readouts are embedded centrally.
-/
noncomputable def QGTFourVector.ofBKMAndBerryReadout
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂) :
    QGTFourVector (FiniteHilbertSpace n) :=
  QGTFourVector.ofBKMInterpolation D parameter observable
    (berryReadoutFourVector
      (W := FiniteHilbertSpace n) berryOperator left right)

@[simp] theorem QGTFourVector.ofBKMAndBerryReadout_totalOperator_apply
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂)
    (i : Fin 4) :
    (QGTFourVector.ofBKMAndBerryReadout
      D parameter observable berryOperator left right).totalOperator i =
      (D.modularInterpolation (parameter i) (observable i)).toLinearMap +
        Complex.I •
          centralOperator (W := FiniteHilbertSpace n)
            ((berryOfOperator (E := E) (berryOperator i)
              (left i) (right i) : ℝ) : ℂ) :=
  rfl

/-- Faithfulness of the complete BKM/Berry soldering: its doubled action
vanishes exactly when all four combined operator channels vanish. -/
theorem QGTSoldering_ofBKMAndBerryReadout_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (parameter : Fin 4 → ℝ)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂) :
    QGTSoldering
        (QGTFourVector.ofBKMAndBerryReadout
          D parameter observable berryOperator left right) = 0
      ↔
    (QGTFourVector.ofBKMAndBerryReadout
      D parameter observable berryOperator left right).totalOperator = 0 := by
  exact QGTSoldering_eq_zero_iff _

end Combined

section IntegratedCombined

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Fully integrated BKM operator channel combined with the evaluated Berry
two-form channel. -/
noncomputable def QGTFourVector.ofBKMTransformAndBerryReadout
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂) :
    QGTFourVector (FiniteHilbertSpace n) :=
  QGTFourVector.ofBKMTransform D observable
    (berryReadoutFourVector
      (W := FiniteHilbertSpace n) berryOperator left right)

@[simp] theorem QGTFourVector.ofBKMTransformAndBerryReadout_totalOperator_apply
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂)
    (i : Fin 4) :
    (QGTFourVector.ofBKMTransformAndBerryReadout
      D observable berryOperator left right).totalOperator i =
      (D.kuboMoriTransform (observable i)).toLinearMap +
        Complex.I •
          centralOperator (W := FiniteHilbertSpace n)
            ((berryOfOperator (E := E) (berryOperator i)
              (left i) (right i) : ℝ) : ℂ) :=
  rfl

theorem QGTSoldering_ofBKMTransformAndBerryReadout_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (observable : Fin 4 → FiniteOperatorAlgebra n)
    (berryOperator : Fin 4 → EndH)
    (left right : Fin 4 → H₂) :
    QGTSoldering
        (QGTFourVector.ofBKMTransformAndBerryReadout
          D observable berryOperator left right) = 0
      ↔
    (QGTFourVector.ofBKMTransformAndBerryReadout
      D observable berryOperator left right).totalOperator = 0 := by
  exact QGTSoldering_eq_zero_iff _

end IntegratedCombined

end InfoGeometry.Unified
