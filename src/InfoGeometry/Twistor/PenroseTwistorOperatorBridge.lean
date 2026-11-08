/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
import InfoGeometry.Twistor.ChiralTwistorSheets

/-!
# First-quantized finite twistor operators on the Penrose carrier

The finite coordinate and derivative matrices from the CCR owner act on the
actual complex Penrose twistor carrier by matrix-to-endomorphism conversion.
Transport along the existing carrier equivalence gives operators on
`PenroseIncidence.Twistor4`. The commutator retains the finite-boundary defect
and its action is resolved explicitly on the two spinor factors.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseTwistorOperatorBridge

open InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.ChiralTwistorSheets
open Matrix

/-- Transport a finite matrix operator on the Penrose `ℂ⁴` carrier to the
equivalent paired-spinor carrier. -/
def transportTwistorMatrix (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Module.End ℂ Twistor4 :=
  (penroseTwistor4CarrierEquiv.symm.toLinearMap.comp (Matrix.toLin' M)).comp
    penroseTwistor4CarrierEquiv.toLinearMap

def firstQuantizedCoordinate : Module.End ℂ Twistor4 :=
  transportTwistorMatrix twistorCoordinate

def firstQuantizedDerivative : Module.End ℂ Twistor4 :=
  transportTwistorMatrix twistorDerivative

/-- The finite-dimensional CCR boundary term, represented as an operator on
the Penrose twistor carrier. -/
def firstQuantizedBoundary : Module.End ℂ Twistor4 :=
  transportTwistorMatrix
    (!![1, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, -1] : Matrix (Fin 4) (Fin 4) ℂ)

def coordinateAction (z : Twistor4) : Twistor4 :=
  (fun i : Fin 2 => if i.val = 0 then z.1 1 else z.2 0,
   fun i : Fin 2 => if i.val = 0 then z.2 1 else 0)

def derivativeAction (z : Twistor4) : Twistor4 :=
  (fun i : Fin 2 => if i.val = 0 then 0 else z.1 0,
   fun i : Fin 2 => if i.val = 0 then z.1 1 else z.2 0)

def boundaryAction (z : Twistor4) : Twistor4 :=
  (fun i : Fin 2 => if i.val = 0 then z.1 0 else 0,
   fun i : Fin 2 => if i.val = 0 then 0 else -z.2 1)

theorem firstQuantizedCoordinate_action (z : Twistor4) :
    firstQuantizedCoordinate z = coordinateAction z := by
  unfold firstQuantizedCoordinate transportTwistorMatrix
  simp only [LinearMap.comp_apply]
  simp only [Matrix.toLin'_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [coordinateAction, penroseTwistor4CarrierEquiv,
        twistorCoordinate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [coordinateAction, penroseTwistor4CarrierEquiv,
        twistorCoordinate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem firstQuantizedDerivative_action (z : Twistor4) :
    firstQuantizedDerivative z = derivativeAction z := by
  unfold firstQuantizedDerivative transportTwistorMatrix
  simp only [LinearMap.comp_apply]
  simp only [Matrix.toLin'_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [derivativeAction, penroseTwistor4CarrierEquiv,
        twistorDerivative, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [derivativeAction, penroseTwistor4CarrierEquiv,
        twistorDerivative, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem firstQuantizedBoundary_action (z : Twistor4) :
    firstQuantizedBoundary z = boundaryAction z := by
  unfold firstQuantizedBoundary transportTwistorMatrix
  simp only [LinearMap.comp_apply]
  simp only [Matrix.toLin'_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [boundaryAction, penroseTwistor4CarrierEquiv,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [boundaryAction, penroseTwistor4CarrierEquiv,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The coordinate/derivative commutator is the exact finite-boundary
operator. The two endpoint spinor coordinates carry opposite signs. -/
theorem firstQuantized_commutator_action (z : Twistor4) :
    (firstQuantizedCoordinate * firstQuantizedDerivative -
      firstQuantizedDerivative * firstQuantizedCoordinate) z = boundaryAction z := by
  change firstQuantizedCoordinate (firstQuantizedDerivative z) -
    firstQuantizedDerivative (firstQuantizedCoordinate z) = boundaryAction z
  simp only [firstQuantizedCoordinate_action, firstQuantizedDerivative_action]
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [coordinateAction, derivativeAction, boundaryAction]
  · funext i
    fin_cases i <;> simp [coordinateAction, derivativeAction, boundaryAction]

/-- In matrix form, the transported CCR commutator is the owner’s boundary
matrix, not the identity operator. -/
theorem firstQuantized_commutator_eq_boundary :
    firstQuantizedCoordinate * firstQuantizedDerivative -
      firstQuantizedDerivative * firstQuantizedCoordinate = firstQuantizedBoundary := by
  apply LinearMap.ext
  intro z
  rw [firstQuantized_commutator_action, firstQuantizedBoundary_action]

end InfoGeometry.Twistor.PenroseTwistorOperatorBridge
