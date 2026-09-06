import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Lie.ChevalleySpinorBlueprint
import InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport

/-!
# Native Clifford representation on the transported split-coordinate carrier

The exterior creation/contraction action already satisfies the hyperbolic
Clifford square law on `Exterior3`.  Conjugation by the existing finite
linear equivalence transports that action to `SplitCarrier`; the universal
property of `CliffordAlgebra` then packages the transported operators as an
associative algebra homomorphism.  No claim about split-octonion
multiplication is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExteriorCliffordRepresentation

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
open InfoGeometry.Lie.ChevalleySpinor

abbrev SplitW := SplitV ℝ V3
abbrev SplitQ := splitQ (R := ℝ) (W := V3)

/-- The transported Chevalley creation/contraction action. -/
def splitCoordinateCliffordAction
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
  SplitW →ₗ[ℝ] SplitEnd :=
  (transportEndAlgEquiv e).toLinearMap.comp
    (spinorAction (R := ℝ) (W := V3))

@[simp] theorem splitCoordinateCliffordAction_apply
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (w : SplitW) :
    splitCoordinateCliffordAction e w =
      transportEnd e (spinorAction (R := ℝ) (W := V3) w) := rfl

theorem splitCoordinateCliffordAction_eq_hodgeDirac
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3)
    (φ : Module.Dual ℝ V3) :
    splitCoordinateCliffordAction e (v, φ) =
      splitCoordinateHodgeDirac3 e v φ := by
  rfl

theorem splitCoordinateCliffordAction_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (w : SplitW) :
    splitCoordinateCliffordAction e w * splitCoordinateCliffordAction e w =
      (SplitQ w) • (1 : SplitEnd) := by
  rw [splitCoordinateCliffordAction_apply, ← transportEnd_mul]
  rw [spinorAction_sq]
  rw [transportEnd_smul, transportEnd_one]

theorem splitCoordinateHodgeDirac3_sq_as_clifford
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3)
    (φ : Module.Dual ℝ V3) :
    splitCoordinateHodgeDirac3 e v φ *
        splitCoordinateHodgeDirac3 e v φ =
      (SplitQ (v, φ)) • (1 : SplitEnd) := by
  rw [← splitCoordinateCliffordAction_eq_hodgeDirac]
  exact splitCoordinateCliffordAction_sq e (v, φ)

/-- The native Clifford algebra representation on `SplitCarrier`. -/
noncomputable def splitCoordinateCliffordRepresentation
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    CliffordAlgebra SplitQ →ₐ[ℝ] SplitEnd :=
  CliffordAlgebra.lift SplitQ
    ⟨splitCoordinateCliffordAction e, splitCoordinateCliffordAction_sq e⟩

@[simp] theorem splitCoordinateCliffordRepresentation_ι
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (w : SplitW) :
    splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ w) =
      splitCoordinateCliffordAction e w := by
  exact CliffordAlgebra.lift_ι_apply _ _ w

@[simp] theorem splitCoordinateCliffordRepresentation_ι_pair
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3)
    (φ : Module.Dual ℝ V3) :
    splitCoordinateCliffordRepresentation e
        (CliffordAlgebra.ι SplitQ (v, φ)) =
      splitCoordinateHodgeDirac3 e v φ := by
  rw [splitCoordinateCliffordRepresentation_ι,
    splitCoordinateCliffordAction_eq_hodgeDirac]

theorem splitCoordinateCliffordRepresentation_ι_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (w : SplitW) :
    splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ w) *
        splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ w) =
      (SplitQ w) • (1 : SplitEnd) := by
  rw [splitCoordinateCliffordRepresentation_ι]
  exact splitCoordinateCliffordAction_sq e w

theorem splitCoordinateCliffordRepresentation_ι_anticommutator
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (w z : SplitW) :
    splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ w) *
          splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ z) +
        splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ z) *
          splitCoordinateCliffordRepresentation e (CliffordAlgebra.ι SplitQ w) =
      (algebraMap ℝ SplitEnd (QuadraticMap.polar SplitQ w z)) := by
  have h := congrArg (splitCoordinateCliffordRepresentation e)
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := SplitQ) w z)
  have h' :
      splitCoordinateCliffordAction e w * splitCoordinateCliffordAction e z +
          splitCoordinateCliffordAction e z * splitCoordinateCliffordAction e w =
        splitCoordinateCliffordRepresentation e
          ((algebraMap ℝ (CliffordAlgebra SplitQ)) (QuadraticMap.polar SplitQ w z)) := by
    simpa only [map_add, map_mul, splitCoordinateCliffordRepresentation_ι] using h
  rw [(splitCoordinateCliffordRepresentation e).commutes] at h'
  simpa only [splitCoordinateCliffordRepresentation_ι] using h'

end InfoGeometry.Canonical.SplitOctonionExteriorCliffordRepresentation
