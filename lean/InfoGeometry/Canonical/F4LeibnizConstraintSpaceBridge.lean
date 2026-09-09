import Mathlib
import InfoGeometry.Canonical.F4LeibnizResidualBridge
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge

/-! Finite coordinate readouts for the existing H3 Jordan-Leibniz residual.
This bridge adds only a basis presentation; the product and derivation predicate
remain owned by the native H3 algebra files. -/

noncomputable section

namespace InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.F4LeibnizResidualBridge
open InfoGeometry.Canonical.H3ZornBasis

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3
abbrev ActionCoord := Fin 27 → Fin 27 → ℝ
abbrev ConstraintCoord := Fin 27 → Fin 27 → Fin 27 → ℝ

def actionReadout (D : EndH3) : ActionCoord := fun i j =>
  (h3ZornCoordinateBasis.repr (D (h3ZornCoordinateBasis i))) j

def actionReadoutLM : EndH3 →ₗ[ℝ] ActionCoord where
  toFun := actionReadout
  map_add' D E := by
    funext i j
    simp [actionReadout]
  map_smul' c D := by
    funext i j
    simp [actionReadout]

theorem actionReadoutLM_injective : Function.Injective actionReadoutLM := by
  intro D E h
  apply LinearMap.ext
  intro x
  rw [← h3ZornCoordinateBasis.sum_repr x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hbasis : D (h3ZornCoordinateBasis i) = E (h3ZornCoordinateBasis i) := by
    apply h3ZornCoordinateBasis.repr.injective
    ext j
    simpa [actionReadoutLM, actionReadout] using congrFun (congrFun h i) j
  rw [hbasis]

def constraintReadout (B : H3 →ₗ[ℝ] H3 →ₗ[ℝ] H3) : ConstraintCoord :=
  fun i j k =>
    (h3ZornCoordinateBasis.repr
      (B (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j))) k

def residualReadout (D : EndH3) : ConstraintCoord := fun i j k =>
  (h3ZornCoordinateBasis.repr
    (residual D (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j))) k

theorem derivation_residual_readout_zero
    (D : EndH3) (hD : H3ZornJordanDerivation D) :
  residualReadout D = 0 := by
  funext i j k
  have hz := (residual_zero_iff D).2 hD
  rw [residualReadout, hz]
  change (h3ZornCoordinateBasis.repr (0 : H3)) k = 0
  rw [map_zero]
  rfl

end InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge
