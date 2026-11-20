/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauKillingLipschitzBridge
import InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation

/-!
# Souriau boost rotor in the real Hestenes Pauli carrier

The finite `Cl(1,1)` boost rotor in the Souriau/Killing owner and the
corresponding real Hestenes-even element have the same Pauli matrix entries.
The equality is stated after the real Hestenes Pauli representation, whose
matrix entries happen to be complex-valued; the Clifford coefficients,
graded tensor algebra, and doubled Krein carrier remain real. This is a
finite-dimensional rotor identification, not a curved-spacetime Kosmann
construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauHestenesRealTensorBridge

open InfoGeometry.Canonical.SouriauKillingLipschitzBridge
open InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv
open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open HestenesEvenPauliEquiv
open HestenesPauliSheetBridge
open HestenesCl14
open InfoGeometry.Clifford.Cl11Matrix
open Matrix

local notation "HestenesEven" => HestenesCl14.ClPlus14
local notation "Tensor2" => InfoGeometry.Canonical.GradedTensorWeylBridge.twoMatrixGradedTensor

/-- The real Hestenes-even boost rotor with the same rapidity convention as
the finite Souriau `Cl(1,1)` owner. Its bivector generator is the real
Hestenes element `sigmaEven 0`. -/
def souriauBoostRotorInHestenesEven (s : ℝ) : HestenesEven :=
  Real.cosh (s / 2) • (1 : HestenesEven) -
    Real.sinh (s / 2) • sigmaEven 0

/-- The forward real Hestenes Pauli matrix of the rotor is the real
`Cl(1,1)` boost rotor entrywise included into `ℂ`. -/
theorem souriauBoostRotor_pauli_entry (s : ℝ) (i j : Fin 2) :
    HestenesPauliSheetBridge.clPlusToPauli (souriauBoostRotorInHestenesEven s) i j =
      (boostRotor s i j : ℂ) := by
  rw [souriauBoostRotorInHestenesEven, map_sub, map_smul, map_smul, map_one,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma0]
  fin_cases i <;> fin_cases j <;>
    simp [boostRotor, J1, HestenesEvenPauliEquiv.pauli1,
      Matrix.smul_apply, Matrix.sub_apply]

/-- The actual real two-factor Koszul tensor representative of the Souriau
boost rotor, obtained by realifying its real matrix entries and transporting
through the existing Morita equivalence. -/
def souriauBoostRotorInRealTensor (s : ℝ) : Tensor2 :=
  twoMatrixGradedTensorMoritaEquiv.symm
    (realNestedMatrixToFin4.symm
      (realify ((boostRotor s).map Complex.ofReal)))

/-- The Souriau boost rotor embedded into the real Koszul tensor is exactly
the already-owned image of the matching real Hestenes-even rotor. This closes
the finite boost-generator bridge on the actual graded-tensor carrier. -/
theorem souriauBoostRotor_realTensor_eq_hestenes (s : ℝ) :
    souriauBoostRotorInRealTensor s =
      hestenesEvenToRealGradedTensor (souriauBoostRotorInHestenesEven s) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  apply realNestedMatrixToFin4.injective
  have hPauli :
      HestenesEvenPauliEquiv.clPlusPauliAlgEquiv
          (souriauBoostRotorInHestenesEven s) =
        (boostRotor s).map Complex.ofReal := by
    change HestenesPauliSheetBridge.clPlusToPauli
      (souriauBoostRotorInHestenesEven s) = _
    ext i j
    simp only [Matrix.map_apply]
    exact souriauBoostRotor_pauli_entry s i j
  simpa [souriauBoostRotorInRealTensor, hestenesEvenToRealGradedTensor,
    commutantToMatrix, realifyCommutantHom, realifyRingHom] using
      congrArg realify hPauli.symm

/-- The reverse real Hestenes Pauli matrix agrees entrywise with the reverse
matrix rotor used in the Souriau vector sandwich. -/
theorem souriauBoostRotorReverse_pauli_entry (s : ℝ) (i j : Fin 2) :
    HestenesPauliSheetBridge.clPlusToPauli
        (Real.cosh (s / 2) • (1 : HestenesEven) +
          Real.sinh (s / 2) • sigmaEven 0) i j =
      (boostRotorReverse s i j : ℂ) := by
  rw [map_add, map_smul, map_smul, map_one,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma0]
  fin_cases i <;> fin_cases j <;>
    simp [boostRotorReverse, J1, HestenesEvenPauliEquiv.pauli1,
      Matrix.smul_apply, Matrix.add_apply]

/-- The Souriau boost's Hestenes-even generator is the exact Pauli image of
the real matrix generator `J1`; this records the bridge at the generator,
before exponentiation or a choice of spinor-bundle connection. -/
theorem souriauBoostGenerator_pauli_entry (i j : Fin 2) :
    HestenesPauliSheetBridge.clPlusToPauli
        (sigmaEven 0) i j = (J1 i j : ℂ) := by
  rw [HestenesEvenPauliEquiv.clPlusToPauli_sigma0]
  fin_cases i <;> fin_cases j <;>
    norm_num [HestenesEvenPauliEquiv.pauli1, J1]

end InfoGeometry.Canonical.SouriauHestenesRealTensorBridge
