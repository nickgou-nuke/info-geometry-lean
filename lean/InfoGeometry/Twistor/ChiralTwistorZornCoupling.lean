import InfoGeometry.Twistor.ChiralTwistorSheets
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

/-!
# Chiral twistor sheets and native Zorn coupling channels

This owner connects concrete real axes in the two Penrose spinor sheets to the
native circular split-octonion roots.  It then transports the existing Zorn
multiplication theorems to those twistor-sheet axes.

The three channels are genuine products in the established Zorn carrier:

* `V₊ × V₋ → ℝ u₊` by the Kronecker pairing;
* `V₊ × V₊ → V₋` by the Levi--Civita cross channel;
* `V₋ × V₋ → V₊` by the opposite Levi--Civita cross channel.

No new multiplication is introduced on the complex twistor carrier itself.
-/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorZornCoupling

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Canonical.ZornMatrix

/-- Scalar axis in either real four-dimensional chiral sheet. -/
def sheetScalarSpinor : Spinor2 :=
  peirce4ToSpinor2 (1, 0)

/-- Root axis `i` in either real four-dimensional chiral sheet. -/
def sheetRootSpinor (i : Fin 3) : Spinor2 :=
  peirce4ToSpinor2 (0, Pi.single i 1)

/-- The positive sheet scalar axis maps to the positive Zorn idempotent. -/
theorem plus_scalar_axis_zorn :
    plusZornMap sheetScalarSpinor = zornPlus := by
  change twistorRealEquivZorn (plusInclusion sheetScalarSpinor) = zornPlus
  rw [← cartesianZorn_scalarPlus]
  rw [← circularPeirceBasis_apply (i := (0 : Fin 8))]
  rw [← twistor_scalarPlus_axis]
  congr 1
  ext i <;> fin_cases i <;> apply Complex.ext <;>
    simp [sheetScalarSpinor, peirce4ToSpinor2, plusInclusion,
      realCoordinatesTwistor]

/-- The negative sheet scalar axis maps to the negative Zorn idempotent. -/
theorem minus_scalar_axis_zorn :
    minusZornMap sheetScalarSpinor = zornMinus := by
  change twistorRealEquivZorn (minusInclusion sheetScalarSpinor) = zornMinus
  rw [← cartesianZorn_scalarMinus]
  rw [← circularPeirceBasis_apply (i := (4 : Fin 8))]
  rw [← twistor_scalarMinus_axis]
  congr 1
  ext i <;> fin_cases i <;> apply Complex.ext <;>
    simp [sheetScalarSpinor, peirce4ToSpinor2, minusInclusion,
      realCoordinatesTwistor]

/-- Positive real twistor root axis `i` is exactly the native positive Zorn root. -/
theorem plus_root_axis_zorn (i : Fin 3) :
    plusZornMap (sheetRootSpinor i) =
      cartesianZornLinearEquiv (rootPlus i) := by
  change twistorRealEquivZorn (plusInclusion (sheetRootSpinor i)) = _
  rw [← circularPeirceBasis_apply
    (i := ⟨i.val + 1, by omega⟩)]
  rw [← twistor_rootPlus_axes i]
  congr 1
  fin_cases i <;>
    ext j <;> fin_cases j <;> apply Complex.ext <;>
      simp [sheetRootSpinor, peirce4ToSpinor2, plusInclusion,
        realCoordinatesTwistor, circularFrame]

/-- Negative real twistor root axis `i` is exactly the native negative Zorn root. -/
theorem minus_root_axis_zorn (i : Fin 3) :
    minusZornMap (sheetRootSpinor i) =
      cartesianZornLinearEquiv (rootMinus i) := by
  change twistorRealEquivZorn (minusInclusion (sheetRootSpinor i)) = _
  rw [← circularPeirceBasis_apply
    (i := ⟨i.val + 5, by omega⟩)]
  rw [← twistor_rootMinus_axes i]
  congr 1
  fin_cases i <;>
    ext j <;> fin_cases j <;> apply Complex.ext <;>
      simp [sheetRootSpinor, peirce4ToSpinor2, minusInclusion,
        realCoordinatesTwistor, circularFrame]

/-- Cross-sheet scalar coupling: positive root `i` times negative root `j`
lands in the positive scalar pole with coefficient `δᵢⱼ`. -/
theorem plus_minus_scalar_coupling (i j : Fin 3) :
    plusZornMap (sheetRootSpinor i) * minusZornMap (sheetRootSpinor j) =
      (if i = j then (1 : ℝ) else 0) • zornPlus := by
  rw [plus_root_axis_zorn, minus_root_axis_zorn]
  exact cartesianZorn_rootPlus_mul_rootMinus_delta i j

/-- Opposite cross-sheet scalar coupling lands in the negative scalar pole. -/
theorem minus_plus_scalar_coupling (i j : Fin 3) :
    minusZornMap (sheetRootSpinor i) * plusZornMap (sheetRootSpinor j) =
      (if i = j then (1 : ℝ) else 0) • zornMinus := by
  rw [minus_root_axis_zorn, plus_root_axis_zorn]
  exact cartesianZorn_rootMinus_mul_rootPlus_delta i j

/-- Positive same-sheet coupling is the native Levi--Civita map `V₊∧V₊ → V₋`. -/
theorem plus_plus_to_minus_coupling (i j : Fin 3) :
    plusZornMap (sheetRootSpinor i) * plusZornMap (sheetRootSpinor j) =
      ∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        minusZornMap (sheetRootSpinor k) := by
  rw [plus_root_axis_zorn, plus_root_axis_zorn]
  rw [cartesianZorn_rootPlus_mul_rootPlus_leviCivita]
  apply Finset.sum_congr rfl
  intro k _
  rw [minus_root_axis_zorn]

/-- Negative same-sheet coupling is the native opposite Levi--Civita map
`V₋∧V₋ → V₊`, with the repository's established lower-root sign. -/
theorem minus_minus_to_plus_coupling (i j : Fin 3) :
    minusZornMap (sheetRootSpinor i) * minusZornMap (sheetRootSpinor j) =
      -∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        plusZornMap (sheetRootSpinor k) := by
  rw [minus_root_axis_zorn, minus_root_axis_zorn]
  rw [cartesianZorn_rootMinus_mul_rootMinus_leviCivita]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [plus_root_axis_zorn]

end InfoGeometry.Twistor.ChiralTwistorZornCoupling
