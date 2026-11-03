/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CircularZornCliffordMinkowskiBridge
import InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge

/-! # Cartan action read out on the circular Zorn section

The Cartan-transformed Hermitian Pauli matrix determines real coordinates.
These are embedded in the existing native Zorn section, whose two circular
readouts recover the coordinates of the actual transformed matrix.
-/

noncomputable section

namespace InfoGeometry.Canonical.CartanCircularZornReadoutBridge

open InfoGeometry.Canonical.CircularZornCliffordMinkowskiBridge
open InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-- Real Minkowski coordinates read from the actual Pauli matrix entries. -/
def pauliMatrixReadout (M : Matrix2C) : Fin 4 → ℝ :=
  ![(M 0 0).re / 2 + (M 1 1).re / 2,
    (M 0 1).re, -(M 0 1).im,
    (M 0 0).re / 2 - (M 1 1).re / 2]

/-- The same real readout applied to the existing four Cartan coordinates. -/
def cartanRealReadout (X : CartanCoordinates) : Fin 4 → ℝ :=
  ![X.plus.re / 2 + X.minus.re / 2, X.transversePlus.re,
    -X.transversePlus.im, X.plus.re / 2 - X.minus.re / 2]

/-- The readout uses the existing Cartan-to-matrix soldering, entrywise. -/
theorem pauliMatrixReadout_matrixOfCartanCoordinates (X : CartanCoordinates) :
    pauliMatrixReadout (matrixOfCartanCoordinates X) = cartanRealReadout X := by
  funext i
  fin_cases i <;> rfl

/-- The Cartan action, followed by its concrete matrix readout, lands in the
existing matched circular Zorn section. -/
def cartanCircularZorn (s : ℂ) (P : PauliParavector) :
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn :=
  circularZornSection (pauliMatrixReadout (bipolarSolderingAction s (pauliHermitian P)).mat)

/-- Both Peirce readouts are the explicit coordinates of the Cartan action
already proved equivalent to the actual half-log matrix action. -/
theorem cartanCircularZorn_two_readouts (s : ℂ) (P : PauliParavector) (i : Fin 4) :
    let u := cartanRealReadout (bipolarCoordinateAction s (pauliCartanCoordinates P))
    circularPeirceBasis.equivFun (cartanCircularZorn s P) (Fin.castAdd 4 i) = u i ∧
    circularPeirceBasis.equivFun (cartanCircularZorn s P) (Fin.addNat i 4) = u i := by
  dsimp only
  unfold cartanCircularZorn
  rw [bipolarSolderingAction_pauliMatrix, pauliMatrixReadout_matrixOfCartanCoordinates]
  exact circularZornSection_two_readouts _ i

/-- The standard Pauli carrier associated with real four-coordinates. -/
def coordinatesPauli (u : Fin 4 → ℝ) : PauliParavector :=
  ⟨u 0, u 1, u 2, u 3⟩

/-- Act on an actual element of the selected Zorn section by extracting its
unique coordinates, applying the existing Pauli Cartan action, and re-embedding. -/
def cartanActionOnZornSection (s : ℂ) (Z : LinearMap.range circularZornSection) :
    LinearMap.range circularZornSection :=
  let u := (LinearEquiv.ofInjective circularZornSection circularZornSection_injective).symm Z
  ⟨cartanCircularZorn s (coordinatesPauli u),
    ⟨pauliMatrixReadout (bipolarSolderingAction s (pauliHermitian (coordinatesPauli u))).mat, rfl⟩⟩

/-- The action on the actual Zorn section intertwines with the original
Pauli matrix action and its Cartan coordinate readout. -/
theorem cartanActionOnZornSection_readouts (s : ℂ)
    (Z : LinearMap.range circularZornSection) (i : Fin 4) :
    let u := (LinearEquiv.ofInjective circularZornSection circularZornSection_injective).symm Z
    let q := cartanRealReadout (bipolarCoordinateAction s (pauliCartanCoordinates (coordinatesPauli u)))
    circularPeirceBasis.equivFun (cartanActionOnZornSection s Z) (Fin.castAdd 4 i) = q i ∧
    circularPeirceBasis.equivFun (cartanActionOnZornSection s Z) (Fin.addNat i 4) = q i := by
  exact cartanCircularZorn_two_readouts s _ i

end InfoGeometry.Canonical.CartanCircularZornReadoutBridge

end
