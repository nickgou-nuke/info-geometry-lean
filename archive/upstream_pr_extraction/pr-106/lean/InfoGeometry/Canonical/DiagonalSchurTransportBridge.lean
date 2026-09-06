import InfoGeometry.Canonical.CartanBerezinianCore

/-!
# Diagonal Schur-admissible doubled transports

The native doubled sheet lift already provides the exact block maps needed by
`SchurAdmissibleTransport`.  This owner packages that diagonal case without
claiming a construction for general off-diagonal TwinWave transports.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiagonalSchurTransportBridge

open InfoGeometry.Canonical.CartanBerezinianCore
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def diagonalSchurAdmissibleTransport
    (Aplus Aminus : E ≃L[ℝ] E) :
    SchurAdmissibleTransport (E := E) where
  T := dualSheetPairLift (E := E) Aplus.toContinuousLinearMap Aminus.toContinuousLinearMap
  Dinv := Aminus
  hD := by simp
  Schur := Aplus
  hSchur := by simp

omit [CompleteSpace E] in
@[simp]
theorem diagonalSchurAdmissibleTransport_T
    (Aplus Aminus : E ≃L[ℝ] E) :
    (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).T =
      dualSheetPairLift (E := E) Aplus.toContinuousLinearMap Aminus.toContinuousLinearMap :=
  rfl

omit [CompleteSpace E] in
theorem diagonalSchurAdmissibleTransport_blocks
    (Aplus Aminus : E ≃L[ℝ] E) :
    plusBlockMap
        (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).T =
        Aplus.toContinuousLinearMap ∧
      minusBlockMap
        (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).T =
        Aminus.toContinuousLinearMap ∧
      plusToMinusBlockMap
        (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).T = 0 ∧
      minusToPlusBlockMap
        (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).T = 0 := by
  simp [diagonalSchurAdmissibleTransport]

omit [CompleteSpace E] in
theorem diagonalSchurAdmissibleTransport_schur
    (Aplus Aminus : E ≃L[ℝ] E) :
    (diagonalSchurAdmissibleTransport (E := E) Aplus Aminus).Schur = Aplus :=
  rfl

end InfoGeometry.Canonical.DiagonalSchurTransportBridge
