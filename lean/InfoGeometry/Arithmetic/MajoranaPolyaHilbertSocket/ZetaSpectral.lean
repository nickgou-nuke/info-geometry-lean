import InfoGeometry.Arithmetic.RHQuantumStabilityBridge
import InfoGeometry.Meta.SocketTarget

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

open InfoGeometry.Arithmetic.RHQuantumStabilityBridge

/-! ## 2. Zero-mode normalizability and zeta spectral sockets -/

/--
Guard separating ordinary Fock norm from Mellin/Plancherel normalization.

The square-free Möbius spinor/Fock series has its own summability domain; the
critical line in the Berry--Keating program is instead a unitary Mellin
normalization statement.
-/
structure FockVsMellinNormalizabilityGuard
    (FockState MellinState FockNorm MellinNorm : Type) where
  fockState : FockState
  mellinState : MellinState
  fockNorm : FockNorm
  mellinNorm : MellinNorm

/--
Majorana zero-mode normalizability packet.

`spectralParameter` is deliberately split into real and imaginary coordinates:
the theorem-safe critical-line predicate is only the algebraic condition
`realPart = 1/2`.
-/
structure MajoranaZeroModeNormalizabilityPacket
    (ZeroMode NormReadout : Type) where
  realPart : ℝ
  imaginaryHeight : ℝ
  zeroMode : ZeroMode
  normReadout : NormReadout
  realPart_eq_half : realPart = (1 / 2 : ℝ)

namespace MajoranaZeroModeNormalizabilityPacket

/-- Concrete model: zero-mode packet on the critical line Re(s) = 1/2.

The critical-line part is definitional because `IsCriticalLineRealPart σ`
is the equality `σ = 1 / 2`. -/
def mkCriticalLine (ZeroMode NormReadout : Type)
    (zeroMode : ZeroMode) (normReadout : NormReadout) (imaginaryHeight : ℝ) :
    MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout where
  realPart := 1/2
  imaginaryHeight := imaginaryHeight
  zeroMode := zeroMode
  normReadout := normReadout
  realPart_eq_half := by rfl

variable {ZeroMode NormReadout : Type}
variable (P : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout)

/-- The packet places the zero-mode real part on the critical line. -/
theorem criticalLine : IsCriticalLineRealPart P.realPart := by
  simpa [IsCriticalLineRealPart] using P.realPart_eq_half

end MajoranaZeroModeNormalizabilityPacket

/--
Hestenes--Krein/colimit Pfaffian/zeta spectral identity socket.

This is where a future categorical owner would connect a Majorana Pfaffian or
determinant readout to the zeta colimit readout.  It also separates zeros of
zeta from singularities of reciprocal zeta.
-/
@[socket_debt_tag]
structure MajoranaPfaffianZetaSpectralSocket
    (SpectralParameter PfaffianReadout ZetaReadout : Type) where
  parameter : SpectralParameter
  pfaffianReadout : PfaffianReadout
  zetaReadout : ZetaReadout


/--
Separation between the inverse-zeta Witten character and the completed-zeta
spectral target.

The Majorana/Fock parity supertrace naturally produces a readout of
`1 / ζ(s)` in the Euler-product half-plane.  A Hilbert--Pólya spectral operator
must instead have a determinant/Pfaffian target proportional to the completed
function on the critical line, commonly written `Ξ(t) = ξ(1/2 + it)`.
-/
@[socket_debt_tag]
structure WittenCharacterVsCompletedXiSocket
    (SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type) where
  parameter : SpectralParameter
  wittenCharacter : WittenCharacter
  completedXi : CompletedXiReadout
  spectralPfaffian : SpectralPfaffianReadout

namespace WittenCharacterVsCompletedXiSocket

end WittenCharacterVsCompletedXiSocket

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
