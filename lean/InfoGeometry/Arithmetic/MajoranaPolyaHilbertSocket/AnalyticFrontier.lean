import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.Bridge
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeDeterminant

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-! ## 8. Analytic frontier sockets -/

/--
Essential self-adjointness and infinite-cutoff limit socket.

The finite-cutoff MBK operator is algebraic.  The infinite operator requires a
choice of dense core, closure, and an essential self-adjointness proof.  This
packet records that obligation without asserting a Kato--Rellich or Nelson
commutator theorem.
-/
@[socket_debt_tag]
structure EssentialSelfAdjointLimitSocket
    (Operator : Type*) where
  diracCutoffSeq : ℕ → Operator
  essentialSelfAdjointLimit : Operator

/--
Zeta/Ray--Singer regularized Pfaffian socket.

Ordinary determinants and Pfaffians require trace-class control.  The MBK
program needs a heat-kernel subtraction/finite-part construction that turns a
divergent trace into a renormalized spectral Pfaffian.
-/
@[socket_debt_tag]
structure ZetaRegularizedPfaffianSocket
    (Operator ZetaReadout : Type*) where
  diracSquare : Operator
  zetaRegularizedDet : ZetaReadout

/--
Completed-`ξ` superdeterminant identity socket.

This is the exact place where a future owner must prove that the bosonic,
fermionic, and Archimedean factors combine into the completed zeta function,
not merely the inverse-zeta Witten character.
-/
@[socket_debt_tag]
structure CompletedXiSuperdeterminantIdentitySocket
    (DeterminantReadout CompletedXiReadout : Type*) where
  relativeSuperdeterminant : DeterminantReadout
  completedXiTarget : CompletedXiReadout

/--
The three-front analytic frontier for the MBK program.

Supplying this packet still does not construct RH in this file; it merely
packages the three analytic fronts that a serious operator proof must close:
essential self-adjointness, zeta-regularized Pfaffian construction, and the
completed-`ξ` superdeterminant identity.
-/
structure MBKAnalyticFrontier
    (Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout DeterminantReadout : Type*) where
  base_bridge :
    MajoranaPolyaHilbertBridge
      Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout
  relativeDeterminant :
    RelativeMBKDeterminantScatteringPacket Operator ScatteringMatrix DeterminantReadout
  essentialSelfAdjoint :
    EssentialSelfAdjointLimitSocket Operator
  zetaRegularized :
    ZetaRegularizedPfaffianSocket Operator ZetaReadout
  completedXiIdentity :
    CompletedXiSuperdeterminantIdentitySocket DeterminantReadout CompletedXiReadout

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
