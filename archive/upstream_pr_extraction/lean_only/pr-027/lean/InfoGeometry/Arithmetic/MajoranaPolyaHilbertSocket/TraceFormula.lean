import InfoGeometry.Meta.SocketTarget

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-! ## 3. Boson/fermion, Archimedean, and trace-formula sockets -/

/--
Boson/fermion superdeterminant bridge.

The square-free Majorana/Fock supertrace gives the inverse-zeta Witten
character.  A spectral-zero determinant targeting `ζ` or completed `ξ` needs
additional bosonic/Dirichlet data or a supplied superdeterminant inversion
mechanism.
-/
@[socket_debt_tag]
structure BosonFermionSuperdeterminantSocket
    (BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type) where
  bosonicReadout : BosonicReadout
  fermionicReadout : FermionicReadout
  superdeterminantReadout : SuperdeterminantReadout
  zetaReadout : ZetaReadout
  inverseZetaReadout : InverseZetaReadout

/--
Archimedean place socket.

The finite-prime Euler product does not contain the factor
`π^{-s/2} Γ(s/2)` or the polynomial `s(s-1)/2`.  A completed-zeta spectral
target must supply an Archimedean/local-infinity readout and a completion law.
-/
@[socket_debt_tag]
structure ArchimedeanGammaFactorSocket
    (SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type) where
  parameter : SpectralParameter
  archimedeanReadout : ArchimedeanReadout
  finitePrimeReadout : FinitePrimeReadout
  completedZetaReadout : CompletedZetaReadout

namespace ArchimedeanGammaFactorSocket
end ArchimedeanGammaFactorSocket

/--
Boundary/scattering mechanism socket.

The bare Berry--Keating dilation has a continuous Mellin spectrum.  A
Hilbert--Pólya construction must supply boundary conditions, a scattering
matrix, or an absorption-spectrum mechanism that produces the relevant
spectral zero data.
-/
@[socket_debt_tag]
structure BoundaryScatteringDiscretizationSocket
    (BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type) where
  boundaryData : BoundaryData
  scatteringMatrix : ScatteringMatrix
  continuousSpectrum : ContinuousSpectrum
  discreteOrAbsorptionReadout : DiscreteOrAbsorptionReadout
  phaseShiftReadout : PhaseShiftReadout

/--
Heat-kernel and explicit-formula socket.

For the combined MBK operator, the square-law suggests a factorized heat trace.
The nontrivial analytic test is that a Mellin transform or scattering trace
formula recovers the Riemann--Weil explicit formula.
-/
@[socket_debt_tag]
structure MBKHeatTraceExplicitFormulaSocket
    (HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type) where
  heatTrace : HeatTrace
  bkHeatTrace : BKHeatTrace
  arithmeticHeatTrace : ArithmeticHeatTrace
  mellinTransformReadout : MellinTransformReadout
  explicitFormulaReadout : ExplicitFormulaReadout

namespace MBKHeatTraceExplicitFormulaSocket
end MBKHeatTraceExplicitFormulaSocket

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
