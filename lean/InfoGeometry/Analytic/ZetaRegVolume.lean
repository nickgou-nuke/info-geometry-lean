import InfoGeometry.Arithmetic.MoebiusSignature
import InfoGeometry.Thermodynamics.SouriauTemperature
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Zeta-Regularized Supervolume

Quarantines the analytic Mellin bridge from the finite parity supertrace
to the zeta-regularized volume as an explicit witness layer.
-/

namespace InfoGeometry.Analytic

/-- A heat-kernel supertrace witness. -/
structure HeatKernelWitness where
  supertrace : ℝ → ℂ
  traceClass : Prop
  smallTimeAsymptotics : Prop
  mellinBridge : Prop

/-- A spectral-zeta witness built from a heat-kernel supertrace. -/
structure SpectralZetaWitness where
  kernel : HeatKernelWitness
  spectralZeta : ℂ → ℂ
  analyticContinuation : Prop
  derivativeAtZero : ℂ

/-- Formal zeta-regularized supervolume. -/
noncomputable def zetaRegularizedSupervolume (Z : SpectralZetaWitness) : ℂ :=
  Complex.exp (-Z.derivativeAtZero)

/-- The analytic volume package is the exponentiated zeta derivative. -/
structure EmergentVolumeWitness where
  zeta : SpectralZetaWitness
  volumeMatches : Prop
end InfoGeometry.Analytic
