import InfoGeometry.Arithmetic.MoebiusSignature
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Algebraic.SplitSuperGeometry
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Zeta-Regularized Supervolume

Quarantines the analytic Mellin bridge from the finite parity supertrace
to the zeta-regularized volume as an explicit witness layer.
-/

namespace InfoGeometry.Analytic

open InfoGeometry.Algebraic.SplitSignature

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

/--
Operator-level translation of the zeta-regularized supervolume language.

The analytic continuation layer remains separate, while the operator-level
primitive is the split Clifford super-Berezinian readout.
-/
structure SplitZetaSupervolumeShadow (n : ℕ) where
  operator : SplitCliffordEnd n := parityOp n
  supertraceReadout : ℝ := cliffordSupertrace n operator
  superBerezinianReadout : ℝ := superBerezinian n operator
  zetaLikePotential : ℝ := superEffectiveAction n operator

@[simp]
theorem zetaLikePotential_eq_neg_log_superBerezinian
    (n : ℕ) (x : SplitCliffordEnd n) :
    (superEffectiveAction n) x = - Real.log ((superBerezinian n) x) :=
  rfl

end InfoGeometry.Analytic
