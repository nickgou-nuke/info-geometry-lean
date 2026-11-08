/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo
import InfoGeometry.Quantum.OperatorSurprisalTraceSplit

/-! Trace-free representatives preserve the full canonical Zorn derivation current. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent

open InfoGeometry.Quantum.OperatorSurprisalTraceSplit

theorem surprisalCurrent_traceFreePart (K : EndCZ) :
    surprisalCurrent (traceFreePart K) = surprisalCurrent K := by
  have hs : surprisalCurrent (traceScalarPart K) = 0 :=
    InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo.scalarOperator_surprisalCurrent_eq_zero
      ((Module.finrank ℝ CZ : ℝ)⁻¹ * LinearMap.trace ℝ CZ K)
  change DerivationDifferentialForms.exteriorDerivativeZero Lane
    (K - traceScalarPart K) = surprisalCurrent K
  rw [map_sub]
  change surprisalCurrent K - surprisalCurrent (traceScalarPart K) = surprisalCurrent K
  rw [hs, sub_zero]

theorem surprisalCurrent_trace (K : EndCZ) (D : ZornDer) :
    LinearMap.trace ℝ CZ (surprisalCurrent K D) = 0 := by
  rw [surprisalCurrent_apply, map_sub, LinearMap.trace_mul_comm, sub_self]

theorem surprisalCurrent_eq_zero_iff_joint_centralizer (K : EndCZ) :
    surprisalCurrent K = 0 ↔ ∀ D : ZornDer, D.1 * K = K * D.1 := by
  constructor
  · intro h D
    apply (surprisalCurrent_eq_zero_iff_commutes K D).mp
    rw [h]
    rfl
  · intro h
    apply LinearMap.ext
    intro D
    exact (surprisalCurrent_eq_zero_iff_commutes K D).mpr (h D)

theorem surprisalCurrent_eq_iff_difference_centralizes (K L : EndCZ) :
    surprisalCurrent K = surprisalCurrent L ↔
      ∀ D : ZornDer, D.1 * (K - L) = (K - L) * D.1 := by
  have hsub : surprisalCurrent (K - L) = surprisalCurrent K - surprisalCurrent L := by
    exact (DerivationDifferentialForms.exteriorDerivativeZero Lane).map_sub K L
  rw [← surprisalCurrent_eq_zero_iff_joint_centralizer, hsub, sub_eq_zero]

end InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent
