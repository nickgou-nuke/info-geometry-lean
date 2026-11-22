/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.RCLike.Sqrt
import InfoGeometry.Canonical.ThermofieldBidirectionalResonator
import InfoGeometry.Canonical.ThermofieldMobiusResonator

/-!
# Continuous and iterated dynamics of the thermofield Möbius resonator

The carriers and one-step round-trip data are owned by
`ThermofieldBidirectionalResonator` and `ThermofieldMobiusResonator`; this
module adds the continuous evolution operator, the iterated round trip, and
the eigenvalue/readout helpers from the pre-integration snapshot.
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldMobiusResonatorDynamics

open Matrix
open InfoGeometry.Canonical.ThermofieldBidirectionalResonator
open InfoGeometry.Canonical.ThermofieldMobiusResonator

/-- Continuous-time evolution operator `exp (t * generator)`. -/
def evolutionOperator (p : ResonatorParams) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (t • generatorMatrix p)

/-- Continuous evolution of a doubled amplitude under fixed resonator data. -/
def evolveAmplitude (p : ResonatorParams) (t : ℝ) (a : TwinAmplitude) : TwinAmplitude :=
  let U := evolutionOperator p t
  ⟨U 0 0 * a.aPlus + U 0 1 * a.aMinus,
   U 1 0 * a.aPlus + U 1 1 * a.aMinus⟩

/-- Eigenvalues of a normalized round-trip matrix. -/
def roundTripEigenvalues
    (M : ThermofieldBidirectionalResonator.RoundTripMatrix) : ℂ × ℂ :=
  let U := M.toMatrix
  let tr := U 0 0 + U 1 1
  let disc := Complex.sqrt (tr ^ 2 - 4 * U.det)
  ((tr + disc) / 2, (tr - disc) / 2)

/-- Resonance phase condition after `n` round trips. -/
def resonanceCondition
    (M : ThermofieldBidirectionalResonator.RoundTripMatrix) (n : ℕ) : Prop :=
  let (lam1, lam2) := roundTripEigenvalues M
  ‖lam1‖ = 1 ∧ ‖lam2‖ = 1 ∧
    (Complex.arg lam1 = 2 * Real.pi * n ∨ Complex.arg lam2 = 2 * Real.pi * n)

/-- Amplitude after `n` discrete round trips. -/
def roundTripEvolve
    (M : ThermofieldBidirectionalResonator.RoundTripMatrix) (n : ℕ)
    (a : TwinAmplitude) : TwinAmplitude :=
  let UN : Matrix (Fin 2) (Fin 2) ℂ := M.toMatrix ^ n
  ⟨UN 0 0 * a.aPlus + UN 0 1 * a.aMinus,
   UN 1 0 * a.aPlus + UN 1 1 * a.aMinus⟩

end InfoGeometry.Canonical.ThermofieldMobiusResonatorDynamics
