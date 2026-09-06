/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Clifford.HestenesBivectorSpinLift

namespace InfoGeometry.Exceptional.G2SpinPhase

open InfoGeometry.Algebra.Clifford

abbrev RootCarrier := Fin 12 → ℂ
abbrev RootOperator := Module.End ℂ RootCarrier

/-! Concrete phase data on the root carrier.  This contract does not identify
the phase operator with a permutation product; that is a separate bridge. -/
structure G2SpinPhaseData where
  B : RootOperator
  inv2 : ℂ
  sqrt3 : ℂ
  h2 : (2 : ℂ) * (inv2 : ℂ) = 1
  h3 : (sqrt3 : ℂ) ^ 2 = 3
  B_sq : IsChiralBivector B
  phase : RootOperator
  phase_eq : phase = cyclotomicPhase B inv2 sqrt3

theorem phase_pow_six (d : G2SpinPhaseData) : d.phase ^ 6 = -1 := by
  rw [d.phase_eq]
  exact cyclotomic_phase_pow_six d.B d.inv2 d.sqrt3 d.h2 d.h3 d.B_sq

theorem phase_pow_twelve (d : G2SpinPhaseData) : d.phase ^ 12 = 1 := by
  rw [d.phase_eq]
  exact cyclotomic_phase_pow_twelve d.B d.inv2 d.sqrt3 d.h2 d.h3 d.B_sq

end InfoGeometry.Exceptional.G2SpinPhase
