-- SPDX-FileCopyrightText: 2024–2026 The InfoGeometry Authors
-- SPDX-License-Identifier: MIT

/-
# Peirce ⟷ Critical-Mirror Bridge

Joins the **Peirce/Krein cluster** (`PauliPeirceKreinBridge`,
`PolarizedPeirceSignBridge`) to the **zeta critical-line cluster**
(`Arithmetic.ZetaCoordinateSymmetry`, `Canonical.ZetaChiralConeAlgebra`).

## The shared object

Both clusters are built from the *same* algebraic device: the normalized `±1`
projection pair attached to an involution,

  `P± = (I ± χ) / 2`,   `χ² = 1`.

- In `PauliPeirceKreinBridge` the involution is the Pauli generator
  `χ = Eplus = σ₃` on `Mat₂(ℝ) = Cl(1,1)`, and `P±` are the Peirce corners; the
  double real Krein carrier's fundamental symmetry `ε` was proved to be that same
  `χ`, so the Krein `±1` eigensheets *are* the Peirce corners.

- In `ZetaCoordinateSymmetry` the involution is `criticalMirror = ⟨−u, v⟩` on
  centered zeta coordinates, and `criticalTangentProjector` /`criticalNormalProjector`
  are its `±1` projectors — the repo already documents them as *"(I + J)/2"* and
  *"(I − J)/2)"*.

- In `ZetaChiralConeAlgebra` the involution is the conjugate-linear `JAction` on zeta
  readouts, with `JPlusProjector = ½(F + J F)` and `JMinusProjector = ½(F − J F)`.

These are distinct carriers, not literally one operator or one eigenspace. This
module records their shared normalized-involution construction and proves an
explicit injective coordinate map from the centered zeta plane into the diagonal
Pauli matrices. It does not identify the full zeta readout space with the Krein space.

## What is proved here

1. The source owner `ZetaCoordinateSymmetry` supplies the critical-mirror projector
   algebra; this file reuses that API rather than duplicating those laws.
3. A concrete coordinate map identifies the critical tangent/normal components with
   left multiplication by the two Pauli Peirce projectors on diagonal matrices.
4. The map is injective by its explicit left inverse; no identification of ambient
   operators or analytic meanings is asserted.

## What is NOT claimed

This module does **not** prove the Riemann functional equation, Schwarz reflection, or
the Riemann Hypothesis; it does not construct the completed `ξ` function, nor the
dilation operator `−i(x ∂ₓ + ½)`. Following the discipline of
`ZetaChiralConeAlgebra`, analytic claims are not inferred from these finite
coordinate identities.

All proofs are native Lean 4 over Mathlib: no `sorry`, no axioms, no certificates, no
structure fields carrying the theorem.
-/

import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.ZetaChiralConeAlgebra
import InfoGeometry.Physics.DilationMetaplecticOperator

noncomputable section

namespace InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-! ## 1. Coordinate transport to the diagonal Pauli carrier

The zeta coordinate plane embeds into the diagonal subalgebra of `Mat₂(ℝ)` as a real
coordinate carrier. The order `(v,u)` makes the critical tangent projection
correspond to the `+1` Pauli corner and the normal projection to the `-1` corner.
This is an explicit transport theorem, not an identification of ambient operators. -/

abbrev CriticalPeirceMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Encode tangent coordinate `v` in the positive Pauli corner and normal coordinate
`u` in the negative corner. -/
def criticalToPeirceDiagonal (x : ZetaCenteredChart) : CriticalPeirceMatrix :=
  !![x.v, 0; 0, x.u]

/-- Read diagonal Peirce coordinates back as centered coordinates `(u,v)`. -/
def peirceDiagonalToCritical (M : CriticalPeirceMatrix) : ZetaCenteredChart :=
  ⟨M 1 1, M 0 0⟩

/-- The coordinate encoding has the displayed inverse. -/
theorem peirceDiagonalToCritical_criticalToPeirceDiagonal (x : ZetaCenteredChart) :
    peirceDiagonalToCritical (criticalToPeirceDiagonal x) = x := by
  cases x
  rfl

/-- The tangent projector transports to left multiplication by the positive Peirce
projector. -/
theorem criticalTangent_transports_to_Pleft (x : ZetaCenteredChart) :
    criticalToPeirceDiagonal (criticalTangentProjector x) =
      pauliChiral.Pleft * criticalToPeirceDiagonal x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [criticalToPeirceDiagonal, criticalTangentProjector,
      pauliChiral_Pleft, Matrix.mul_apply, Fin.sum_univ_two]

/-- The normal projector transports to left multiplication by the negative Peirce
projector. -/
theorem criticalNormal_transports_to_Pright (x : ZetaCenteredChart) :
    criticalToPeirceDiagonal (criticalNormalProjector x) =
      pauliChiral.Pright * criticalToPeirceDiagonal x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [criticalToPeirceDiagonal, criticalNormalProjector,
      pauliChiral_Pright, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 2. Functional duality and the critical mirror are distinct coordinate maps

In centered coordinates functional duality is `(u,v) ↦ (-u,-v)`, whereas the
critical-mirror coordinate reflection is `(u,v) ↦ (-u,v)`. They agree only on
the real `u` coordinate; conflating the full maps loses the imaginary-coordinate sign.
-/
/-- The functional dual therefore **fixes the critical line**: `σ = ½` is the seam. -/
theorem criticalLine_fixed_by_functionalDual {z : ZetaAffineChart}
    (hz : chartCriticalLine z) : chartCriticalLine (chartFunctionalDual z) := by
  rw [chartCriticalLine] at hz ⊢
  rw [chartFunctionalDual, hz]
  ring

/-! ## 3. Unconditional coordinate symmetry of the critical line -/

/-- Conjugation preserves the real coordinate, hence preserves the critical line. -/
theorem criticalLine_invariant_under_conjugation {z : ZetaAffineChart}
    (hz : chartCriticalLine z) : chartCriticalLine (chartConjugation z) := by
  simpa [chartCriticalLine, chartConjugation] using hz

/-! ## 4. The algebraic dilation shadow

The operator-level owner already proves the exact eigenvalue equation for the
Mellin mode.  This bridge only transports its real-eigenvalue consequence; it
adds no analytic premise and makes no claim about the distribution of zeta
zeros.
-/

/-- A real dilation eigenvalue forces the centered spectral parameter to lie on
`Re(s) = 1/2`. -/
theorem dilation_real_eigenvalue_forces_critical
    (s : ℂ) (E : ℝ)
    (hE : InfoGeometry.Physics.DilationMetaplectic.eigenvalue s = (E : ℂ)) :
    s.re = 1 / 2 := by
  apply (InfoGeometry.Physics.DilationMetaplectic.eigenvalue_im_eq_zero_iff s).mp
  simpa using congrArg Complex.im hE

end InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

end
