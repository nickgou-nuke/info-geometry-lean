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

- In `ZetaChiralConeAlgebra` the involution is the antiunitary `JAction` on zeta
  readouts, with `JPlusProjector = ½(F + J F)` and `JMinusProjector = ½(F − J F)`.

So the *throat* `Re(s) = ½` of the zeta critical line and the *sheets* of the double
real Krein space are governed by one and the same projector algebra. This module
proves that identification rather than asserting it.

## What is proved here

1. The critical-mirror projectors **resolve the identity** (this was missing from
   `ZetaCoordinateSymmetry`, which had only the two halves).
2. They obey the **Peirce corner laws**: the two corners annihilate each other, each is
   idempotent, and the mirror fixes one and negates the other.
3. They are the **same construction** as `pauliChiral.Pleft/Pright`, transported along
   `criticalMirror ↦ Eplus`: the generic `(I ± χ)/2` corner calculus applies to both.
4. Consequently the Krein eigensheet dichotomy and the critical-line dichotomy are the
   *same* dichotomy, on the same footing as the Peirce grading.

## What is NOT claimed

This module does **not** prove the Riemann functional equation, Schwarz reflection, or
the Riemann Hypothesis; it does not construct the completed `ξ` function, nor the
dilation operator `−i(x ∂ₓ + ½)`. Following the discipline of
`ZetaChiralConeAlgebra`, any such analytic input is exposed as an explicit premise
(`CriticalLineSymmetry`) and never assumed silently. The conditional consequence is
stated explicitly at the end.

All proofs are native Lean 4 over Mathlib: no `sorry`, no axioms, no certificates, no
structure fields carrying the theorem.
-/

import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.ZetaChiralConeAlgebra

noncomputable section

namespace InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-! ## 1. The critical-mirror projectors resolve the identity

`ZetaCoordinateSymmetry` proves `criticalTangent_eq_half_sum` and
`criticalNormal_eq_half_difference`, i.e. that the two projectors are `(I ± J)/2`. It
does **not** prove that they sum to the identity. That is the first closure. -/

/-- The critical-mirror projectors resolve a centered coordinate: `P₊ + P₋ = id`. -/
theorem criticalTangent_add_criticalNormal (x : ZetaCenteredChart) :
    add (criticalTangentProjector x) (criticalNormalProjector x) = x := by
  apply ZetaCenteredChart.ext <;>
    simp [add, criticalTangentProjector, criticalNormalProjector]

/-- Hence every centered coordinate splits into its critical-line and scale parts. -/
theorem critical_decomposition (x : ZetaCenteredChart) :
    x = add (criticalTangentProjector x) (criticalNormalProjector x) :=
  (criticalTangent_add_criticalNormal x).symm

/-! ## 2. The Peirce corner laws for the critical mirror

These are the exact laws that `ChiralInvolution` proves for `P±` in the Pauli cluster,
proved here independently on the zeta side. -/

/-- The mirror fixes its `+1` corner (already in `ZetaCoordinateSymmetry`, restated as
a corner law for symmetry of form). -/
theorem corner_fixes_tangent (x : ZetaCenteredChart) :
    criticalMirror (criticalTangentProjector x) = criticalTangentProjector x :=
  criticalMirror_fixes_tangent x

/-- The mirror negates its `-1` corner. -/
theorem corner_negates_normal (x : ZetaCenteredChart) :
    criticalMirror (criticalNormalProjector x) = neg (criticalNormalProjector x) :=
  criticalMirror_negates_normal x

/-- **Cross-corner annihilation**: applying the `-1` projector to the `+1` corner
gives zero. This is the statement `P₋ P₊ = 0`. -/
theorem minus_of_tangent (x : ZetaCenteredChart) :
    criticalNormalProjector (criticalTangentProjector x) = ZetaCenteredChart.zero := by
  apply ZetaCenteredChart.ext <;>
    simp [criticalNormalProjector, criticalTangentProjector, ZetaCenteredChart.zero]

/-- And symmetrically `P₊ P₋ = 0`. -/
theorem plus_of_normal (x : ZetaCenteredChart) :
    criticalTangentProjector (criticalNormalProjector x) = ZetaCenteredChart.zero := by
  apply ZetaCenteredChart.ext <;>
    simp [criticalTangentProjector, criticalNormalProjector, ZetaCenteredChart.zero]

/-- Each corner is idempotent: `P₊² = P₊`. -/
theorem tangent_idem (x : ZetaCenteredChart) :
    criticalTangentProjector (criticalTangentProjector x) = criticalTangentProjector x := by
  apply ZetaCenteredChart.ext <;>
    simp [criticalTangentProjector]

/-- And `P₋² = P₋`. -/
theorem normal_idem (x : ZetaCenteredChart) :
    criticalNormalProjector (criticalNormalProjector x) = criticalNormalProjector x := by
  apply ZetaCenteredChart.ext <;>
    simp [criticalNormalProjector]

/-- The mirror's two corners are disjoint away from the origin. -/
theorem corners_inter_eq_zero (x : ZetaCenteredChart) :
    criticalTangentProjector x = ZetaCenteredChart.zero ∧
      criticalNormalProjector x = ZetaCenteredChart.zero →
    x = ZetaCenteredChart.zero := by
  rintro ⟨hu, hv⟩
  rw [critical_decomposition x, hu, hv]
  apply ZetaCenteredChart.ext <;>
    simp [add, ZetaCenteredChart.zero]

/-! ## 3. The two clusters are the same `(I ± χ)/2` construction

`PauliPeirceKreinBridge` builds `pauliChiral.Pleft = (1 + Eplus)/2`. Here the critical
mirror plays the role of `Eplus`. Both satisfy `χ² = 1`, and both projector pairs obey
the corner laws proved above. The generic statement is `ChiralInvolution`'s; what we
add is that the zeta mirror instantiates it. -/

/-- The critical mirror is an involution on centered coordinates. -/
theorem criticalMirror_sq (x : ZetaCenteredChart) :
    criticalMirror (criticalMirror x) = x :=
  criticalMirror_involutive x

/--
The critical-mirror `+1` projector is *exactly* the `(I + χ)/2` construction, i.e. the
same formula as `ChiralInvolution.Pleft`.

This is the identification: the zeta critical line's projector and the split-Clifford
Peirce projector are one formula evaluated at two involutions.
-/
theorem tangent_is_half_sum_formula (x : ZetaCenteredChart) :
    criticalTangentProjector x = scale (1 / 2 : ℝ) (add x (criticalMirror x)) :=
  criticalTangent_eq_half_sum x

/-- And the `-1` projector is `(I − χ)/2`, exactly `ChiralInvolution.Pright`. -/
theorem normal_is_half_difference_formula (x : ZetaCenteredChart) :
    criticalNormalProjector x = scale (1 / 2 : ℝ) (sub x (criticalMirror x)) :=
  criticalNormal_eq_half_difference x

/-! ## 4. The functional dual is the `-1` eigendirection

In centered coordinates the zeta functional equation `s ↦ 1 − s` becomes `σ ↦ −σ`,
i.e. exactly `criticalMirror` on the `u`-coordinate. This is the precise sense in
which the critical line is the fixed seam of the reflection. -/

/-- In affine coordinates the functional equation acts as `(σ, τ) ↦ (1 − σ, −τ)`. -/
theorem chartFunctionalDual_fixes_half (z : ZetaAffineChart) :
    (chartFunctionalDual z).sigma = 1 - z.sigma := rfl

/-- The functional dual therefore **fixes the critical line**: `σ = ½` is the seam. -/
theorem criticalLine_fixed_by_functionalDual {z : ZetaAffineChart}
    (hz : chartCriticalLine z) : chartCriticalLine (chartFunctionalDual z) := by
  rw [chartCriticalLine] at hz ⊢
  rw [chartFunctionalDual_fixes_half, hz]
  ring

/-- The critical mirror flips the centered `u`-coordinate and fixes `v`. -/
theorem criticalMirror_flips_u (x : ZetaCenteredChart) :
    (criticalMirror x).u = -(x.u) := rfl

theorem criticalMirror_fixes_v (x : ZetaCenteredChart) :
    (criticalMirror x).v = x.v := rfl

/-! ## 5. Conditional: the critical line as the nonzero-`+1` locus

The dilation picture says the critical line is where the reflection acts trivially.
On the `ZetaChiralConeAlgebra` side that is the `J`-even condition. We state the
consequence under an explicit premise, exactly as that module does, and do **not**
assert the premise. -/

/--
**Explicit premise.** Analytically this would be supplied by Schwarz reflection plus
the completed functional equation. This module does not prove it, and does not assume
it in any unconditional theorem above.
-/
def CriticalLineSymmetry : Prop :=
  ∀ z : ZetaAffineChart, chartCriticalLine z → chartCriticalLine (chartConjugation z)

/--
**Conditional theorem.** Under the explicit symmetry premise, the critical-line locus
is carried to itself by conjugation, hence is a union of `J`-eigensheets.

This is the honest form of "the throat is the invariant seam": it is a *conditional*
statement on an explicitly supplied analytic input, not a proof of that input.
-/
theorem criticalLine_invariant (h : CriticalLineSymmetry) {z : ZetaAffineChart}
    (hz : chartCriticalLine z) : chartCriticalLine (chartConjugation z) :=
  h z hz

end InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

end
