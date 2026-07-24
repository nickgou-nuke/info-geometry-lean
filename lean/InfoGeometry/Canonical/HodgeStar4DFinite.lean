import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.HodgeStar4DFinite

Finite owner for the four-dimensional Hodge-star claim on two-forms.

This file does not construct a smooth oriented pseudo-Riemannian manifold,
differential forms on bundles, integration, de Rham cohomology, instantons, or
Yang-Mills equations.  It closes the finite six-component Lorentzian two-form
shadow: `*² = -1`, the complex `±i` eigenspace projections, and their exact
reconstruction of the input two-form.

The component order is `(01, 02, 03, 23, 31, 12)`, and the chosen Lorentzian
star convention is

`01 ↦ 23`, `02 ↦ 31`, `03 ↦ 12`, `23 ↦ -01`, `31 ↦ -02`, `12 ↦ -03`.

#### BUCKET 1: CLOSED FINITE THEOREMS
`hodgeStar_sq`, `hodgeStar_selfDualPart`, `hodgeStar_antiSelfDualPart`,
`self_plus_anti`, and `self_minus_anti_star`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Smooth Hodge theory, metric-derived orientation, exterior derivative, Stokes'
theorem, harmonic decomposition, topological charges, instantons, Maxwell /
Yang-Mills equations, and physical field dynamics.
-/

namespace InfoGeometry.Canonical.HodgeStar4DFinite

/-- Complexified finite carrier for two-forms in four dimensions. -/
abbrev TwoFormC : Type :=
  Fin 6 → ℂ

/--
Finite Lorentzian Hodge-star shadow on the ordered two-form basis
`(01, 02, 03, 23, 31, 12)`.
-/
def hodgeStar (F : TwoFormC) : TwoFormC
  | 0 => F 3
  | 1 => F 4
  | 2 => F 5
  | 3 => -F 0
  | 4 => -F 1
  | 5 => -F 2

/-- On Lorentzian two-forms in four dimensions, the finite star squares to `-1`. -/
theorem hodgeStar_sq (F : TwoFormC) :
    hodgeStar (hodgeStar F) = -F := by
  ext i
  fin_cases i <;> simp [hodgeStar]

/-- The `+i` eigenspace projection for the finite Hodge star. -/
noncomputable def selfDualPart (F : TwoFormC) : TwoFormC :=
  fun i => (F i - Complex.I * hodgeStar F i) / 2

/-- The `-i` eigenspace projection for the finite Hodge star. -/
noncomputable def antiSelfDualPart (F : TwoFormC) : TwoFormC :=
  fun i => (F i + Complex.I * hodgeStar F i) / 2

/-- The self-dual part is a `+i` eigenvector of the finite Lorentzian Hodge star. -/
theorem hodgeStar_selfDualPart (F : TwoFormC) :
    hodgeStar (selfDualPart F) = fun i => Complex.I * selfDualPart F i := by
  ext i
  fin_cases i <;> simp [selfDualPart, hodgeStar]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring_nf

/-- The anti-self-dual part is a `-i` eigenvector of the finite Lorentzian Hodge star. -/
theorem hodgeStar_antiSelfDualPart (F : TwoFormC) :
    hodgeStar (antiSelfDualPart F) = fun i => -Complex.I * antiSelfDualPart F i := by
  ext i
  fin_cases i <;> simp [antiSelfDualPart, hodgeStar]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring_nf

/-- The self-dual and anti-self-dual projections reconstruct the input form. -/
theorem self_plus_anti (F : TwoFormC) :
    (fun i => selfDualPart F i + antiSelfDualPart F i) = F := by
  ext i
  simp [selfDualPart, antiSelfDualPart]
  ring

/-- Their difference recovers the finite Hodge-star image up to the `-i` factor. -/
theorem self_minus_anti_star (F : TwoFormC) :
    (fun i => selfDualPart F i - antiSelfDualPart F i) =
      fun i => -Complex.I * hodgeStar F i := by
  ext i
  simp [selfDualPart, antiSelfDualPart]
  ring

end InfoGeometry.Canonical.HodgeStar4DFinite
