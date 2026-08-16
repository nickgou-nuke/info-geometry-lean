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

/-! The two spectral readouts are genuine idempotent projections. -/

theorem selfDualPart_idempotent (F : TwoFormC) :
    selfDualPart (selfDualPart F) = selfDualPart F := by
  have h := hodgeStar_selfDualPart F
  funext i
  dsimp [selfDualPart]
  rw [congrFun h i]
  calc (selfDualPart F i - Complex.I * (Complex.I * selfDualPart F i)) / 2
    _ = (selfDualPart F i - (Complex.I * Complex.I) * selfDualPart F i) / 2 := by ring
    _ = (selfDualPart F i - (-1) * selfDualPart F i) / 2 := by rw [Complex.I_mul_I]
    _ = selfDualPart F i := by ring

theorem antiSelfDualPart_idempotent (F : TwoFormC) :
    antiSelfDualPart (antiSelfDualPart F) = antiSelfDualPart F := by
  have h := hodgeStar_antiSelfDualPart F
  funext i
  dsimp [antiSelfDualPart]
  rw [congrFun h i]
  calc (antiSelfDualPart F i + Complex.I * (-Complex.I * antiSelfDualPart F i)) / 2
    _ = (antiSelfDualPart F i - (Complex.I * Complex.I) * antiSelfDualPart F i) / 2 := by ring
    _ = (antiSelfDualPart F i - (-1) * antiSelfDualPart F i) / 2 := by rw [Complex.I_mul_I]
    _ = antiSelfDualPart F i := by ring

theorem selfDualPart_antiSelfDualPart_zero (F : TwoFormC) :
    selfDualPart (antiSelfDualPart F) = 0 := by
  have h := hodgeStar_antiSelfDualPart F
  funext i
  change (antiSelfDualPart F i - Complex.I * hodgeStar (antiSelfDualPart F) i) / 2 = 0
  rw [congrFun h i]
  dsimp [antiSelfDualPart]
  ring_nf
  simp [Complex.I_sq]

theorem antiSelfDualPart_selfDualPart_zero (F : TwoFormC) :
    antiSelfDualPart (selfDualPart F) = 0 := by
  have h := hodgeStar_selfDualPart F
  funext i
  change (selfDualPart F i + Complex.I * hodgeStar (selfDualPart F) i) / 2 = 0
  rw [congrFun h i]
  dsimp [selfDualPart]
  ring_nf
  simp [Complex.I_sq]

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
