import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.DiscreteStokesFinite

Finite cochain owner for the Stokes/topological-language corridor.

This file does not construct smooth manifolds, differential forms, exterior
calculus, integration theory, de Rham cohomology, Chern classes, instantons, or
topological quantum numbers.  It closes the smallest honest combinatorial
surface behind the slogan `∫ dω = ∫∂ ω`: the oriented `2`-simplex with vertices
`0,1,2`.

The oriented edge order is `(01, 12, 02)`.  The oriented boundary of the face
`012` is `01 + 12 - 02`.

#### BUCKET 1: CLOSED FINITE THEOREMS
`finite_stokes`, `d1_d0_eq_zero`, and `boundary1_boundary2_eq_zero`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Smooth exterior derivatives, integration over manifolds, Stokes' theorem for
chains, de Rham cohomology, Hodge decomposition, characteristic classes,
instanton number integrality, and physical topological charge laws.
-/

namespace InfoGeometry.Canonical.DiscreteStokesFinite

/-- Scalar functions on the three vertices of the oriented triangle. -/
abbrev ZeroCochain : Type :=
  Fin 3 → ℝ

/-- One-cochains on the ordered edges `(01, 12, 02)`. -/
abbrev OneCochain : Type :=
  Fin 3 → ℝ

/-- Two-cochains on the single oriented face `012`. -/
abbrev TwoCochain : Type :=
  ℝ

/-- Coboundary of a zero-cochain on the ordered edges `(01, 12, 02)`. -/
def d0 (f : ZeroCochain) : OneCochain
  | 0 => f 1 - f 0
  | 1 => f 2 - f 1
  | 2 => f 2 - f 0

/-- Coboundary of a one-cochain evaluated on the oriented face `012`. -/
def d1 (a : OneCochain) : TwoCochain :=
  a 0 + a 1 - a 2

/-- Boundary integral around `∂[012] = [01] + [12] - [02]`. -/
def boundaryIntegral (a : OneCochain) : ℝ :=
  a 0 + a 1 - a 2

/-- Bulk integral of a two-cochain over the single face. -/
def bulkIntegral (b : TwoCochain) : ℝ :=
  b

/-- Finite Stokes law on one oriented triangle. -/
theorem finite_stokes (a : OneCochain) :
    bulkIntegral (d1 a) = boundaryIntegral a := by
  rfl

/-- Exact one-cochains are closed: `d₁ (d₀ f) = 0`. -/
theorem d1_d0_eq_zero (f : ZeroCochain) :
    d1 (d0 f) = 0 := by
  simp [d0, d1]

/-- Zero-chains indexed by vertices. -/
abbrev ZeroChain : Type :=
  Fin 3 → ℝ

/-- One-chains indexed by ordered edges `(01, 12, 02)`. -/
abbrev OneChain : Type :=
  Fin 3 → ℝ

/-- Two-chains indexed by the single face. -/
abbrev TwoChain : Type :=
  ℝ

/-- Boundary of a one-chain as signed endpoint incidence. -/
def boundary1 (e : OneChain) : ZeroChain := fun v =>
  match v with
  | 0 => -e 0 - e 2
  | 1 => e 0 - e 1
  | 2 => e 1 + e 2

/-- Boundary of the oriented face `012` in edge coordinates `(01, 12, 02)`. -/
def boundary2 (t : TwoChain) : OneChain
  | 0 => t
  | 1 => t
  | 2 => -t

/-- Boundary of a boundary vanishes for the oriented triangle. -/
theorem boundary1_boundary2_eq_zero (t : TwoChain) :
    boundary1 (boundary2 t) = 0 := by
  ext v
  fin_cases v <;> simp [boundary1, boundary2]

end InfoGeometry.Canonical.DiscreteStokesFinite
