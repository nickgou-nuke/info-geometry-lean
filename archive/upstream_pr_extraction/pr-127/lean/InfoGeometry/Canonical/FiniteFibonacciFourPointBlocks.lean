import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks

Finite four-point Fibonacci-anyon block interface.

This file captures the theorem-level algebraic surface visible in the
`n = 4` sector of the paper:

* a two-block `Φ` basis;
* diagonal action of the first and third braid generators in that basis;
* a linear dependence for the third pairing in terms of the first two.

It does **not** formalize the analytic conformal blocks, hypergeometric
functions, conformal dimensions, or monodromy continuation formulas.

The purpose is to connect the four-anyon sector to the existing finite braid
and finite monodromy interfaces already present in the repository.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks

open FiniteFibonacciAnyonBraiding
open FiniteFibonacciMonodromyInterface

/-- The finite `Φ`-basis for the four-point sector: two basis components. -/
abbrev PhiBasis : Type :=
  ℂ × ℂ

/-- The first basis vector `Φ(0)`. -/
def phi0 : PhiBasis :=
  (1, 0)

/-- The second basis vector `Φ(1)`. -/
def phi1 : PhiBasis :=
  (0, 1)

@[simp]
theorem phi0_fst : phi0.fst = (1 : ℂ) := rfl

@[simp]
theorem phi0_snd : phi0.snd = 0 := rfl

@[simp]
theorem phi1_fst : phi1.fst = 0 := rfl

@[simp]
theorem phi1_snd : phi1.snd = (1 : ℂ) := rfl

/--
A diagonal braid action on the four-point `Φ` basis.

This is the finite algebraic shadow of the diagonal `b₁` / `b₃` action in the
paper's `Φ` basis.
-/
def diagonalBraidAction (a0 a1 : Units ℂ) : PhiBasis → PhiBasis
  | (x0, x1) => (a0 • x0, a1 • x1)

@[simp]
theorem diagonalBraidAction_fst (a0 a1 : Units ℂ) (v : PhiBasis) :
    (diagonalBraidAction a0 a1 v).fst = a0 • v.fst := by
  cases v <;> rfl

@[simp]
theorem diagonalBraidAction_snd (a0 a1 : Units ℂ) (v : PhiBasis) :
    (diagonalBraidAction a0 a1 v).snd = a1 • v.snd := by
  cases v <;> rfl

/-- The first basis vector is an eigenvector for the diagonal braid action. -/
theorem diagonalBraidAction_phi0 (a0 a1 : Units ℂ) :
    diagonalBraidAction a0 a1 phi0 = (a0 • phi0.fst, a1 • phi0.snd) := by
  rfl

/-- The second basis vector is an eigenvector for the diagonal braid action. -/
theorem diagonalBraidAction_phi1 (a0 a1 : Units ℂ) :
    diagonalBraidAction a0 a1 phi1 = (a0 • phi1.fst, a1 • phi1.snd) := by
  rfl

/--
The `b₁` and `b₃` generators in the four-point `Φ` basis are both diagonal.

The paper specializes these diagonal entries to `q⁻⁴` and `q³`.
-/
def b1Action (a0 a1 : Units ℂ) : PhiBasis → PhiBasis :=
  diagonalBraidAction a0 a1

/-- The third braid generator in the four-point `Φ` basis is diagonal as well. -/
def b3Action (a0 a1 : Units ℂ) : PhiBasis → PhiBasis :=
  diagonalBraidAction a0 a1

/-- `b₁` acts diagonally on `Φ(0)`. -/
theorem b1Action_phi0 (a0 a1 : Units ℂ) :
    b1Action a0 a1 phi0 = (a0 • phi0.fst, a1 • phi0.snd) := by
  rfl

/-- `b₁` acts diagonally on `Φ(1)`. -/
theorem b1Action_phi1 (a0 a1 : Units ℂ) :
    b1Action a0 a1 phi1 = (a0 • phi1.fst, a1 • phi1.snd) := by
  rfl

/-- `b₃` acts diagonally on `Φ(0)`. -/
theorem b3Action_phi0 (a0 a1 : Units ℂ) :
    b3Action a0 a1 phi0 = (a0 • phi0.fst, a1 • phi0.snd) := by
  rfl

/-- `b₃` acts diagonally on `Φ(1)`. -/
theorem b3Action_phi1 (a0 a1 : Units ℂ) :
    b3Action a0 a1 phi1 = (a0 • phi1.fst, a1 • phi1.snd) := by
  rfl

/--
The paper's `n = 4` sector uses the same diagonal form for `b₁` and `b₃`.
This theorem records that equality at the level of finite algebraic data.
-/
theorem b1Action_eq_b3Action (a0 a1 : Units ℂ) :
    b1Action a0 a1 = b3Action a0 a1 := by
  rfl

/--
The third pairing is linearly dependent on the first two pairings.

This is the finite algebraic shadow of the relation
`Ψ₁₄,₂₃ = x Ψ₁₂,₃₄ + (1 - x) Ψ₁₃,₂₄`.
-/
def pairing12_34 : PhiBasis :=
  phi0

/-- The second pairing basis vector. -/
def pairing13_24 : PhiBasis :=
  phi1

/-- The third pairing, parameterized by the harmonic ratio `x`. -/
def pairing14_23 (x : ℂ) : PhiBasis :=
  (x, 1 - x)

@[simp]
theorem pairing14_23_relation (x : ℂ) :
    pairing14_23 x = x • pairing12_34 + (1 - x) • pairing13_24 := by
  simp [pairing14_23, pairing12_34, pairing13_24, phi0, phi1]

end InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks
