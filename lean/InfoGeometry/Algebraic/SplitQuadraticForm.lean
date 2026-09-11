/-
InfoGeometry/Algebraic/SplitQuadraticForm.lean

Strictly real split quadratic substrate.

This file separates:
  * the real diagonal split quadratic module `ℝ^(n,n)`;
  * the integral hyperbolic Narain charge lattice.
No complex imports.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebraic.SplitSignature

/-- Index type for the split basis. -/
abbrev SplitIndex (n : ℕ) : Type :=
  Sum (Fin n) (Fin n)

/-- The real split module `ℝ^(n,n)`. -/
abbrev SplitModule (n : ℕ) : Type :=
  SplitIndex n → ℝ

/-- Positive sector index. -/
def posIndex {n : ℕ} (i : Fin n) : SplitIndex n :=
  Sum.inl i

/-- Negative sector index. -/
def negIndex {n : ℕ} (i : Fin n) : SplitIndex n :=
  Sum.inr i

/-- Split weights: `+1` on the left sector and `-1` on the right sector. -/
def splitWeight (n : ℕ) : SplitIndex n → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp]
theorem splitWeight_inl {n : ℕ} (i : Fin n) :
    splitWeight n (Sum.inl i) = 1 :=
  rfl

@[simp]
theorem splitWeight_inr {n : ℕ} (i : Fin n) :
    splitWeight n (Sum.inr i) = -1 :=
  rfl

/--
The diagonal split quadratic form of signature `(n,n)`.

`Q(x,y) = ∑ᵢ xᵢ² - ∑ᵢ yᵢ²`.
-/
def splitQuadraticForm (n : ℕ) :
    QuadraticForm ℝ (SplitModule n) :=
  QuadraticMap.weightedSumSquares ℝ (splitWeight n)

@[simp]
theorem splitQuadraticForm_apply
    {n : ℕ} (v : SplitModule n) :
    splitQuadraticForm n v =
      ∑ i : SplitIndex n, splitWeight n i * (v i * v i) := by
  simp [splitQuadraticForm]

/-- Coordinate basis vector in the split module. -/
def splitBasisVector {n : ℕ} (i : SplitIndex n) : SplitModule n :=
  fun j => if j = i then 1 else 0

@[simp]
theorem splitBasisVector_self {n : ℕ} (i : SplitIndex n) :
    splitBasisVector i i = 1 := by
  simp [splitBasisVector]

@[simp]
theorem splitBasisVector_ne {n : ℕ} {i j : SplitIndex n} (h : j ≠ i) :
    splitBasisVector i j = 0 := by
  simp [splitBasisVector, h]

@[simp]
theorem splitQuadraticForm_basisVector
    {n : ℕ} (i : SplitIndex n) :
    splitQuadraticForm n (splitBasisVector i) = splitWeight n i := by
  classical
  simp [splitQuadraticForm, splitBasisVector]

@[simp]
theorem splitQuadraticForm_posBasisVector
    {n : ℕ} (i : Fin n) :
    splitQuadraticForm n (splitBasisVector (Sum.inl i)) = 1 := by
  simpa using splitQuadraticForm_basisVector (n := n) (Sum.inl i)

@[simp]
theorem splitQuadraticForm_negBasisVector
    {n : ℕ} (i : Fin n) :
    splitQuadraticForm n (splitBasisVector (Sum.inr i)) = -1 := by
  simpa using splitQuadraticForm_basisVector (n := n) (Sum.inr i)

/-- The real split Clifford algebra `Cl(n,n)`. -/
abbrev Cl_nn (n : ℕ) : Type :=
  CliffordAlgebra (splitQuadraticForm n)

/-- The real spin group associated to the split Clifford algebra. -/
abbrev Spin_nn (n : ℕ) : Type :=
  spinGroup (splitQuadraticForm n)

/-- Integral Narain charge lattice model. -/
abbrev NarainCharge (n : ℕ) : Type :=
  (Fin n → ℤ) × (Fin n → ℤ)

/-- The even hyperbolic Narain quadratic readout. -/
def narainQuadratic (n : ℕ) (v : NarainCharge n) : ℤ :=
  2 * ∑ i : Fin n, v.1 i * v.2 i

theorem narainQuadratic_even
    {n : ℕ} (v : NarainCharge n) :
    ∃ k : ℤ, narainQuadratic n v = 2 * k := by
  refine ⟨∑ i : Fin n, v.1 i * v.2 i, ?_⟩
  simp [narainQuadratic]

/--
Unnormalized realification of a Narain charge into the split real module.

The compatibility with the diagonal split form is a separate isometry layer.
-/
def narainToSplit {n : ℕ} (v : NarainCharge n) : SplitModule n :=
  fun i =>
    match i with
    | Sum.inl j => ((v.1 j + v.2 j : ℤ) : ℝ)
    | Sum.inr j => ((v.1 j - v.2 j : ℤ) : ℝ)

end InfoGeometry.Algebraic.SplitSignature
