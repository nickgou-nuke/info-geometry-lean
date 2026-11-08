import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.PositiveMeasure
import InfoGeometry.Stratum.Gauge

/-!
# InfoGeometry.Stratum.DiagonalFunctor

Layer 1 → Layer 2 functorial embedding.

Given a finite type `α` equipped with a `PositiveMeasure α ℝ`, we embed it
into the diagonal of a positive definite matrix `Matrix α α ℝ`.
The construction respects the `PosGauge` action: scaling a measure by a
positive scalar corresponds exactly to scaling the resulting diagonal matrix
by the same scalar via the `SMul` instance of matrices.
-/

namespace InfoGeometry.Stratum

open Matrix

noncomputable section

/-- Convert a positive measure on a finite type `α` into a diagonal matrix.
The diagonal entry at `i` is the mass `μ i`. Off‑diagonal entries are zero. -/
@[simp]
def measureToDiagonal {α : Type*} [Fintype α] (μ : PositiveMeasure α ℝ) : Matrix α α ℝ :=
  by
    classical
    exact fun i j => if h : i = j then μ i else 0

/-- The gauge action on positive measures translates to the scalar action on
matrices via `measureToDiagonal`. -/
lemma measureToDiagonal_smul {α : Type*} [Fintype α] (c : ℝ) (hc : 0 < c) (μ : PositiveMeasure α ℝ) :
    measureToDiagonal (InfoGeometry.PositiveMeasure.scale c hc μ) = c • measureToDiagonal μ := by
  classical
  ext i j
  by_cases h : i = j
  · subst h
    simp [measureToDiagonal, InfoGeometry.PositiveMeasure.scale_apply]
  · simp [measureToDiagonal, h]

/-- Functorial map from the commutative layer to the finite non‑commutative layer.
We package the construction as a `MulAction` homomorphism, i.e. a linear map
that respects the `PosGauge` action. -/
structure DiagonalFunctor (α : Type*) [Fintype α] where
  toFun : PositiveMeasure α ℝ → Matrix α α ℝ
  map_smul' : ∀ (c : ℝ) (hc : 0 < c) (μ : PositiveMeasure α ℝ),
    toFun (InfoGeometry.PositiveMeasure.scale c hc μ) = c • toFun μ

/-- The canonical diagonal functor. -/
def diagonalFunctor {α : Type*} [Fintype α] : DiagonalFunctor α :=
  { toFun := measureToDiagonal
    map_smul' := by intro c hc μ; exact measureToDiagonal_smul (α := α) c hc μ }

end

end InfoGeometry.Stratum
