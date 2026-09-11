import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# InfoGeometry.Analysis.SouriauThermodynamics

Repaired finite Souriau thermodynamics core salvaged from deleted material.

This file keeps only kernel-checkable algebraic content:

* the trace-zero `2 × 2` complex matrix carrier as a real submodule;
* linear dual readouts;
* the affine cocycle readout formula as data;
* the elementary Bregman identity at equal temperatures.

It does not claim a global Souriau coadjoint-orbit theorem.
-/

open Matrix BigOperators

namespace InfoGeometry.Analysis

/-! ### 1. Trace-zero carrier and dual readouts -/

/-- The trace-zero `2 × 2` complex matrices, as a real submodule. -/
noncomputable def sl2cSubmodule : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {M | M.trace = 0}
  zero_mem' := by
    simp
  add_mem' := by
    intro A B hA hB
    change (A + B).trace = 0
    rw [Matrix.trace_add, hA, hB]
    simp
  smul_mem' := by
    intro c A hA
    change (c • A).trace = 0
    rw [Matrix.trace_smul, hA]
    simp

/-- The Lie-algebra carrier used here: trace-zero `2 × 2` complex matrices. -/
noncomputable abbrev SL2cAlgebra := sl2cSubmodule

/-- Linear real-valued readouts on the trace-zero carrier. -/
abbrev SL2cDual := SL2cAlgebra →ₗ[ℝ] ℝ

/-- Canonical evaluation pairing between a linear readout and a temperature vector. -/
noncomputable def souriauPairing (M : SL2cDual) (β : SL2cAlgebra) : ℝ :=
  M β

/-! ### 2. Affine cocycle readout -/

/--
A finite matrix readout modeled on Souriau's affine cocycle term.
It is a readout formula only; no cocycle law for a concrete group action is
claimed here.
-/
noncomputable def souriauCocycleReadout
    (g : Matrix (Fin 2) (Fin 2) ℂ) : SL2cAlgebra → ℝ :=
  fun β => Complex.re (g * β.val).trace

/-- Affine coadjoint-style transformation supplied with an external linear action. -/
noncomputable def affineCoadjointAction
    (g : Matrix (Fin 2) (Fin 2) ℂ)
    (M : SL2cDual)
    (AdStar : SL2cDual → SL2cAlgebra → ℝ) : SL2cAlgebra → ℝ :=
  fun β => AdStar M β + souriauCocycleReadout g β

/-! ### 3. Bregman divergence gap -/

/--
The finite Souriau/Bregman divergence expression.  The differential readout is
linear, so its value at `β₁ - β₂` vanishes when `β₁ = β₂`.
-/
noncomputable def souriauBregmanDivergence
    (Φ : SL2cAlgebra → ℝ)
    (nablaΦ : SL2cAlgebra → SL2cDual)
    (β₁ β₂ : SL2cAlgebra) : ℝ :=
  let M₂ := nablaΦ β₂
  Φ β₁ - Φ β₂ - souriauPairing M₂ (β₁ - β₂)

/-- The Bregman gap vanishes at equal temperatures. -/
theorem bregman_gap_identity
    (Φ : SL2cAlgebra → ℝ)
    (nablaΦ : SL2cAlgebra → SL2cDual)
    (β : SL2cAlgebra) :
    souriauBregmanDivergence Φ nablaΦ β β = 0 := by
  simp [souriauBregmanDivergence, souriauPairing]

end InfoGeometry.Analysis
