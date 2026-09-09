import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Trace-zero complex Cartan line

The associative algebra `M₂(ℂ)` is not itself the Lie algebra `sl₂(ℂ)`.
For the finite matrix realization used by the bipolar construction, the exact
Lie-algebra carrier is the trace-zero submodule, with bracket given by the
matrix commutator.  The logarithmic generator lies in the one-dimensional
complex line spanned by `σ3c` inside that trace-zero carrier.

This file proves only the required finite statements.  It does not assert the
full Lie-group equivalence `Spin⁺(1,3) ≃ SL₂(ℂ)` or the complexified Lorentz
identity `so(4,ℂ) ≃ sl₂(ℂ) ⊕ sl₂(ℂ)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarComplexCartanLine

open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Trace-zero `2 × 2` complex matrices, the finite carrier underlying
`sl₂(ℂ)` in this development. -/
def traceZeroMatrices : Submodule ℂ Matrix2C where
  carrier := {X | Matrix.trace X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change Matrix.trace X = 0 at hX
    change Matrix.trace Y = 0 at hY
    have hX' : X 0 0 + X 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hX
    have hY' : Y 0 0 + Y 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hY
    simp [Matrix.trace, Matrix.add_apply, Fin.sum_univ_two]
    linear_combination hX' + hY'
  smul_mem' := by
    intro c X hX
    change Matrix.trace X = 0 at hX
    have hX' : X 0 0 + X 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hX
    simp [Matrix.trace, Matrix.smul_apply, Fin.sum_univ_two]
    linear_combination c * hX'

@[simp] theorem mem_traceZeroMatrices (X : Matrix2C) :
    X ∈ traceZeroMatrices ↔ Matrix.trace X = 0 :=
  by change (X ∈ ({X | Matrix.trace X = 0} : Set Matrix2C) ↔ _); rfl

/-- The diagonal Pauli grading matrix is trace zero. -/
theorem sigma3c_mem_traceZeroMatrices :
    σ3c ∈ traceZeroMatrices := by
  rw [mem_traceZeroMatrices]
  simp [σ3c, Matrix.trace, Fin.sum_univ_two]

/-- The complex Cartan line used by the bipolar logarithmic lift. -/
def cartanLine : Submodule ℂ Matrix2C :=
  Submodule.span ℂ ({σ3c} : Set Matrix2C)

/-- The Cartan line lies inside the trace-zero matrix carrier. -/
theorem cartanLine_le_traceZeroMatrices :
    cartanLine ≤ traceZeroMatrices := by
  rw [cartanLine]
  refine Submodule.span_le.2 ?_
  intro X hX
  have hEq : X = σ3c := Set.mem_singleton_iff.mp hX
  rw [hEq]
  exact sigma3c_mem_traceZeroMatrices

/-- Every element of the line is a scalar multiple of `σ3c`. -/
theorem cartanLine_normal_form
    {X : Matrix2C} (hX : X ∈ cartanLine) :
    ∃ c : ℂ, c • σ3c = X := by
  exact Submodule.mem_span_singleton.mp hX

/-- The line is abelian for the matrix commutator. -/
theorem cartanLine_commutator_zero
    {X Y : Matrix2C} (hX : X ∈ cartanLine) (hY : Y ∈ cartanLine) :
    X * Y - Y * X = 0 := by
  rcases cartanLine_normal_form hX with ⟨a, rfl⟩
  rcases cartanLine_normal_form hY with ⟨b, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ3c, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring

/-- The noncompact coefficient belongs to the complex Cartan line. -/
theorem Kboost_mem_cartanLine : Kboost ∈ cartanLine := by
  rw [Kboost, cartanLine]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton σ3c))

/-- The compact coefficient belongs to the same complex Cartan line. -/
theorem Kcirc_mem_cartanLine : Kcirc ∈ cartanLine := by
  rw [Kcirc, cartanLine]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton σ3c))

/-- Every point-dependent logarithmic Cartan generator belongs to the same
trace-zero complex line. -/
theorem bipolarLogarithmicCartan_mem_cartanLine (s : ℂ) :
    bipolarLogarithmicCartan s ∈ cartanLine := by
  rw [bipolarLogarithmicCartan]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ Kboost_mem_cartanLine)
    (Submodule.smul_mem _ _ Kcirc_mem_cartanLine)

/-- Hence the logarithmic generator is trace zero. -/
theorem bipolarLogarithmicCartan_trace_zero (s : ℂ) :
    Matrix.trace (bipolarLogarithmicCartan s) = 0 := by
  rw [← mem_traceZeroMatrices]
  exact cartanLine_le_traceZeroMatrices
    (bipolarLogarithmicCartan_mem_cartanLine s)

/-- Compact exact-carrier packet. -/
theorem bipolar_complex_cartan_line_packet (s : ℂ) :
    Kboost ∈ cartanLine ∧
      Kcirc ∈ cartanLine ∧
      bipolarLogarithmicCartan s ∈ cartanLine ∧
      Matrix.trace (bipolarLogarithmicCartan s) = 0 ∧
      ∀ {X Y : Matrix2C},
        X ∈ cartanLine → Y ∈ cartanLine → X * Y - Y * X = 0 := by
  exact ⟨Kboost_mem_cartanLine,
    Kcirc_mem_cartanLine,
    bipolarLogarithmicCartan_mem_cartanLine s,
    bipolarLogarithmicCartan_trace_zero s,
    fun hX hY => cartanLine_commutator_zero hX hY⟩

end InfoGeometry.Canonical.BipolarComplexCartanLine
