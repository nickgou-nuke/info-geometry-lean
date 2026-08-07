import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier
import InfoGeometry.Canonical.HestenesBivectorSelfDuality

namespace InfoGeometry.Canonical.LorentzSelfDualLieSplit

open CliffordAlgebra TensorProduct
open InfoGeometry.Canonical.HestenesBivectorCarrier
open InfoGeometry.Canonical.HestenesBivectorSelfDuality

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M) [InfoGeometry.Canonical.CliffordParity.HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q]

abbrev sl2c := LieAlgebra.SpecialLinear.sl (n := Fin 2) (R := ℂ)

theorem finrank_sl2c : Module.finrank ℂ sl2c = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  have h_range : Module.finrank ℂ (LinearMap.range (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) = 1 := by
    have trace_surj : LinearMap.range (Matrix.traceLinearMap (Fin 2) ℂ ℂ) = ⊤ := by
      apply LinearMap.range_eq_top.2
      intro x
      use Matrix.diagonal (fun i => if i = 0 then x else 0)
      simp [Matrix.traceLinearMap, Matrix.trace, Matrix.diagonal]
    rw [trace_surj, finrank_top, Module.finrank_self]
  have h_mat : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
    rw [Module.finrank_matrix]
    norm_num
  rw [h_range, h_mat] at h
  have h_ker : Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) = 3 := by
    omega
  exact h_ker

theorem finrank_selfDualProj : Module.finrank ℂ (LinearMap.range (selfDualProj Q)) = 3 := by
  sorry

theorem finrank_antiSelfDualProj : Module.finrank ℂ (LinearMap.range (antiSelfDualProj Q)) = 3 := by
  sorry

/-- The self-dual range is linearly equivalent to sl(2, ℂ). -/
theorem selfDual_linearEquiv_sl2c :
    Nonempty (LinearMap.range (selfDualProj Q) ≃ₗ[ℂ] sl2c) := by
  haveI : Module.Finite ℂ sl2c := Module.finite_of_finrank_pos (by rw [finrank_sl2c]; decide)
  haveI : Module.Finite ℂ (LinearMap.range (selfDualProj Q)) := Module.finite_of_finrank_pos (by rw [finrank_selfDualProj Q]; decide)
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [finrank_selfDualProj Q, finrank_sl2c]

/-- The anti-self-dual range is linearly equivalent to sl(2, ℂ). -/
theorem antiSelfDual_linearEquiv_sl2c :
    Nonempty (LinearMap.range (antiSelfDualProj Q) ≃ₗ[ℂ] sl2c) := by
  haveI : Module.Finite ℂ sl2c := Module.finite_of_finrank_pos (by rw [finrank_sl2c]; decide)
  haveI : Module.Finite ℂ (LinearMap.range (antiSelfDualProj Q)) := Module.finite_of_finrank_pos (by rw [finrank_antiSelfDualProj Q]; decide)
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [finrank_antiSelfDualProj Q, finrank_sl2c]

theorem finrank_complexBivector : Module.finrank ℂ (ComplexBivector Q) = 6 := by
  sorry

/-- The full direct-sum linear equivalence of the complexified bivector space.
    so(1,3)_C ≃ sl(2, ℂ) ⊕ sl(2, ℂ). -/
theorem complexBivector_linearEquiv_directSum :
    Nonempty (ComplexBivector Q ≃ₗ[ℂ] (sl2c × sl2c)) := by
  haveI : Module.Finite ℂ sl2c := Module.finite_of_finrank_pos (by rw [finrank_sl2c]; decide)
  haveI : Module.Finite ℂ (ComplexBivector Q) := Module.finite_of_finrank_pos (by rw [finrank_complexBivector Q]; decide)
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [finrank_complexBivector Q]
  have h1 : Module.finrank ℂ (sl2c × sl2c) = Module.finrank ℂ sl2c + Module.finrank ℂ sl2c := Module.finrank_prod
  rw [h1, finrank_sl2c]

end InfoGeometry.Canonical.LorentzSelfDualLieSplit
