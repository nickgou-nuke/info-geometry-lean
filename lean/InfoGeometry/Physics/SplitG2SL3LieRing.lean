import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Derivation.AdjointAction
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The concrete trace-zero `sl₃(ℝ)` Lie ring

The carrier is the kernel of the matrix-trace linear map.  The bracket is the
matrix commutator.  This is an actual Mathlib `LieRing` instance; no claim
about a split-octonion realization is made here.
-/

namespace InfoGeometry.Physics.SplitG2SL3LieRing

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

noncomputable def traceMap : Matrix3 →ₗ[ℝ] ℝ where
  toFun M := Matrix.trace M
  map_add' M N := by simp
  map_smul' c M := by simp

noncomputable abbrev SL3 := traceMap.ker

noncomputable instance : Bracket SL3 SL3 where
  bracket X Y :=
    ⟨X.1 * Y.1 - Y.1 * X.1, by
      change Matrix.trace (X.1 * Y.1 - Y.1 * X.1) = 0
      rw [Matrix.trace_sub, Matrix.trace_mul_comm]
      exact sub_self _⟩

@[simp] theorem bracket_val (X Y : SL3) :
    (⁅X, Y⁆ : SL3).1 = X.1 * Y.1 - Y.1 * X.1 := rfl

noncomputable instance : LieRing SL3 where
  add_lie X Y Z := by
    apply Subtype.ext
    change
      (X.1 + Y.1) * Z.1 - Z.1 * (X.1 + Y.1) =
        (X.1 * Z.1 - Z.1 * X.1) + (Y.1 * Z.1 - Z.1 * Y.1)
    noncomm_ring
  lie_add X Y Z := by
    apply Subtype.ext
    change
      X.1 * (Y.1 + Z.1) - (Y.1 + Z.1) * X.1 =
        (X.1 * Y.1 - Y.1 * X.1) + (X.1 * Z.1 - Z.1 * X.1)
    noncomm_ring
  lie_self X := by
    apply Subtype.ext
    change X.1 * X.1 - X.1 * X.1 = 0
    noncomm_ring
  leibniz_lie X Y Z := by
    apply Subtype.ext
    change
      X.1 * (Y.1 * Z.1 - Z.1 * Y.1) -
          (Y.1 * Z.1 - Z.1 * Y.1) * X.1 =
        ((X.1 * Y.1 - Y.1 * X.1) * Z.1 -
          Z.1 * (X.1 * Y.1 - Y.1 * X.1)) +
        (Y.1 * (X.1 * Z.1 - Z.1 * X.1) -
          (X.1 * Z.1 - Z.1 * X.1) * Y.1)
    noncomm_ring

noncomputable instance : LieAlgebra ℝ SL3 where
  lie_smul c X Y := by
    apply Subtype.ext
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem trace_range_eq_top : LinearMap.range traceMap = ⊤ := by
  apply top_unique
  intro c hc
  let A : Matrix3 := (c / 3) • (1 : Matrix3)
  have hA : traceMap A = c := by
    change Matrix.trace A = c
    simp [A]
  exact ⟨A, hA⟩

theorem finrank_SL3 : Module.finrank ℝ SL3 = 8 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker traceMap
  rw [trace_range_eq_top] at hrank
  have hmatrix : Module.finrank ℝ Matrix3 = 9 := by
    simp [Module.finrank_matrix]
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by
    simp
  rw [htop, hmatrix] at hrank
  change Module.finrank ℝ traceMap.ker = 8
  omega

@[simp] theorem trace_bracket (X Y : SL3) :
    Matrix.trace (⁅X, Y⁆ : SL3).1 = 0 := by
  exact (⁅X, Y⁆ : SL3).2

/-- The stabilizer embeds into the ambient matrix Lie algebra. -/
noncomputable def inclusion : SL3 →ₗ⁅ℝ⁆ Matrix3 where
  toFun X := X.1
  map_add' X Y := rfl
  map_smul' c X := rfl
  map_lie' := by
    intro X Y
    rfl

@[simp] theorem inclusion_apply (X : SL3) :
    inclusion X = X.1 := by
  change X.1 = X.1
  rfl

/-! The intrinsic adjoint action, in Mathlib's derivation carrier. -/

noncomputable def adjointAction : SL3 →ₗ⁅ℝ⁆ LieDerivation ℝ SL3 SL3 :=
  LieDerivation.ad ℝ SL3

@[simp] theorem adjointAction_apply (X Y : SL3) :
    adjointAction X Y = ⁅X, Y⁆ := by
  change -⁅Y, X⁆ = ⁅X, Y⁆
  exact lie_skew X Y

end InfoGeometry.Physics.SplitG2SL3LieRing
