/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorialKillingLieClosure
import InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure
import InfoGeometry.Geometry.AssociativeGaugeConnection
import InfoGeometry.Physics.MatrixTraceBimodulePairingNative
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Real full-matrix instances of Killing and Erlangen closure

The existing native trace pairing and inner derivation are connected to the
new infinitesimal and group stabilizer owners on the full matrix algebra.
The pairing `Tr(XY)` is symmetric and nondegenerate; it is indefinite on
real two-by-two matrices. It is not presented as a positive Hilbert metric.

All invertible matrix conjugations preserve this functional and pairing.
Consequently every actual unit-valued flow supplies both preservation
premises of the automorphism-family closure theorem. An explicit pair of
noncommuting real matrices also shows that the Leibniz law by itself does
not force invariance of an independently chosen functional.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealMatrixKillingErlangen

open InfoGeometry.Geometry.AssociativeGaugeConnection
open InfoGeometry.Physics
open InfoGeometry.Canonical.FlowErlangenClosure
open OperatorInvariantErlangenClosure
open scoped OperatorInvariantPullback

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bundle the existing trace pairing as a native bilinear form. -/
def matrixTraceForm : LinearMap.BilinForm ℝ (Matrix n n ℝ) :=
  LinearMap.mk₂ ℝ (tracePairingNative (n := n))
    (by intro X Y Z; simp [tracePairingNative, add_mul])
    (by intro c X Y; simp [tracePairingNative, smul_mul_assoc])
    (by intro X Y Z; simp [tracePairingNative, mul_add])
    (by intro c X Y; simp [tracePairingNative, mul_smul_comm])

@[simp] theorem matrixTraceForm_apply (X Y : Matrix n n ℝ) :
    matrixTraceForm X Y = Matrix.trace (X * Y) := rfl

theorem matrixTraceForm_symmetric (X Y : Matrix n n ℝ) :
    matrixTraceForm X Y = matrixTraceForm Y X :=
  tracePairing_native_comm X Y

/-- The full trace pairing separates both arguments. -/
theorem matrixTraceForm_nondegenerate :
    (matrixTraceForm (n := n)).Nondegenerate := by
  constructor
  · intro X hX
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    simpa only [matrixTraceForm_apply, zero_mul, Matrix.trace_zero] using hX Y
  · intro Y hY
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    simpa only [matrixTraceForm_apply, mul_zero, Matrix.trace_zero] using hY X

/-- The existing inner commutator is Killing for trace and the trace pairing. -/
theorem innerDerivative_isOperatorialKilling (H : Matrix n n ℝ) :
    IsOperatorialKillingField (Matrix.traceLinearMap n ℝ ℝ) matrixTraceForm
      (innerDerivative (R := ℝ) H) := by
  refine ⟨innerDerivative_isLeibniz H, ?_, ?_⟩
  · intro X
    change Matrix.trace (H * X - X * H) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm H X, sub_self]
  · intro X Y
    change Matrix.trace ((H * X - X * H) * Y) +
      Matrix.trace (X * (H * Y - Y * H)) = 0
    rw [matrix_trace_commutator_pairing]
    exact neg_add_cancel _

/-- A whole family of inner derivations generates a genuine Killing Lie algebra. -/
theorem inner_lieSpan_le_killing (S : Set (Matrix n n ℝ)) :
    LieSubalgebra.lieSpan ℝ (Module.End ℝ (Matrix n n ℝ))
        ((fun H => innerDerivative (R := ℝ) H) '' S) ≤
      operatorialKillingLieSubalgebra (Matrix.traceLinearMap n ℝ ℝ) matrixTraceForm := by
  apply lieSpan_le_operatorialKilling
  rintro D ⟨H, _, rfl⟩
  exact innerDerivative_isOperatorialKilling H

/-- Native algebra automorphisms induced by all invertible real matrices. -/
def matrixInnerAut : (Matrix n n ℝ)ˣ →* (Matrix n n ℝ ≃ₐ[ℝ] Matrix n n ℝ) :=
  (MulSemiringAction.toAlgAut (ConjAct (Matrix n n ℝ)ˣ) ℝ (Matrix n n ℝ)).comp
    ConjAct.toConjAct.toMonoidHom

@[simp] theorem matrixInnerAut_apply (u : (Matrix n n ℝ)ˣ) (X : Matrix n n ℝ) :
    matrixInnerAut u X = (u : Matrix n n ℝ) * X * (↑u⁻¹ : Matrix n n ℝ) := rfl

theorem matrixInnerAut_preserves_trace (u : (Matrix n n ℝ)ˣ) (X : Matrix n n ℝ) :
    Matrix.traceLinearMap n ℝ ℝ (matrixInnerAut u X) = Matrix.traceLinearMap n ℝ ℝ X :=
  Matrix.trace_units_conj u X

theorem matrixInnerAut_preserves_form (u : (Matrix n n ℝ)ˣ) (X Y : Matrix n n ℝ) :
    matrixTraceForm (matrixInnerAut u X) (matrixInnerAut u Y) = matrixTraceForm X Y := by
  change Matrix.trace (matrixInnerAut u X * matrixInnerAut u Y) = Matrix.trace (X * Y)
  rw [← map_mul]
  exact matrixInnerAut_preserves_trace u (X * Y)

/-- Concrete finite-time symmetries lie in the same functional/form stabilizer. -/
theorem matrixInnerAut_mem_stabilizer (u : (Matrix n n ℝ)ˣ) :
    matrixInnerAut u ∈ functionalFormAutomorphismSubgroup
      (Matrix.traceLinearMap n ℝ ℝ) matrixTraceForm := by
  rw [mem_functionalFormAutomorphismSubgroup_iff]
  exact ⟨matrixInnerAut_preserves_trace u, matrixInnerAut_preserves_form u⟩

/-- Unit-valued motions become actual algebra-automorphism motions. -/
def matrixInnerFlow {Time : Type*} [Monoid Time]
    (ρ : Time →* (Matrix n n ℝ)ˣ) : Time →* (Matrix n n ℝ ≃ₐ[ℝ] Matrix n n ℝ) :=
  matrixInnerAut.comp ρ

/-- The generic Galois-closure theorem applies to the full real matrix carrier. -/
theorem matrix_inner_flowFamily_erlangen_closure
    {ι Time : Type*} [Monoid Time] (ρ : ι → Time →* (Matrix n n ℝ)ˣ) :
    symmetryClosure (Matrix n n ℝ ≃ₐ[ℝ] Matrix n n ℝ)
        (((Matrix n n ℝ) →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ (Matrix n n ℝ))
        (flowFamilySubgroup (fun i => matrixInnerFlow (ρ i))) ≤
      functionalFormAutomorphismSubgroup (Matrix.traceLinearMap n ℝ ℝ) matrixTraceForm :=
  (automorphism_flowFamily_erlangen_closure (Matrix.traceLinearMap n ℝ ℝ) matrixTraceForm
    (fun i => matrixInnerFlow (ρ i))
    (fun i t => matrixInnerAut_preserves_trace (ρ i t))
    (fun i t => matrixInnerAut_preserves_form (ρ i t))).2

section TwoByTwo

abbrev RealMatrixTwo := Matrix (Fin 2) (Fin 2) ℝ

def raising : RealMatrixTwo := !![0, 1; 0, 0]
def lowering : RealMatrixTwo := !![0, 0; 1, 0]
def diagonalGenerator : RealMatrixTwo := !![1, 0; 0, 0]

/-- A coordinate functional supplies an independent invariant choice. -/
def entryZero : RealMatrixTwo →ₗ[ℝ] ℝ where
  toFun X := X 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem raising_lowering_noncommute : raising * lowering ≠ lowering * raising := by
  intro h
  have h00 := congrArg (fun X : RealMatrixTwo => X 0 0) h
  norm_num [raising, lowering, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem innerDerivative_raising_lowering_entry :
    entryZero (innerDerivative (R := ℝ) raising lowering) = 1 := by
  norm_num [entryZero, innerDerivative, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    raising, lowering, Matrix.mul_apply, Fin.sum_univ_two]

/-- A genuine nonzero derivation need not preserve the chosen functional. -/
theorem leibniz_not_imply_functional_invariance :
    InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ RealMatrixTwo
        (innerDerivative (R := ℝ) raising) ∧
      ¬ (∀ X, entryZero (innerDerivative (R := ℝ) raising X) = 0) := by
  refine ⟨innerDerivative_isLeibniz raising, ?_⟩
  intro h
  have hbad := h lowering
  rw [innerDerivative_raising_lowering_entry] at hbad
  exact one_ne_zero hbad

/-- The positive Frobenius pairing has an independent invariance condition.
The same real inner derivation preserves trace but has a nonzero metric defect. -/
theorem frobenius_killing_defect :
    Matrix.trace ((innerDerivative (R := ℝ) diagonalGenerator raising).transpose * raising) +
      Matrix.trace (raising.transpose *
        innerDerivative (R := ℝ) diagonalGenerator raising) = 2 := by
  norm_num [innerDerivative, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    diagonalGenerator, raising, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Even the Leibniz rule together with trace annihilation does not imply
skewness for the positive Frobenius pairing. -/
theorem leibniz_trace_not_imply_frobenius_killing :
    InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ RealMatrixTwo
        (innerDerivative (R := ℝ) diagonalGenerator) ∧
      (∀ X, Matrix.trace (innerDerivative (R := ℝ) diagonalGenerator X) = 0) ∧
      ¬ (∀ X Y : RealMatrixTwo,
        Matrix.trace ((innerDerivative (R := ℝ) diagonalGenerator X).transpose * Y) +
          Matrix.trace (X.transpose * innerDerivative (R := ℝ) diagonalGenerator Y) = 0) := by
  refine ⟨innerDerivative_isLeibniz diagonalGenerator,
    (innerDerivative_isOperatorialKilling diagonalGenerator).2.1, ?_⟩
  intro h
  have hbad := h raising raising
  rw [frobenius_killing_defect] at hbad
  norm_num at hbad

theorem matrixTraceForm_positive_direction :
    matrixTraceForm (1 : RealMatrixTwo) 1 = 2 := by
  simp [matrixTraceForm_apply]

theorem matrixTraceForm_negative_direction :
    matrixTraceForm (raising - lowering) (raising - lowering) = -2 := by
  norm_num [matrixTraceForm_apply, raising, lowering, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_two]

end TwoByTwo

end InfoGeometry.OperatorAlgebra.RealMatrixKillingErlangen
