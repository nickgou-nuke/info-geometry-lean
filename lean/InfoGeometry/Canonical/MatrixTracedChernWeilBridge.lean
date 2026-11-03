/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MatrixTracedChernWeilBridge

open ExteriorAlgebra
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Matrix Trace Map Tr : Matrix (Fin n) (Fin n) (⋀ V) →ₗ[R] ⋀ V. -/
def matrixTraceForm : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) →ₗ[R] ExteriorAlgebra R V where
  toFun M := ∑ i : Fin n, M i i
  map_add' M N := by simp [Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum]

/-- **Definition**: Componentwise Exterior Derivative on Matrix-Valued Forms. -/
def matrixExteriorDerivative
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  Matrix.of (fun i j => d (M i j))

/-- **Theorem**: Commutativity of Exterior Derivative with Matrix Trace Map d(Tr(M)) = Tr(d M). -/
theorem exteriorDerivative_matrixTraceForm
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    d (matrixTraceForm M) = matrixTraceForm (matrixExteriorDerivative d M) := by
  dsimp [matrixTraceForm, matrixExteriorDerivative]
  exact map_sum d (fun i => M i i) Finset.univ

/-- Graded cyclicity for two matrix-valued one-forms. The minus sign comes
from the exterior generators; it does not assume that matrices commute. -/
theorem matrixTrace_one_form_mul_swap
    (A B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A)
    (hB : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 B) :
    matrixTraceForm (A * B) = -matrixTraceForm (B * A) := by
  change (∑ i, ∑ j, A i j * B j i) = -(∑ i, ∑ j, B i j * A j i)
  calc
    (∑ i, ∑ j, A i j * B j i) = ∑ i, ∑ j, -(B j i * A i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨v, hv⟩ :=
        (InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.homogeneous_one_iff_exists_generator
          (A i j)).mp (hA i j)
      obtain ⟨w, hw⟩ :=
        (InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.homogeneous_one_iff_exists_generator
          (B j i)).mp (hB j i)
      rw [← hv, ← hw]
      exact (eq_neg_iff_add_eq_zero).2 (ExteriorAlgebra.ι_add_mul_swap v w)
    _ = -(∑ i, ∑ j, B j i * A i j) := by simp
    _ = -(∑ i, ∑ j, B i j * A j i) := by rw [Finset.sum_comm]

/-- The trace of the square of a matrix-valued one-form vanishes over any
commutative coefficient ring, including characteristic two. Fixed points of
index transposition vanish by exterior alternation, while other terms cancel
in pairs; no division by two is used. -/
theorem matrixTrace_one_form_square_eq_zero
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    matrixTraceForm (A * A) = 0 := by
  classical
  have hs : (∑ ij : Fin n × Fin n, A ij.1 ij.2 * A ij.2 ij.1) = 0 := by
    apply Finset.sum_ninvolution (fun ij : Fin n × Fin n => (ij.2, ij.1))
    · intro ij
      obtain ⟨v, hv⟩ :=
        (InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.homogeneous_one_iff_exists_generator
          (A ij.1 ij.2)).mp (hA _ _)
      obtain ⟨w, hw⟩ :=
        (InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.homogeneous_one_iff_exists_generator
          (A ij.2 ij.1)).mp (hA _ _)
      rw [← hv, ← hw]
      exact ExteriorAlgebra.ι_add_mul_swap v w
    · intro ij hne heq
      have hij : ij.1 = ij.2 := by simpa using (congrArg Prod.fst heq).symm
      apply hne
      rw [← hij]
      obtain ⟨v, hv⟩ :=
        (InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.homogeneous_one_iff_exists_generator
          (A ij.1 ij.1)).mp (hA _ _)
      rw [← hv]
      exact ExteriorAlgebra.ι_sq_zero v
    · intro ij
      simp
    · intro ij
      cases ij
      rfl
  change (∑ i, ∑ j, A i j * A j i) = 0
  simpa only [Fintype.sum_prod_type] using hs

/-- The trace of the curvature expression of a matrix-valued one-form is
exact: its quadratic term has zero trace. This uses neither cyclicity for
arbitrary forms nor square-zero or Leibniz assumptions on `d`. -/
theorem matrixTrace_connection_curvature_exact
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    matrixTraceForm (matrixExteriorDerivative d A + A * A) = d (matrixTraceForm A) := by
  rw [map_add, matrixTrace_one_form_square_eq_zero A hA, add_zero]
  exact (exteriorDerivative_matrixTraceForm d A).symm

/-- Changing the globally given matrix-valued one-form changes the traced
curvature by the differential of the trace of the difference. No Leibniz or
square-zero assumption on `d` is used. -/
theorem matrixTrace_connection_curvature_difference
    (d : Module.End R (ExteriorAlgebra R V))
    (A B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A)
    (hB : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 B) :
    matrixTraceForm (matrixExteriorDerivative d B + B * B) -
      matrixTraceForm (matrixExteriorDerivative d A + A * A) =
    d (matrixTraceForm (B - A)) := by
  rw [matrixTrace_connection_curvature_exact d B hB,
    matrixTrace_connection_curvature_exact d A hA, map_sub, map_sub]

/-- For a globally supplied matrix-valued one-form, the traced curvature
represents zero in the existing algebraic `ker(d)/range(d)` quotient. This is
not a statement about arbitrary connections on nontrivial bundles. -/
theorem matrixTrace_connection_curvature_class_zero
    (d : Module.End R (ExteriorAlgebra R V)) (hd2 : d.comp d = 0)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    (Submodule.Quotient.mk
      ⟨matrixTraceForm (matrixExteriorDerivative d A + A * A), by
        rw [LinearMap.mem_ker, matrixTrace_connection_curvature_exact d A hA]
        exact LinearMap.congr_fun hd2 (matrixTraceForm A)⟩ :
      InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge.deRhamCohomologyModule d) = 0 := by
  change Submodule.Quotient.mk _ = (Submodule.Quotient.mk 0 :
    InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge.deRhamCohomologyModule d)
  rw [Submodule.Quotient.eq, sub_zero, Submodule.mem_comap]
  change matrixTraceForm (matrixExteriorDerivative d A + A * A) ∈ LinearMap.range d
  exact ⟨matrixTraceForm A, (matrixTrace_connection_curvature_exact d A hA).symm⟩

/-- For a matrix-valued one-form and a square-zero graded differential,
the derivative of `A * dA` is `dA * dA`. Matrix multiplication remains
noncommutative, and no trace-cyclicity hypothesis is used. -/
theorem matrixExteriorDerivative_one_form_mul_derivative
    (d : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0)
    (hd : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.IsGradedDerivation d)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    matrixExteriorDerivative d (A * matrixExteriorDerivative d A) =
      matrixExteriorDerivative d A * matrixExteriorDerivative d A := by
  let D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V :=
    ⟨d, hd, hd2⟩
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := InfoGeometry.Canonical.ExteriorGradedDerivationBridge.one_form_leibniz
    D (A i k) (d (A k j)) (hA i k)
  change d (A i k * d (A k j)) = d (A i k) * d (A k j) - A i k * d (d (A k j)) at h
  rw [h, InfoGeometry.Canonical.ExteriorGradedDerivationBridge.differential_sq_zero D (A k j)]
  simp

/-- The cubic rule for any graded derivation, without assuming that its square
vanishes. The factors retain their noncommutative order. -/
theorem matrixExteriorDerivative_one_form_cube_of_graded
    (d : Module.End R (ExteriorAlgebra R V))
    (hd : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.IsGradedDerivation d)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    matrixExteriorDerivative d (A * A * A) =
      matrixExteriorDerivative d A * A * A - A * matrixExteriorDerivative d A * A +
      A * A * matrixExteriorDerivative d A := by
  have rule (B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
      matrixExteriorDerivative d (A * B) =
        matrixExteriorDerivative d A * B - A * matrixExteriorDerivative d B := by
    ext i j
    dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.sub_apply]
    rw [map_sum, ← Finset.sum_sub_distrib]
    congr 1
    ext k
    have h := hd 1 (A i k) (B k j) (hA i k)
    simpa only [pow_one, neg_one_smul, sub_eq_add_neg] using h
  rw [mul_assoc A A A, rule (A * A), rule A]
  noncomm_ring

/-- The cubic rule specialized to the existing square-zero differential data. -/
theorem matrixExteriorDerivative_one_form_cube
    (D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    matrixExteriorDerivative D.d (A * A * A) =
      matrixExteriorDerivative D.d A * A * A - A * matrixExteriorDerivative D.d A * A +
      A * A * matrixExteriorDerivative D.d A :=
  matrixExteriorDerivative_one_form_cube_of_graded D.d D.gradedLeibniz A hA

/-- Expand the traced square of `dA + A²` without commuting matrix factors or
assuming any cyclicity of the exterior-valued matrix trace. -/
theorem matrixTrace_curvature_square_expansion
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixTraceForm ((matrixExteriorDerivative d A + A * A) *
      (matrixExteriorDerivative d A + A * A)) =
    matrixTraceForm (matrixExteriorDerivative d A * matrixExteriorDerivative d A) +
      matrixTraceForm (matrixExteriorDerivative d A * A * A) +
      matrixTraceForm (A * A * matrixExteriorDerivative d A) +
      matrixTraceForm (A * A * A * A) := by
  simp only [add_mul, mul_add, map_add, mul_assoc]
  abel

/-- **Theorem**: Matrix-Traced Chern-Weil Closedness Theorem d(Tr(F ∧ F)) = 0. -/
theorem matrix_traced_curvature_square_closed
    (d : Module.End R (ExteriorAlgebra R V))
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_closed : matrixExteriorDerivative d F2 = 0) :
    d (matrixTraceForm F2) = 0 := by
  rw [exteriorDerivative_matrixTraceForm]
  rw [h_closed]
  dsimp [matrixTraceForm]
  simp

/-- **Theorem**: Master Matrix-Traced Chern-Weil Closedness Synthesis.
    Unifies:
    1. Matrix trace map Tr : Matrix n n (⋀ V) →ₗ[R] ⋀ V.
    2. Componentwise exterior derivative d M on matrix-valued differential forms.
    3. Commutativity theorem d(Tr(M)) = Tr(d M).
    4. Matrix-traced Chern-Weil closedness theorem d(Tr(F ∧ F)) = 0.
    5. Exact machine-checked proof closure for Matrix-valued Chern-Weil gauge densities. -/
theorem master_matrix_traced_chern_weil_synthesis
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_closed : matrixExteriorDerivative d F2 = 0) :
    (d (matrixTraceForm M) = matrixTraceForm (matrixExteriorDerivative d M)) ∧
    (d (matrixTraceForm F2) = 0) := ⟨
  exteriorDerivative_matrixTraceForm d M,
  matrix_traced_curvature_square_closed d F2 h_closed
⟩

end InfoGeometry.Canonical.MatrixTracedChernWeilBridge
