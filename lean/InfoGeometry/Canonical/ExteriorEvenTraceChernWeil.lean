/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GradedConnectionBianchiBridge
import InfoGeometry.Canonical.GradedChernWeilBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Even exterior forms and matrix-traced curvature

Degree-two exterior elements are central in the exterior algebra. Their
matrix-valued counterparts need not commute as matrices, but their traces are
cyclic against arbitrary matrix-valued forms. This supplies precisely the
cyclicity needed for the trace of a square of a homogeneous curvature.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorEvenTraceChernWeil

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
open InfoGeometry.Canonical.GradedChernWeilBridge
open InfoGeometry.Canonical.GradedConnectionBianchiBridge
open scoped BigOperators

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- The local homogeneous predicate is Mathlib's fixed-degree submodule. -/
theorem homogeneous_iff_fixedDegree (k : ℕ) (x : ExteriorAlgebra R V) :
    IsHomogeneousExteriorDegree k x ↔ x ∈ ⋀[R]^k V := by
  unfold IsHomogeneousExteriorDegree
  rw [← ιMulti_span_fixedDegree]
  have hfun : (fun v : Fin k → V => (List.ofFn (fun i => ι R (v i))).prod) =
      (ιMulti R k : (Fin k → V) → ExteriorAlgebra R V) := by
    funext v
    exact (ιMulti_apply v).symm
  rw [hfun]

/-- Exterior products add their homogeneous degrees. -/
theorem homogeneous_mul {i j : ℕ} {x y : ExteriorAlgebra R V}
    (hx : IsHomogeneousExteriorDegree i x) (hy : IsHomogeneousExteriorDegree j y) :
    IsHomogeneousExteriorDegree (i + j) (x * y) := by
  rw [homogeneous_iff_fixedDegree] at hx hy ⊢
  exact SetLike.GradedMonoid.toGradedMul.mul_mem hx hy

/-- The matrix square of a degree-one connection is a degree-two form. -/
theorem matrix_one_form_square_homogeneous
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) : MatrixIsHomogeneous 2 (A * A) := by
  intro i j
  apply (homogeneous_iff_fixedDegree (R := R) (V := V) 2 _).2
  change (∑ k, A i k * A k j) ∈ ⋀[R]^2 V
  apply Submodule.sum_mem _
  intro k hk
  exact (homogeneous_iff_fixedDegree (R := R) (V := V) 2 _).1
    (homogeneous_mul (i := 1) (j := 1) (hA i k) (hA k j))

/-- Degree raising on one-forms suffices to place the curvature of a
degree-one connection in degree two. -/
theorem connection_curvature_homogeneous
    (d : Module.End R (ExteriorAlgebra R V))
    (hd : ∀ x, IsHomogeneousExteriorDegree 1 x → IsHomogeneousExteriorDegree 2 (d x))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    MatrixIsHomogeneous 2
      (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection d A) := by
  intro i j
  have hs := matrix_one_form_square_homogeneous A hA i j
  have hdA := hd (A i j) (hA i j)
  rw [homogeneous_iff_fixedDegree] at hs hdA ⊢
  change d (A i j) + (A * A) i j ∈ ⋀[R]^2 V
  exact Submodule.add_mem _ hdA hs

/-- Every homogeneous two-form commutes with every exterior element. -/
theorem homogeneous_two_central (x : ExteriorAlgebra R V)
    (hx : IsHomogeneousExteriorDegree 2 x) (y : ExteriorAlgebra R V) :
    Commute x y := by
  change x ∈ Submodule.span R (Set.range (fun v : Fin 2 → V =>
    (List.ofFn (fun i => ι R (v i))).prod)) at hx
  refine Submodule.span_induction (p := fun z _ => Commute z y) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨v, rfl⟩
    change Commute ((List.ofFn (fun i => ι R (v i))).prod) y
    rw [← ιMulti_apply]
    induction y using ExteriorAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right r (ιMulti R 2 v)
    | ι w =>
      have h := ι_mul_ιMulti_anticomm (R := R) w v
      simp only [show (-1 : ℤˣ) ^ 2 = 1 by norm_num, one_smul] at h
      exact h.symm
    | mul a b ha hb => exact ha.mul_right hb
    | add a b ha hb => exact ha.add_right hb
  · exact Commute.zero_left y
  · intro a b _ _ ha hb
    exact ha.add_left hb
  · intro c a _ ha
    exact ha.smul_left c

/-- Entries of the square of a degree-two form matrix commute with every
exterior element; no commutativity of matrix multiplication is assumed. -/
theorem curvature_square_entry_central
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) (i j : Fin n) (y : ExteriorAlgebra R V) :
    Commute ((F * F) i j) y := by
  rw [Matrix.mul_apply]
  apply Commute.sum_left
  intro k hk
  exact (homogeneous_two_central (F i k) (hF i k) y).mul_left
    (homogeneous_two_central (F k j) (hF k j) y)

/-- Trace cyclicity for a matrix-valued homogeneous two-form against an
arbitrary matrix. This is degree-restricted: it is not blanket cyclicity for
arbitrary exterior-valued matrices. -/
theorem matrix_trace_even_cyclic
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    matrixTraceForm (A * F) = matrixTraceForm (F * A) := by
  change (∑ i, ∑ j, A i j * F j i) =
    ∑ i, ∑ j, F i j * A j i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact (homogeneous_two_central (F i j) (hF i j) (A j i)).eq.symm

/-- Restricted trace cyclicity holds for the square of a degree-two matrix. -/
theorem curvature_square_trace_cyclic
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    matrixTraceForm (A * (F * F)) = matrixTraceForm ((F * F) * A) := by
  change (∑ i, ∑ j, A i j * (F * F) j i) =
    ∑ i, ∑ j, (F * F) i j * A j i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact (curvature_square_entry_central F hF i j (A j i)).eq.symm

/-- Matrix multiplication adds entrywise exterior degrees. -/
theorem matrix_mul_homogeneous {i j : ℕ}
    (X Y : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hX : MatrixIsHomogeneous i X)
    (hY : MatrixIsHomogeneous j Y) :
    MatrixIsHomogeneous (i + j) (X * Y) := by
  intro p q
  apply (homogeneous_iff_fixedDegree (R := R) (V := V) (i + j) _).2
  change (∑ k, X p k * Y k q) ∈ ⋀[R]^(i + j) V
  apply Submodule.sum_mem _
  intro k hk
  exact (homogeneous_iff_fixedDegree (R := R) (V := V) (i + j) _).1
    (homogeneous_mul (hX p k) (hY k q))

/-- The matrix extension of the graded Leibniz rule for a degree-one left
factor. -/
theorem matrixExteriorDerivative_one_form_mul
    (D : ExteriorDifferentialData R V)
    (A B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    matrixExteriorDerivative D.d (A * B) =
      matrixExteriorDerivative D.d A * B - A * matrixExteriorDerivative D.d B := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.sub_apply]
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext k
  exact one_form_leibniz D (A i k) (B k j) (hA i k)

/-- The matrix extension of the graded Leibniz rule for a degree-two left
factor. -/
theorem matrixExteriorDerivative_two_form_mul
    (D : ExteriorDifferentialData R V)
    (F B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    matrixExteriorDerivative D.d (F * B) =
      matrixExteriorDerivative D.d F * B + F * matrixExteriorDerivative D.d B := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.add_apply]
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext k
  exact two_form_leibniz D (F i k) (B k j) (hF i k)

/-- Degree-one and degree-three exterior forms anticommute. This graded
relation is used for matrix-trace cyclicity, not as a commutative replacement
for the matrix product. -/
theorem homogeneous_one_three_anticommute
    (x y : ExteriorAlgebra R V)
    (hx : IsHomogeneousExteriorDegree 1 x)
    (hy : IsHomogeneousExteriorDegree 3 y) :
    x * y = -(y * x) := by
  rcases (homogeneous_one_iff_exists_generator x).mp hx with ⟨v, rfl⟩
  rw [homogeneous_iff_fixedDegree] at hy
  rw [← ιMulti_span_fixedDegree] at hy
  change y ∈ Submodule.span R (Set.range (ιMulti R 3)) at hy
  have hmono (w : Fin 3 → V) :
      ι R v * ιMulti R 3 w = -(ιMulti R 3 w * ι R v) := by
    have h := ι_mul_ιMulti_anticomm (R := R) v w
    have hsign : (-1 : ℤˣ) ^ 3 = -1 := by norm_num
    rw [hsign, Units.neg_smul, one_smul] at h
    exact h
  refine Submodule.span_induction
    (p := fun z _ => ι R v * z = -(z * ι R v)) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨w, rfl⟩
    exact hmono w
  · simp
  · intro a b _ _ ha hb
    simp only [mul_add, add_mul, ha, hb, neg_add]
  · intro c a _ ha
    simp only [mul_smul_comm, smul_mul_assoc, ha, smul_neg]

/-- Graded cyclicity for the trace of a matrix-valued 1-form times a
matrix-valued 3-form. The proof retains the full noncommutative matrix product
and uses only the exterior-degree sign on each entry. -/
theorem matrix_trace_one_three_anticommute
    (A B : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A)
    (hB : MatrixIsHomogeneous 3 B) :
    matrixTraceForm (A * B) = -matrixTraceForm (B * A) := by
  change (∑ i, ∑ j, A i j * B j i) =
    -(∑ i, ∑ j, B i j * A j i)
  calc
    (∑ i, ∑ j, A i j * B j i) =
        ∑ i, ∑ j, -(B j i * A i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact homogeneous_one_three_anticommute (A i j) (B j i)
        (hA i j) (hB j i)
    _ = -(∑ i, ∑ j, B j i * A i j) := by simp
    _ = -(∑ i, ∑ j, B i j * A j i) := by
      congr 1
      rw [Finset.sum_comm]

/-- The matrix trace of the fourth power of a homogeneous 1-form vanishes
over a torsion-free characteristic-zero coefficient module. This is the
degree-four term needed in the Chern--Simons curvature-square expansion. -/
theorem matrix_trace_fourth_power_one_form_eq_zero
    [NoZeroDivisors R] [CharZero R]
    [Module.IsTorsionFree R (ExteriorAlgebra R V)]
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    matrixTraceForm (A * A * A * A) = 0 := by
  have hA2 : MatrixIsHomogeneous 2 (A * A) :=
    matrix_one_form_square_homogeneous A hA
  have hA3 : MatrixIsHomogeneous 3 (A * A * A) := by
    have h := matrix_mul_homogeneous (A * A) A hA2 hA
    simpa using h
  have hcycle := matrix_trace_one_three_anticommute A (A * A * A) hA hA3
  have hnegative : matrixTraceForm (A * A * A * A) =
      -matrixTraceForm (A * A * A * A) := by
    simpa [mul_assoc] using hcycle
  have hsum : matrixTraceForm (A * A * A * A) +
      matrixTraceForm (A * A * A * A) = 0 := by
    calc
      _ = -matrixTraceForm (A * A * A * A) +
          matrixTraceForm (A * A * A * A) := congrArg
            (fun x => x + matrixTraceForm (A * A * A * A)) hnegative
      _ = 0 := neg_add_cancel _
  have hmul : (2 : R) • matrixTraceForm (A * A * A * A) = 0 := by
    rw [two_smul]
    exact hsum
  rcases smul_eq_zero.mp hmul with htwo | htrace
  · norm_num at htwo
  · exact htrace

/-- Trace reduction for the covariant derivative of a square of a homogeneous
two-form. The needed cyclicity is proved for this degree-constrained product,
not assumed for arbitrary exterior-valued matrices. -/
theorem trace_covariantDerivative_curvature_square
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    matrixTraceForm (covariantDerivative A D.d (F * F)) =
      D.d (matrixTraceForm (F * F)) := by
  simp only [covariantDerivative, matrixCommutator, LinearMap.map_add,
    LinearMap.map_sub]
  rw [curvature_square_trace_cyclic A F hF, sub_self, add_zero]
  exact (exteriorDerivative_matrixTraceForm D.d (F * F)).symm

/-- The finite Chern–Weil trace is closed from the graded Leibniz law,
degree-two curvature, and Bianchi; no blanket cyclicity hypothesis is used. -/
theorem graded_bianchi_chern_weil_closed
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0) :
    D.d (matrixTraceForm (F * F)) = 0 := by
  have hcov : covariantDerivative A D.d (F * F) = 0 :=
    covariant_curvature_square_closed A F D.d
      (graded_covariant_two_form_square_leibniz D A F hF) hBianchi
  rw [← trace_covariantDerivative_curvature_square D A F hF, hcov,
    LinearMap.map_zero]

/-- A homogeneous connection and its homogeneous curvature give a closed
traced square. Curvature homogeneity is explicit: the current differential
interface does not itself assert that the differential raises degree. -/
theorem connection_chern_weil_closed
    (D : ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A)
    (hF : MatrixIsHomogeneous 2
      (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A)) :
    D.d (matrixTraceForm
      (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A *
        InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A)) = 0 := by
  exact graded_bianchi_chern_weil_closed D A
    (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) hF
    (graded_connection_curvature_bianchi D A hA)

/-- The Chern--Weil class of a Bianchi-closed curvature square is unchanged by
an exact perturbation of its traced representative. -/
theorem connection_curvature_square_class_exact_invariance
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0)
    (ω : ExteriorAlgebra R V) :
    Submodule.Quotient.mk
      ⟨matrixTraceForm (F * F) + D.d ω, by
        rw [LinearMap.mem_ker, LinearMap.map_add,
          graded_bianchi_chern_weil_closed D A F hF hBianchi,
          differential_sq_zero D ω, add_zero]⟩ =
    (Submodule.Quotient.mk
      ⟨matrixTraceForm (F * F),
        graded_bianchi_chern_weil_closed D A F hF hBianchi⟩ :
      DeRhamCohomologyQuotientBridge.deRhamCohomologyModule D.d) := by
  rw [Submodule.Quotient.eq]
  rw [Submodule.mem_comap]
  dsimp [Submodule.subtype]
  rw [LinearMap.mem_range]
  exact ⟨ω, by abel⟩

/-- Closedness from the degree-one connection and degree-raising differential;
neither curvature homogeneity nor matrix trace cyclicity is assumed. -/
theorem degree_raising_connection_chern_weil_closed
    (D : ExteriorDifferentialData R V)
    (hd : ∀ x, IsHomogeneousExteriorDegree 1 x → IsHomogeneousExteriorDegree 2 (D.d x))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    D.d (matrixTraceForm
      (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A *
        InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A)) = 0 := by
  exact connection_chern_weil_closed D A hA (connection_curvature_homogeneous D.d hd A hA)

end InfoGeometry.Canonical.ExteriorEvenTraceChernWeil

end
