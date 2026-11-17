/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Degree-zero Hodge decomposition for a finite matrix commutator frame

The differential sends a full matrix `X` to the family `[Q i, X]`. Its
codomain is the actual finite Hilbert direct product `PiLp 2`, and its
codifferential is the native Hilbert--Schmidt adjoint. The harmonic space
is the joint centralizer of the frame; it becomes the center when the
frame generates the whole matrix algebra. The complementary coexact
space is a linear subspace, with no multiplicative closure asserted.

This is a degree-zero construction. No higher differential, square-zero
extension, Chevalley--Eilenberg complex, or infinite-dimensional limit is
assumed or asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge

open Matrix
open scoped InnerProductSpace ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

local instance : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The actual degree-zero differential into the finite Hilbert product. -/
def differential (Q : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] PiLp 2 (fun _ : ι => Matrix n n ℂ) :=
  (WithLp.linearEquiv 2 ℂ (ι → Matrix n n ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun i => LieAlgebra.ad ℂ (Matrix n n ℂ) (Q i))

omit [Fintype ι] in
@[simp] theorem differential_apply (Q : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) (i : ι) :
    differential Q X i = Q i * X - X * Q i := rfl

/-- The coderivative is a sum of the adjoint-generator commutators. -/
def codifferential (Q : ι → Matrix n n ℂ) :
    PiLp 2 (fun _ : ι => Matrix n n ℂ) →ₗ[ℂ] Matrix n n ℂ :=
  ∑ i, (LieAlgebra.ad ℂ (Matrix n n ℂ) (Q i)ᴴ).comp
    (PiLp.projₗ 2 (fun _ : ι => Matrix n n ℂ) i)

@[simp] theorem codifferential_apply (Q : ι → Matrix n n ℂ)
    (W : PiLp 2 (fun _ : ι => Matrix n n ℂ)) :
    codifferential Q W = ∑ i, ((Q i)ᴴ * W i - W i * (Q i)ᴴ) := by
  simp only [codifferential, LinearMap.sum_apply, LinearMap.comp_apply,
    LieAlgebra.ad_apply, Ring.lie_def, PiLp.projₗ_apply]

/-- Cyclic matrix trace proves the Hilbert adjunction, with the ordered
commutators unchanged. -/
theorem differential_adjunction (Q : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) (W : PiLp 2 (fun _ : ι => Matrix n n ℂ)) :
    inner ℂ (differential Q X) W = inner ℂ X (codifferential Q W) := by
  rw [PiLp.inner_apply, codifferential_apply]
  change (∑ i, trace (W i * 1 * (Q i * X - X * Q i)ᴴ)) =
    trace ((∑ i, ((Q i)ᴴ * W i - W i * (Q i)ᴴ)) * 1 * Xᴴ)
  simp only [Matrix.mul_one, Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_comm (W i), Matrix.trace_mul_comm _ Xᴴ]
  exact MatrixTraceGeometry.trace_star_lie (Q i) X (W i)

/-- The constructed coderivative is exactly Mathlib's native metric adjoint. -/
theorem codifferential_eq_adjoint (Q : ι → Matrix n n ℂ) :
    codifferential Q = (differential Q).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro W X
  simpa only [inner_conj_symm] using
    (congrArg (star : ℂ → ℂ) (differential_adjunction Q X W)).symm

omit [Fintype ι] in
/-- A harmonic degree-zero input commutes with every generator of the frame. -/
theorem differential_eq_zero_iff (Q : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    differential Q X = 0 ↔ ∀ i, Q i * X = X * Q i := by
  constructor
  · intro h i
    have hi := congrArg (fun W : PiLp 2 (fun _ : ι => Matrix n n ℂ) => W i) h
    exact sub_eq_zero.mp hi
  · intro h
    apply PiLp.ext
    intro i
    exact sub_eq_zero.mpr (h i)

omit [Fintype ι] in
/-- The kernel is the actual native joint centralizer, rather than a field
supplied as a decomposition assumption. -/
theorem ker_differential (Q : ι → Matrix n n ℂ) :
    (differential Q).ker =
      (Subalgebra.centralizer ℂ (Set.range Q)).toSubmodule := by
  ext X
  rw [LinearMap.mem_ker, differential_eq_zero_iff]
  change (∀ i, Q i * X = X * Q i) ↔
    ∀ Y ∈ Set.range Q, Y * X = X * Y
  constructor
  · rintro h Y ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (Q i) ⟨i, rfl⟩

/-- The degree-zero Laplacian has the same centralizer kernel. -/
theorem ker_laplacian (Q : ι → Matrix n n ℂ) :
    ((codifferential Q).comp (differential Q)).ker =
      (Subalgebra.centralizer ℂ (Set.range Q)).toSubmodule := by
  rw [codifferential_eq_adjoint, LinearMap.ker_adjoint_comp_self, ker_differential]

/-- Coexact matrices are precisely the Hilbert--Schmidt orthogonal
complement of the joint centralizer. -/
theorem range_codifferential (Q : ι → Matrix n n ℂ) :
    (codifferential Q).range =
      (Subalgebra.centralizer ℂ (Set.range Q)).toSubmoduleᗮ := by
  rw [codifferential_eq_adjoint, ← LinearMap.orthogonal_ker, ker_differential]

/-- Every matrix has a unique centralizer component whose residual is
coexact. Existence uses finite-dimensional orthogonal projection. -/
theorem existsUnique_centralizer_coexact (Q : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    ∃! C : Matrix n n ℂ,
      C ∈ Subalgebra.centralizer ℂ (Set.range Q) ∧
        X - C ∈ (codifferential Q).range := by
  let K := (Subalgebra.centralizer ℂ (Set.range Q)).toSubmodule
  obtain ⟨C, hC, W, hW, hX⟩ := K.exists_add_mem_mem_orthogonal X
  have hres : X - C ∈ Kᗮ := by
    simpa only [hX, add_sub_cancel_left] using hW
  refine ⟨C, ⟨hC, ?_⟩, ?_⟩
  · rwa [range_codifferential]
  · rintro D ⟨hD, hDres⟩
    rw [range_codifferential] at hDres
    have hdK : D - C ∈ K := K.sub_mem hD hC
    have hdO : D - C ∈ Kᗮ := by
      have hsub := Kᗮ.sub_mem hres hDres
      convert hsub using 1 <;> abel
    apply sub_eq_zero.mp
    exact inner_self_eq_zero.mp ((K.mem_orthogonal _).mp hdO _ hdK)

omit [Fintype ι] in
/-- Generating the whole algebra, not just choosing a frame, identifies
the joint centralizer with the center. -/
theorem centralizer_eq_center_of_adjoin_eq_top (Q : ι → Matrix n n ℂ)
    (hQ : Algebra.adjoin ℂ (Set.range Q) = ⊤) :
    Subalgebra.centralizer ℂ (Set.range Q) = Subalgebra.center ℂ (Matrix n n ℂ) := by
  apply le_antisymm
  · intro X hX
    rw [Subalgebra.mem_center_iff]
    intro Y
    have hY : Y ∈ Algebra.adjoin ℂ (Set.range Q) := by rw [hQ]; trivial
    have hcomm := Algebra.commute_of_mem_adjoin_of_forall_mem_commute hY
      (fun Z hZ => ((Subalgebra.mem_centralizer_iff ℂ).mp hX Z hZ).symm)
    exact hcomm.eq.symm
  · exact Subalgebra.center_le_centralizer (R := ℂ) (Set.range Q)

/-- For a generating frame, the degree-zero harmonic space is the center. -/
theorem ker_laplacian_eq_center (Q : ι → Matrix n n ℂ)
    (hQ : Algebra.adjoin ℂ (Set.range Q) = ⊤) :
    ((codifferential Q).comp (differential Q)).ker =
      (Subalgebra.center ℂ (Matrix n n ℂ)).toSubmodule := by
  rw [ker_laplacian, centralizer_eq_center_of_adjoin_eq_top Q hQ]

/-- For a generating frame, the coexact space is the center's actual
Hilbert--Schmidt orthogonal complement. -/
theorem range_codifferential_eq_center_orthogonal (Q : ι → Matrix n n ℂ)
    (hQ : Algebra.adjoin ℂ (Set.range Q) = ⊤) :
    (codifferential Q).range = (Subalgebra.center ℂ (Matrix n n ℂ)).toSubmoduleᗮ := by
  rw [range_codifferential, centralizer_eq_center_of_adjoin_eq_top Q hQ]

/-- Every coexact output is traceless, even for a frame that does not
generate the full matrix algebra. -/
theorem trace_codifferential (Q : ι → Matrix n n ℂ)
    (W : PiLp 2 (fun _ : ι => Matrix n n ℂ)) :
    Matrix.trace (codifferential Q W) = 0 := by
  rw [codifferential_apply, Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [Matrix.trace_sub, Matrix.trace_mul_comm ((Q i)ᴴ), sub_self]

/-- For a nonempty matrix index, the coexact space cannot be a unital
subalgebra because it excludes the identity. -/
theorem one_not_mem_range_codifferential [Nonempty n] (Q : ι → Matrix n n ℂ) :
    (1 : Matrix n n ℂ) ∉ (codifferential Q).range := by
  rintro ⟨W, hW⟩
  have h := trace_codifferential Q W
  rw [hW, Matrix.trace_one] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h

/-- Matrix units give a concrete generating frame in every finite dimension. -/
theorem adjoin_matrixUnits_eq_top :
    Algebra.adjoin ℂ
      (Set.range (fun p : n × n => Matrix.single p.1 p.2 (1 : ℂ))) = ⊤ := by
  apply Algebra.eq_top_iff.mpr
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  apply Subalgebra.sum_mem
  intro i _
  apply Subalgebra.sum_mem
  intro j _
  have hunit : Matrix.single i j (1 : ℂ) ∈
      Algebra.adjoin ℂ
        (Set.range (fun p : n × n => Matrix.single p.1 p.2 (1 : ℂ))) :=
    Algebra.subset_adjoin ⟨(i, j), rfl⟩
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (Algebra.adjoin ℂ
      (Set.range (fun p : n × n => Matrix.single p.1 p.2 (1 : ℂ)))).smul_mem hunit (X i j)

/-- For the full two-by-two matrix-unit frame, a coexact matrix squares
to the identity. Thus coexactness has no general multiplicative closure. -/
theorem matrixUnits_coexact_square_counterexample :
    ∃ X : Matrix (Fin 2) (Fin 2) ℂ,
      X ∈ (codifferential
        (fun p : Fin 2 × Fin 2 => Matrix.single p.1 p.2 (1 : ℂ))).range ∧
      X * X = 1 ∧
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ∉ (codifferential
        (fun p : Fin 2 × Fin 2 => Matrix.single p.1 p.2 (1 : ℂ))).range := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let W : PiLp 2 (fun _ : Fin 2 × Fin 2 => Matrix (Fin 2) (Fin 2) ℂ) :=
    WithLp.toLp 2 fun p => if p = (0, 0) then !![0, 1; -1, 0] else 0
  refine ⟨X, ⟨W, ?_⟩, ?_, one_not_mem_range_codifferential _⟩
  · rw [codifferential_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [W, X, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- A genuine coexact matrix has zero overlap with the harmonic identity,
while insertion of that same matrix gives a nonzero numerator. Any
normalized two-boundary quotient therefore needs an explicit nonzero
overlap hypothesis. No value for division by zero is interpreted here. -/
theorem coexact_zero_overlap_nonzero_numerator :
    ∃ X : Matrix (Fin 2) (Fin 2) ℂ,
      X ∈ (codifferential
        (fun p : Fin 2 × Fin 2 => Matrix.single p.1 p.2 (1 : ℂ))).range ∧
      inner ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) X = 0 ∧
      inner ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) (X * X) = 2 := by
  obtain ⟨X, ⟨W, hW⟩, hXX, _⟩ := matrixUnits_coexact_square_counterexample
  refine ⟨X, ⟨W, hW⟩, ?_, ?_⟩
  · change Matrix.trace (X * 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) = 0
    simp only [Matrix.conjTranspose_one, Matrix.mul_one]
    rw [← hW]
    exact trace_codifferential _ _
  · rw [hXX]
    change Matrix.trace
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) = 2
    norm_num

end InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge
