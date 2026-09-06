import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# AFP CBO `Extra_Jordan_Normal_Form` adapters

This file ports the finite matrix and Gram-Schmidt-facing facts from AFP's
`Extra_Jordan_Normal_Form` into Lean-native APIs.  Matrix dimensions are carried
by Lean types, so no carrier side conditions are needed.
-/

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ExtraJordanNormalForm

open Matrix
open FiniteMatrix

variable {ι κ E : Type*}

/-- AFP `mat_entry_explicit`: a matrix entry is recovered by acting on a ket. -/
theorem matrix_entry_explicit [Fintype ι] [DecidableEq ι]
    (M : Matrix κ ι ℂ) (i : κ) (j : ι) :
    (M *ᵥ ketPi j) i = M i j := by
  simpa [ketPi] using congrFun (Matrix.mulVec_single_one M j) i

/-- AFP `mat_adjoint_swap`: conjugate-transpose swaps indices and conjugates. -/
theorem mat_adjoint_swap (M : Matrix κ ι ℂ) (i : κ) (j : ι) :
    Mᴴ j i = star (M i j) :=
  Matrix.conjTranspose_apply M i j

/-- AFP `cscalar_prod_adjoint` in finite coordinate dot-product form. -/
theorem cscalar_prod_adjoint [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℂ) (v : FinKetSpace ι) (u : FinKetSpace κ) :
    star v ⬝ᵥ (Mᴴ *ᵥ u) = star (M *ᵥ v) ⬝ᵥ u :=
  FiniteMatrix.dotProduct_conjTranspose_mulVec M v u

/-- Lean-native alias of the matrix adjoint. -/
abbrev matAdjoint {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Aᴴ

@[simp]
theorem minus_one_smul_vec (v : ι → ℂ) :
    (-1 : ℂ) • v = -v := by
  ext i
  simp

/-- AFP `vec_is_zero`, Lean-native for finite/Pi coordinate vectors. -/
def vecIsZero (v : ι → ℂ) : Prop :=
  ∀ i, v i = 0

theorem vecIsZero_iff_eq_zero (v : ι → ℂ) :
    vecIsZero v ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    exact hv i
  · intro hv i
    simp [hv]

/-- Matrices are equal when they act equally on all coordinate vectors. -/
theorem matrix_eq_of_mulVec_eq [Fintype ι] [DecidableEq ι]
    {M N : Matrix κ ι ℂ}
    (h : ∀ v : FinKetSpace ι, M *ᵥ v = N *ᵥ v) :
    M = N := by
  ext i j
  have hij := congrFun (h (ketPi j)) i
  simpa [matrix_entry_explicit] using hij

theorem list_map_add_vec (v w : ι → ℂ) :
    (fun i => v i + w i) = v + w :=
  rfl

theorem list_map_smul_vec (c : ℂ) (v : ι → ℂ) :
    (fun i => c * v i) = c • v := by
  ext i
  simp

/-- AFP-style dot product on finite complex coordinate vectors. -/
abbrev dot {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  dotProduct v w

/-- Hermitian dot product on finite complex coordinate vectors. -/
abbrev cDot {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  dotProduct (star v) w

/-- The inverse-row vector used in the finite complex JNF corridor. -/
abbrev vecInv {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  fun i => star (v i) * (cDot v v)⁻¹

/-- Columns are pairwise conjugate-orthogonal, with nonzero self-overlap. -/
def corthogonalMatrix {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  (∀ i j, i ≠ j → cDot (fun k => A k i) (fun k => A k j) = 0) ∧
  (∀ i, cDot (fun k => A k i) (fun k => A k i) ≠ 0)

/-- Explicit inverse from a conjugate-orthogonal matrix. -/
abbrev corthogonalInverse {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => vecInv (fun k => A k i) j

/-- The inverse-row vector evaluates to `1` against its source vector. -/
theorem dot_vecInv_self [Fintype ι] (v : ι → ℂ) (h : cDot v v ≠ 0) :
    dot (vecInv v) v = 1 := by
  have hsum :
      ∑ x, v x * (star (v x) * (cDot v v)⁻¹) =
        (∑ x, v x * star (v x)) * (cDot v v)⁻¹ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_mul (s := Finset.univ) (f := fun x => v x * star (v x))
        (a := (cDot v v)⁻¹)).symm
  have hconj : (∑ x, v x * star (v x)) = cDot v v := by
    simp [cDot, dotProduct, mul_comm]
  rw [show dot (vecInv v) v = ∑ x, v x * (star (v x) * (cDot v v)⁻¹) by
    simp [dot, vecInv, dotProduct, mul_assoc, mul_left_comm, mul_comm]]
  rw [hsum, hconj]
  exact mul_inv_cancel₀ h

/-- The explicit conjugate-orthogonal inverse is a left inverse. -/
theorem corthogonalInverse_mul [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : corthogonalMatrix A) :
    corthogonalInverse A * A = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have hcalc :
        (corthogonalInverse A * A) i i = dot (vecInv (fun k => A k i)) (fun k => A k i) := by
      simp [corthogonalInverse, dot, vecInv, Matrix.mul_apply, dotProduct, mul_assoc,
        mul_left_comm, mul_comm]
    rw [hcalc]
    simpa [dot, cDot, dotProduct, mul_comm] using
      (dot_vecInv_self (v := fun k => A k i) (hA.2 i))
  · have hzero := hA.1 i j hij
    have hcalc :
        (corthogonalInverse A * A) i j =
          cDot (fun k => A k i) (fun k => A k j) *
            (cDot (fun k => A k i) (fun k => A k i))⁻¹ := by
      rw [Matrix.mul_apply]
      have hsum :
          ∑ x, A x j * (star (A x i) * (cDot (fun k => A k i) (fun k => A k i))⁻¹) =
            (∑ x, A x j * star (A x i)) * (cDot (fun k => A k i) (fun k => A k i))⁻¹ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Finset.sum_mul (s := Finset.univ)
            (f := fun x => A x j * star (A x i))
            (a := (cDot (fun k => A k i) (fun k => A k i))⁻¹)).symm
      simpa [corthogonalInverse, vecInv, cDot, dotProduct, mul_assoc, mul_left_comm, mul_comm]
        using hsum
    rw [hcalc, hzero]
    simp [hij]

section GramSchmidt

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/--
Mathlib's actual Gram-Schmidt orthonormal-basis construction.

This is the Lean-native replacement for AFP's list-level `gram_schmidt0`
construction when the index cardinality is the Hilbert-space dimension.
-/
abbrev gramSchmidtBasis
    (hcard : Module.finrank ℂ E = Fintype.card ι)
    (f : ι → E) :
    OrthonormalBasis ι ℂ E :=
  InnerProductSpace.gramSchmidtOrthonormalBasis hcard f

theorem gramSchmidtBasis_orthonormal
    (hcard : Module.finrank ℂ E = Fintype.card ι)
    (f : ι → E) :
    Orthonormal ℂ (gramSchmidtBasis (E := E) hcard f) :=
  (gramSchmidtBasis (E := E) hcard f).orthonormal

theorem gramSchmidtBasis_apply_of_orthogonal
    (hcard : Module.finrank ℂ E = Fintype.card ι)
    {f : ι → E}
    (hf : Pairwise fun i j => inner ℂ (f i) (f j) = 0)
    {i : ι}
    (hi : f i ≠ 0) :
    gramSchmidtBasis (E := E) hcard f i = (‖f i‖⁻¹ : ℂ) • f i :=
  InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal hcard hf hi

end GramSchmidt

end ExtraJordanNormalForm
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
