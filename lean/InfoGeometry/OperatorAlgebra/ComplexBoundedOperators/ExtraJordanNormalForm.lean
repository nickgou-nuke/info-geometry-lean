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

section GramSchmidt

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [Fintype ι]

/--
Mathlib's actual Gram-Schmidt orthonormal-basis construction.

This is the Lean-native replacement for AFP's list-level `gram_schmidt0`
construction when the index cardinality is the Hilbert-space dimension.
-/
abbrev gramSchmidtBasis
    (hcard : finrank ℂ E = Fintype.card ι)
    (f : ι → E) :
    OrthonormalBasis ι ℂ E :=
  gramSchmidtOrthonormalBasis hcard f

theorem gramSchmidtBasis_orthonormal
    (hcard : finrank ℂ E = Fintype.card ι)
    (f : ι → E) :
    Orthonormal ℂ (gramSchmidtBasis (E := E) hcard f) :=
  (gramSchmidtBasis (E := E) hcard f).orthonormal

theorem gramSchmidtBasis_apply_of_orthogonal
    (hcard : finrank ℂ E = Fintype.card ι)
    {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫_ℂ = 0)
    {i : ι}
    (hi : f i ≠ 0) :
    gramSchmidtBasis (E := E) hcard f i = (‖f i‖⁻¹ : ℂ) • f i :=
  gramSchmidtOrthonormalBasis_apply_of_orthogonal hcard hf hi

end GramSchmidt

end ExtraJordanNormalForm
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
