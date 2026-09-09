import Mathlib
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Clifford.Cl55SpinorDimensionReadout

/-!
# Dyadic/Morita reconstruction for the native `Cl(5,5)` spinor model

The repository already proves

  `cl55SpinorAlgEquiv : Cl55 ≃ₐ[ℝ] SpinorMatrix 5`

with `SpinorMatrix 5 = Matrix (Fin 32) (Fin 32) ℝ`.
This owner adds the exact rank-one dyadic reconstruction of that matrix algebra
and transports it back to the Clifford carrier.

A single 16-dimensional half-spinor endomorphism algebra has real dimension
`16^2 = 256`.  Two diagonal half-spinor blocks have dimension `512`; they are
the correct size for an even-Clifford block decomposition, but this file does
not identify them with the native even subalgebra.  The full `32 × 32` operator
algebra has dimension `1024` and requires all four chiral source/target blocks.

No octonionic, twistor, chirality-eigenspace, or conformal interpretation is
promoted here without a separate intertwining theorem.
-/

namespace InfoGeometry.Clifford.Clifford55

open Matrix
open InfoGeometry.Clifford.SpinorRep

noncomputable section

abbrev Spinor32 : Type := SpinorSpace 5
abbrev Mat32 : Type := SpinorMatrix 5
abbrev HalfSpinor16 : Type := Fin 16 → ℝ
abbrev HalfSpinorMatrix : Type := Matrix (Fin 16) (Fin 16) ℝ
abbrev EvenTwoBlockCarrier : Type := HalfSpinorMatrix × HalfSpinorMatrix
abbrev FourBlockCarrier : Type :=
  HalfSpinorMatrix × HalfSpinorMatrix × HalfSpinorMatrix × HalfSpinorMatrix

/-- Rank-one operator `|ψ⟩⟨φ|` in the concrete 32-dimensional spinor carrier. -/
def ketBra (ψ φ : Spinor32) : Mat32 :=
  fun i j => ψ i * φ j

/-- Matrix-unit dyad associated with the standard spinor basis. -/
def dyadicAtom (ij : Fin 32 × Fin 32) : Mat32 :=
  ketBra (Pi.single ij.1 (1 : ℝ)) (Pi.single ij.2 (1 : ℝ))

@[simp] theorem dyadicAtom_apply (i j a b : Fin 32) :
    dyadicAtom (i, j) a b =
      (if i = a then 1 else 0) * (if j = b then 1 else 0) := by
  simp [dyadicAtom, ketBra, Pi.single_apply, eq_comm]

/-- Every spinor operator is exactly a finite linear combination of rank-one
ket-bra dyads. -/
theorem matrix_eq_sum_dyadic (A : Mat32) :
    A = ∑ i : Fin 32, ∑ j : Fin 32, A i j • dyadicAtom (i, j) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply, dyadicAtom, ketBra,
    Pi.single_apply, eq_comm]

/-- The dyadic atoms span the full matrix operator space. -/
theorem dyadic_span_top :
    Submodule.span ℝ (Set.range dyadicAtom) = (⊤ : Submodule ℝ Mat32) := by
  apply top_unique
  intro A hA
  rw [matrix_eq_sum_dyadic A]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.sum_mem _ (fun j _ => ?_)
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨(i, j), rfl⟩)

/-- The Clifford-side rank-one atoms obtained through the already-proved
algebra equivalence `Cl55 ≃ M₃₂(ℝ)`. -/
def cliffordDyadicAtom (ij : Fin 32 × Fin 32) : Cl55 :=
  cl55SpinorAlgEquiv.symm (dyadicAtom ij)

/-- Exact dyadic reconstruction of every element of `Cl(5,5)`.  The
coefficients are simply the matrix entries of its native spinor image. -/
theorem cl55_eq_sum_dyadic (x : Cl55) :
    x = ∑ i : Fin 32, ∑ j : Fin 32,
      (cl55SpinorAlgEquiv x) i j • cliffordDyadicAtom (i, j) := by
  calc
    x = cl55SpinorAlgEquiv.symm (cl55SpinorAlgEquiv x) := by simp
    _ = cl55SpinorAlgEquiv.symm
        (∑ i : Fin 32, ∑ j : Fin 32,
          (cl55SpinorAlgEquiv x) i j • dyadicAtom (i, j)) := by
      rw [← matrix_eq_sum_dyadic (cl55SpinorAlgEquiv x)]
    _ = ∑ i : Fin 32, ∑ j : Fin 32,
        (cl55SpinorAlgEquiv x) i j • cliffordDyadicAtom (i, j) := by
      simp [cliffordDyadicAtom, map_sum, map_smul]

/-- A single real 16-dimensional half-spinor endomorphism block has dimension
`256`. -/
theorem halfSpinorMatrix_finrank :
    Module.finrank ℝ HalfSpinorMatrix = 256 := by
  simp [HalfSpinorMatrix, Module.finrank_matrix, Fintype.card_fin]

/-- Two diagonal 16×16 blocks have dimension `512`, the dimension expected for
the even half of a 1024-dimensional Clifford algebra.  This is only a dimension
ledger, not an identification with `Cl55`'s native even subalgebra. -/
theorem evenTwoBlockCarrier_finrank :
    Module.finrank ℝ EvenTwoBlockCarrier = 512 := by
  simp [EvenTwoBlockCarrier, HalfSpinorMatrix, Module.finrank_prod,
    Module.finrank_matrix, Fintype.card_fin]

/-- Four 16×16 source/target blocks recover the full `32×32` operator-space
dimension. -/
theorem fourBlockCarrier_finrank :
    Module.finrank ℝ FourBlockCarrier = 1024 := by
  simp [FourBlockCarrier, HalfSpinorMatrix, Module.finrank_prod,
    Module.finrank_matrix, Fintype.card_fin]

/-- The full dyadic operator carrier and `Cl(5,5)` have the same native finite
dimension, with the stronger algebra equivalence supplied by
`cl55SpinorAlgEquiv`. -/
theorem cl55_and_dyadic_operator_finrank :
    Module.finrank ℝ Cl55 = 1024 ∧ Module.finrank ℝ Mat32 = 1024 := by
  exact ⟨cl55_finrank, spinorMatrix_finrank⟩

/-- Kernel-level statement of the correct reconstruction hierarchy: one
16×16 block is strictly smaller than the full Clifford operator algebra, while
four such blocks have the full dimension. -/
theorem half_block_not_full_dimension :
    Module.finrank ℝ HalfSpinorMatrix < Module.finrank ℝ Cl55 := by
  rw [halfSpinorMatrix_finrank, cl55_finrank]
  norm_num

end

end InfoGeometry.Clifford.Clifford55
