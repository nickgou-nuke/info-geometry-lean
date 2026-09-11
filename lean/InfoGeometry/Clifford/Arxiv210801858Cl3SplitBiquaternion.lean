import InfoGeometry.Clifford.Cl3ComplexMatrixProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# arXiv:2108.01858v2 — finite `Cl(3)` split-biquaternion slice

This module records the theorem-safe algebraic core of

*V. Vaibhava and T. P. Singh, "Left-Right Symmetric Fermions and Sterile
Neutrinos from Complex Split Biquaternions and Bioctonions",
arXiv:2108.01858v2*.

The paper uses the complex split-biquaternion interpretation of `Cl(3)`.  The
repository owner for the kernel proof is
`InfoGeometry.Clifford.Cl3ComplexMatrixProduct`, which proves the concrete
finite classification

`CliffordAlgebra q3 ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ`.

This file only re-exports the finite split/chirality facts relevant to that
paper:

* complex dimension `8`;
* chirality maps to `(1,-1)`;
* the two projectors map to `(1,0)` and `(0,1)`;
* the classification equivalence is available from the owner.

No theorem here asserts sterile-neutrino phenomenology, Pati--Salam gauge
symmetry, Higgs coupling, dark-matter physics, generation counting, `Cl(7)`
bioctonion classification, or exceptional-Jordan/E₆ physics.
-/

namespace InfoGeometry.Clifford.Arxiv210801858Cl3SplitBiquaternion

/-- Complex dimension of the finite `Cl(3)` / split-biquaternion carrier. -/
theorem cl3_complex_dimension_eight :
    Module.finrank ℂ (CliffordAlgebra InfoGeometry.Clifford.Cl3ComplexMatrixProduct.q3) = 8 :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.finrank_cl3

/-- The product target `M₂(ℂ) × M₂(ℂ)` has complex dimension eight. -/
theorem split_biquaternion_product_dimension_eight :
    Module.finrank ℂ InfoGeometry.Clifford.Cl3ComplexMatrixProduct.ProdMat2C = 8 :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.finrank_prodMat2C

/-- Chirality is the finite block-sign element `(1,-1)`. -/
theorem chirality_block_split :
    InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
        InfoGeometry.Clifford.Cl3ComplexMatrixProduct.chirality = (1, -1) :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd_chirality

/-- The left split-biquaternion projector maps to the first matrix block. -/
theorem left_projector_block :
    InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
        InfoGeometry.Clifford.Cl3ComplexMatrixProduct.pL = (1, 0) :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd_pL

/-- The right split-biquaternion projector maps to the second matrix block. -/
theorem right_projector_block :
    InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
        InfoGeometry.Clifford.Cl3ComplexMatrixProduct.pR = (0, 1) :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd_pR

/-- The concrete algebra equivalence supplied by the owner file. -/
noncomputable def cl3_split_biquaternion_equiv :
    CliffordAlgebra InfoGeometry.Clifford.Cl3ComplexMatrixProduct.q3 ≃ₐ[ℂ]
      InfoGeometry.Clifford.Cl3ComplexMatrixProduct.ProdMat2C :=
  InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3EquivProdMat2C

/-- Consolidated paper-safe finite split-biquaternion packet. -/
theorem arxiv210801858_cl3_split_biquaternion_packet :
    Module.finrank ℂ (CliffordAlgebra InfoGeometry.Clifford.Cl3ComplexMatrixProduct.q3) = 8 ∧
      Module.finrank ℂ InfoGeometry.Clifford.Cl3ComplexMatrixProduct.ProdMat2C = 8 ∧
      InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
          InfoGeometry.Clifford.Cl3ComplexMatrixProduct.chirality = (1, -1) ∧
      InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
          InfoGeometry.Clifford.Cl3ComplexMatrixProduct.pL = (1, 0) ∧
      InfoGeometry.Clifford.Cl3ComplexMatrixProduct.cl3ToProd
          InfoGeometry.Clifford.Cl3ComplexMatrixProduct.pR = (0, 1) := by
  exact ⟨cl3_complex_dimension_eight, split_biquaternion_product_dimension_eight,
    chirality_block_split, left_projector_block, right_projector_block⟩

end InfoGeometry.Clifford.Arxiv210801858Cl3SplitBiquaternion
