import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.SplitComplex

/-!
# Native split-composition seed inside `Cl(1,1)`

This file records the first carrier-safe step in the split-composition ladder.
It does not yet claim a full algebra equivalence
`CliffordAlgebra.even q11 ≃ₐ[ℝ] SplitComplex.Carrier ℝ`, because the current
split-complex coordinate owner is not yet bundled as a real algebra.

What is proved here is the exact native even generator:

* `e₊e₋` is an element of `CliffordAlgebra.even q11`;
* under the already proved Pauli equivalence `cl11EquivMat`, it is exactly
  the matrix `J1`;
* this even generator squares to `1`, which is the defining split-complex
  relation `ε² = 1`.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCompositionCl11Bridge

open InfoGeometry.Clifford.Cl11Matrix

/-- The canonical bivector generator of the even subalgebra of `Cl(1,1)`. -/
def cl11EvenSplitGenerator : CliffordAlgebra.even q11 :=
  (CliffordAlgebra.even.ι q11).bilin (1, 0) (0, 1)

/-- Forgetting the even-subalgebra wrapper gives the ordinary Clifford bivector
`e₊e₋`. -/
@[simp] theorem cl11EvenSplitGenerator_val :
    (cl11EvenSplitGenerator : CliffordAlgebra q11) = J1_cl := by
  rfl

/-- Under the established Pauli algebra equivalence, the even bivector is the
split-square matrix generator `J1`. -/
@[simp] theorem cl11EvenSplitGenerator_matrix :
    cl11EquivMat (cl11EvenSplitGenerator : CliffordAlgebra q11) = J1 := by
  rw [cl11EvenSplitGenerator_val, J1_cl, map_mul,
    cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  exact Eplus_mul_Eminus

/-- The native even generator satisfies the split-complex relation `ε² = 1`. -/
@[simp] theorem cl11EvenSplitGenerator_sq :
    cl11EvenSplitGenerator * cl11EvenSplitGenerator = 1 := by
  apply Subtype.ext
  apply cl11EquivMat.injective
  simp only [Subalgebra.coe_mul, Subalgebra.coe_one, map_mul, map_one,
    cl11EvenSplitGenerator_matrix]
  exact J1_sq

/-- Generator-level compatibility with the repository split-complex seed:
both distinguished generators square to the multiplicative identity. -/
theorem cl11_even_split_complex_generator_relations :
    cl11EvenSplitGenerator * cl11EvenSplitGenerator = 1 ∧
      InfoGeometry.Canonical.SplitComplex.Carrier.eps (R := ℝ) *
        InfoGeometry.Canonical.SplitComplex.Carrier.eps (R := ℝ) = 1 := by
  exact ⟨cl11EvenSplitGenerator_sq,
    InfoGeometry.Canonical.SplitComplex.Carrier.eps_sq (R := ℝ)⟩

end InfoGeometry.Clifford.SplitCompositionCl11Bridge
