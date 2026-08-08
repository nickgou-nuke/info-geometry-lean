import proofs.D5DiagonalComplexification

/-!
# Lie bridge for the complexification of diagonal `so(5,5)`

The existing file proves a linear equivalence between the scalar extension of
real `diagonalSO55` and the complex matrix carrier.  This owner upgrades the
map to a Lie equivalence by proving bracket preservation.
-/

noncomputable section
namespace D5DiagonalComplexificationLie

open scoped TensorProduct
open D5DiagonalComplexification
open TKK55Complexification
open SO55HyperbolicDiagonalLieEquiv

abbrev ComplexDiagIn := TKK55Complexification.ComplexDiagonalSO55
abbrev ComplexDiagOut := D5DiagonalComplexification.complexDiagonalSO55
abbrev RealDiag := SO55HyperbolicDiagonalLieEquiv.diagonalSO55

/-- The real embedding preserves the matrix commutator. -/
theorem embedRealDiagonal_lie (A B : RealDiag) :
    embedRealDiagonal ⁅A, B⁆ =
      ⁅embedRealDiagonal A, embedRealDiagonal B⁆ := by
  apply Subtype.ext
  change embedRealMatrix (A.1 * B.1 - B.1 * A.1) =
    embedRealMatrix A.1 * embedRealMatrix B.1 -
      embedRealMatrix B.1 * embedRealMatrix A.1
  simp [sub_eq_add_neg, embedRealMatrix_add, embedRealMatrix_mul,
    map_neg]

/-- Scalar extension of the real embedding preserves the complex Lie bracket. -/
theorem complexificationToDiagonal_lie (x y : ComplexDiagIn) :
    complexificationToDiagonal ⁅x, y⁆ =
      ⁅complexificationToDiagonal x,
        complexificationToDiagonal y⁆ := by
  refine x.induction_on ?_ ?_ ?_
  · simp
  · intro z A
    refine y.induction_on ?_ ?_ ?_
    · simp
    · intro w B
      simp only [complexificationToDiagonal_tmul]
      change complexificationToDiagonal ⁅z ⊗ₜ[ℝ] A, w ⊗ₜ[ℝ] B⁆ = _
      simp [embedRealDiagonal_lie, mul_comm, mul_left_comm, mul_assoc]
    · intro u v hu hv
      simp [lie_add, map_add, hu, hv]
  · intro u v hu hv
    simp [add_lie, map_add, hu, hv]

/-- Complexified diagonal `so(5,5)` as a genuine complex Lie equivalence. -/
def diagonalComplexificationLieHom :
    ComplexDiagIn →ₗ⁅ℂ⁆ ComplexDiagOut where
  toLinearMap := complexificationToDiagonal
  map_lie' := fun {x y} => complexificationToDiagonal_lie x y

 def diagonalComplexificationLieEquiv :
    ComplexDiagIn ≃ₗ⁅ℂ⁆ ComplexDiagOut :=
  LieEquiv.ofBijective diagonalComplexificationLieHom <|
    diagonalComplexificationLinearEquiv.bijective

@[simp] theorem diagonalComplexificationLieEquiv_apply (x : ComplexDiagIn) :
    diagonalComplexificationLieEquiv x = complexificationToDiagonal x := rfl

end D5DiagonalComplexificationLie
end noncomputable section
