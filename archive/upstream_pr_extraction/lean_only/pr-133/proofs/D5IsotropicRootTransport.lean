import proofs.D5IsotropicDiagonalLieEquiv

/-!
# Transport of complex `D₅` root eigenvectors through the isotropic/diagonal Lie equivalence

This owner transports the already-certified matrix root calculus into the
existing diagonal `so(5,5)`-form carrier.  It does not identify this carrier
with the real TKK carrier; that requires the separate scalar-extension
construction in `TKK55Complexification`.
-/

noncomputable section
namespace D5IsotropicRootTransport

open D5ComplexMatrixRootSpaces
open D5IsotropicDiagonalLieEquiv

abbrev IsoSO10 := D5IsotropicDiagonalLieEquiv.isotropicSO10
abbrev DiagSO10 := D5IsotropicDiagonalLieEquiv.diagonalSO10

 def isotropicCartan (h : Half → ℂ) : IsoSO10 :=
  ⟨cartan h, cartan_isSplitOrthogonal h⟩

def isotropicDifferenceRoot (i j : Half) (hij : i ≠ j) : IsoSO10 :=
  ⟨differenceRootMatrix i j, differenceRoot_isSplitOrthogonal i j hij⟩

def isotropicSumRoot (i j : Half) (hij : i ≠ j) : IsoSO10 :=
  ⟨sumRootMatrix i j, sumRoot_isSplitOrthogonal i j hij⟩

def isotropicNegSumRoot (i j : Half) (hij : i ≠ j) : IsoSO10 :=
  ⟨negSumRootMatrix i j, negSumRoot_isSplitOrthogonal i j hij⟩

def diagonalCartan (h : Half → ℂ) : DiagSO10 :=
  isotropicDiagonalLieEquiv (isotropicCartan h)

def diagonalDifferenceRoot (i j : Half) (hij : i ≠ j) : DiagSO10 :=
  isotropicDiagonalLieEquiv (isotropicDifferenceRoot i j hij)

def diagonalSumRoot (i j : Half) (hij : i ≠ j) : DiagSO10 :=
  isotropicDiagonalLieEquiv (isotropicSumRoot i j hij)

def diagonalNegSumRoot (i j : Half) (hij : i ≠ j) : DiagSO10 :=
  isotropicDiagonalLieEquiv (isotropicNegSumRoot i j hij)

theorem isotropic_difference_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅isotropicCartan h, isotropicDifferenceRoot i j hij⁆ =
      (h i - h j) • isotropicDifferenceRoot i j hij := by
  apply Subtype.ext
  change commutator (cartan h) (differenceRootMatrix i j) =
    (h i - h j) • differenceRootMatrix i j
  exact cartan_bracket_difference h i j

theorem isotropic_sum_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅isotropicCartan h, isotropicSumRoot i j hij⁆ =
      (h i + h j) • isotropicSumRoot i j hij := by
  apply Subtype.ext
  change commutator (cartan h) (sumRootMatrix i j) =
    (h i + h j) • sumRootMatrix i j
  exact cartan_bracket_sum h i j

theorem isotropic_negSum_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅isotropicCartan h, isotropicNegSumRoot i j hij⁆ =
      (-h i - h j) • isotropicNegSumRoot i j hij := by
  apply Subtype.ext
  change commutator (cartan h) (negSumRootMatrix i j) =
    (-h i - h j) • negSumRootMatrix i j
  exact cartan_bracket_negSum h i j

theorem diagonal_difference_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅diagonalCartan h, diagonalDifferenceRoot i j hij⁆ =
      (h i - h j) • diagonalDifferenceRoot i j hij := by
  change ⁅isotropicDiagonalLieEquiv (isotropicCartan h),
      isotropicDiagonalLieEquiv (isotropicDifferenceRoot i j hij)⁆ = _
  rw [← isotropicDiagonalLieEquiv.map_lie]
  rw [isotropic_difference_root_eigen h i j hij]
  rw [map_smul]
  rfl

theorem diagonal_sum_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅diagonalCartan h, diagonalSumRoot i j hij⁆ =
      (h i + h j) • diagonalSumRoot i j hij := by
  change ⁅isotropicDiagonalLieEquiv (isotropicCartan h),
      isotropicDiagonalLieEquiv (isotropicSumRoot i j hij)⁆ = _
  rw [← isotropicDiagonalLieEquiv.map_lie]
  rw [isotropic_sum_root_eigen h i j hij]
  rw [map_smul]
  rfl

theorem diagonal_negSum_root_eigen (h : Half → ℂ) (i j : Half)
    (hij : i ≠ j) :
    ⁅diagonalCartan h, diagonalNegSumRoot i j hij⁆ =
      (-h i - h j) • diagonalNegSumRoot i j hij := by
  change ⁅isotropicDiagonalLieEquiv (isotropicCartan h),
      isotropicDiagonalLieEquiv (isotropicNegSumRoot i j hij)⁆ = _
  rw [← isotropicDiagonalLieEquiv.map_lie]
  rw [isotropic_negSum_root_eigen h i j hij]
  rw [map_smul]
  rfl

theorem diagonal_difference_root_ne_zero (i j : Half) (hij : i ≠ j) :
    diagonalDifferenceRoot i j hij ≠ 0 := by
  intro h
  have h' := congrArg (fun x => isotropicDiagonalLieEquiv.symm x) h
  have hzero : isotropicDifferenceRoot i j hij = 0 := by
    simpa [diagonalDifferenceRoot] using h'
  apply differenceRootMatrix_ne_zero hij
  simpa [isotropicDifferenceRoot] using congrArg Subtype.val hzero

end D5IsotropicRootTransport
end noncomputable section
