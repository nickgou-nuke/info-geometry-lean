import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Crawford Dirac bispinor densities: explicit finite kernel

This module gives a concrete finite model for the Crawford layer:
Dirac bispinor densities indexed by the standard sixteen Clifford labels.

The model is deliberately explicit:

* spinors are functions `Fin 4 → ℂ`;
* Dirac matrices are `4 × 4` complex matrices;
* the Weyl-basis gamma matrices are written entry-by-entry;
* the sixteen bilinear labels are an enumerated finite type;
* density carriers are functions from those labels to scalars;
* the defining finite Clifford matrix identities are proved by entrywise
  matrix calculation.

The module proves exactly this finite coordinate layer.  It does not assert an
unproved inversion theorem.
-/

namespace InfoGeometry
namespace Clifford
namespace CrawfordDiracBispinorDensities

/-- Four-component complex Dirac spinor. -/
abbrev DiracSpinor : Type :=
  Fin 4 → ℂ

/-- Four-by-four complex Dirac matrix. -/
abbrev DiracMatrix : Type :=
  Matrix (Fin 4) (Fin 4) ℂ

/-- `γ⁰` in the Weyl basis. -/
def gamma0 : DiracMatrix :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- `γ¹` in the Weyl basis. -/
def gamma1 : DiracMatrix :=
  !![(0 : ℂ), 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- `γ²` in the Weyl basis. -/
def gamma2 : DiracMatrix :=
  !![(0 : ℂ), 0, 0, -Complex.I;
     0, 0, Complex.I, 0;
     0, Complex.I, 0, 0;
     -Complex.I, 0, 0, 0]

/-- `γ³` in the Weyl basis. -/
def gamma3 : DiracMatrix :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

/-- Chirality matrix `γ⁵` in the Weyl basis. -/
def gamma5 : DiracMatrix :=
  !![(-1 : ℂ), 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Minkowski gamma matrices indexed by `Fin 4`. -/
def gamma (mu : Fin 4) : DiracMatrix :=
  match mu with
  | 0 => gamma0
  | 1 => gamma1
  | 2 => gamma2
  | 3 => gamma3

theorem gamma0_mul_self : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gamma1_mul_self : gamma1 * gamma1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem gamma2_mul_self : gamma2 * gamma2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem gamma3_mul_self : gamma3 * gamma3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem gamma5_mul_self : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gamma0_gamma1_anticomm : gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma1]

theorem gamma0_gamma2_anticomm : gamma0 * gamma2 + gamma2 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma2]

theorem gamma0_gamma3_anticomm : gamma0 * gamma3 + gamma3 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma3]

theorem gamma1_gamma2_anticomm : gamma1 * gamma2 + gamma2 * gamma1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2]

theorem gamma1_gamma3_anticomm : gamma1 * gamma3 + gamma3 * gamma1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma3]

theorem gamma2_gamma3_anticomm : gamma2 * gamma3 + gamma3 * gamma2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma2, gamma3]

theorem gamma5_gamma0_anticomm : gamma5 * gamma0 + gamma0 * gamma5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0]

theorem gamma5_gamma1_anticomm : gamma5 * gamma1 + gamma1 * gamma5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma1]

theorem gamma5_gamma2_anticomm : gamma5 * gamma2 + gamma2 * gamma5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma2]

theorem gamma5_gamma3_anticomm : gamma5 * gamma3 + gamma3 * gamma5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma3]

/-- Six unordered bivector labels `μ < ν`. -/
inductive BivectorLabel where
  | b01
  | b02
  | b03
  | b12
  | b13
  | b23
deriving DecidableEq, Repr

/-- Left index of a bivector label. -/
def bivectorLeft : BivectorLabel → Fin 4
  | BivectorLabel.b01 => 0
  | BivectorLabel.b02 => 0
  | BivectorLabel.b03 => 0
  | BivectorLabel.b12 => 1
  | BivectorLabel.b13 => 1
  | BivectorLabel.b23 => 2

/-- Right index of a bivector label. -/
def bivectorRight : BivectorLabel → Fin 4
  | BivectorLabel.b01 => 1
  | BivectorLabel.b02 => 2
  | BivectorLabel.b03 => 3
  | BivectorLabel.b12 => 2
  | BivectorLabel.b13 => 3
  | BivectorLabel.b23 => 3

/-- The sixteen Crawford/Dirac bilinear labels. -/
inductive DiracBilinearLabel where
  | scalar
  | pseudoscalar
  | vector (mu : Fin 4)
  | axial (mu : Fin 4)
  | bivector (b : BivectorLabel)
deriving DecidableEq, Repr

/-- Explicit map from the sixteen labels to `Fin 16`. -/
def diracBilinearLabelToFin : DiracBilinearLabel → Fin 16
  | DiracBilinearLabel.scalar => 0
  | DiracBilinearLabel.pseudoscalar => 1
  | DiracBilinearLabel.vector 0 => 2
  | DiracBilinearLabel.vector 1 => 3
  | DiracBilinearLabel.vector 2 => 4
  | DiracBilinearLabel.vector 3 => 5
  | DiracBilinearLabel.axial 0 => 6
  | DiracBilinearLabel.axial 1 => 7
  | DiracBilinearLabel.axial 2 => 8
  | DiracBilinearLabel.axial 3 => 9
  | DiracBilinearLabel.bivector BivectorLabel.b01 => 10
  | DiracBilinearLabel.bivector BivectorLabel.b02 => 11
  | DiracBilinearLabel.bivector BivectorLabel.b03 => 12
  | DiracBilinearLabel.bivector BivectorLabel.b12 => 13
  | DiracBilinearLabel.bivector BivectorLabel.b13 => 14
  | DiracBilinearLabel.bivector BivectorLabel.b23 => 15

/-- Explicit inverse map from `Fin 16` to the sixteen labels. -/
def finToDiracBilinearLabel (k : Fin 16) : DiracBilinearLabel :=
  if k = 0 then DiracBilinearLabel.scalar
  else if k = 1 then DiracBilinearLabel.pseudoscalar
  else if k = 2 then DiracBilinearLabel.vector 0
  else if k = 3 then DiracBilinearLabel.vector 1
  else if k = 4 then DiracBilinearLabel.vector 2
  else if k = 5 then DiracBilinearLabel.vector 3
  else if k = 6 then DiracBilinearLabel.axial 0
  else if k = 7 then DiracBilinearLabel.axial 1
  else if k = 8 then DiracBilinearLabel.axial 2
  else if k = 9 then DiracBilinearLabel.axial 3
  else if k = 10 then DiracBilinearLabel.bivector BivectorLabel.b01
  else if k = 11 then DiracBilinearLabel.bivector BivectorLabel.b02
  else if k = 12 then DiracBilinearLabel.bivector BivectorLabel.b03
  else if k = 13 then DiracBilinearLabel.bivector BivectorLabel.b12
  else if k = 14 then DiracBilinearLabel.bivector BivectorLabel.b13
  else DiracBilinearLabel.bivector BivectorLabel.b23

theorem finToDiracBilinearLabel_left_inverse (l : DiracBilinearLabel) :
    finToDiracBilinearLabel (diracBilinearLabelToFin l) = l := by
  cases l with
  | scalar => rfl
  | pseudoscalar => rfl
  | vector mu =>
      fin_cases mu <;> rfl
  | axial mu =>
      fin_cases mu <;> rfl
  | bivector b =>
      cases b <;> rfl

theorem diracBilinearLabelToFin_right_inverse (k : Fin 16) :
    diracBilinearLabelToFin (finToDiracBilinearLabel k) = k := by
  fin_cases k <;> simp [finToDiracBilinearLabel, diracBilinearLabelToFin]

/-- Explicit equivalence between Crawford labels and `Fin 16`. -/
def diracBilinearLabelEquivFin16 : DiracBilinearLabel ≃ Fin 16 where
  toFun := diracBilinearLabelToFin
  invFun := finToDiracBilinearLabel
  left_inv := finToDiracBilinearLabel_left_inverse
  right_inv := diracBilinearLabelToFin_right_inverse

instance : Fintype DiracBilinearLabel :=
  Fintype.ofEquiv (Fin 16) diracBilinearLabelEquivFin16.symm

theorem diracBilinearLabel_card :
    Fintype.card DiracBilinearLabel = 16 := by
  rw [Fintype.card_congr diracBilinearLabelEquivFin16]
  rfl

/-- Real Crawford density carrier: sixteen real bispinor densities. -/
abbrev RealDiracBispinorDensity : Type :=
  DiracBilinearLabel → ℝ

/-- Complex Crawford density carrier. -/
abbrev ComplexDiracBispinorDensity : Type :=
  DiracBilinearLabel → ℂ

theorem realDiracBispinorDensity_finrank :
    Module.finrank ℝ RealDiracBispinorDensity = 16 := by
  rw [Module.finrank_fintype_fun_eq_card, diracBilinearLabel_card]

theorem complexDiracBispinorDensity_finrank :
    Module.finrank ℂ ComplexDiracBispinorDensity = 16 := by
  rw [Module.finrank_fintype_fun_eq_card, diracBilinearLabel_card]

/-- Coordinate map from label-indexed real densities to `Fin 16` coordinates. -/
def realDensityCoordinates (rho : RealDiracBispinorDensity) : Fin 16 → ℝ :=
  fun k => rho (finToDiracBilinearLabel k)

/-- Build a real density from its `Fin 16` coordinates. -/
def realDensityOfCoordinates (x : Fin 16 → ℝ) : RealDiracBispinorDensity :=
  fun l => x (diracBilinearLabelToFin l)

@[simp] theorem realDensityOfCoordinates_coordinates (rho : RealDiracBispinorDensity) :
    realDensityOfCoordinates (realDensityCoordinates rho) = rho := by
  ext l
  simp [realDensityOfCoordinates, realDensityCoordinates,
    finToDiracBilinearLabel_left_inverse]

@[simp] theorem realDensityCoordinates_ofCoordinates (x : Fin 16 → ℝ) :
    realDensityCoordinates (realDensityOfCoordinates x) = x := by
  ext k
  simp [realDensityOfCoordinates, realDensityCoordinates,
    diracBilinearLabelToFin_right_inverse]

/-- Matrix assigned to each of the sixteen bilinear labels. -/
def diracBilinearMatrix : DiracBilinearLabel → DiracMatrix
  | DiracBilinearLabel.scalar => 1
  | DiracBilinearLabel.pseudoscalar => gamma5
  | DiracBilinearLabel.vector mu => gamma mu
  | DiracBilinearLabel.axial mu => gamma mu * gamma5
  | DiracBilinearLabel.bivector b => gamma (bivectorLeft b) * gamma (bivectorRight b)

/-- Explicit bispinor density component `ψbar Γ_l ψ`. -/
def bispinorDensityComponent
    (psiBar psi : DiracSpinor) (l : DiracBilinearLabel) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    psiBar a * diracBilinearMatrix l a b * psi b

/-- The full sixteen-component complex bispinor density. -/
def bispinorDensity (psiBar psi : DiracSpinor) : ComplexDiracBispinorDensity :=
  fun l => bispinorDensityComponent psiBar psi l

@[simp] theorem bispinorDensity_apply
    (psiBar psi : DiracSpinor) (l : DiracBilinearLabel) :
    bispinorDensity psiBar psi l = bispinorDensityComponent psiBar psi l := by
  rfl

end CrawfordDiracBispinorDensities
end Clifford
end InfoGeometry
