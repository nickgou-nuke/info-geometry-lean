import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Canonical.H3ZornBasis

/-- Coordinate linear map from $H_3(\mathbb{O}_s)$ to $\mathbb{R}^{27}$. -/
def h3ZornToCoord : H3Zorn ℝ →ₗ[ℝ] (Fin 27 → ℝ) where
  toFun X := h3ZornCoordinate X
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' r X := by ext i; fin_cases i <;> rfl

theorem h3ZornToCoord_injective :
    Function.Injective h3ZornToCoord := by
  intro X Y hXY
  have h := congrFun hXY
  apply H3Zorn.ext_h3
  · exact h 0
  · exact h 1
  · exact h 2
  · apply ZornVectorMatrix.ext
    · exact h 3
    · funext j; fin_cases j
      · exact h 4
      · exact h 5
      · exact h 6
    · funext j; fin_cases j
      · exact h 7
      · exact h 8
      · exact h 9
    · exact h 10
  · apply ZornVectorMatrix.ext
    · exact h 11
    · funext j; fin_cases j
      · exact h 12
      · exact h 13
      · exact h 14
    · funext j; fin_cases j
      · exact h 15
      · exact h 16
      · exact h 17
    · exact h 18
  · apply ZornVectorMatrix.ext
    · exact h 19
    · funext j; fin_cases j
      · exact h 20
      · exact h 21
      · exact h 22
    · funext j; fin_cases j
      · exact h 23
      · exact h 24
      · exact h 25
    · exact h 26

theorem h3ZornToCoord_surjective :
    Function.Surjective h3ZornToCoord := by
  intro c
  let X : H3Zorn ℝ :=
    { α₁ := c 0, α₂ := c 1, α₃ := c 2,
      a := { a := c 3, v := fun j => match j with | 0 => c 4 | 1 => c 5 | 2 => c 6,
             w := fun j => match j with | 0 => c 7 | 1 => c 8 | 2 => c 9, b := c 10 },
      b := { a := c 11, v := fun j => match j with | 0 => c 12 | 1 => c 13 | 2 => c 14,
             w := fun j => match j with | 0 => c 15 | 1 => c 16 | 2 => c 17, b := c 18 },
      c := { a := c 19, v := fun j => match j with | 0 => c 20 | 1 => c 21 | 2 => c 22,
             w := fun j => match j with | 0 => c 23 | 1 => c 24 | 2 => c 25, b := c 26 } }
  use X
  ext i
  fin_cases i <;> rfl

/-- Explicit Linear Equivalence $H_3(\mathbb{O}_s) \cong \mathbb{R}^{27}$. -/
def h3ZornLinearEquiv : H3Zorn ℝ ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  LinearEquiv.ofBijective h3ZornToCoord ⟨h3ZornToCoord_injective, h3ZornToCoord_surjective⟩

theorem h3ZornCoordinate_probe_eq (i j : Fin 27) :
    h3ZornCoordinate (h3ZornProbe i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

/-- 🏆 **The Canonical 27-Element Basis for H₃(𝕆_s)** -/
def h3ZornCoordinateBasis : Module.Basis (Fin 27) ℝ (H3Zorn ℝ) :=
  (Pi.basisFun ℝ (Fin 27)).map h3ZornLinearEquiv.symm

@[simp] theorem h3ZornCoordinateBasis_apply (i : Fin 27) :
    h3ZornCoordinateBasis i = h3ZornProbe i := by
  apply h3ZornLinearEquiv.injective
  have h_symm := h3ZornLinearEquiv.apply_symm_apply (Pi.basisFun ℝ (Fin 27) i)
  have h_basis : h3ZornLinearEquiv (h3ZornCoordinateBasis i) = Pi.basisFun ℝ (Fin 27) i := by
    dsimp [h3ZornCoordinateBasis]
    exact h_symm
  rw [h_basis]
  ext j
  rw [Pi.basisFun_apply, Pi.single_apply]
  dsimp [h3ZornLinearEquiv, h3ZornToCoord]
  rw [h3ZornCoordinate_probe_eq]
  by_cases h : i = j
  · subst h
    simp
  · have hne : ¬ j = i := by intro hj; exact h hj.symm
    simp [h, hne]

/-- **Theorem (Dimension of Albert Carrier)**: $\dim_{\mathbb{R}} H_3(\mathbb{O}_s) = 27$. -/
theorem finrank_H3Zorn :
    Module.finrank ℝ (H3Zorn ℝ) = 27 := by
  rw [h3ZornLinearEquiv.finrank_eq]
  simp

/-- **Theorem (Repr Coordinates Match h3ZornCoordinate)**:
    $$(h3ZornCoordinateBasis.repr X) j = h3ZornCoordinate X j$$
-/
theorem h3ZornCoordinateBasis_repr_apply (X : H3Zorn ℝ) (j : Fin 27) :
    (h3ZornCoordinateBasis.repr X) j = h3ZornCoordinate X j := by
  dsimp [h3ZornCoordinateBasis]
  simp [Pi.basisFun_repr, h3ZornLinearEquiv, h3ZornToCoord]

end InfoGeometry.Canonical.H3ZornBasis
