import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import InfoGeometry.Canonical.TwoSheetStokesKreinTopological

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetStokesKreinRealLinear

open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint
open InfoGeometry.Canonical.TwoSheetStokesKreinTopological

def stokesKreinAdjointRealLinear : StokesQuad →ₗ[ℝ] StokesQuad where
  toFun := stokesKreinAdjoint
  map_add' q r := by
    rcases q with ⟨q0, q3, q1, q2⟩
    rcases r with ⟨r0, r3, r1, r2⟩
    simp [stokesKreinAdjoint, star_add, add_comm]
  map_smul' c q := by
    rcases q with ⟨q0, q1, q2, q3⟩
    simp [stokesKreinAdjoint, star_smul, star_trivial]

theorem stokesKreinAdjointRealLinear_apply (q : StokesQuad) :
    stokesKreinAdjointRealLinear q = stokesKreinAdjoint q := rfl

def stokesKreinAdjointRealLinearEquiv : StokesQuad ≃ₗ[ℝ] StokesQuad where
  toLinearMap := stokesKreinAdjointRealLinear
  invFun := stokesKreinAdjoint
  left_inv q := by
    rcases q with ⟨q0, q1, q2, q3⟩
    simp [stokesKreinAdjoint, stokesKreinAdjointRealLinear, star_star]
  right_inv q := by
    rcases q with ⟨q0, q1, q2, q3⟩
    simp [stokesKreinAdjoint, stokesKreinAdjointRealLinear, star_star]

theorem stokesKreinAdjointRealLinearEquiv_apply (q : StokesQuad) :
    stokesKreinAdjointRealLinearEquiv q = stokesKreinAdjoint q := rfl

def stokesKreinAdjointContinuousLinearEquiv :
    StokesQuad ≃L[ℝ] StokesQuad :=
  ContinuousLinearEquiv.mk stokesKreinAdjointRealLinearEquiv
    (by
      have h : Continuous (stokesKreinAdjoint : StokesQuad → StokesQuad) := by
        have heq : (stokesKreinAdjointHomeomorph : StokesQuad → StokesQuad) =
            stokesKreinAdjoint := by
          funext q
          exact stokesKreinAdjointHomeomorph_apply q
        rw [← heq]
        exact stokesKreinAdjointHomeomorph.continuous
      simpa only [stokesKreinAdjointRealLinearEquiv_apply] using h)
    (by
      have h : Continuous (stokesKreinAdjoint : StokesQuad → StokesQuad) := by
        have heq : (stokesKreinAdjointHomeomorph : StokesQuad → StokesQuad) =
            stokesKreinAdjoint := by
          funext q
          exact stokesKreinAdjointHomeomorph_apply q
        rw [← heq]
        exact stokesKreinAdjointHomeomorph.continuous
      simpa only [stokesKreinAdjointRealLinearEquiv_apply] using h)

theorem stokesKreinAdjointContinuousLinearEquiv_apply (q : StokesQuad) :
    stokesKreinAdjointContinuousLinearEquiv q = stokesKreinAdjoint q := by
  exact stokesKreinAdjointRealLinearEquiv_apply q

end InfoGeometry.Canonical.TwoSheetStokesKreinRealLinear
