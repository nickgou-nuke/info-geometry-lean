import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Canonical.TwoSheetOperatorCoordinates

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetStokesCoordinates

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates

abbrev StokesQuad := M3C × M3C × M3C × M3C

def blocksToStokes : OperatorBlocks →ₗ[ℂ] StokesQuad where
  toFun b :=
    let pp := b.1
    let pn := b.2.1
    let np := b.2.2.1
    let nn := b.2.2.2
    ( (2 : ℂ)⁻¹ • (pp + nn),
      (2 : ℂ)⁻¹ • (pn + np),
      (2 * Complex.I)⁻¹ • (np - pn),
      (2 : ℂ)⁻¹ • (pp - nn) )
  map_add' A B := by
    apply Prod.ext
    · ext i j
      simp [Matrix.add_apply]
      ring
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_apply]
        ring
      · apply Prod.ext
        · ext i j
          simp [Matrix.add_apply]
          ring
        · ext i j
          simp [Matrix.add_apply]
          ring
  map_smul' c A := by
    apply Prod.ext
    · ext i j
      simp [Matrix.smul_apply]
      ring
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_apply]
        ring
      · apply Prod.ext
        · ext i j
          simp [Matrix.smul_apply]
          ring
        · ext i j
          simp [Matrix.smul_apply]
          ring

def stokesToBlocks : StokesQuad →ₗ[ℂ] OperatorBlocks where
  toFun q :=
    let a0 := q.1
    let a1 := q.2.1
    let a2 := q.2.2.1
    let a3 := q.2.2.2
    (a0 + a3, a1 - Complex.I • a2, a1 + Complex.I • a2, a0 - a3)
  map_add' A B := by
    apply Prod.ext
    · ext i j
      simp [Matrix.add_apply]
      ring
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_apply]
        ring
      · apply Prod.ext
        · ext i j
          simp [Matrix.add_apply]
          ring
        · ext i j
          simp [Matrix.add_apply]
          ring
  map_smul' c A := by
    apply Prod.ext
    · ext i j
      simp [Matrix.smul_apply]
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_apply]
        ring
      · apply Prod.ext
        · ext i j
          simp [Matrix.smul_apply]
          ring
        · ext i j
          simp [Matrix.smul_apply]
          ring

theorem stokesToBlocks_blocksToStokes (b : OperatorBlocks) :
    stokesToBlocks (blocksToStokes b) = b := by
  rcases b with ⟨pp, pn, np, nn⟩
  apply Prod.ext
  · ext i j
    simp [blocksToStokes, stokesToBlocks]
    all_goals field_simp
    all_goals ring_nf
  · apply Prod.ext
    · ext i j
      simp [blocksToStokes, stokesToBlocks]
      all_goals field_simp
      all_goals ring_nf
      all_goals ring_nf
      all_goals simp [Complex.I_mul_I]
      all_goals ring
    · apply Prod.ext
      · ext i j
        simp [blocksToStokes, stokesToBlocks]
        all_goals field_simp
        all_goals ring_nf
        all_goals simp [Complex.I_mul_I]
        all_goals ring
      · ext i j
        simp [blocksToStokes, stokesToBlocks]
        all_goals field_simp
        all_goals ring_nf
        all_goals simp [Complex.I_mul_I]
        all_goals ring

theorem blocksToStokes_stokesToBlocks (q : StokesQuad) :
    blocksToStokes (stokesToBlocks q) = q := by
  rcases q with ⟨a0, a1, a2, a3⟩
  apply Prod.ext
  · ext i j
    simp [blocksToStokes, stokesToBlocks]
    all_goals field_simp
    all_goals ring_nf
  · apply Prod.ext
    · ext i j
      simp [blocksToStokes, stokesToBlocks]
      all_goals field_simp
      all_goals ring_nf
      all_goals simp [Complex.I_mul_I]
      all_goals ring
    · apply Prod.ext
      · ext i j
        simp [blocksToStokes, stokesToBlocks]
        all_goals field_simp
        all_goals ring_nf
        all_goals simp [Complex.I_mul_I]
        all_goals ring
      · ext i j
        simp [blocksToStokes, stokesToBlocks]
        all_goals field_simp
        all_goals ring_nf
        all_goals simp [Complex.I_mul_I]
        all_goals ring

def stokesLinearEquiv : OperatorBlocks ≃ₗ[ℂ] StokesQuad where
  toLinearMap := blocksToStokes
  invFun := stokesToBlocks
  left_inv := stokesToBlocks_blocksToStokes
  right_inv := blocksToStokes_stokesToBlocks

def operatorStokesLinearEquiv : M6C ≃ₗ[ℂ] StokesQuad :=
  blockLinearEquiv.trans stokesLinearEquiv

end InfoGeometry.Canonical.TwoSheetStokesCoordinates
