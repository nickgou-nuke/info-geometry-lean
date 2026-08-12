import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import proofs.PatchRepresentation

open Matrix

/-- Cartan Decomposition: Symmetric Part (Even under transposition) -/
noncomputable def symmPart (M : Patch2x2) : Patch2x2 :=
  (2 : ℝ)⁻¹ • (M + Mᵀ)

/-- Cartan Decomposition: Skew-Symmetric Part (Odd under transposition) -/
noncomputable def skewPart (M : Patch2x2) : Patch2x2 :=
  (2 : ℝ)⁻¹ • (M - Mᵀ)

/-- Всяка матрица се разлага точно на своята симетрична и антисиметрична част -/
theorem symmPart_add_skewPart (M : Patch2x2) :
    symmPart M + skewPart M = M := by
  ext i j
  dsimp [symmPart, skewPart]
  ring

/-- Симетричната част е инвариантна спрямо транспониране -/
theorem symmPart_transpose (M : Patch2x2) :
    (symmPart M)ᵀ = symmPart M := by
  ext i j
  dsimp [symmPart]
  ring

/-- Антисиметричната част сменя знака си при транспониране -/
theorem skewPart_transpose (M : Patch2x2) :
    (skewPart M)ᵀ = -skewPart M := by
  ext i j
  dsimp [skewPart]
  ring
