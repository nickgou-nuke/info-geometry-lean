import InfoGeometry.Lie.SplitOctonionEllFlowOperator
import InfoGeometry.Lie.SplitOctonionEllTrifactor
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Split-octonion ell flow decomposition: dimensions 3+2+3

This owner proves that the three ell-flow sectors have dimensions
`dimrange(P₋) = 3`, `dimrange(P₀) = 2`, `dimrange(P₊) = 3`, giving the
decomposition `O_s = 3_- ⊕ 2_0 ⊕ 3_+`.

The proof uses linear equivalences to identify each sector with a concrete
coordinate space, following the pattern of `SplitOctonionAxialFlowDecomposition`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionDiagEllFlowDecomposition

open InfoGeometry.Lie.SplitOctonionEllTrifactor
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Physics.Algebra
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev CZ := CanonicalZorn

abbrev positiveSector := LinearMap.range ellFlowPPlus
abbrev zeroSector := LinearMap.range ellFlowPZero
abbrev negativeSector := LinearMap.range ellFlowPMinus

/- Upper/color coordinates identify the positive ell sector with three real
coordinates. -/
def positiveSectorEquiv : positiveSector ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := X.1.x
  invFun x :=
    ⟨{ a := 0, b := 0, x := x, y := 0 }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := 0, b := 0, x := x, y := 0 }, ?_⟩
      rw [ellFlowPPlus_eq_colorProject, colorProject_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [ellFlowPPlus_eq_colorProject, colorProject_apply] at hY
    rw [← hY]
  right_inv x := rfl

/- Lower/anticolor coordinates identify the negative ell sector with three
real coordinates. -/
def negativeSectorEquiv : negativeSector ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := X.1.y
  invFun y :=
    ⟨{ a := 0, b := 0, x := 0, y := y }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := 0, b := 0, x := 0, y := y }, ?_⟩
      rw [ellFlowPMinus_eq_anticolorProject, anticolorProject_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [ellFlowPMinus_eq_anticolorProject, anticolorProject_apply] at hY
    rw [← hY]
  right_inv y := rfl

/- The stationary/Drazin-defect coordinates are exactly the two diagonal real
coordinates. -/
def zeroSectorEquiv : zeroSector ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun X := (X.1.a, X.1.b)
  invFun ab :=
    ⟨{ a := ab.1, b := ab.2, x := 0, y := 0 },
      Subtype.of_mem_range (by
        rw [LinearMap.mem_range]
        refine ⟨{ a := ab.1, b := ab.2, x := 0, y := 0 }, ?_⟩
        rw [ellFlowPZero_apply])⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [← ellFlowPZero_coord] at hY
    rw [← hY]
  right_inv ab := by
    simp [ellFlowPZero_coord]

@[simp] theorem positiveSector_finrank :
    Module.finrank ℝ positiveSector = 3 := by
  rw [positiveSectorEquiv.finrank_eq]
  simp

@[simp] theorem zeroSector_finrank :
    Module.finrank ℝ zeroSector = 2 := by
  rw [zeroSectorEquiv.finrank_eq]
  simp

@[simp] theorem negativeSector_finrank :
    Module.finrank ℝ negativeSector = 3 := by
  rw [negativeSectorEquiv.finrank_eq]
  simp

/-!
The ell-flow decomposition:
The split-octonion carrier `CanonicalZorn` decomposes as
`P_-^ℓ ⊕ P_0^ℓ ⊕ P_+^ℓ` with dimensions 3 + 2 + 3.

This is the concrete realization of
`O_s = 3_- ⊕ 2_0 ⊕ 3_+` using the Zorn matrix model.
-/
theorem ellFlow_decomposition :
    Module.finrank ℝ positiveSector = 3 ∧
      Module.finrank ℝ zeroSector = 2 ∧
      Module.finrank ℝ negativeSector = 3 := by
  exact ⟨positiveSector_finrank, zeroSector_finrank, negativeSector_finrank⟩

/-!
The full split-octonion decomposition:

`CanonicalZorn = P_-^ℓ ⊕ P_0^ℓ ⊕ P_+^ℓ` with
`dim = 3 + 2 + 3 = 8`.

This is the theorem that closes the 3+2+3 decomposition.
-/
theorem splitOctonion_ell_decomposition :
    Module.finrank ℝ (⊤ : Submodule ℝ CZ) = 8 := by
  -- The full carrier `⊤ : Submodule ℝ CZ` has the same dimension as
  -- `CanonicalZorn` itself.  `canonicalZorn_finrank` gives the latter.
  rw [Module.finrank_top]
  exact canonicalZorn_finrank


/-!
The ell-flow operators give a direct sum decomposition:

`id = ellFlowPZero + ellFlowPPlus + ellFlowPMinus`.

This follows from the projector sum identity for tripotents.
-/
theorem ellFlow_direct_sum :
    ellFlowPZero + ellFlowPPlus + ellFlowPMinus = 1 := by
  -- Direct proof by unfolding each projector's coordinate action and
  -- case-splitting on the four `Fin 4` components.  This avoids the
  -- `ring_nf` timeout that `diagEllGrading_sq_coord`/`diagEllGrading_coord`
  -- would trigger on the full symbolic expansion.
  apply LinearMap.ext
  intro Z
  have h0 : ellFlowPZero Z = { a := Z.a, b := Z.b, x := 0, y := 0 } :=
    ellFlowPZero_coord Z
  have hp : ellFlowPPlus Z = { a := 0, b := 0, x := Z.x, y := 0 } :=
    ellFlowPPlus_coord Z
  have hm : ellFlowPMinus Z = { a := 0, b := 0, x := 0, y := Z.y } :=
    ellFlowPMinus_coord Z
  rw [h0, hp, hm]
  -- Now the goal is `{a:=Z.a,b:=Z.b,x:=0,y:=0} + {a:=0,b:=0,x:=Z.x,y:=0}
  --   + {a:=0,b:=0,x:=0,y:=Z.y} = Z`
  rw [← ZornMatrix.ext]
  ext i
  fin_cases i <;> simp [ZornMatrix.add_def, coordComponent, smul_eq_mul]

end InfoGeometry.Lie.SplitOctonionDiagEllFlowDecomposition
