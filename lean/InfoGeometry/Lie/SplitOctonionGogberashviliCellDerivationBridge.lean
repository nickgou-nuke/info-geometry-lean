import InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Derivations on the explicit Gogberashvili carrier

The canonical derivation algebra is transported to the explicit
`ZornCell ℝ` carrier through the kernel-checked multiplication-preserving
linear equivalence.  This file adds no new derivation algebra; it records
the transported Leibniz theorem.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionGogberashviliCellDerivationBridge

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge
open InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge

abbrev Cell := InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℝ
abbrev Der := SplitOctonionGogberashviliDerivationBridge.Der

local instance : LieRing (Module.End ℝ Cell) := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (Module.End ℝ Cell) := LieAlgebra.ofAssociativeAlgebra

def cellDerivation (D : Der) : Module.End ℝ Cell :=
  cellToPaper.symm.toLinearMap.comp
    ((paperDerivation D).comp cellToPaper.toLinearMap)

theorem cellDerivation_apply (D : Der) (X : Cell) :
    cellDerivation D X =
      cellToPaper.symm (paperDerivation D (cellToPaper X)) := rfl

theorem cellDerivation_toCanonical (D : Der) (X : Cell) :
    cellToCanonical (cellDerivation D X) = D.1 (cellToCanonical X) := by
  simp [cellToCanonical, cellDerivation_apply, paperDerivation_apply]

def cellConj (X : Cell) : Cell :=
  { r := X.s
    s := X.r
    x1 := -X.x1
    x2 := -X.x2
    x3 := -X.x3
    y1 := -X.y1
    y2 := -X.y2
    y3 := -X.y3 }

theorem cellToPaper_cellConj (X : Cell) :
    cellToPaper (cellConj X) =
      paperConj (cellToPaper X) := by
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem cellDerivation_conj_identity_left (D : Der) (X : Cell) :
    cellDerivation D X * cellConj X +
        X * cellDerivation D (cellConj X) = 0 := by
  apply cellToPaper.injective
  rw [map_add, cellToPaper_mul, cellToPaper_mul,
    cellDerivation_apply, cellDerivation_apply, cellToPaper_cellConj]
  simp only [LinearEquiv.apply_symm_apply]
  exact paperDerivation_conj_norm_identity_left D (cellToPaper X)

theorem cellDerivation_isDerivation (D : Der) (X Y : Cell) :
    cellDerivation D (X * Y) =
      cellDerivation D X * Y + X * cellDerivation D Y := by
  apply cellToPaper.injective
  rw [cellDerivation_apply, cellDerivation_apply, cellDerivation_apply]
  rw [cellToPaper_mul]
  rw [paperDerivation_isDerivation]
  calc
    cellToPaper (cellToPaper.symm
      (paperDerivation D (cellToPaper X) * cellToPaper Y +
        cellToPaper X * paperDerivation D (cellToPaper Y))) =
      paperDerivation D (cellToPaper X) * cellToPaper Y +
        cellToPaper X * paperDerivation D (cellToPaper Y) := by simp
    _ = cellToPaper
        (cellToPaper.symm (paperDerivation D (cellToPaper X)) * Y +
          X * cellToPaper.symm (paperDerivation D (cellToPaper Y))) := by
      symm
      have h_add := cellToPaper.map_add
        (cellToPaper.symm (paperDerivation D (cellToPaper X)) * Y)
        (X * cellToPaper.symm (paperDerivation D (cellToPaper Y)))
      calc
        _ = cellToPaper
              (cellToPaper.symm (paperDerivation D (cellToPaper X)) * Y) +
            cellToPaper
              (X * cellToPaper.symm (paperDerivation D (cellToPaper Y))) := h_add
        _ = paperDerivation D (cellToPaper X) * cellToPaper Y +
            cellToPaper X * paperDerivation D (cellToPaper Y) := by
          rw [cellToPaper_mul, cellToPaper_mul]
          simp

@[simp] theorem cellDerivation_map_one (D : Der) :
    cellDerivation D
        InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.oneZ = 0 := by
  apply cellToPaper.injective
  rw [cellDerivation_apply, cellToPaper_oneZ]
  simp only [LinearEquiv.apply_symm_apply]
  change paperDerivation D (InfoGeometry.Algebra.ZornMatrix.I : PaperZorn) =
    cellToPaper 0
  rw [paperDerivation_map_one]
  apply InfoGeometry.Algebra.ZornMatrix.ext <;> rfl

theorem cellDerivation_lie (D E : Der) :
    cellDerivation ⁅D, E⁆ = ⁅cellDerivation D, cellDerivation E⁆ := by
  ext X
  apply cellToPaper.injective
  simp only [cellDerivation_apply]
  rw [paperDerivation_lie]
  simp [cellDerivation, LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]

noncomputable def cellDerivationLinear :
    Der →ₗ[ℝ] Module.End ℝ Cell :=
  (LinearEquiv.conj cellToPaper.symm).toLinearMap.comp paperDerivationLinear

theorem cellDerivationLinear_apply (D : Der) :
    cellDerivationLinear D = cellDerivation D := by
  ext X
  simp [cellDerivationLinear, cellDerivation, paperDerivationLinear,
    paperDerivation, LinearEquiv.conj_apply_apply]

noncomputable def cellDerivationLieHom :
    Der →ₗ⁅ℝ⁆ Module.End ℝ Cell where
  __ := cellDerivationLinear
  map_lie' := by
    intro D E
    change cellDerivationLinear ⁅D, E⁆ =
      ⁅cellDerivationLinear D, cellDerivationLinear E⁆
    rw [cellDerivationLinear_apply, cellDerivationLinear_apply,
      cellDerivationLinear_apply]
    exact cellDerivation_lie D E

theorem cellDerivationLieHom_injective :
    Function.Injective cellDerivationLieHom := by
  intro D E h
  apply paperDerivationLieHom_injective
  apply LinearMap.ext
  intro Y
  let X : Cell := cellToPaper.symm Y
  have hX := congrArg (fun F : Module.End ℝ Cell => F X) h
  change cellDerivationLinear D X = cellDerivationLinear E X at hX
  rw [cellDerivationLinear_apply, cellDerivationLinear_apply] at hX
  change paperDerivation D Y = paperDerivation E Y
  simpa [cellDerivation_apply, X] using congrArg cellToPaper hX

noncomputable def cellDerivationLieEquiv :
    Der ≃ₗ⁅ℝ⁆ (cellDerivationLieHom).range :=
  LieEquiv.ofInjective cellDerivationLieHom cellDerivationLieHom_injective

theorem finrank_cellDerivationRange :
    Module.finrank ℝ (cellDerivationLieHom).range = 14 := by
  rw [← cellDerivationLieEquiv.toLinearEquiv.finrank_eq]
  exact CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

end InfoGeometry.Lie.SplitOctonionGogberashviliCellDerivationBridge
