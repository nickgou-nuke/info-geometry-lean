import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
import InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer
import InfoGeometry.Canonical.SplitOctonionPaperBasisBridge
import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

/-!
# Gogberashvili `ZornCell` carrier bridge

This file identifies the explicit eight-coordinate `ZornCell` carrier with
the paper `ZornMatrix` carrier.  The map is a genuine linear equivalence and
preserves the native Zorn product.  The existing paper-to-canonical map then
gives the corresponding canonical-carrier equivalence.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Canonical.SplitOctonionPaperBasisBridge
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

abbrev Cell := InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℝ
abbrev Paper := InfoGeometry.Algebra.ZornMatrix ℝ
abbrev Canonical := InfoGeometry.Canonical.ZornMatrix ℝ

def cellToPaper : Cell ≃ₗ[ℝ] Paper where
  toFun X :=
    { a := X.r
      v := ![X.x1, X.x2, X.x3]
      w := ![X.y1, X.y2, X.y3]
      b := X.s }
  invFun X :=
    { r := X.a
      s := X.b
      x1 := X.v 0
      x2 := X.v 1
      x3 := X.v 2
      y1 := X.w 0
      y2 := X.w 1
      y3 := X.w 2 }
  left_inv X := by
    cases X
    rfl
  right_inv X := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' X Y := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_smul' c X := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl

@[simp] theorem cellToPaper_apply (X : Cell) :
    cellToPaper X =
      ({ a := X.r
         v := ![X.x1, X.x2, X.x3]
         w := ![X.y1, X.y2, X.y3]
         b := X.s } : Paper) := rfl

@[simp] theorem cellToPaper_mul (X Y : Cell) :
    cellToPaper (X * Y) = cellToPaper X * cellToPaper Y := by
  change cellToPaper (ZornCell.mulZ X Y) = cellToPaper X * cellToPaper Y
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [cellToPaper, ZornCell.mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot]
  · funext i
    fin_cases i <;>
      simp [cellToPaper, ZornCell.mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add, InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.Vec3.smul, InfoGeometry.Algebra.Vec3.cross]
      <;> ring
  · funext i
    fin_cases i <;>
      simp [cellToPaper, ZornCell.mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add, InfoGeometry.Algebra.Vec3.smul,
        InfoGeometry.Algebra.Vec3.cross]
      <;> ring
  · simp [cellToPaper, ZornCell.mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot]

theorem cellToPaper_detZ (X : Cell) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm (cellToPaper X) =
      ZornCell.detZ X := by
  change X.r * X.s -
      (X.x1 * X.y1 + X.x2 * X.y2 + X.x3 * X.y3) = _
  rfl

@[simp] theorem cellToPaper_oneZ :
    cellToPaper InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.oneZ =
      paperOne := by
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem cellToPaper_I :
    cellToPaper InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I =
      paperI := by
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I,
      paperI,
      InfoGeometry.Algebra.ZornMatrix.E11, InfoGeometry.Algebra.ZornMatrix.E22]
  · funext i
    fin_cases i <;>
      simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I,
        paperI,
        InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.ZornMatrix.E11, InfoGeometry.Algebra.ZornMatrix.E22]
  · funext i
    fin_cases i <;>
      simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I,
        paperI,
        InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.ZornMatrix.E11, InfoGeometry.Algebra.ZornMatrix.E22]
  · simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I,
      paperI,
      InfoGeometry.Algebra.ZornMatrix.E11, InfoGeometry.Algebra.ZornMatrix.E22]

theorem cellToPaper_J (i : Fin 3) :
    cellToPaper (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J i) =
      paperJ i := by
  fin_cases i <;>
    apply InfoGeometry.Algebra.ZornMatrix.ext
  all_goals
    simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J,
      paperJ, InfoGeometry.Algebra.Vec3.add,
      InfoGeometry.Algebra.ZornMatrix.add, InfoGeometry.Algebra.ZornMatrix.U,
      InfoGeometry.Algebra.ZornMatrix.V,
      InfoGeometry.Algebra.ZornMatrix.Vec3.basis]
  all_goals try
    funext k
    fin_cases k <;>
      simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J,
        paperJ, InfoGeometry.Algebra.Vec3.add,
        InfoGeometry.Algebra.ZornMatrix.add, InfoGeometry.Algebra.ZornMatrix.U,
        InfoGeometry.Algebra.ZornMatrix.V,
        InfoGeometry.Algebra.ZornMatrix.Vec3.basis]

theorem cellToPaper_j (i : Fin 3) :
    cellToPaper (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.j i) =
      -paperj i := by
  fin_cases i <;>
    change _ = InfoGeometry.Algebra.ZornMatrixRealModule.neg _ <;>
    ext <;>
      simp [cellToPaper, InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.j,
        paperj, InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.ZornMatrix.sub,
        InfoGeometry.Algebra.ZornMatrix.U,
        InfoGeometry.Algebra.ZornMatrix.V,
        InfoGeometry.Algebra.ZornMatrix.Vec3.basis,
        InfoGeometry.Algebra.ZornMatrixRealModule.neg,
        InfoGeometry.Algebra.Vec3.smul]

@[simp] theorem cellToPaper_symm_paperJ (i : Fin 3) :
    cellToPaper.symm (paperJ i) =
      InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J i := by
  apply cellToPaper.injective
  change paperJ i = cellToPaper
    (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J i)
  rw [cellToPaper_J]

@[simp] theorem cellToPaper_symm_paperj (i : Fin 3) :
    cellToPaper.symm (paperj i) =
      -InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.j i := by
  apply cellToPaper.injective
  change paperj i = cellToPaper
    (-InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.j i)
  rw [map_neg, cellToPaper_j, neg_neg]

def cellToCanonical : Cell ≃ₗ[ℝ] Canonical :=
  cellToPaper.trans paperCanonicalLinearEquiv

@[simp] theorem cellToCanonical_mul (X Y : Cell) :
    cellToCanonical (X * Y) = cellToCanonical X * cellToCanonical Y := by
  change paperCanonicalLinearEquiv (cellToPaper (X * Y)) =
    paperCanonicalLinearEquiv (cellToPaper X) *
      paperCanonicalLinearEquiv (cellToPaper Y)
  rw [cellToPaper_mul, paperCanonicalLinearEquiv_mul]

theorem cellToCanonical_norm (X : Cell) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
      (cellToCanonical X) =
      ZornCell.detZ X := by
  rw [cellToCanonical, LinearEquiv.trans_apply]
  rw [← paperCanonicalLinearEquiv_norm]
  exact cellToPaper_detZ X

@[simp] theorem cellToCanonical_oneZ :
    cellToCanonical InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.oneZ =
      paperCanonicalLinearEquiv paperOne := by
  change paperCanonicalLinearEquiv (cellToPaper oneZ) = _
  rw [cellToPaper_oneZ]

theorem cellToCanonical_I :
    cellToCanonical InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.I =
      paperCanonicalLinearEquiv paperI := by
  change paperCanonicalLinearEquiv (cellToPaper I) = _
  rw [cellToPaper_I]

theorem cellToCanonical_J (i : Fin 3) :
    cellToCanonical (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.J i) =
      paperCanonicalLinearEquiv (paperJ i) := by
  change paperCanonicalLinearEquiv (cellToPaper (J i)) = _
  rw [cellToPaper_J]

theorem cellToCanonical_j (i : Fin 3) :
    cellToCanonical (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.j i) =
      paperCanonicalLinearEquiv (-paperj i) := by
  change paperCanonicalLinearEquiv (cellToPaper (j i)) = _
  rw [cellToPaper_j]

end InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge
