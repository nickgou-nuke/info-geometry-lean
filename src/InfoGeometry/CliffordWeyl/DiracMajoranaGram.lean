/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracPeircePerfectPairing
import InfoGeometry.Physics.MajoranaKreinPfaffianCarrier
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The Gram matrix of the actual perfect Dirac corner pairing defines a
nonsingular doubled skew carrier through the existing off-diagonal pairing.
No signed Pfaffian value or positivity assertion is made.
-/
noncomputable section
namespace InfoGeometry.Physics.KasparovKreinData
open Matrix InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Physics.MajoranaKreinPfaffianCarrier
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable (K : KasparovKreinData (Matrix n n ℝ))
variable (P : Matrix n n ℝ) (hP : P * P = P) (hPK : K.diracAdjoint P = P)
variable (b : Module.Basis ι ℝ (LinearMap.range (component10Linear P)))

def diracCornerGram : Matrix ι ι ℝ :=
  LinearMap.BilinForm.toMatrix b (K.diracCornerTracePairing P hP hPK)

@[simp] theorem diracCornerGram_apply (i j : ι) :
    diracCornerGram K P hP hPK b i j =
      trace ((b i).val * K.diracAdjoint (b j).val) := by
  simp only [diracCornerGram, LinearMap.BilinForm.toMatrix_apply,
    diracCornerTracePairing_apply]

theorem diracCornerGram_readout
    (X Y : LinearMap.range (component10Linear P)) :
    trace (X.val * K.diracAdjoint Y.val) =
      (b.repr X) ⬝ᵥ (diracCornerGram K P hP hPK b) *ᵥ (b.repr Y) :=
  LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
    (K.diracCornerTracePairing P hP hPK) X Y

theorem diracCornerGram_det_ne_zero :
    (diracCornerGram K P hP hPK b).det ≠ 0 := by
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (K.diracCornerTracePairing_isPerfPair P hP hPK).nondegenerate

def diracCornerDoubledSkew : Matrix (Sum ι ι) (Sum ι ι) ℝ :=
  offDiagonalPairing (diracCornerGram K P hP hPK b)

theorem diracCornerDoubledSkew_transpose :
    (diracCornerDoubledSkew K P hP hPK b).transpose =
      -diracCornerDoubledSkew K P hP hPK b :=
  offDiagonalPairing_skew (diracCornerGram K P hP hPK b)

theorem diracCornerDoubledSkew_det_ne_zero :
    (diracCornerDoubledSkew K P hP hPK b).det ≠ 0 :=
  (offDiagonalPairing_det_ne_zero_iff (diracCornerGram K P hP hPK b)).mpr
    (diracCornerGram_det_ne_zero K P hP hPK b)

end InfoGeometry.Physics.KasparovKreinData
