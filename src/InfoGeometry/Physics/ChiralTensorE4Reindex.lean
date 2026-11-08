import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex
import InfoGeometry.External.Auto.TLChain
import InfoGeometry.Physics.ChiralTensorMatrixBridge

/-!
# Index-safe readout for the two-site chiral TL matrix

`TLChain.e4` uses `Fin 4`, while the canonical Kronecker matrix bridge uses
`Fin 2 × Fin 2`.  This owner records the explicit Mathlib reindexing between
those carriers without identifying the two types definitionally.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralTensorE4Reindex

open InfoGeometry.External.Auto
open InfoGeometry.Physics.ChiralTensorMatrixBridge

def pairToFinFour : Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

def e4OnPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.reindex pairToFinFour.symm pairToFinFour.symm TLChain.e4

theorem e4OnPair_apply (i j : Fin 2 × Fin 2) :
    e4OnPair i j = TLChain.e4 (pairToFinFour i) (pairToFinFour j) := by
  rfl

theorem pairToFinFour_bijective : Function.Bijective pairToFinFour :=
  pairToFinFour.bijective

theorem e4OnPair_sq :
    e4OnPair * e4OnPair = (2 : ℂ) • e4OnPair := by
  calc
    e4OnPair * e4OnPair =
        Matrix.reindex pairToFinFour.symm pairToFinFour.symm
          (TLChain.e4 * TLChain.e4) := by
      simpa [e4OnPair, Matrix.reindexLinearEquiv_apply] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ pairToFinFour.symm
          pairToFinFour.symm pairToFinFour.symm TLChain.e4 TLChain.e4)
    _ = Matrix.reindex pairToFinFour.symm pairToFinFour.symm
          ((2 : ℂ) • TLChain.e4) := by rw [TLChain.e4_sq]
    _ = (2 : ℂ) • e4OnPair := by
      ext i j
      rfl

def e4ProjectorOnPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • e4OnPair

theorem e4ProjectorOnPair_idempotent :
    e4ProjectorOnPair * e4ProjectorOnPair = e4ProjectorOnPair := by
  unfold e4ProjectorOnPair
  rw [smul_mul_smul, e4OnPair_sq]
  norm_num [smul_smul]

end InfoGeometry.Physics.ChiralTensorE4Reindex
