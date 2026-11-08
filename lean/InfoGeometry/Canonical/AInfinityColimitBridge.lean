import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Canonical.CPTKMSColimitTower

/-!
# The diagonal finite-stage bridge

This owner uses the existing diagonal inductive-limit carrier.  It does not
identify the set of cylinder functions with an additive type, nor does it
invent a second tensor-colimit construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.AInfinityColimitBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CPTKMSColimitTower

abbrev AInfinity : Type := diagonalUHFInductiveLimit.AInf

def stageToTensor (n : ℕ) (f : DiagAlg n) : AInfinity :=
  diagonalUHFInductiveLimit.inj n f

def diagAlgToMatrix (n : ℕ) (f : DiagAlg n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  let e : BitWord n ≃ Fin (2 ^ n) :=
    Fintype.equivFinOfCardEq (by simp [BitWord])
  Matrix.diagonal (fun i => f (e.symm i))

def cylinderToTensor (n : ℕ) (f : DiagAlg n) : AInfinity :=
  stageToTensor n f

@[simp] theorem cylinderToTensor_cylinder (n : ℕ) (f : DiagAlg n) :
    cylinderToTensor n f = stageToTensor n f := rfl

@[simp] theorem cylinderToTensor_succ (n : ℕ) (f : DiagAlg n) :
    cylinderToTensor (n + 1) (diagEmbedSucc n f) =
      stageToTensor (n + 1) (diagEmbedSucc n f) := rfl

theorem stageToTensor_compatible (n : ℕ) (f : DiagAlg n) :
    stageToTensor (n + 1) (diagEmbedSucc n f) = stageToTensor n f := by
  exact diagonalUHFInductiveLimit.inj_compat n f

theorem trace_compatibility (n : ℕ) (f : DiagAlg n) :
    Matrix.trace (diagAlgToMatrix n f) =
      ∑ w : BitWord n, f w := by
  classical
  let e : BitWord n ≃ Fin (2 ^ n) :=
    Fintype.equivFinOfCardEq (by simp [BitWord])
  rw [show Matrix.trace (diagAlgToMatrix n f) =
      ∑ i : Fin (2 ^ n), f (e.symm i) by
    simp [diagAlgToMatrix, Matrix.trace, e]]
  exact e.symm.sum_comp f

end InfoGeometry.Canonical.AInfinityColimitBridge
