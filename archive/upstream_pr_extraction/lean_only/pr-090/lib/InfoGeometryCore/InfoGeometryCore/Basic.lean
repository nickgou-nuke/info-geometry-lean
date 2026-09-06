import Mathlib

/-!
# Minimal repository-owned InfoGeometry core

This compatibility owner replaces an unavailable local-only submodule with the
small theorem surface actually consumed by the parent repository: `2 × 2`
real/complex matrix carriers, the Pauli matrices, golden-ratio constants, and
the finite tripotent classifier `{-1,0,+1}`.

No broader claim about the historical private `InfoGeometryCore` checkout is
made here.
-/

noncomputable section

namespace InfoGeometryCore

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- First complex Pauli matrix. -/
def sigma1C : M2C := !![0, 1; 1, 0]

/-- Second complex Pauli matrix. -/
def sigma2C : M2C := !![0, -Complex.I; Complex.I, 0]

/-- Third complex Pauli matrix. -/
def sigma3C : M2C := !![1, 0; 0, -1]

/-- Real golden ratio. -/
def phiR : ℝ := (1 + Real.sqrt 5) / 2

/-- Complex golden ratio obtained from the real one. -/
def phiC : ℂ := ((1 + Real.sqrt 5) / 2 : ℝ)

/-- Three-valued tripotent spectral label. -/
inductive TripotentState where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

namespace TripotentState

/-- Integer realization `{-1,0,+1}`. -/
def toInt : TripotentState → ℤ
  | neg => -1
  | zero => 0
  | pos => 1

/-- Canonical cyclic permutation of the three tripotent branches. -/
def trialityCycle : TripotentState → TripotentState
  | neg => zero
  | zero => pos
  | pos => neg

@[simp] theorem trialityCycle_three (s : TripotentState) :
    trialityCycle (trialityCycle (trialityCycle s)) = s := by
  cases s <;> rfl

/-- Indicator of the negative branch. -/
def pNeg : TripotentState → ℤ
  | neg => 1
  | zero => 0
  | pos => 0

/-- Indicator of the zero branch. -/
def pZero : TripotentState → ℤ
  | neg => 0
  | zero => 1
  | pos => 0

/-- Indicator of the positive branch. -/
def pPos : TripotentState → ℤ
  | neg => 0
  | zero => 0
  | pos => 1

@[simp] theorem cube_eq_self (s : TripotentState) :
    toInt s ^ 3 = toInt s := by
  cases s <;> norm_num [toInt]

@[simp] theorem trifactor_projector_partition (s : TripotentState) :
    pNeg s + pZero s + pPos s = 1 := by
  cases s <;> norm_num [pNeg, pZero, pPos]

@[simp] theorem trifactor_projector_idempotent (s : TripotentState) :
    pNeg s * pNeg s = pNeg s ∧
      pZero s * pZero s = pZero s ∧
      pPos s * pPos s = pPos s := by
  cases s <;> norm_num [pNeg, pZero, pPos]

end TripotentState

end InfoGeometryCore
