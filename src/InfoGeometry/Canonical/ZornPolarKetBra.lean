/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarOperatorAdjoint
import Mathlib.LinearAlgebra.Trace

/-! Endomorphisms of rank at most one built from the native split-polar bra. These are
associative operators on ZornCoord, not products in the Zorn algebra. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornPolarKetBra
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge

def ketBra (X Y : ZornCoord) : Module.End ℝ ZornCoord :=
  (polarForm Y).smulRight X

theorem ketBra_mul (X Y U V : ZornCoord) :
    ketBra X Y * ketBra U V = polarPair Y U • ketBra X V := by
  apply LinearMap.ext
  intro W
  simp [ketBra, smul_smul, mul_comm]

theorem ketBra_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm (ketBra X Y) (ketBra Y X) := by
  intro U V
  change polarForm (polarForm Y U • X) V = polarForm U (polarForm X V • Y)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change polarPair Y U * polarPair X V = polarPair X V * polarPair U Y
  rw [polarPair_symm Y U, mul_comm]

theorem ketBra_trace (X Y : ZornCoord) :
    LinearMap.trace ℝ ZornCoord (ketBra X Y) = polarPair Y X :=
  LinearMap.trace_smulRight (polarForm Y) X

theorem ketBra_sq_zero (X Y : ZornCoord) (h : polarPair Y X = 0) :
    ketBra X Y * ketBra X Y = 0 := by
  rw [ketBra_mul, h, zero_smul]

theorem ketBra_idempotent (X Y : ZornCoord) (h : polarPair Y X = 1) :
    ketBra X Y * ketBra X Y = ketBra X Y := by
  rw [ketBra_mul, h, one_smul]

/-- A null vector gives a concrete square-zero polar ket-bra. -/
theorem null_ketBra_sq_zero :
    ketBra (zornMk 1 0 0 0) (zornMk 1 0 0 0) *
      ketBra (zornMk 1 0 0 0) (zornMk 1 0 0 0) = 0 := by
  apply ketBra_sq_zero
  norm_num [polarPair, zornMk, zornA, zornB, zornX, zornY, dot3]

/-- That self-paired null ket-bra is nonzero despite its zero square. -/
theorem null_ketBra_ne_zero :
    ketBra (zornMk 1 0 0 0) (zornMk 1 0 0 0) ≠ 0 := by
  intro h
  have he := congrArg (fun T : Module.End ℝ ZornCoord =>
    zornA (T (zornMk 0 2 0 0))) h
  norm_num [ketBra, polarForm, polarPair, zornMk, zornA, zornB, zornX, zornY, dot3] at he

end InfoGeometry.Canonical.ZornPolarKetBra
