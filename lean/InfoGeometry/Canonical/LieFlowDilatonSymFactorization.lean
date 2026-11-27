/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.LieFlowLogJacobianBridge
import InfoGeometry.Canonical.LieFlowLogJacobianBridge

/-!
# Symmetric dilaton factorization of the log-Jacobian readout

The log-volume readout of a finite Lie flow factors through the symmetric
dilaton part of its generator. This is a transport theorem between already
owned symmetric/trace/dilaton projections, not a new structure or wrapper.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieFlowDilatonSymFactorization

open InfoGeometry.Analysis.LieFlowLogJacobianBridge
open InfoGeometry.Canonical.LieFlowLogJacobian
open Matrix
open scoped Matrix

theorem lieFlowLogJacobian_eq_dilatonPart_symPart
    {n : ℕ} (hn : n ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    lieFlowLogJacobian A t = lieFlowLogJacobian (dilatonPart (symPart A)) t := by
  rw [lieFlowLogJacobian_eq_symPart A t]
  exact lieFlowLogJacobian_eq_dilatonPart hn (symPart A) t

/-- A skew (Killing-type) generator preserves finite log-volume: the exact
`lieFlowLogJacobian` readout vanishes. This is the finite carrier shadow of
the transcript's contact-volume preservation claim. -/
theorem lieFlowLogJacobian_eq_zero_of_skew
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A) (t : ℝ) :
    lieFlowLogJacobian A t = 0 := by
  exact lieFlowLogJacobian_eq_zero_of_trace_zero A
    (skewMatrix_trace_zero A hA) t

end InfoGeometry.Canonical.LieFlowDilatonSymFactorization
