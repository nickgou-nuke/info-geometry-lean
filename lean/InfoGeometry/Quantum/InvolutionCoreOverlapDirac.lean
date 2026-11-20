/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.OverlapDiracFromInvolutions
import InfoGeometry.Quantum.InvolutionCore

/-!
# The overlap operator on the real involution core

The existing `InvolutionCore` owns two actual real-linear involutions without
an interaction law.  Their native endomorphism algebra therefore carries the
overlap operator `id + J ∘ eps` and its Ginsparg--Wilson relation.

Its zero modes are exactly the vectors on which `eps` and `-J` agree.  Both
involutions preserve this kernel.  These statements need neither a Hilbert
completion nor finite dimension, a spectral gap, or primitive complex scalars.
No integer index or determinant is asserted.
-/

namespace InfoGeometry.Quantum.InvolutionCore

open InfoGeometry.OperatorAlgebra.OverlapDirac

/-- The overlap expression as an actual real-linear endomorphism. -/
noncomputable def overlapDirac (X : InvolutionCore) : Module.End ℝ X :=
  overlapOperator X.J X.eps

/-- This uses the composite already owned by `InvolutionCore`. -/
theorem overlapDirac_eq_id_add_je (X : InvolutionCore) :
    X.overlapDirac = LinearMap.id + X.je := rfl

@[simp] theorem overlapDirac_apply (X : InvolutionCore) (v : X) :
    X.overlapDirac v = v + X.J (X.eps v) := rfl

/-- The Ginsparg--Wilson identity holds in the native real endomorphism ring. -/
theorem overlapDirac_ginspargWilson (X : InvolutionCore) :
    X.J.comp X.overlapDirac + X.overlapDirac.comp X.J =
      (X.overlapDirac.comp X.J).comp X.overlapDirac := by
  exact ginspargWilson X.J X.eps X.J_sq X.eps_sq

/-- A zero mode is precisely a vector on which the two involutions act with
opposite sign.  The statement includes the zero vector. -/
theorem overlapDirac_apply_eq_zero_iff (X : InvolutionCore) (v : X) :
    X.overlapDirac v = 0 ↔ X.eps v = -X.J v := by
  constructor
  · intro h
    have hsum : X.J v + X.eps v = 0 := by
      simpa only [overlapDirac_apply, map_add, J_sq_apply, map_zero] using
        congrArg X.J h
    calc
      X.eps v = -X.J v + (X.J v + X.eps v) := by abel
      _ = -X.J v := by rw [hsum, add_zero]
  · intro h
    rw [overlapDirac_apply, h, map_neg, J_sq_apply, add_neg_cancel]

/-- The first involution preserves the native linear-map kernel. -/
theorem J_mem_ker_overlapDirac (X : InvolutionCore) {v : X}
    (hv : v ∈ LinearMap.ker X.overlapDirac) :
    X.J v ∈ LinearMap.ker X.overlapDirac := by
  change X.overlapDirac v = 0 at hv
  change X.overlapDirac (X.J v) = 0
  have h := congrArg (fun f : Module.End ℝ X => f v)
    (overlapDirac_ginspargWilson X)
  change X.J (X.overlapDirac v) + X.overlapDirac (X.J v) =
    X.overlapDirac (X.J (X.overlapDirac v)) at h
  simpa only [hv, map_zero, zero_add] using h

/-- The second involution preserves the same kernel by the intertwining law. -/
theorem eps_mem_ker_overlapDirac (X : InvolutionCore) {v : X}
    (hv : v ∈ LinearMap.ker X.overlapDirac) :
    X.eps v ∈ LinearMap.ker X.overlapDirac := by
  change X.overlapDirac v = 0 at hv
  change X.overlapDirac (X.eps v) = 0
  have h := congrArg (fun f : Module.End ℝ X => f v)
    (chirality_intertwining X.J X.eps X.J_sq X.eps_sq)
  change X.J (X.overlapDirac v) = X.overlapDirac (X.eps v) at h
  rw [hv, map_zero] at h
  exact h.symm

end InfoGeometry.Quantum.InvolutionCore
