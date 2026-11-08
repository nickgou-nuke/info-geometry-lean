/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Trace-adjoint identities for the two Peirce backpropagation variations

For finite square matrices over a commutative star ring, these lemmas identify
the adjoints of the two first-variation maps under the sesquilinear trace
pairing `⟪X,Y⟫ = trace (star X * Y)`. They are algebraic trace identities;
positivity, a real Hilbert structure, an optimization objective, and a neural
network memory bound are not asserted here.
-/

namespace InfoGeometry.Canonical.PeirceBackpropTraceGradient

open InfoGeometry.OperatorAlgebra.PeirceSpine
open Matrix

variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

/-- The upper Peirce parameter gradient appearing in the backward formula. -/
def primalGradient (P Xbar Xout : Matrix n n R) : Matrix n n R :=
  P * (Xbar * star Xout) * (1 - P)

/-- The lower Peirce parameter gradient, with the outer upper gate included. -/
def dualGradient (P Np Xbar Xmid : Matrix n n R) : Matrix n n R :=
  (1 - P) * (star (1 + Np) * Xbar * star Xmid) * P

/-- The primal gate variation and the proposed output-space gradient are
adjoints for the trace pairing. Hermiticity of `P` is the only projector-side
assumption needed for this trace identity. -/
theorem primal_variation_trace_adjoint
    {P dA Xbar Xout : Matrix n n R} (hPstar : star P = P) :
    trace (star Xbar * (conePlus P dA * Xout)) =
      trace (star (primalGradient P Xbar Xout) * dA) := by
  have hQstar : star (1 - P) = 1 - P := by simp [star_sub, hPstar]
  have hGrad :
      star (primalGradient P Xbar Xout) =
        (1 - P) * (Xout * star Xbar) * P := by
    simp [primalGradient, star_mul, hPstar, hQstar]; noncomm_ring
  calc
    trace (star Xbar * (conePlus P dA * Xout)) =
        trace ((star Xbar * P * dA) * ((1 - P) * Xout)) := by
          simp only [conePlus]
          congr 1
          noncomm_ring
    _ = trace (((1 - P) * Xout) * (star Xbar * P * dA)) :=
      Matrix.trace_mul_comm _ _
    _ = trace (star (primalGradient P Xbar Xout) * dA) := by
      rw [hGrad]
      congr 1
      noncomm_ring

/-- The lower-gate variation, including its left multiplication by the upper
gate, has the displayed dual gradient under the same trace pairing. -/
theorem dual_variation_trace_adjoint
    {P Np dC Xbar Xmid : Matrix n n R} (hPstar : star P = P) :
    trace (star Xbar * ((1 + Np) * (coneMinus P dC * Xmid))) =
      trace (star (dualGradient P Np Xbar Xmid) * dC) := by
  have hQstar : star (1 - P) = 1 - P := by simp [star_sub, hPstar]
  have hGrad :
      star (dualGradient P Np Xbar Xmid) =
        P * (Xmid * star Xbar * (1 + Np)) * (1 - P) := by
    simp [dualGradient, star_mul, hPstar, hQstar]
    noncomm_ring
  calc
    trace (star Xbar * ((1 + Np) * (coneMinus P dC * Xmid))) =
        trace ((star Xbar * (1 + Np) * (1 - P)) * (dC * (P * Xmid))) := by
          simp only [coneMinus]
          congr 1
          noncomm_ring
    _ = trace ((dC * (P * Xmid)) *
        (star Xbar * (1 + Np) * (1 - P))) := Matrix.trace_mul_comm _ _
    _ = trace (dC * (P * Xmid * star Xbar * (1 + Np) * (1 - P))) := by
      congr 1
      noncomm_ring
    _ = trace ((P * Xmid * star Xbar * (1 + Np) * (1 - P)) * dC) :=
      Matrix.trace_mul_comm _ _
    _ = trace (star (dualGradient P Np Xbar Xmid) * dC) := by
      rw [hGrad]
      congr 1
      noncomm_ring

end InfoGeometry.Canonical.PeirceBackpropTraceGradient
