/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse

/-!
# Dirichlet energy and the group-inverse Green form

This module proves the algebraic Green identity for a self-adjoint operator
with a group inverse.  It does not assert positivity of the quadratic form;
that additionally requires a positive-semidefinite hypothesis on the
operator.  The finite weighted detailed-balance owner is
`InfoGeometry.Probability.FiniteMarkovWeightedAdjoint`.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For a self-adjoint operator `L` and its group inverse `G`, the quadratic
form of `L` equals the Green quadratic form of the source `L x`. -/
theorem dirichletForm_eq_groupInverse_greenForm
    (L G : Module.End ℝ V) (hG : IsGroupInverse L G)
    (hL : ∀ u v : V, @inner ℝ V _ u (L v) = @inner ℝ V _ (L u) v)
    (x : V) :
    @inner ℝ V _ x (L x) = @inner ℝ V _ (L x) (G (L x)) := by
  have hLGL : (L * G * L) x = L x :=
    congrArg (fun T : Module.End ℝ V => T x) hG.1
  calc
    @inner ℝ V _ x (L x) = @inner ℝ V _ x ((L * G * L) x) := by
      rw [← hLGL]
    _ = @inner ℝ V _ x (L (G (L x))) := by
      simp only [Module.End.mul_apply]
    _ = @inner ℝ V _ (L x) (G (L x)) := hL x (G (L x))

end InfoGeometry.QuantumContext.MarkovDrazin
