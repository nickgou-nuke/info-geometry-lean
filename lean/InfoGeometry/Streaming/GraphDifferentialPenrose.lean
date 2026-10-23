/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Streaming.BipartiteGraphDirac
import InfoGeometry.Canonical.Drazin

/-!
# Graph differential: inverse support versus adjoint dynamics

The existing differential acts from vertex to edge cochains. Its adjoint
codifferential is not automatically its Moore–Penrose inverse. A rectangular
reflexive inverse of the incidence matrix supplies the two algebraic Penrose
equations on the native cochain carrier. The transpose choice is admissible
for the first equation exactly when `B Bᵀ B = B`.
-/

noncomputable section
namespace InfoGeometry.Streaming.BipartiteGraphDirac

variable {v e : Type*} [Fintype v] [Fintype e] [DecidableEq v] [DecidableEq e]

/-- The graph differential has zero Drazin inverse, irrespective of edge weights. -/
theorem differential_drazin_zero (B : Matrix e v ℝ) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse (differential B) 0 2 := by
  refine InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk (by simp) (by simp) ?_
  simp [pow_two, differential_sq]

omit [DecidableEq v] [DecidableEq e] in
/-- A rectangular generalized inverse supplies the first Penrose equation on cochains. -/
theorem differential_reverse_differential (B : Matrix e v ℝ) (M : Matrix v e ℝ)
    (h : B * M * B = B) :
    differential B * codifferential M.transpose * differential B = differential B := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp [differential, codifferential, Module.End.mul_apply]
  · simpa [differential, codifferential, Module.End.mul_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] using congrArg (fun T : Matrix e v ℝ => T.mulVec x.1) h

omit [DecidableEq v] [DecidableEq e] in
/-- The reverse Penrose equation is inherited from the rectangular reflexive inverse. -/
theorem reverse_differential_reverse (B : Matrix e v ℝ) (M : Matrix v e ℝ)
    (h : M * B * M = M) :
    codifferential M.transpose * differential B * codifferential M.transpose =
      codifferential M.transpose := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simpa [differential, codifferential, Module.End.mul_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] using congrArg (fun T : Matrix v e ℝ => T.mulVec x.2) h
  · simp [differential, codifferential, Module.End.mul_apply]

omit [DecidableEq e] in
/-- The adjoint can satisfy the first Penrose equation only at partial-isometry normalization. -/
theorem differential_codifferential_penrose_iff (B : Matrix e v ℝ) :
    differential B * codifferential B * differential B = differential B ↔
      B * B.transpose * B = B := by
  constructor
  · intro h
    ext a i
    have hx := congrArg (fun T : Module.End ℝ (Cochain v e) =>
      (T (Pi.single i 1, 0)).2 a) h
    simpa [differential, codifferential, Module.End.mul_apply,
      Matrix.mulVec_mulVec, Matrix.mulVec_single, ← Matrix.col_mul_eq_mulVec_col,
      Matrix.mul_assoc] using hx
  · intro h
    simpa using differential_reverse_differential B B.transpose h

end InfoGeometry.Streaming.BipartiteGraphDirac
