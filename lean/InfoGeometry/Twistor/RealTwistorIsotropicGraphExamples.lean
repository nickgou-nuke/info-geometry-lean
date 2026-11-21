/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorIsotropicGraph

/-!
# Nonzero real clock example and a failed symmetry hypothesis

The already constructed clock on `DoubledSpace ℝ` supplies a concrete phase
with square minus one and a nonzero isotropic incidence graph.  The commuting
operator `-phase` supplies a counterexample if symmetry is omitted: its phased
graph is the identity graph, with a vector of neutral square two.

This two-real-dimensional spinor model checks nonvacuity of the general
algebraic theorem. It is not a Lorentzian four-dimensional spacetime model.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorIsotropicGraphExamples

open InfoGeometry.Krein RealTwistorIncidence RealTwistorIsotropicGraph
open scoped InnerProductSpace

abbrev Spinor := DoubledSpace ℝ

/-- Use the existing real clock; no new phase representation is postulated. -/
def phase : Module.End ℝ Spinor := (clockAxis (E := ℝ)).toLinearMap

theorem phase_sq : phase * phase = -1 := by
  apply LinearMap.ext
  intro u
  exact congrArg (fun T : Spinor →L[ℝ] Spinor => T u) (clockAxis_sq ℝ)

theorem phase_skew (u v : Spinor) : ⟪phase u, v⟫_ℝ = -⟪u, phase v⟫_ℝ := by
  change ⟪complex_i u, v⟫_ℝ = -⟪u, complex_i v⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right (complex_i (E := ℝ)) u v,
    adjoint_complex_i]
  change ⟪u, -(complex_i v)⟫_ℝ = -⟪u, complex_i v⟫_ℝ
  exact inner_neg_right u (complex_i v)

def axisVector : Spinor := to_doubled (1 : ℝ) 0

theorem axisVector_ne_zero : axisVector ≠ 0 := by
  intro h
  have hf := congrArg WithLp.fst h
  norm_num [axisVector, to_doubled] at hf

theorem phase_graph_isotropic :
    ∀ z ∈ incidenceSpace phase, ∀ w ∈ incidenceSpace phase,
      hessian_indefinite_formCoord z w = 0 :=
  (incidenceSpace_isotropic_iff phase).mpr phase_skew

theorem phase_graph_invariant :
    ∀ z ∈ incidenceSpace phase, phase.prodMap phase z ∈ incidenceSpace phase :=
  (incidenceSpace_phase_invariant_iff phase phase).mpr (Commute.refl phase)

/-- A concrete nonzero vector belongs to the null incidence graph. -/
theorem nonzero_phase_graph_vector :
    ∃ z : Spinor × Spinor, z ≠ 0 ∧ z ∈ incidenceSpace phase ∧
      hessian_indefinite_formCoord z z = 0 := by
  refine ⟨incidenceMap phase axisVector, ?_, ⟨axisVector, rfl⟩, ?_⟩
  · intro h
    exact axisVector_ne_zero (congrArg Prod.snd h)
  · exact phase_graph_isotropic _ ⟨axisVector, rfl⟩ _ ⟨axisVector, rfl⟩

theorem identity_graph_pairing :
    hessian_indefinite_formCoord (incidenceMap (1 : Module.End ℝ Spinor) axisVector)
      (incidenceMap (1 : Module.End ℝ Spinor) axisVector) = 2 := by
  rw [hessian_incidenceMap]
  norm_num [axisVector, to_doubled, WithLp.prod_inner_apply]

theorem identity_graph_not_isotropic :
    ¬ (∀ z ∈ incidenceSpace (1 : Module.End ℝ Spinor),
      ∀ w ∈ incidenceSpace (1 : Module.End ℝ Spinor),
        hessian_indefinite_formCoord z w = 0) := by
  intro h
  have hzero := h (incidenceMap 1 axisVector) ⟨axisVector, rfl⟩
    (incidenceMap 1 axisVector) ⟨axisVector, rfl⟩
  rw [identity_graph_pairing] at hzero
  norm_num at hzero

theorem phase_commutes_neg_phase : Commute phase (-phase) := by
  change phase * (-phase) = (-phase) * phase
  rw [mul_neg, neg_mul]

theorem phase_mul_neg_phase : phase * (-phase) = 1 := by
  rw [mul_neg, phase_sq, neg_neg]

/-- Commutation with the phase alone does not make an incidence graph null. -/
theorem neg_phase_not_isSymmetric : ¬ (-phase).IsSymmetric := by
  intro h
  have hskew := phase_mul_skew phase (-phase) phase_skew h phase_commutes_neg_phase
  rw [phase_mul_neg_phase] at hskew
  exact identity_graph_not_isotropic ((incidenceSpace_isotropic_iff 1).mpr hskew)

end InfoGeometry.Twistor.RealTwistorIsotropicGraphExamples
