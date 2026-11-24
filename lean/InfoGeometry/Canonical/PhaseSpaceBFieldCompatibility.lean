/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GeneralizedSolderingBridge

/-!
# B-field transport of the real phase-space grading

The generalized-metric involution and the primal/dual grading are different
endomorphisms. Transporting both by a skew B-field preserves anticommutation;
retaining the original grading works exactly when the B-field vanishes.
On the existing carrier `E × E*`, this file constructs the
transported grading, proves its neutral anti-isometry and Clifford relations,
and identifies the exact obstruction for retaining the original grading.

Everything is real and algebraic. No closedness of a differential B-field,
Courant integrability, spectral-triple domain, or DFT field equation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.PhaseSpaceBFieldCompatibility

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open InfoGeometry.Canonical.GeneralizedSolderingBridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Transport the primal/dual grading by the same B-transform as the metric involution. -/
def transportedGrading (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  G.bTransform * neutralParaInvolution * G.bTransformInv

@[simp] theorem transportedGrading_apply (G : GeneralizedMetricDatum E)
    (x : E) (φ : Module.Dual ℝ E) :
    transportedGrading G (x, φ) = (x, (2 : ℝ) • G.bField.twist x - φ) := by
  apply Prod.ext
  · rfl
  · change G.bField.twist x + -(φ - G.bField.twist x) = _
    simp [two_smul, sub_eq_add_neg, add_left_comm, add_comm]

/-- In the already constructed soldered coordinates, the transported grading is diagonal. -/
@[simp] theorem transportedGrading_soldering (G : GeneralizedMetricDatum E) (x y : E) :
    transportedGrading G (generalizedSoldering G (x, y)) =
      generalizedSoldering G (x, -y) := by
  simp [generalizedSoldering_apply, two_smul, sub_eq_add_neg,
    add_assoc, add_comm]

theorem transportedGrading_sq (G : GeneralizedMetricDatum E) :
    transportedGrading G * transportedGrading G = 1 := by
  apply LinearMap.ext
  intro X
  obtain ⟨⟨x, y⟩, rfl⟩ := (generalizedSoldering G).surjective X
  change transportedGrading G (transportedGrading G (generalizedSoldering G (x, y))) = _
  simp only [transportedGrading_soldering, neg_neg, Module.End.one_apply]

theorem transportedGrading_neutral_anti_isometry (G : GeneralizedMetricDatum E)
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (transportedGrading G X) (transportedGrading G Y) =
      -canonicalNeutralBilin X Y := by
  obtain ⟨⟨x, y⟩, rfl⟩ := (generalizedSoldering G).surjective X
  obtain ⟨⟨u, v⟩, rfl⟩ := (generalizedSoldering G).surjective Y
  rw [transportedGrading_soldering, transportedGrading_soldering,
    generalizedSoldering_neutralPairing, generalizedSoldering_neutralPairing]
  simp [add_comm]

/-- Transporting both operators preserves the real Clifford relation. -/
theorem transportedGrading_polarization_anticommute (G : GeneralizedMetricDatum E) :
    transportedGrading G * G.polarization =
      -(G.polarization * transportedGrading G) := by
  apply LinearMap.ext
  intro X
  obtain ⟨⟨x, y⟩, rfl⟩ := (generalizedSoldering G).surjective X
  change transportedGrading G (G.polarization (generalizedSoldering G (x, y))) =
    -(G.polarization (transportedGrading G (generalizedSoldering G (x, y))))
  rw [generalizedSoldering_polarization_swap, transportedGrading_soldering,
    transportedGrading_soldering, generalizedSoldering_polarization_swap]
  simpa using map_neg (generalizedSoldering G) (-y, x)

/-- The real square-minus-one endomorphism produced by the two compatible involutions. -/
def transportedPhase (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  transportedGrading G * G.polarization

@[simp] theorem transportedPhase_soldering (G : GeneralizedMetricDatum E) (x y : E) :
    transportedPhase G (generalizedSoldering G (x, y)) =
      generalizedSoldering G (y, -x) := by
  change transportedGrading G (G.polarization (generalizedSoldering G (x, y))) = _
  rw [generalizedSoldering_polarization_swap, transportedGrading_soldering]

theorem transportedPhase_sq (G : GeneralizedMetricDatum E) :
    transportedPhase G * transportedPhase G = -1 := by
  apply LinearMap.ext
  intro X
  obtain ⟨⟨x, y⟩, rfl⟩ := (generalizedSoldering G).surjective X
  change transportedPhase G (transportedPhase G (generalizedSoldering G (x, y))) =
    -(generalizedSoldering G (x, y))
  rw [transportedPhase_soldering, transportedPhase_soldering]
  exact map_neg (generalizedSoldering G) (x, y)

theorem polarization_transportedPhase_polarization (G : GeneralizedMetricDatum E) :
    G.polarization * transportedPhase G * G.polarization = -transportedPhase G := by
  apply LinearMap.ext
  intro X
  obtain ⟨⟨x, y⟩, rfl⟩ := (generalizedSoldering G).surjective X
  change G.polarization (transportedPhase G (G.polarization
    (generalizedSoldering G (x, y)))) = -(transportedPhase G (generalizedSoldering G (x, y)))
  rw [generalizedSoldering_polarization_swap, transportedPhase_soldering,
    generalizedSoldering_polarization_swap, transportedPhase_soldering]
  simpa using map_neg (generalizedSoldering G) (y, -x)

/-- The original grading is retained precisely for a vanishing B-field. -/
theorem transportedGrading_eq_original_iff (G : GeneralizedMetricDatum E) :
    transportedGrading G = neutralParaInvolution ↔ G.bField.twist = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hy := congrArg (fun T : Module.End ℝ (PhaseSpaceCarrier E) => (T (x, 0)).2 y) h
    simp only [transportedGrading_apply, neutralParaInvolution_apply,
      sub_zero, LinearMap.smul_apply, smul_eq_mul, neg_zero, LinearMap.zero_apply] at hy
    change G.bField.twist x y = 0
    linarith
  · intro h
    apply LinearMap.ext
    rintro ⟨x, φ⟩
    simp [transportedGrading_apply, h]

/-- Exact obstruction to identifying every generalized-metric involution with
an operator odd for the fixed primal/dual grading. -/
theorem originalGrading_polarization_anticommute_iff (G : GeneralizedMetricDatum E) :
    neutralParaInvolution * G.polarization =
      -(G.polarization * neutralParaInvolution) ↔ G.bField.twist = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun T : Module.End ℝ (PhaseSpaceCarrier E) => (T (x, 0)).1) h
    have he : -(G.metric.gFlat.symm (G.bField.twist x)) =
        G.metric.gFlat.symm (G.bField.twist x) := by
      simpa [polarization_apply, neutralParaInvolution_apply] using hx
    have hb := congrArg G.metric.gFlat he
    apply LinearMap.ext
    intro y
    have hy := congrArg (fun φ : Module.Dual ℝ E => φ y) hb
    simp only [map_neg, LinearEquiv.apply_symm_apply, LinearMap.neg_apply] at hy
    change G.bField.twist x y = 0
    linarith
  · intro h
    rw [← (transportedGrading_eq_original_iff G).mpr h]
    exact transportedGrading_polarization_anticommute G

/-- For a nonzero B-field, the fixed grading genuinely fails the relation. -/
theorem originalGrading_not_anticommute_of_twist_ne_zero (G : GeneralizedMetricDatum E)
    (hB : G.bField.twist ≠ 0) :
    neutralParaInvolution * G.polarization ≠
      -(G.polarization * neutralParaInvolution) := by
  exact fun h => hB ((originalGrading_polarization_anticommute_iff G).mp h)

end InfoGeometry.Canonical.PhaseSpaceBFieldCompatibility
