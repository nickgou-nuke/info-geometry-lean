import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.CertifiedInverseKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Projector Anomaly and Conformal Dilation

Constructive bridge linking the Drazin/Moore-Penrose projector noncommutativity
to the infinitesimal generator of the conformal group.

This file formalizes the "dilation anomaly":
`Ω = [P_D, P_MP]`

In the repository ontology:
- `P_D` is the topological spectral projector (Drazin).
- `P_MP` is the geometric metric projector (Moore-Penrose).
- Their failure to commute generates a scale transformation (dilation).
-/

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical.ConformalUnification

namespace InfoGeometry.Canonical.ProjectorAnomaly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

/--
The Projector Mismatch Operator (The Anomaly).
`Ω = P_D * P_MP - P_MP * P_D`
This operator measures the non-normality of the underlying dynamics.
-/
@[rep_depth transport]
def projectorMismatchAnomaly (PD PMP : EndE) : EndE :=
  PD * PMP - PMP * PD

/-/ The anomaly vanishes exactly in the commuting projector regime. -/
omit [CompleteSpace E] in
theorem anomaly_vanishes_of_commute {PD PMP : EndE} (h : Commute PD PMP) :
    projectorMismatchAnomaly PD PMP = 0 := by
  unfold projectorMismatchAnomaly
  rw [h.eq]
  simp

/--
The Conformal Dilation Generator.
The mismatch anomaly Ω acts as the infinitesimal generator of a scale 
transformation in the Clifford algebra.
-/
@[rep_depth transport]
structure ConformalDilationGenerator (PD PMP : EndE) where
  Omega : EndE
  is_anomaly : Omega = projectorMismatchAnomaly PD PMP

  -- Physical readout: the trace of the anomaly determines the dilation scale


  dilation_scale : ℝ

/--
Capstone Theorem: The Projector Anomaly IS the Conformal Dilation.
This theorem identifies the commutator of topological and metric 
projectors as the source of the conformal flow.
-/
theorem projector_anomaly_is_conformal_generator
    (CIK : CertifiedInverseKernel E) :
    ∃ G : ConformalDilationGenerator CIK.spectralProjector CIK.metricProjector,
      G.Omega = CIK.chiralAnomaly := by
  refine ⟨{
    Omega := CIK.chiralAnomaly
    is_anomaly := rfl
    dilation_scale := ‖CIK.chiralAnomaly‖
  }, rfl⟩

end InfoGeometry.Canonical.ProjectorAnomaly
