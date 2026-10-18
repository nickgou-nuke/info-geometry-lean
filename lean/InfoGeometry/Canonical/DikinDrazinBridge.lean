import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorSurgery

/-!
# Dikin / Drazin Bridge

This module closes the finite coordinate-free algebra requested by the Dikin /
Drazin interlock:

* a tripotent operator `M`, with `M³ = M`, has an idempotent core projector
  `P_core = M²`;
* the complementary null projector `P_null = 1 - P_core` gives a partition of
  the identity;
* a Dikin/Hessian quadratic readout is stable on the Drazin core from an
  explicit core-positivity premise.

#### BUCKET 1: CLOSED FINITE THEOREMS
`coreProjector_idempotent`, `core_null_partition`, and
`dikin_metric_stability_in_core` are closed from explicit algebraic/positivity
premises.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`dikin_metric_stability_in_core` depends on the named premise
`core_positive_definite`; no Hessian positivity theorem is hidden as data.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove self-concordance, barrier containment, a true Dikin
ellipsoid theorem, analytic cone feasibility, or Riemann-zeta consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.DikinDrazinBridge

open Complex

universe u

/--
Coordinate-free Dikin/Drazin system.

`M` is the structural tripotent operator.  `Hessian` is the supplied local metric
operator.  The only metric positivity used by this file is the explicit premise
`core_positive_definite`, restricted to the Drazin core image `M² x`.
-/
structure DikinDrazinSystem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  M : E →L[ℂ] E
  tripotent : M ∘L M ∘L M = M
  Hessian : E →L[ℂ] E
  core_positive_definite :
    ∀ x : E, M (M x) ≠ 0 → 0 < (inner ℂ (M (M x)) (Hessian (M (M x)))).re

namespace DikinDrazinSystem

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (sys : DikinDrazinSystem E)

/-- The Drazin core projector `P_core = M²`. -/
def P_core : E →L[ℂ] E :=
  sys.M ∘L sys.M

/-- The complementary Drazin null projector `P_null = 1 - M²`. -/
def P_null : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - sys.P_core

/-- Dikin/Hessian quadratic readout at a tangent vector. -/
def dikinMetricDistance (v : E) : ℝ :=
  (inner ℂ v (sys.Hessian v)).re

/--
Tripotency makes the Drazin core projector idempotent: `(M²)² = M²`.
-/
theorem coreProjector_idempotent :
    sys.P_core ∘L sys.P_core = sys.P_core := by
  apply ContinuousLinearMap.ext
  intro x
  have h_apply :=
    congrArg (fun F : E →L[ℂ] E => F (sys.M x)) sys.tripotent
  simpa [P_core, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc]
    using h_apply

/-- The core and null Drazin projectors sum to the identity. -/
theorem core_null_partition :
    sys.P_core + sys.P_null = ContinuousLinearMap.id ℂ E := by
  ext x
  simp [P_core, P_null]

/--
If a vector has nonzero Drazin-core projection, the supplied Dikin metric is
strictly positive on that projected core vector.
-/
theorem dikin_metric_stability_in_core
    (x : E) (h_nonzero : sys.P_core x ≠ 0) :
    0 < dikinMetricDistance sys (sys.P_core x) := by
  simpa [dikinMetricDistance, P_core] using
    sys.core_positive_definite x h_nonzero

end DikinDrazinSystem

/-! ## Finite attention-Laplacian projector algebra

The following statements are conditional on an actual Drazin inverse witness
and, for annihilation of the harmonic complement, the index-one law.  They do
not assert existence of a Drazin inverse for an arbitrary attention operator.
-/

namespace AttentionLaplacian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

local notation "EndV" => V →ₗ[ℝ] V

/-- The dynamic projector associated with a Laplacian `L` and a chosen
    Drazin Green operator `G`. -/
def dynamicProjector (L G : EndV) : EndV := L * G

/-- The complementary harmonic projector. -/
def harmonicProjector (L G : EndV) : EndV := 1 - dynamicProjector L G

/-- The Drazin dynamic projector is idempotent by the outer-inverse law. -/
theorem dynamicProjector_idempotent
    {L G : EndV} (hD : OperatorSurgery.IsDrazinInverse L G) :
    dynamicProjector L G * dynamicProjector L G = dynamicProjector L G := by
  exact OperatorSurgery.drazin_indexOne_projector_idempotent_ring hD.1

/-- Dynamic and harmonic projectors partition the identity. -/
theorem projectors_partition (L G : EndV) :
    dynamicProjector L G + harmonicProjector L G = 1 := by
  simp [dynamicProjector, harmonicProjector]

/-- The two projectors have zero product, under the Drazin outer-inverse law. -/
theorem dynamic_harmonic_disjoint
    {L G : EndV} (hD : OperatorSurgery.IsDrazinInverse L G) :
    dynamicProjector L G * harmonicProjector L G = 0 := by
  rw [harmonicProjector, mul_sub, mul_one,
    dynamicProjector_idempotent hD]
  exact sub_self _

/-- Under the index-one law, the Laplacian annihilates the harmonic projector. -/
theorem laplacian_annihilates_harmonic
    {L G : EndV} (hD : OperatorSurgery.IsDrazinInverse L G)
    (hIndexOne : L * G * L = L) :
    L * harmonicProjector L G = 0 := by
  exact OperatorSurgery.drazin_indexOne_annihilates_right_defect_ring
    hIndexOne hD.2.1

end AttentionLaplacian

end InfoGeometry.Canonical.DikinDrazinBridge
