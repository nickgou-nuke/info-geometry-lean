import InfoGeometry.Meta.Architecture
import Mathlib

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TopologicalGapShadow

Proof-carrying shadow spectrum for the discrete SUSY / hopping lane.

This file introduces only the owner surfaces that the current repo can support:

* the SUSY hopping operator as the repo-native real odd-odd closure `{Q, Q}`,
* the BPS/Drazin core as the kernel of that operator,
* the excited state sector as the orthogonal complement of the core,
* a proof-carrying topological gap datum,
* vanishing entropy-production readout on the core.

It does **not** claim a full spectral theorem, unbounded-operator analysis, or
any theorem about Riemann zeros.
-/

namespace InfoGeometry.Canonical.TopologicalGapShadow

section Core

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- The discrete SUSY / hopping operator on the real doubled carrier `{Q, Q}`. -/
@[rep_depth operator]
noncomputable def susyHoppingOperator (Q : EndH) : EndH :=
  Q * Q + Q * Q

/-- The BPS / Drazin core is the kernel of the hopping operator. -/
@[rep_depth operator]
noncomputable def DrazinCore (Q : EndH) : Submodule ℝ E :=
  (susyHoppingOperator Q).ker

/-- The excited sector is the orthogonal complement of the core. -/
@[rep_depth operator]
noncomputable def ExcitedStateSector (Q : EndH) : Submodule ℝ E :=
  (DrazinCore Q)ᗮ

/--
Proof-carrying topological gap datum: a strictly positive lower bound on the
energy readout away from the BPS core.
-/
@[rep_depth operator]
structure GapDatum (Q : EndH) where
  Δ : ℝ
  gap_positive : Δ > 0
  bound :
    ∀ ψ, ψ ∈ ExcitedStateSector Q →
      ‖(susyHoppingOperator Q) ψ‖ ≥ Δ * ‖ψ‖

/-- Core states are annihilated by the SUSY hopping operator. -/
@[rep_depth operator]
theorem susyHoppingOperator_eq_zero_on_core
    (Q : EndH) {ψ : E} (h_core : ψ ∈ DrazinCore Q) :
    susyHoppingOperator Q ψ = 0 := by
  exact h_core

/--
Entropy-production shadow vanishes on the BPS / Drazin core.

This is the owner-level statement that dissipation lives outside the protected
kernel sector.
-/
@[capstone, rep_depth operator]
theorem entropy_production_vanishes_on_core
    (Q : EndH) (ψ : E) (h_core : ψ ∈ DrazinCore Q) :
    ‖(susyHoppingOperator Q) ψ‖ = 0 := by
  rw [susyHoppingOperator_eq_zero_on_core (Q := Q) h_core]
  simp

/--
Combined packet for the shadow gap lane.
-/
@[rep_depth operator]
theorem topological_gap_shadow_packet
    (Q : EndH) :
    (∀ {ψ : E}, ψ ∈ DrazinCore Q → susyHoppingOperator Q ψ = 0)
      ∧
    (∀ ψ : E, ψ ∈ DrazinCore Q → ‖(susyHoppingOperator Q) ψ‖ = 0) := by
  refine ⟨?_, ?_⟩
  · intro ψ hψ
    exact susyHoppingOperator_eq_zero_on_core (Q := Q) hψ
  · intro ψ hψ
    exact entropy_production_vanishes_on_core (Q := Q) ψ hψ

/--
Secondary bridge: if the SUSY hopping operator is normal, its range lies in the
excited sector `(ker H)ᗮ`.

This is the operatorial form of "dissipation propagates away from the BPS core"
without introducing any finite-dimensional diagonalization assumptions.
-/
@[rep_depth operator]
theorem range_le_excitedStateSector_of_isStarNormal
    (Q : EndH) (hNormal : IsStarNormal (susyHoppingOperator Q)) :
    (susyHoppingOperator Q).range ≤ ExcitedStateSector Q := by
  intro y hy
  change y ∈ ((susyHoppingOperator Q).ker)ᗮ
  rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range
      (T := susyHoppingOperator Q) hNormal]
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz' := (Submodule.mem_orthogonal _ _).1 hz
  simpa [real_inner_comm] using hz' y hy

end Core

end InfoGeometry.Canonical.TopologicalGapShadow
