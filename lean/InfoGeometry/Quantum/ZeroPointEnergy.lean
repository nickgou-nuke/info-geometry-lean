import InfoGeometry.Architecture.SpinFactor
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A finite-dimensional variance-floor implication

This module packages a Spin Factor domain point together with an explicit
variance lower-bound hypothesis. It proves that this supplied bound is strictly
positive when the real dimension is positive. The bound is input data in
`SpinFactorState`; this file does not derive it from the Hessian, construct a
thermodynamic limit, or prove a topological obstruction.
-/

namespace InfoGeometry.Quantum.ZeroPointEnergy

open InfoGeometry.Architecture.SpinFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A finite-dimensional Spin Factor point equipped with a real variance value
and an explicit lower-bound hypothesis. The field `cramer_rao_floor` is an
assumption carried by this model, not a theorem derived here from the Hessian. -/
structure SpinFactorState (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] where
  x : E
  domain_mem : SpinFactorDomain x
  -- The variance value supplied by the model
  variance_limit : ℝ
  -- Explicit lower-bound assumption; no derivation is included in this structure.
  cramer_rao_floor : (1 / (4 * (Module.finrank ℝ E : ℝ))) ≤ variance_limit

/-- If the input model carries the stated finite-dimensional floor and the
dimension is positive, then its variance value is positive. -/
lemma zero_point_energy_positive (S : SpinFactorState E)
    (h_pos : 0 < Module.finrank ℝ E) :
    0 < S.variance_limit := by
  have h_rank_pos : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast h_pos
  have h_floor_pos : 0 < 1 / (4 * (Module.finrank ℝ E : ℝ)) := by
    apply div_pos
    · norm_num
    · linarith
  exact lt_of_lt_of_le h_floor_pos S.cramer_rao_floor

end InfoGeometry.Quantum.ZeroPointEnergy
