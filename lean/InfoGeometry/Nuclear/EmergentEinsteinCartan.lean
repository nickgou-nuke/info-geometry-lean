import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite vector readout for a proposed rotating-frame model

This module defines finite real vectors for a rotating-frame/current model,
forms their cross and scalar triple products, and proves a conditional
nonvanishing statement for a positively weighted scalar. It does not define
an Einstein-Cartan connection, spacetime torsion, a Nieh-Yan form, or a
physical spectral mass gap; those require additional geometric and dynamical
data.
-/

namespace InfoGeometry.Nuclear.EmergentEinsteinCartan

/-! ### 1. The Rotating Frame and Spin Connection -/

/-- 
  Model input consisting of a nonzero angular-velocity vector. No gauge
  connection is constructed from this data.
-/
structure RotatingFrame where
  -- The collective angular velocity vector of the core
  omega_coll : Fin 3 → ℝ
  -- Assumption that the core is actually rotating (non-static)
  h_rotating : ∃ i, omega_coll i ≠ 0

/-- 
  A finite vector readout that copies the supplied angular-velocity vector.
-/
def angular_velocity_readout (R : RotatingFrame) : Fin 3 → ℝ :=
  -- The spatial components of the connection are directly proportional to the rotation
  fun i => R.omega_coll i

/-! ### 2. Valence Currents and Spacetime Torsion -/

/--
  Two finite real vectors used as model inputs.
-/
structure ValenceCurrents where
  j_pi : Fin 3 → ℝ
  j_nu : Fin 3 → ℝ

/-- 
  Coordinate cross-product readout of the two input vectors. It is not a
  spacetime torsion tensor without an additional map and geometric data.
-/
def current_cross_product (V : ValenceCurrents) : Fin 3 → ℝ :=
  fun i => match i with
  | ⟨0, _⟩ => V.j_pi ⟨1, by decide⟩ * V.j_nu ⟨2, by decide⟩ - V.j_pi ⟨2, by decide⟩ * V.j_nu ⟨1, by decide⟩
  | ⟨1, _⟩ => V.j_pi ⟨2, by decide⟩ * V.j_nu ⟨0, by decide⟩ - V.j_pi ⟨0, by decide⟩ * V.j_nu ⟨2, by decide⟩
  | ⟨2, _⟩ => V.j_pi ⟨0, by decide⟩ * V.j_nu ⟨1, by decide⟩ - V.j_pi ⟨1, by decide⟩ * V.j_nu ⟨0, by decide⟩

/-! ### 3. A scalar triple-product readout -/

/-- 
  Model data and a positive scalar weight. No spacetime is constructed here.
-/
structure EmergentSpacetime where
  frame : RotatingFrame
  valence : ValenceCurrents
  G_eff : ℝ
  h_G_pos : G_eff > 0

/--
  Scalar triple product of the input angular-velocity and current vectors.
  This scalar is not identified with a Nieh-Yan invariant.
-/
def scalar_triple_readout (S : EmergentSpacetime) : ℝ :=
  let A := angular_velocity_readout S.frame
  let T := current_cross_product S.valence
  (A ⟨0, by decide⟩ * T ⟨0, by decide⟩) + 
  (A ⟨1, by decide⟩ * T ⟨1, by decide⟩) + 
  (A ⟨2, by decide⟩ * T ⟨2, by decide⟩)

/-- 
  The scalar triple-product readout multiplied by the model's positive weight.
-/
def weighted_scalar_readout (S : EmergentSpacetime) : ℝ :=
  S.G_eff * scalar_triple_readout S

/-! ### 4. Synthesis: The Non-Degeneracy Theorem -/

/--
  A nonzero scalar readout remains nonzero after multiplication by the
  positive model weight. This is a real-number fact, not a spectral-gap
  theorem.
-/
theorem weighted_scalar_readout_ne_zero (S : EmergentSpacetime)
    (h_readout : scalar_triple_readout S ≠ 0) :
    weighted_scalar_readout S ≠ 0 := by
  unfold weighted_scalar_readout
  exact mul_ne_zero (ne_of_gt S.h_G_pos) h_readout

end InfoGeometry.Nuclear.EmergentEinsteinCartan
