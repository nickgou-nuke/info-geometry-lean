/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixGibbs
import InfoGeometry.Thermo.RealDensityRadialFlow

/-! # A logarithmic Gibbs chart for radial density mixing

Every strictly positive trace-one real matrix is the normalized exponential
of its native CFC logarithm. Mixing a positive semidefinite trace-one matrix
with a nonzero amount of the central density gives such a faithful matrix.
Thus the radial owner has an explicit self-adjoint Gibbs exponent throughout
the segment with parameter less than one, even for a singular input state.

This is an exact pointwise connection between the existing state constructors.
It does not identify this logarithmic path with the affine Hamiltonian
isotherms, or assert smoothness or entropy monotonicity of the radial path.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixGibbsRadialChart

open SouriauHilbertSchmidtOnsager RealMatrixGibbs RealDensityRadialFlow
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Mat" => MatrixSpace n

/-- The real CFC logarithm supplies an exponent for every faithful density. -/
theorem density_log_of_trace_one (ρ : Mat) (hρ : IsStrictlyPositive ρ)
    (htr : Matrix.trace ρ = 1) : density (CFC.log ρ) = ρ := by
  simp only [density, partition, CFC.exp_log ρ hρ, htr, inv_one, one_smul]

/-- The central density is positive definite in nonzero dimension. -/
theorem uniformDensity_posDef (hn : n ≠ 0) : (uniformDensity n).PosDef := by
  change ((n : ℝ)⁻¹ • (1 : Mat)).PosDef
  exact Matrix.PosDef.one.smul
    (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))

/-- A positive central contribution makes the radial state faithful, including
when the input state is only positive semidefinite. -/
theorem radialMix_strictlyPositive (hn : n ≠ 0) (r : ℝ) (ρ : Mat)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hρ : ρ.PosSemidef) :
    IsStrictlyPositive (radialMix r ρ) := by
  apply Matrix.isStrictlyPositive_iff_posDef.mpr
  exact Matrix.PosDef.posSemidef_add (hρ.smul hr₀)
    ((uniformDensity_posDef hn).smul (sub_pos.mpr hr₁))

/-- The constructed radial state is exactly the Gibbs density of its explicit
self-adjoint logarithmic exponent; faithfulness and trace one are derived. -/
theorem radialMix_gibbs_realization (hn : n ≠ 0) (r : ℝ) (ρ : Mat)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ = 1) :
    IsSelfAdjoint (CFC.log (radialMix r ρ)) ∧
      density (CFC.log (radialMix r ρ)) = radialMix r ρ := by
  refine ⟨IsSelfAdjoint.log, ?_⟩
  exact density_log_of_trace_one _ (radialMix_strictlyPositive hn r ρ hr₀ hr₁ hρ)
    (radialMix_trace hn r ρ htr)

end InfoGeometry.Thermo.RealMatrixGibbsRadialChart
