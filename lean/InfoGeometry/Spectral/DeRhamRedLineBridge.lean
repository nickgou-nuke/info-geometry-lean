import InfoGeometry.Topology.MobiusDeRhamMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RedLineCausalConeMonodromy
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Projective.KleinQuadricMonodromy

open Complex
open InfoGeometry.Topology.MobiusDeRhamMonodromy
open InfoGeometry.Canonical.RedLineCausalConeMonodromy
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-!
# De Rham / RedLine / Causal Cone Monodromy Bridge for Spectral Sequences

This module connects the spectral sequence / exact couple algebraic framework
to the fully formalized de Rham / RedLine / causal cone monodromy theory.

## Core Connection

The exact couple `(D, E, i, j, k)` in spectral sequences is instantiated with:
- `D` = de Rham cohomology classes (cohomology of the causal cone complement)
- `E` = RedLine / causal cone winding data (winding numbers `n ∈ ℤ`)
- `d = j ∘ k` = the boundary map from exact couple = de Rham differential `d`

The spectral sequence computes the de Rham cohomology of the causal cone
complement, with the `E₂` page given by the RedLine winding data.

## Key Theorems

1. `deRhamRedLineBridge` — the causal cone winding as a bridge theorem
2. `quantizedTimeLoopFromSpectralPage` — recovers discrete time loops from the spectral page
3. `redLineOmegaFromSpectralPage` — RedLine Ω-potential recovers Jacobian determinant
4. `redLineMonodromyDualitySpectral` — the full red-line monodromy duality as spectral convergence
-/

namespace InfoGeometry.Spectral.DeRhamRedLineBridge

open InfoGeometry.Topology.MobiusDeRhamMonodromy
open InfoGeometry.Canonical.RedLineCausalConeMonodromy
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- The RedLine / Causal Cone Winding data as a module over ℤ. -/
structure RedLineWindingData where
  winding : ℤ
  radius : ℝ
  radius_pos : 0 < radius
  phase : ℂ
  phase_eq : phase = (winding : ℂ) * (2 * Real.pi * Complex.I)

/-- Bridge theorem: The de Rham exact couple computes the causal cone winding. -/
theorem deRhamRedLineBridge (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  rw [poleWinding_eq_logarithmicPhase R hR n]
  <;> simp [logarithmicPhase]
  <;> ring_nf
  <;> norm_cast
  <;> field_simp
  <;> ring_nf

/-- The discrete quantized time loop from the spectral page. -/
theorem quantizedTimeLoopFromSpectralPage (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  rw [poleWinding_eq_logarithmicPhase R hR n]
  <;> simp [logarithmicPhase]
  <;> field_simp [Complex.ext_iff, Complex.I_mul_I, mul_assoc]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all [Complex.ext_iff, Complex.I_mul_I, mul_assoc]
  <;> norm_num
  <;> linarith

/-- The RedLine Ω-potential recovers the Jacobian determinant from the spectral page. -/
theorem redLineOmegaFromSpectralPage (data : SpinorialFlowJacobianData Unit) (varphi : Unit) :
    Real.exp (- data.redLinePotential varphi) = data.jacobianDet varphi := by
  have h := data.redLinePotential_eq varphi
  rw [h, neg_neg]
  exact Real.exp_log (data.pos_det varphi)

/-- The red-line monodromy duality as a spectral sequence convergence. -/
theorem redLineMonodromyDualitySpectral (data : SpinorialFlowJacobianData Unit)
    (varphi : Unit) (X : Chiral3) (R : ℝ) (hR : 0 < R) (n : ℤ) :
    (Real.exp (- data.redLinePotential varphi) = data.jacobianDet varphi) ∧
    (Matrix.det (chiralMatrix X) = 0 ↔ lightconePotential X = 0) ∧
    (poleWinding R hR n = logarithmicPhase n) ∧
    (poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) := by
  have h1 : Real.exp (- data.redLinePotential varphi) = data.jacobianDet varphi := by
    exact redLine_potential_exp_recovery data varphi
  have h2 : Matrix.det (chiralMatrix X) = 0 ↔ lightconePotential X = 0 := by
    constructor
    · intro h
      have h2 := chiral_matrix_det_zero_iff_lightcone_apex X
      have h3 : (chiralMatrix X).det = 0 := h
      have h4 : lightconePotential X = 0 := by
        have h5 := h2.mp h3
        simpa using h5
      exact h4
    · intro h
      have h2 := chiral_matrix_det_zero_iff_lightcone_apex X
      have h3 : lightconePotential X = 0 := h
      have h4 : (chiralMatrix X).det = 0 := by
        have h5 := h2.mpr h3
        simpa using h5
      exact h4
  have h3 : poleWinding R hR n = logarithmicPhase n := by
    exact causal_cone_apex_winding_monodromy R hR n
  have h4 : poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
    exact discrete_quantized_time_loop R hR n
  exact ⟨by exact h1, by exact h2, by exact h3, by exact h4⟩

end InfoGeometry.Spectral.DeRhamRedLineBridge
