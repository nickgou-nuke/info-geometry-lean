/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Conformal.MaxwellStressTensor
import InfoGeometry.Conformal.MannheimWeylKazanasCosmology
import InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance
import InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Constructive Open-Debt Closure (`MA₉`–`MA₁₂`): PT Stokes Wedge & 4D Weyl UV Convergence, Mannheim–Kazanas Rotation Curves, NJL Collective Higgs Pole, & Local Weyl Stress-Energy Trace

Closes the constructive open mathematical problems identified in the epistemic compilation ledger
without scalar/certificate shortcuts or axiom extensions:

1. **Archetype `MA₉` — PT Stokes-Wedge Gaussian Measure Theory & 4D Weyl UV Power-Counting**:
   - Exact `MeasureTheory.Integrable (ghostStokesIntegrand b θ) ↔ Real.cos (2 * θ) < 0` on
     `exp(b * (exp(-i θ) * y)²)`: real-axis divergence at `θ = 0` vs. convergent PT imaginary
     axis at `θ = π / 2` with exact Gaussian value `∫ y, exp(-b * y²) = √(π / b) > 0`;
   - Topological loop identity `L - 1 = I - V` forcing `weylSuperficialDegree L V I = 4`
     (power-counting renormalizable to all loop orders) vs. `einsteinSuperficialDegree = 2 L + 2`;
   - 4D radial momentum UV `MeasureTheory.IntegrableOn` for `weylBubbleUVIntegrand m₁ m₂` on
     `Set.Ioi Λ` (`O(k⁻⁵)` via `integrableOn_Ioi_rpow_of_lt`) vs. non-integrable `k¹` and `k³`
     Einstein graviton bubbles (`integrableOn_Ioi_rpow_iff`).

2. **Archetype `MA₁₀` — Mannheim–Kazanas Geodesic Galactic Rotation Curve, Transition Radius & Tully–Fisher Law**:
   - Exact geodesic formula `(c² r / 2) * deriv B(r) = B⋆ c² / r + (Γ_tot c² / 2) r - κ c² r²`
     for `B(r) = mannheimKazanasPotential 1 (N⋆ β⋆) (N⋆ γ⋆ + γ₀) κ r`;
   - Strict dark-matter-free velocity boost over Newtonian Keplerian decay;
   - Exact square completion proving `mkTransitionRadius B⋆ Γ_tot = √(2 B⋆ / Γ_tot)` achieves the
     minimum flat-regime velocity with exact Baryonic Tully–Fisher fourth-power law
     `(v_c²)² = 2 c⁴ B⋆ Γ_tot`, plus outer de Sitter turnover at `r = Γ_tot / (4 κ)`.

3. **Archetype `MA₁₁` — NJL Collective Goldstone Zero-Mode & Dynamical Bound-State Higgs Pole**:
   - Under `g * I_gap = 1`, exact factorizations `1 - g Π_P(q²) = (g J / 2) q²` (massless Goldstone
     pole `q² = 0`) and `1 - g Π_S(q²) = (g J / 2) (q² - 4 m_dyn²)` (`M_H = 2 m_dyn` pole with
     positive ghost-free derivative slope `g J / 2 > 0`);
   - Under Mannheim's `γ_θ = -1` attractive tensor threshold shift `0 < ΔA < 4 m_dyn²`, the dressed
     Higgs bound-state pole sits strictly inside `(0, 4 m_dyn²)` below threshold `2 m_dyn`.

4. **Archetype `MA₁₂` — Position-Dependent Weyl Dirac Spin-Connection Cancellation & On-Shell Traceless `T_{μν}`**:
   - `HasDerivAt` local Weyl rescaling product rule canceling inhomogeneous `β'(x)` terms under the
     curved spin-connection shift **iff** `w = -(d - 1) / 2` (uniquely `-3/2` in `d = 4`);
   - 4D Maxwell trace-freeness iff `d = 4`;
   - Exact 4D signature-general trace identity for combined Maxwell + Yukawa-Dirac + improved
     conformal scalar stress-energy tensor:
     `∑ μ, ε μ * conformalMatterStress4 ... μ = S * conformalScalarFieldEq ...`,
     vanishing identically on-shell (`= 0`) even with dynamically induced fermion and `λ S⁴` masses,
     locking cosmological `4 λ S⁴ = R S² / 6 + tr_matter` when `W_{μν} = 0`.
-/

noncomputable section

namespace InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure

open Filter MeasureTheory Set BigOperators
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology
open InfoGeometry.MetaCompiler

/-! ## Archetype `MA₉`: PT Stokes Wedge & 4D Weyl Quantum-Gravity UV Power-Counting -/

section MA9_PTStokesWedgeAndWeylUV

/-- PT Stokes-wedge rotated Gaussian path-integral integrand `exp(b * (exp(-i θ) * y)²)`. -/
def ghostStokesIntegrand (b θ y : ℝ) : ℂ :=
  Complex.exp ((b : ℂ) * (Complex.exp (-Complex.I * (θ : ℂ)) * (y : ℂ)) ^ 2)

/-- Superficial UV degree of divergence of a 4D fourth-derivative conformal Weyl-gravity graph
with `L` loops, `V` vertices, and `I` internal propagators: `4 L + 4 V - 4 I`. -/
def weylSuperficialDegree (L V I : ℤ) : ℤ :=
  4 * L + 4 * V - 4 * I

/-- Superficial UV degree of divergence of a 4D two-derivative Einstein–Hilbert graph:
`4 L + 2 V - 2 I`. -/
def einsteinSuperficialDegree (L V I : ℤ) : ℤ :=
  4 * L + 2 * V - 2 * I

/-- Radial 4D Euclidean 1-loop self-energy integrand `k³ / ((k² + m₁²)² (k² + m₂²)²)` for
fourth-order conformal propagators. -/
def weylBubbleUVIntegrand (m₁ m₂ k : ℝ) : ℝ :=
  k ^ 3 / ((k ^ 2 + m₁ ^ 2) ^ 2 * (k ^ 2 + m₂ ^ 2) ^ 2)

lemma stokes_exponent_re (b θ y : ℝ) :
    ((b : ℂ) * (Complex.exp (-Complex.I * (θ : ℂ)) * (y : ℂ)) ^ 2).re =
      b * Real.cos (2 * θ) * y ^ 2 := by
  have hsq : (Complex.exp (-Complex.I * (θ : ℂ)) * (y : ℂ)) ^ 2 =
      Complex.exp (((-(2 * θ) : ℝ) : ℂ) * Complex.I) * ((y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 1
    · congr 1
      push_cast
      ring
    · push_cast
      ring
  rw [hsq]
  have heuler : Complex.exp (((-(2 * θ) : ℝ) : ℂ) * Complex.I) =
      (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [heuler]
  rw [show (b : ℂ) * (((Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I) *
      ((y ^ 2 : ℝ) : ℂ)) =
      ((b * Real.cos (2 * θ) * y ^ 2 : ℝ) : ℂ) +
        ((-b * Real.sin (2 * θ) * y ^ 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  ring

/-- **PT Stokes-Wedge Gaussian Measure Theorem & 4D Weyl UV Convergence (`MA₉`)**:
1. Exact `MeasureTheory.Integrable (ghostStokesIntegrand b θ) ↔ Real.cos (2 * θ) < 0` (`b > 0`);
2. Real-axis divergence at `θ = 0` vs. PT imaginary-axis convergence at `θ = π / 2` with exact
   Gaussian integral `∫ y, exp(-b * y²) = √(π / b) > 0`;
3. Euler loop identity `L - 1 = I - V` yields constant `weylSuperficialDegree = 4` independent of
   loop count `L`, whereas `einsteinSuperficialDegree = 2 * L + 2`;
4. For any `0 < Λ` and masses `m₁, m₂`, the 4D Weyl radial loop integrand is `IntegrableOn`
   `Set.Ioi Λ`, whereas Einstein's `k¹` and `k³` radial loop integrands diverge on `Set.Ioi Λ`. -/
theorem pt_stokes_wedge_gaussian_and_weyl_uv_convergence :
    (∀ b θ y : ℝ, ‖ghostStokesIntegrand b θ y‖ = Real.exp (-(-b * Real.cos (2 * θ)) * y ^ 2)) ∧
    (∀ b θ : ℝ, 0 < b →
      (MeasureTheory.Integrable (ghostStokesIntegrand b θ) ↔ Real.cos (2 * θ) < 0)) ∧
    (∀ b : ℝ, 0 < b →
      ¬ MeasureTheory.Integrable (fun q : ℝ => Real.exp (b * q ^ 2)) ∧
      ¬ MeasureTheory.Integrable (ghostStokesIntegrand b 0) ∧
      MeasureTheory.Integrable (ghostStokesIntegrand b (Real.pi / 2)) ∧
      (∀ y : ℝ, ghostStokesIntegrand b (Real.pi / 2) y = (Real.exp (-b * y ^ 2) : ℂ)) ∧
      (∫ y : ℝ, Real.exp (-b * y ^ 2) = Real.sqrt (Real.pi / b)) ∧
      0 < ∫ y : ℝ, Real.exp (-b * y ^ 2)) ∧
    (∀ L V I : ℤ, L - 1 = I - V →
      weylSuperficialDegree L V I = 4 ∧ einsteinSuperficialDegree L V I = 2 * L + 2) ∧
    (∀ Λ m₁ m₂ : ℝ, 0 < Λ →
      MeasureTheory.IntegrableOn (weylBubbleUVIntegrand m₁ m₂) (Set.Ioi Λ) ∧
      ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (1 : ℝ)) (Set.Ioi Λ) ∧
      ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (3 : ℝ)) (Set.Ioi Λ)) := by
  have hnorm_formula : ∀ b θ y : ℝ,
      ‖ghostStokesIntegrand b θ y‖ = Real.exp (-(-b * Real.cos (2 * θ)) * y ^ 2) := by
    intro b θ y
    unfold ghostStokesIntegrand
    rw [Complex.norm_exp, stokes_exponent_re]
    congr 1
    ring
  have hcrit : ∀ b θ : ℝ, 0 < b →
      (MeasureTheory.Integrable (ghostStokesIntegrand b θ) ↔ Real.cos (2 * θ) < 0) := by
    intro b θ hb
    have hcont : Continuous (ghostStokesIntegrand b θ) := by
      unfold ghostStokesIntegrand
      fun_prop
    rw [← MeasureTheory.integrable_norm_iff hcont.aestronglyMeasurable]
    have hfun : (fun y : ℝ => ‖ghostStokesIntegrand b θ y‖) =
        fun y : ℝ => Real.exp (-(-b * Real.cos (2 * θ)) * y ^ 2) := by
      ext y
      exact hnorm_formula b θ y
    rw [hfun, integrable_exp_neg_mul_sq_iff]
    constructor
    · intro hpos
      nlinarith [hb, hpos]
    · intro hneg
      nlinarith [hb, hneg]
  refine ⟨hnorm_formula, hcrit, ?_, ?_, ?_⟩
  · intro b hb
    have hdiv_real : ¬ MeasureTheory.Integrable (fun q : ℝ => Real.exp (b * q ^ 2)) := by
      have heq : (fun q : ℝ => Real.exp (b * q ^ 2)) =
          fun q : ℝ => Real.exp (-(-b) * q ^ 2) := by
        ext q; ring_nf
      rw [heq, integrable_exp_neg_mul_sq_iff]
      linarith [hb]
    have hdiv0 : ¬ MeasureTheory.Integrable (ghostStokesIntegrand b 0) := by
      rw [hcrit b 0 hb]
      norm_num
    have hconvPi : MeasureTheory.Integrable (ghostStokesIntegrand b (Real.pi / 2)) := by
      rw [hcrit b (Real.pi / 2) hb]
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
      norm_num
    have hvalPi : ∀ y : ℝ,
        ghostStokesIntegrand b (Real.pi / 2) y = (Real.exp (-b * y ^ 2) : ℂ) := by
      intro y
      unfold ghostStokesIntegrand
      have harg : -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
          ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      have he_pi : Complex.exp (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
        rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
            Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
        push_cast
        ring
      rw [he_pi]
      have hsq_arg : (b : ℂ) * (-Complex.I * (y : ℂ)) ^ 2 = ((-b * y ^ 2 : ℝ) : ℂ) := by
        calc
          (b : ℂ) * (-Complex.I * (y : ℂ)) ^ 2
              = (b : ℂ) * (Complex.I ^ 2 * (y : ℂ) ^ 2) := by ring
          _ = (b : ℂ) * ((-1 : ℂ) * (y : ℂ) ^ 2) := by rw [Complex.I_sq]
          _ = ((-b * y ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsq_arg, Complex.ofReal_exp]
    have hintG : ∫ y : ℝ, Real.exp (-b * y ^ 2) = Real.sqrt (Real.pi / b) := integral_gaussian b
    have hposG : 0 < ∫ y : ℝ, Real.exp (-b * y ^ 2) := by
      rw [hintG]
      exact Real.sqrt_pos.mpr (div_pos Real.pi_pos hb)
    exact ⟨hdiv_real, hdiv0, hconvPi, hvalPi, hintG, hposG⟩
  · intro L V I hEuler
    refine ⟨?_, ?_⟩
    · unfold weylSuperficialDegree
      linarith [hEuler]
    · unfold einsteinSuperficialDegree
      linarith [hEuler]
  · intro Λ m₁ m₂ hΛ
    have hintMajor : MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (-5 : ℝ)) (Set.Ioi Λ) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1) hΛ
    have hcont : ContinuousOn (weylBubbleUVIntegrand m₁ m₂) (Set.Ioi Λ) := by
      intro k hk
      unfold weylBubbleUVIntegrand
      have hkpos : 0 < k := lt_trans hΛ (Set.mem_Ioi.mp hk)
      have hden_ne : (k ^ 2 + m₁ ^ 2) ^ 2 * (k ^ 2 + m₂ ^ 2) ^ 2 ≠ 0 := by
        have h1 : 0 < k ^ 2 + m₁ ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hkpos) (sq_nonneg m₁)
        have h2 : 0 < k ^ 2 + m₂ ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hkpos) (sq_nonneg m₂)
        exact mul_ne_zero (pow_ne_zero 2 h1.ne') (pow_ne_zero 2 h2.ne')
      exact ((continuousAt_id.pow 3).div
        (((continuousAt_id.pow 2).add continuousAt_const).pow 2 |>.mul
          (((continuousAt_id.pow 2).add continuousAt_const).pow 2)) hden_ne).continuousWithinAt
    have hintWeyl : MeasureTheory.IntegrableOn (weylBubbleUVIntegrand m₁ m₂) (Set.Ioi Λ) := by
      refine hintMajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with k hk
      have hkpos : 0 < k := lt_trans hΛ (Set.mem_Ioi.mp hk)
      have hk_sq_pos : 0 < k ^ 2 := sq_pos_of_pos hkpos
      have h1_le : k ^ 2 ≤ k ^ 2 + m₁ ^ 2 := le_add_of_nonneg_right (sq_nonneg m₁)
      have h2_le : k ^ 2 ≤ k ^ 2 + m₂ ^ 2 := le_add_of_nonneg_right (sq_nonneg m₂)
      have h1_sq : (k ^ 2) ^ 2 ≤ (k ^ 2 + m₁ ^ 2) ^ 2 :=
        sq_le_sq' (by linarith [hk_sq_pos, h1_le]) h1_le
      have h2_sq : (k ^ 2) ^ 2 ≤ (k ^ 2 + m₂ ^ 2) ^ 2 :=
        sq_le_sq' (by linarith [hk_sq_pos, h2_le]) h2_le
      have hden_ge : k ^ 8 ≤ (k ^ 2 + m₁ ^ 2) ^ 2 * (k ^ 2 + m₂ ^ 2) ^ 2 := by
        calc
          k ^ 8 = (k ^ 2) ^ 2 * (k ^ 2) ^ 2 := by ring
          _ ≤ (k ^ 2 + m₁ ^ 2) ^ 2 * (k ^ 2 + m₂ ^ 2) ^ 2 :=
            mul_le_mul h1_sq h2_sq (sq_nonneg _) (sq_nonneg _)
      have hnonneg : 0 ≤ weylBubbleUVIntegrand m₁ m₂ k := by
        unfold weylBubbleUVIntegrand
        exact div_nonneg (pow_nonneg hkpos.le 3) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hdiv_le : weylBubbleUVIntegrand m₁ m₂ k ≤ k ^ 3 / k ^ 8 := by
        unfold weylBubbleUVIntegrand
        exact div_le_div_of_nonneg_left (pow_nonneg hkpos.le 3) (pow_pos hkpos 8) hden_ge
      have hrpow : k ^ 3 / k ^ 8 = k ^ (-5 : ℝ) := by
        rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hkpos.le,
            Real.rpow_natCast]
        field_simp [hkpos.ne']
      rw [Real.norm_of_nonneg hnonneg, ← hrpow]
      exact hdiv_le
    have hdiv1 : ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (1 : ℝ)) (Set.Ioi Λ) := by
      rw [integrableOn_Ioi_rpow_iff hΛ]
      norm_num
    have hdiv3 : ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (3 : ℝ)) (Set.Ioi Λ) := by
      rw [integrableOn_Ioi_rpow_iff hΛ]
      norm_num
    exact ⟨hintWeyl, hdiv1, hdiv3⟩

/-- Inductive constructive representation of connected 4D Feynman graphs built by attaching
tree edges `(ΔV = 1, ΔI = 1, ΔL = 0)` or closing loop chords `(ΔV = 0, ΔI = 1, ΔL = 1)`
from a base single-vertex graph `(V = 1, I = 0, L = 0)`. -/
inductive ConnectedFeynmanGraph : Type
  | singleVertex
  | addTreeEdge (G : ConnectedFeynmanGraph)
  | addLoopChord (G : ConnectedFeynmanGraph)
  deriving DecidableEq, Repr

/-- Number of vertices `V` of a connected Feynman graph. -/
def fgVertices : ConnectedFeynmanGraph → ℤ
  | .singleVertex => 1
  | .addTreeEdge G => fgVertices G + 1
  | .addLoopChord G => fgVertices G

/-- Number of internal propagators `I` of a connected Feynman graph. -/
def fgEdges : ConnectedFeynmanGraph → ℤ
  | .singleVertex => 0
  | .addTreeEdge G => fgEdges G + 1
  | .addLoopChord G => fgEdges G + 1

/-- Loop number `L` of a connected Feynman graph. -/
def fgLoops : ConnectedFeynmanGraph → ℤ
  | .singleVertex => 0
  | .addTreeEdge G => fgLoops G
  | .addLoopChord G => fgLoops G + 1

/-- **Constructive Connected-Graph Euler Law & All-Loop 4D Weyl Power-Counting (`MA₉`)**:
Every `G : ConnectedFeynmanGraph` unconditionally proves `L - 1 = I - V`, forcing
`weylSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 4` (independent of loop count `L`)
and `einsteinSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 2 * fgLoops G + 2`,
discharging the Euler loop premise `hEuler`. -/
theorem connectedFeynmanGraph_euler_and_weyl_degree (G : ConnectedFeynmanGraph) :
    fgLoops G - 1 = fgEdges G - fgVertices G ∧
    weylSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 4 ∧
    einsteinSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 2 * fgLoops G + 2 := by
  have hEuler : fgLoops G - 1 = fgEdges G - fgVertices G := by
    induction G with
    | singleVertex => simp [fgLoops, fgEdges, fgVertices]
    | addTreeEdge G ih =>
      simp only [fgLoops, fgEdges, fgVertices]
      omega
    | addLoopChord G ih =>
      simp only [fgLoops, fgEdges, fgVertices]
      omega
  have hw := pt_stokes_wedge_gaussian_and_weyl_uv_convergence.2.2.2.1
    (fgLoops G) (fgVertices G) (fgEdges G) hEuler
  exact ⟨hEuler, hw.1, hw.2⟩

end MA9_PTStokesWedgeAndWeylUV

/-! ## Archetype `MA₁₀`: Mannheim–Kazanas Geodesic Galactic Rotation Curves & Tully–Fisher Law -/

section MA10_MannheimKazanasRotationCurve

/-- Circular geodesic orbital velocity squared `v²(r) = (c² r / 2) B'(r)` induced by
the Mannheim–Kazanas conformal metric potential `B(r)`. -/
def mkCircularVelocitySq (c Bstar Gtot κ r : ℝ) : ℝ :=
  Bstar * c ^ 2 / r + (Gtot * c ^ 2 / 2) * r - κ * c ^ 2 * r ^ 2

/-- Newtonian-to-conformal linear transition radius `r_trans = √(2 B⋆ / Γ_tot)`. -/
def mkTransitionRadius (Bstar Gtot : ℝ) : ℝ :=
  Real.sqrt (2 * Bstar / Gtot)

/-- **Mannheim–Kazanas Galactic Rotation Curve, Transition Radius & Baryonic Tully–Fisher (`MA₁₀`)**:
1. Differentiating `mannheimKazanasPotential 1 (N⋆ β⋆) (N⋆ γ⋆ + γ₀) κ r` via
   `mannheimKazanas_deriv1_eq` reproduces `(c² r / 2) B'(r) = mkCircularVelocitySq`;
2. Without non-baryonic dark matter (`B⋆` baryonic only), the linear conformal potential term
   strictly boosts `v²(r)` above the Keplerian prediction `B⋆ c² / r` throughout `r < Γ_tot / (2 κ)`
   (or all `r > 0` when `κ = 0`);
3. At `κ = 0`, square completion gives `v²(r) - c² √(2 B⋆ Γ_tot) = c² (√(B⋆/r) - √(Γ_tot r / 2))² ≥ 0`,
   with equality iff `r = mkTransitionRadius B⋆ Γ_tot` and exact fourth-power Baryonic Tully–Fisher
   flat-velocity law `(v²(r_trans))² = 2 c⁴ B⋆ Γ_tot`;
4. Outer quadratic de Sitter turnover occurs at `r = Γ_tot / (4 κ)`. -/
theorem mannheim_kazanas_galactic_rotation_geodesic_and_tully_fisher :
    (∀ c Nstar βstar γstar γ₀ κ r : ℝ, r ≠ 0 →
      (c ^ 2 * r / 2) * deriv (mannheimKazanasPotential 1 (Nstar * βstar) (Nstar * γstar + γ₀) κ) r =
        mkCircularVelocitySq c (Nstar * βstar) (Nstar * γstar + γ₀) κ r) ∧
    (∀ c Bstar Gtot κ r : ℝ, 0 < c → 0 < r → 0 < Gtot → 0 ≤ κ →
      (κ = 0 ∨ r < Gtot / (2 * κ)) →
      Bstar * c ^ 2 / r < mkCircularVelocitySq c Bstar Gtot κ r) ∧
    (∀ c Bstar Gtot r : ℝ, 0 < c → 0 < Bstar → 0 < Gtot → 0 < r →
      mkCircularVelocitySq c Bstar Gtot 0 r - c ^ 2 * Real.sqrt (2 * Bstar * Gtot) =
        c ^ 2 * (Real.sqrt (Bstar / r) - Real.sqrt (Gtot * r / 2)) ^ 2 ∧
      c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ≤ mkCircularVelocitySq c Bstar Gtot 0 r ∧
      (mkCircularVelocitySq c Bstar Gtot 0 r = c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ↔
        r = mkTransitionRadius Bstar Gtot) ∧
      (mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot)) ^ 2 =
        2 * c ^ 4 * Bstar * Gtot) ∧
    (∀ c Gtot κ r : ℝ, 0 < c → 0 < Gtot → 0 < κ →
      HasDerivAt (fun x : ℝ => (Gtot * c ^ 2 / 2) * x - κ * c ^ 2 * x ^ 2)
        (Gtot * c ^ 2 / 2 - 2 * κ * c ^ 2 * r) r ∧
      (deriv (fun x : ℝ => (Gtot * c ^ 2 / 2) * x - κ * c ^ 2 * x ^ 2) r = 0 ↔
        r = Gtot / (4 * κ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c Nstar βstar γstar γ₀ κ r hr
    rw [mannheimKazanas_deriv1_eq 1 (Nstar * βstar) (Nstar * γstar + γ₀) κ hr]
    unfold mannheimKazanasDeriv1 mkCircularVelocitySq
    field_simp [hr]
  · intro c Bstar Gtot κ r hc hr hG hκ hcase
    unfold mkCircularVelocitySq
    rcases hcase with rfl | hlt
    · have hboost : 0 < (Gtot * c ^ 2 / 2) * r :=
        mul_pos (div_pos (mul_pos hG (sq_pos_of_pos hc)) zero_lt_two) hr
      linarith [hκ, hboost]
    · have hgap : 0 < Gtot / 2 - κ * r := by
        rcases eq_or_lt_of_le hκ with rfl | hκ_pos
        · rw [zero_mul, sub_zero]
          exact div_pos hG zero_lt_two
        · have hmul : r * (2 * κ) < Gtot := (lt_div_iff₀ (mul_pos zero_lt_two hκ_pos)).mp hlt
          linarith
      have hboost : 0 < (Gtot / 2 - κ * r) * c ^ 2 * r :=
        mul_pos (mul_pos hgap (sq_pos_of_pos hc)) hr
      linarith [hboost]
  · intro c Bstar Gtot r hc hB hG hr
    have hsq1 : Real.sqrt (Bstar / r) ^ 2 = Bstar / r :=
      Real.sq_sqrt (div_pos hB hr).le
    have hsq2 : Real.sqrt (Gtot * r / 2) ^ 2 = Gtot * r / 2 :=
      Real.sq_sqrt (div_pos (mul_pos hG hr) zero_lt_two).le
    have hcross : 2 * Real.sqrt (Bstar / r) * Real.sqrt (Gtot * r / 2) =
        Real.sqrt (2 * Bstar * Gtot) := by
      have hmul_rt : Real.sqrt (Bstar / r) * Real.sqrt (Gtot * r / 2) =
          Real.sqrt (2 * Bstar * Gtot) / 2 := by
        rw [← Real.sqrt_mul (div_pos hB hr).le]
        have harg : (Bstar / r) * (Gtot * r / 2) = (2 * Bstar * Gtot) / 4 := by
          field_simp [hr.ne']
          ring
        rw [harg, Real.sqrt_div (mul_pos (mul_pos zero_lt_two hB) hG).le,
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_lt_two.le]
      linarith
    have hcomp : mkCircularVelocitySq c Bstar Gtot 0 r - c ^ 2 * Real.sqrt (2 * Bstar * Gtot) =
        c ^ 2 * (Real.sqrt (Bstar / r) - Real.sqrt (Gtot * r / 2)) ^ 2 := by
      unfold mkCircularVelocitySq
      calc
        Bstar * c ^ 2 / r + (Gtot * c ^ 2 / 2) * r - 0 * c ^ 2 * r ^ 2 -
            c ^ 2 * Real.sqrt (2 * Bstar * Gtot)
            = c ^ 2 * (Bstar / r + Gtot * r / 2 - Real.sqrt (2 * Bstar * Gtot)) := by ring
        _ = c ^ 2 * (Real.sqrt (Bstar / r) ^ 2 -
              2 * Real.sqrt (Bstar / r) * Real.sqrt (Gtot * r / 2) +
              Real.sqrt (Gtot * r / 2) ^ 2) := by rw [hsq1, hsq2, hcross]; ring
        _ = c ^ 2 * (Real.sqrt (Bstar / r) - Real.sqrt (Gtot * r / 2)) ^ 2 := by ring
    have hge : c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ≤ mkCircularVelocitySq c Bstar Gtot 0 r := by
      have hsq_nonneg : 0 ≤ c ^ 2 * (Real.sqrt (Bstar / r) - Real.sqrt (Gtot * r / 2)) ^ 2 :=
        mul_nonneg (sq_nonneg c) (sq_nonneg _)
      linarith [hcomp, hsq_nonneg]
    have hiff : mkCircularVelocitySq c Bstar Gtot 0 r = c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ↔
        r = mkTransitionRadius Bstar Gtot := by
      rw [← sub_eq_zero, hcomp, mul_eq_zero]
      have hc2 : c ^ 2 ≠ 0 := (sq_pos_of_pos hc).ne'
      rw [or_iff_right hc2, sq_eq_zero_iff, sub_eq_zero]
      constructor
      · intro heq
        have hsq_eq : (Real.sqrt (Bstar / r)) ^ 2 = (Real.sqrt (Gtot * r / 2)) ^ 2 := by
          rw [heq]
        rw [hsq1, hsq2] at hsq_eq
        have hr2 : r ^ 2 = 2 * Bstar / Gtot := by
          have hcross_eq : 2 * Bstar = r ^ 2 * Gtot := by
            have := congrArg (· * (2 * r)) hsq_eq
            field_simp [hr.ne'] at this
            linarith
          exact eq_div_of_mul_eq hG.ne' (by linarith [hcross_eq])
        unfold mkTransitionRadius
        rw [← hr2, Real.sqrt_sq hr.le]
      · intro hr_trans
        have hr2 : r ^ 2 = 2 * Bstar / Gtot := by
          rw [hr_trans]
          unfold mkTransitionRadius
          exact Real.sq_sqrt (div_pos (mul_pos zero_lt_two hB) hG).le
        have harg : Bstar / r = Gtot * r / 2 := by
          field_simp [hr.ne']
          have hmul : 2 * Bstar = r ^ 2 * Gtot := (div_eq_iff hG.ne').mp hr2.symm
          linarith
        rw [harg]
    have hrt_pos : 0 < mkTransitionRadius Bstar Gtot := by
      unfold mkTransitionRadius
      exact Real.sqrt_pos.mpr (div_pos (mul_pos zero_lt_two hB) hG)
    have hval_trans :
        mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot) =
          c ^ 2 * Real.sqrt (2 * Bstar * Gtot) := by
      have hiff_t := hcomp_t_eval c Bstar Gtot hc hB hG hrt_pos
      exact hiff_t
    have htf :
        (mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot)) ^ 2 =
          2 * c ^ 4 * Bstar * Gtot := by
      rw [hval_trans, mul_pow, Real.sq_sqrt (mul_pos (mul_pos zero_lt_two hB) hG).le]
      ring
    exact ⟨hcomp, hge, hiff, htf⟩
  · intro c Gtot κ r hc hG hκ
    have h1 : HasDerivAt (fun x : ℝ => (Gtot * c ^ 2 / 2) * x) (Gtot * c ^ 2 / 2) r := by
      simpa using (hasDerivAt_id r).const_mul (Gtot * c ^ 2 / 2)
    have h2 : HasDerivAt (fun x : ℝ => κ * c ^ 2 * x ^ 2) (κ * c ^ 2 * (2 * r)) r := by
      convert (hasDerivAt_pow 2 r).const_mul (κ * c ^ 2) using 1
      norm_num
    have hder : HasDerivAt (fun x : ℝ => (Gtot * c ^ 2 / 2) * x - κ * c ^ 2 * x ^ 2)
        (Gtot * c ^ 2 / 2 - 2 * κ * c ^ 2 * r) r := by
      refine (h1.sub h2).congr_deriv ?_
      ring
    refine ⟨hder, ?_⟩
    rw [hder.deriv]
    constructor
    · intro hz
      have hcr : 2 * κ * c ^ 2 * r = Gtot * c ^ 2 / 2 := (sub_eq_zero.mp hz).symm
      have hc2 : c ^ 2 ≠ 0 := (sq_pos_of_pos hc).ne'
      have h4kr : 4 * κ * r = Gtot := by
        have hdiv := congrArg (· / c ^ 2) hcr
        field_simp [hc2] at hdiv
        linarith
      exact eq_div_of_mul_eq (mul_ne_zero (by norm_num) hκ.ne') (by linarith [h4kr])
    · intro hturn
      rw [hturn]
      field_simp [hG.ne', hκ.ne']
      ring
where
  hcomp_t_eval (c Bstar Gtot : ℝ) (hc : 0 < c) (hB : 0 < Bstar) (hG : 0 < Gtot)
      (hrt_pos : 0 < mkTransitionRadius Bstar Gtot) :
      mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot) =
        c ^ 2 * Real.sqrt (2 * Bstar * Gtot) := by
    have hrt_sq : (mkTransitionRadius Bstar Gtot) ^ 2 = 2 * Bstar / Gtot := by
      unfold mkTransitionRadius
      exact Real.sq_sqrt (div_pos (mul_pos zero_lt_two hB) hG).le
    have hrt_val : mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot) =
        c ^ 2 * (Gtot * mkTransitionRadius Bstar Gtot) := by
      unfold mkCircularVelocitySq
      have hinv : Bstar / mkTransitionRadius Bstar Gtot =
          Gtot * mkTransitionRadius Bstar Gtot / 2 := by
        field_simp [hrt_pos.ne']
        have hm : 2 * Bstar = (mkTransitionRadius Bstar Gtot) ^ 2 * Gtot :=
          (div_eq_iff hG.ne').mp hrt_sq.symm
        linarith
      calc
        Bstar * c ^ 2 / mkTransitionRadius Bstar Gtot +
            (Gtot * c ^ 2 / 2) * mkTransitionRadius Bstar Gtot -
            0 * c ^ 2 * (mkTransitionRadius Bstar Gtot) ^ 2
            = c ^ 2 * (Bstar / mkTransitionRadius Bstar Gtot +
                Gtot * mkTransitionRadius Bstar Gtot / 2) := by ring
        _ = c ^ 2 * (Gtot * mkTransitionRadius Bstar Gtot) := by rw [hinv]; ring
    rw [hrt_val]
    congr 1
    unfold mkTransitionRadius
    calc
      Gtot * Real.sqrt (2 * Bstar / Gtot)
          = Real.sqrt (Gtot ^ 2) * Real.sqrt (2 * Bstar / Gtot) := by
            conv_lhs => arg 1; rw [← Real.sqrt_sq hG.le]
      _ = Real.sqrt (Gtot ^ 2 * (2 * Bstar / Gtot)) :=
            (Real.sqrt_mul (sq_nonneg Gtot) (2 * Bstar / Gtot)).symm
      _ = Real.sqrt (2 * Bstar * Gtot) := by
            congr 1
            field_simp [hG.ne']

end MA10_MannheimKazanasRotationCurve

/-! ## Archetype `MA₁₁`: NJL Collective Goldstone & Dynamical Bound-State Higgs Pole -/

section MA11_DynamicalBoundStateHiggs

/-- NJL pseudoscalar Goldstone 1-loop polarization scalar `I_gap - (q² / 2) J(q²)`. -/
def njlPseudoscalarPolarization (Igap Jq qSq : ℝ) : ℝ :=
  Igap - (qSq / 2) * Jq

/-- NJL scalar Higgs 1-loop polarization scalar `I_gap - ((q² - 4 m_dyn²) / 2) J(q²)`. -/
def njlScalarPolarization (Igap Jq mDyn qSq : ℝ) : ℝ :=
  Igap - ((qSq - 4 * mDyn ^ 2) / 2) * Jq

/-- Inverse pseudoscalar Bethe–Salpeter propagator `1 - g Π_P(q²)`. -/
def njlInvPropagatorP (g Igap Jq qSq : ℝ) : ℝ :=
  1 - g * njlPseudoscalarPolarization Igap Jq qSq

/-- Inverse scalar Higgs Bethe–Salpeter propagator `1 - g Π_S(q²)`. -/
def njlInvPropagatorS (g Igap Jq mDyn qSq : ℝ) : ℝ :=
  1 - g * njlScalarPolarization Igap Jq mDyn qSq

/-- Anomalous-dimension `γ_θ = -1` bound-state shifted scalar inverse propagator
`1 - g (I_gap - ((q² - 4 m_dyn² + ΔA) / 2) J)`. -/
def njlDressedInvPropagatorS (g Igap Jq mDyn ΔA qSq : ℝ) : ℝ :=
  1 - g * (Igap - ((qSq - 4 * mDyn ^ 2 + ΔA) / 2) * Jq)

/-- **NJL Collective Goldstone Zero-Mode & Dynamical Bound-State Higgs Pole (`MA₁₁`)**:
Whenever `0 < g`, `0 < Jq`, `0 < mDyn`, and the nontrivial fermion gap equation `g * I_gap = 1` holds:
1. `njlInvPropagatorP g Igap Jq qSq = (g * Jq / 2) * qSq`, vanishing **iff** `qSq = 0`
   (massless Nambu–Goldstone boson mode);
2. `njlInvPropagatorS g Igap Jq mDyn qSq = (g * Jq / 2) * (qSq - 4 * mDyn ^ 2)`, vanishing
   **iff** `qSq = (2 * mDyn) ^ 2` (`M_H = 2 m_dyn` collective scalar Higgs bound state) with
   strictly positive ghost-free `HasDerivAt` slope `g * Jq / 2 > 0`;
3. Under an attractive conformal/QED tensor binding shift `0 < ΔA < 4 * mDyn ^ 2`, the dressed
   bound-state Higgs pole sits strictly in `(0, (2 * mDyn) ^ 2)`. -/
theorem dynamical_electroweak_goldstone_and_boundstate_higgs_poles
    {g Igap Jq mDyn : ℝ} (hg : 0 < g) (hJ : 0 < Jq) (hm : 0 < mDyn) (hgap : g * Igap = 1) :
    (∀ qSq : ℝ, njlInvPropagatorP g Igap Jq qSq = (g * Jq / 2) * qSq ∧
      (njlInvPropagatorP g Igap Jq qSq = 0 ↔ qSq = 0)) ∧
    (∀ qSq : ℝ, njlInvPropagatorS g Igap Jq mDyn qSq = (g * Jq / 2) * (qSq - 4 * mDyn ^ 2) ∧
      (njlInvPropagatorS g Igap Jq mDyn qSq = 0 ↔ qSq = (2 * mDyn) ^ 2)) ∧
    HasDerivAt (njlInvPropagatorS g Igap Jq mDyn) (g * Jq / 2) ((2 * mDyn) ^ 2) ∧
    0 < g * Jq / 2 ∧
    0 < (2 * mDyn) ^ 2 ∧
    (∀ ΔA : ℝ, 0 < ΔA → ΔA < 4 * mDyn ^ 2 →
      ∀ qSq : ℝ, (njlDressedInvPropagatorS g Igap Jq mDyn ΔA qSq = 0 ↔ qSq = 4 * mDyn ^ 2 - ΔA) ∧
        0 < 4 * mDyn ^ 2 - ΔA ∧ 4 * mDyn ^ 2 - ΔA < (2 * mDyn) ^ 2) := by
  have hslope_pos : 0 < g * Jq / 2 := div_pos (mul_pos hg hJ) zero_lt_two
  have hm2_pos : 0 < (2 * mDyn) ^ 2 := sq_pos_of_pos (mul_pos zero_lt_two hm)
  have hP : ∀ qSq : ℝ, njlInvPropagatorP g Igap Jq qSq = (g * Jq / 2) * qSq ∧
      (njlInvPropagatorP g Igap Jq qSq = 0 ↔ qSq = 0) := by
    intro qSq
    have hfac : njlInvPropagatorP g Igap Jq qSq = (g * Jq / 2) * qSq := by
      unfold njlInvPropagatorP njlPseudoscalarPolarization
      linear_combination -hgap
    refine ⟨hfac, ?_⟩
    rw [hfac, mul_eq_zero]
    exact or_iff_right hslope_pos.ne'
  have hS : ∀ qSq : ℝ,
      njlInvPropagatorS g Igap Jq mDyn qSq = (g * Jq / 2) * (qSq - 4 * mDyn ^ 2) ∧
      (njlInvPropagatorS g Igap Jq mDyn qSq = 0 ↔ qSq = (2 * mDyn) ^ 2) := by
    intro qSq
    have hfac : njlInvPropagatorS g Igap Jq mDyn qSq = (g * Jq / 2) * (qSq - 4 * mDyn ^ 2) := by
      unfold njlInvPropagatorS njlScalarPolarization
      linear_combination -hgap
    refine ⟨hfac, ?_⟩
    rw [hfac, mul_eq_zero, or_iff_right hslope_pos.ne', sub_eq_zero]
    constructor <;> intro hq <;> linarith [hq]
  have hder : HasDerivAt (njlInvPropagatorS g Igap Jq mDyn) (g * Jq / 2) ((2 * mDyn) ^ 2) := by
    have hlin :=
      ((hasDerivAt_id ((2 * mDyn) ^ 2)).sub_const (4 * mDyn ^ 2)).const_mul (g * Jq / 2)
    have hlin' : HasDerivAt (fun x : ℝ => (g * Jq / 2) * (x - 4 * mDyn ^ 2))
        (g * Jq / 2) ((2 * mDyn) ^ 2) := by
      refine hlin.congr_deriv ?_
      ring
    refine hlin'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (hS x).1)
  refine ⟨hP, hS, hder, hslope_pos, hm2_pos, ?_⟩
  intro ΔA hΔ0 hΔlt qSq
  have hfacD : njlDressedInvPropagatorS g Igap Jq mDyn ΔA qSq =
      (g * Jq / 2) * (qSq - (4 * mDyn ^ 2 - ΔA)) := by
    unfold njlDressedInvPropagatorS
    linear_combination -hgap
  have hiffD : njlDressedInvPropagatorS g Igap Jq mDyn ΔA qSq = 0 ↔ qSq = 4 * mDyn ^ 2 - ΔA := by
    rw [hfacD, mul_eq_zero, or_iff_right hslope_pos.ne', sub_eq_zero]
  exact ⟨hiffD, by linarith [hΔlt], by linarith [hΔ0]⟩

/-- Cutoff-regularized 4D Euclidean 1-loop NJL fermion gap integral `∫₀^{Λ²} u / (u + m²) du`. -/
def njlGapIntegral (Λ m : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Λ ^ 2, u / (u + m ^ 2)

/-- Cutoff-regularized 4D Euclidean 1-loop NJL scalar/pseudoscalar form-factor integral
`∫₀^{Λ²} u / (u + Δ)² du`. -/
def njlFormFactorIntegral (Λ Δ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Λ ^ 2, u / (u + Δ) ^ 2

/-- Closed-form evaluation & strict positivity of the 1-loop NJL form-factor integral
`∫₀^{Λ²} u / (u + Δ)² du = log((Λ² + Δ) / Δ) - Λ² / (Λ² + Δ) > 0` for `0 < Λ`, `0 < Δ`. -/
theorem njlFormFactorIntegral_eval_and_pos
    {Λ Δ : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ) :
    njlFormFactorIntegral Λ Δ = Real.log ((Λ ^ 2 + Δ) / Δ) - Λ ^ 2 / (Λ ^ 2 + Δ) ∧
    0 < njlFormFactorIntegral Λ Δ := by
  have hΛ2 : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have hIcc : Set.uIcc (0 : ℝ) (Λ ^ 2) = Set.Icc 0 (Λ ^ 2) := Set.uIcc_of_le (sq_nonneg Λ)
  let F : ℝ → ℝ := fun u => Real.log (u + Δ) + Δ / (u + Δ)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (Λ ^ 2),
      HasDerivAt F (u / (u + Δ) ^ 2) u := by
    intro u hu
    rw [hIcc] at hu
    have hpos : 0 < u + Δ := by linarith [hu.1, hΔ]
    have hadd : HasDerivAt (fun y : ℝ => y + Δ) 1 u := (hasDerivAt_id u).add_const Δ
    have hlog := hadd.log hpos.ne'
    have hinv : HasDerivAt (fun y : ℝ => Δ / (y + Δ)) (Δ * (-1 / (u + Δ) ^ 2)) u := by
      have hi := hadd.inv hpos.ne'
      have hc := hi.const_mul Δ
      refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
        simp [div_eq_mul_inv])
    have htot : HasDerivAt F (1 / (u + Δ) + Δ * (-1 / (u + Δ) ^ 2)) u :=
      (hlog.add hinv).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    refine htot.congr_deriv ?_
    field_simp [hpos.ne']
    ring
  have hcont : ContinuousOn (fun u : ℝ => u / (u + Δ) ^ 2) (Set.uIcc 0 (Λ ^ 2)) := by
    intro u hu
    rw [hIcc] at hu
    have hpos : 0 < u + Δ := by linarith [hu.1, hΔ]
    exact (continuousAt_id.div ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hpos.ne')).continuousWithinAt
  have heval : njlFormFactorIntegral Λ Δ =
      Real.log ((Λ ^ 2 + Δ) / Δ) - Λ ^ 2 / (Λ ^ 2 + Δ) := by
    unfold njlFormFactorIntegral
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have hden_pos : 0 < Λ ^ 2 + Δ := by linarith
    have hlog_div : Real.log ((Λ ^ 2 + Δ) / Δ) = Real.log (Λ ^ 2 + Δ) - Real.log Δ :=
      Real.log_div hden_pos.ne' hΔ.ne'
    have h0 : F 0 = Real.log Δ + 1 := by
      simp only [F, zero_add]
      rw [div_self hΔ.ne']
    dsimp only [F] at h0 ⊢
    rw [zero_add, div_self hΔ.ne', hlog_div]
    field_simp [hden_pos.ne']
    ring
  have hpos : 0 < njlFormFactorIntegral Λ Δ := by
    rw [heval]
    have hden_pos : 0 < Λ ^ 2 + Δ := by linarith
    have hlt1 : Δ / (Λ ^ 2 + Δ) < 1 := (div_lt_one hden_pos).mpr (by linarith)
    have hr_pos : 0 < Δ / (Λ ^ 2 + Δ) := div_pos hΔ hden_pos
    have hlog_lt := Real.log_lt_sub_one_of_pos hr_pos hlt1.ne
    have hinv_log : Real.log ((Λ ^ 2 + Δ) / Δ) = -Real.log (Δ / (Λ ^ 2 + Δ)) := by
      rw [← inv_div Δ (Λ ^ 2 + Δ), Real.log_inv]
    have hfrac : 1 - Δ / (Λ ^ 2 + Δ) = Λ ^ 2 / (Λ ^ 2 + Δ) := by
      field_simp [hden_pos.ne']
      ring
    linarith [hlog_lt, hinv_log, hfrac]
  exact ⟨heval, hpos⟩

/-- Closed-form evaluation, positivity/cutoff bounds, continuity, and strict antitonicity of the
1-loop NJL gap integral `njlGapIntegral Λ m` on `(0, ∞)`. -/
theorem njlGapIntegral_eval_and_strictAnti {Λ : ℝ} (hΛ : 0 < Λ) :
    (∀ m : ℝ, 0 < m →
      njlGapIntegral Λ m = Λ ^ 2 - m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) ∧
      0 < njlGapIntegral Λ m ∧
      njlGapIntegral Λ m < Λ ^ 2 ∧
      njlGapIntegral Λ m ≤ Λ ^ 4 / (Λ ^ 2 + m ^ 2) ∧
      njlGapIntegral Λ m ≤ Λ ^ 4 / m ^ 2) ∧
    ContinuousOn (njlGapIntegral Λ) (Set.Ioi 0) ∧
    StrictAntiOn (njlGapIntegral Λ) (Set.Ioi 0) := by
  have hΛ2 : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have heval_pos : ∀ m : ℝ, 0 < m →
      njlGapIntegral Λ m = Λ ^ 2 - m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) ∧
      0 < njlGapIntegral Λ m ∧
      njlGapIntegral Λ m < Λ ^ 2 ∧
      njlGapIntegral Λ m ≤ Λ ^ 4 / (Λ ^ 2 + m ^ 2) ∧
      njlGapIntegral Λ m ≤ Λ ^ 4 / m ^ 2 := by
    intro m hm
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hden : 0 < Λ ^ 2 + m ^ 2 := by linarith
    have hIcc : Set.uIcc (0 : ℝ) (Λ ^ 2) = Set.Icc 0 (Λ ^ 2) := Set.uIcc_of_le (sq_nonneg Λ)
    let F : ℝ → ℝ := fun u => u - m ^ 2 * Real.log (u + m ^ 2)
    have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (Λ ^ 2), HasDerivAt F (u / (u + m ^ 2)) u := by
      intro u hu
      rw [hIcc] at hu
      have hpos : 0 < u + m ^ 2 := by linarith [hu.1, hm2]
      have hadd : HasDerivAt (fun y : ℝ => y + m ^ 2) 1 u := (hasDerivAt_id u).add_const (m ^ 2)
      have hlog := (hadd.log hpos.ne').const_mul (m ^ 2)
      have htot := ((hasDerivAt_id u).sub hlog).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
      refine htot.congr_deriv ?_
      field_simp [hpos.ne']
      ring
    have hcont : ContinuousOn (fun u : ℝ => u / (u + m ^ 2)) (Set.uIcc 0 (Λ ^ 2)) := by
      intro u hu
      rw [hIcc] at hu
      have hpos : 0 < u + m ^ 2 := by linarith [hu.1, hm2]
      exact (continuousAt_id.div (continuousAt_id.add continuousAt_const) hpos.ne').continuousWithinAt
    have hev : njlGapIntegral Λ m = Λ ^ 2 - m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) := by
      unfold njlGapIntegral
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
      have hlog_div : Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) =
          Real.log (Λ ^ 2 + m ^ 2) - Real.log (m ^ 2) :=
        Real.log_div hden.ne' hm2.ne'
      dsimp only [F]
      rw [zero_add, hlog_div]
      ring
    have hratio_gt1 : 1 < (Λ ^ 2 + m ^ 2) / m ^ 2 := (one_lt_div hm2).mpr (by linarith)
    have hlog_pos : 0 < Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) := Real.log_pos hratio_gt1
    have hlog_lt : Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) < (Λ ^ 2 + m ^ 2) / m ^ 2 - 1 :=
      Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hratio_gt1) hratio_gt1.ne'
    have hpos : 0 < njlGapIntegral Λ m := by
      rw [hev]
      have hmul : m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) < Λ ^ 2 := by
        calc
          m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2)
              < m ^ 2 * ((Λ ^ 2 + m ^ 2) / m ^ 2 - 1) :=
                mul_lt_mul_of_pos_left hlog_lt hm2
          _ = Λ ^ 2 := by field_simp [hm2.ne']; ring
      linarith
    have hlt_L2 : njlGapIntegral Λ m < Λ ^ 2 := by
      rw [hev]
      have hm_log : 0 < m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) := mul_pos hm2 hlog_pos
      linarith
    have hle_den : njlGapIntegral Λ m ≤ Λ ^ 4 / (Λ ^ 2 + m ^ 2) := by
      rw [hev]
      have hinv_pos : 0 < m ^ 2 / (Λ ^ 2 + m ^ 2) := div_pos hm2 hden
      have hlog_inv := Real.log_le_sub_one_of_pos hinv_pos
      have hinv_eq : Real.log (m ^ 2 / (Λ ^ 2 + m ^ 2)) =
          -Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) := by
        rw [← inv_div (Λ ^ 2 + m ^ 2) (m ^ 2), Real.log_inv]
      have hlog_ge : Λ ^ 2 / (Λ ^ 2 + m ^ 2) ≤ Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) := by
        have h1 : 1 - m ^ 2 / (Λ ^ 2 + m ^ 2) = Λ ^ 2 / (Λ ^ 2 + m ^ 2) := by
          field_simp [hden.ne']; ring
        linarith [hlog_inv, hinv_eq, h1]
      have hmul : m ^ 2 * (Λ ^ 2 / (Λ ^ 2 + m ^ 2)) ≤
          m ^ 2 * Real.log ((Λ ^ 2 + m ^ 2) / m ^ 2) :=
        mul_le_mul_of_nonneg_left hlog_ge hm2.le
      have hdiff : Λ ^ 2 - m ^ 2 * (Λ ^ 2 / (Λ ^ 2 + m ^ 2)) = Λ ^ 4 / (Λ ^ 2 + m ^ 2) := by
        field_simp [hden.ne']; ring
      linarith [hmul, hdiff]
    have hle_m2 : njlGapIntegral Λ m ≤ Λ ^ 4 / m ^ 2 := by
      have hsub : Λ ^ 4 / (Λ ^ 2 + m ^ 2) ≤ Λ ^ 4 / m ^ 2 :=
        div_le_div_of_nonneg_left (pow_nonneg hΛ.le 4) hm2 (by linarith)
      exact le_trans hle_den hsub
    exact ⟨hev, hpos, hlt_L2, hle_den, hle_m2⟩
  have hder_all : ∀ m : ℝ, 0 < m →
      HasDerivAt (njlGapIntegral Λ) (-2 * m * njlFormFactorIntegral Λ (m ^ 2)) m := by
    intro m hm
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hden : 0 < Λ ^ 2 + m ^ 2 := by linarith
    have hev_nhds : njlGapIntegral Λ =ᶠ[nhds m]
        fun x : ℝ => Λ ^ 2 - x ^ 2 * Real.log ((Λ ^ 2 + x ^ 2) / x ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hm] with x hx
      exact (heval_pos x hx).1
    have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * m) m := by
      simpa using (hasDerivAt_pow 2 m).congr_deriv (by ring)
    have hLadd : HasDerivAt (fun x : ℝ => Λ ^ 2 + x ^ 2) (2 * m) m :=
      ((hasDerivAt_pow 2 m).const_add (Λ ^ 2)).congr_deriv (by ring)
    have hquot : HasDerivAt (fun x : ℝ => (Λ ^ 2 + x ^ 2) / x ^ 2)
        ((2 * m * m ^ 2 - (Λ ^ 2 + m ^ 2) * (2 * m)) / (m ^ 2) ^ 2) m :=
      hLadd.div hx2 hm2.ne'
    have hq_pos : 0 < (Λ ^ 2 + m ^ 2) / m ^ 2 := div_pos hden hm2
    have hlog := hquot.log hq_pos.ne'
    have hprod := hx2.mul hlog
    have hsub : HasDerivAt (fun x : ℝ => Λ ^ 2 - x ^ 2 * Real.log ((Λ ^ 2 + x ^ 2) / x ^ 2)) _ m :=
      ((hasDerivAt_const m (Λ ^ 2)).sub hprod).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    have hder : HasDerivAt (njlGapIntegral Λ) _ m := hsub.congr_of_eventuallyEq hev_nhds
    refine hder.congr_deriv ?_
    rw [(njlFormFactorIntegral_eval_and_pos hΛ hm2).1]
    field_simp [hm.ne', hm2.ne', hden.ne']
    ring
  have hcont : ContinuousOn (njlGapIntegral Λ) (Set.Ioi 0) := fun m hm =>
    (hder_all m hm).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn (njlGapIntegral Λ) (Set.Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont
    intro m hm
    rw [isOpen_Ioi.interior_eq] at hm
    have hm_pos : 0 < m := hm
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm_pos
    rw [(hder_all m hm_pos).deriv]
    have hff := (njlFormFactorIntegral_eval_and_pos hΛ hm2).2
    nlinarith [hm_pos, hff]
  exact ⟨heval_pos, hcont, hanti⟩

/-- **Existence & Uniqueness of the Supercritical 1-Loop NJL Mass Gap (`MA₁₁` `hgap` Discharge)**:
For any UV cutoff `0 < Λ` and any supercritical four-fermion coupling `g` (`1 < g * Λ²`), there
exists a **unique** positive dynamical fermion mass `0 < mDyn` solving the 1-loop gap integral
equation `g * njlGapIntegral Λ mDyn = 1` constructively via the Intermediate Value Theorem and
`StrictAntiOn` monotonicity (discharging `hgap : g * Igap = 1` and `0 < mDyn`). -/
theorem njl_supercritical_gap_solution_exists_unique
    {Λ g : ℝ} (hΛ : 0 < Λ) (hsuper : 1 < g * Λ ^ 2) :
    ∃! mDyn : ℝ, 0 < mDyn ∧ g * njlGapIntegral Λ mDyn = 1 := by
  have hΛ2 : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have hg : 0 < g := by nlinarith [hΛ2, hsuper]
  have hgap_pos : 0 < Λ ^ 2 - 1 / g := by
    rw [sub_pos, div_lt_iff₀ hg]
    linarith [hsuper]
  let mLow := min (Λ / 2) ((Λ ^ 2 - 1 / g) / (4 * Λ))
  have hmLow_pos : 0 < mLow :=
    lt_min (div_pos hΛ zero_lt_two) (div_pos hgap_pos (mul_pos (by norm_num) hΛ))
  have hmLow_le_L : mLow ≤ Λ := le_trans (min_le_left _ _) (by linarith)
  have hmLow_le_bnd : 4 * mLow * Λ ≤ Λ ^ 2 - 1 / g := by
    have h1 : mLow ≤ (Λ ^ 2 - 1 / g) / (4 * Λ) := min_le_right _ _
    have h2 : mLow * (4 * Λ) ≤ Λ ^ 2 - 1 / g :=
      (le_div_iff₀ (mul_pos (by norm_num) hΛ)).mp h1
    linarith [h2]
  have hLow_val : 1 / g ≤ njlGapIntegral Λ mLow := by
    have heval := (njlGapIntegral_eval_and_strictAnti hΛ).1 mLow hmLow_pos
    rw [heval.1]
    have hmLow2 : 0 < mLow ^ 2 := sq_pos_of_pos hmLow_pos
    have hz_pos : 0 < Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) :=
      Real.sqrt_pos.mpr (div_pos (add_pos hΛ2 hmLow2) hmLow2)
    have hlog_rt : Real.log (Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2)) ≤
        Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos hz_pos
    have hlog2 : Real.log ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) =
        2 * Real.log (Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2)) := by
      have hsq : Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) ^ 2 = (Λ ^ 2 + mLow ^ 2) / mLow ^ 2 :=
        Real.sq_sqrt (div_pos (add_pos hΛ2 hmLow2) hmLow2).le
      conv_lhs => rw [← hsq, Real.log_pow]
      norm_num
    have hrt_le : Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) ≤ (Λ + mLow) / mLow := by
      rw [Real.sqrt_le_left (div_pos (add_pos hΛ hmLow_pos) hmLow_pos).le, div_pow]
      exact div_le_div_of_nonneg_right (by nlinarith [hΛ, hmLow_pos]) hmLow2.le
    have hlog_bnd : mLow ^ 2 * Real.log ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2) ≤ 4 * mLow * Λ := by
      calc
        mLow ^ 2 * Real.log ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2)
            = mLow ^ 2 * (2 * Real.log (Real.sqrt ((Λ ^ 2 + mLow ^ 2) / mLow ^ 2))) := by
              rw [hlog2]
        _ ≤ mLow ^ 2 * (2 * ((Λ + mLow) / mLow)) := by
              apply mul_le_mul_of_nonneg_left _ hmLow2.le
              linarith [hlog_rt, hrt_le]
        _ = 2 * mLow * Λ + 2 * mLow ^ 2 := by
              field_simp [hmLow_pos.ne']
        _ ≤ 4 * mLow * Λ := by
              nlinarith [hmLow_pos, hmLow_le_L]
    linarith [hmLow_le_bnd, hlog_bnd]
  let mHigh := max (mLow + 1) (Real.sqrt (g * Λ ^ 4))
  have hmLow_lt_high : mLow < mHigh := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hmHigh_pos : 0 < mHigh := lt_trans hmLow_pos hmLow_lt_high
  have hmHigh2_ge : g * Λ ^ 4 ≤ mHigh ^ 2 := by
    have hsq : (Real.sqrt (g * Λ ^ 4)) ^ 2 = g * Λ ^ 4 :=
      Real.sq_sqrt (mul_nonneg hg.le (pow_nonneg hΛ.le 4))
    have hge : Real.sqrt (g * Λ ^ 4) ≤ mHigh := le_max_right _ _
    have hsgn : 0 ≤ Real.sqrt (g * Λ ^ 4) := Real.sqrt_nonneg _
    nlinarith
  have hHigh_val : njlGapIntegral Λ mHigh ≤ 1 / g := by
    have hle := (njlGapIntegral_eval_and_strictAnti hΛ).1 mHigh hmHigh_pos |>.2.2.2.2
    have hmHigh2_pos : 0 < mHigh ^ 2 := sq_pos_of_pos hmHigh_pos
    have h1 : Λ ^ 4 / mHigh ^ 2 ≤ 1 / g := by
      rw [div_le_div_iff₀ hmHigh2_pos hg]
      nlinarith
    exact le_trans hle h1
  have hcont_Icc : ContinuousOn (njlGapIntegral Λ) (Set.Icc mLow mHigh) :=
    (njlGapIntegral_eval_and_strictAnti hΛ).2.1.mono fun x hx =>
      Set.mem_Ioi.mpr (lt_of_lt_of_le hmLow_pos hx.1)
  have hivt := intermediate_value_Icc' hmLow_lt_high.le hcont_Icc
  obtain ⟨mDyn, hm_mem, hm_eq⟩ := hivt ⟨hHigh_val, hLow_val⟩
  have hmDyn_pos : 0 < mDyn := lt_of_lt_of_le hmLow_pos hm_mem.1
  have hmDyn_gap : g * njlGapIntegral Λ mDyn = 1 := by
    rw [hm_eq, mul_div_cancel₀ _ hg.ne']
  refine ⟨mDyn, ⟨hmDyn_pos, hmDyn_gap⟩, ?_⟩
  rintro m' ⟨hm'_pos, hm'_gap⟩
  have hanti := (njlGapIntegral_eval_and_strictAnti hΛ).2.2
  have heq : njlGapIntegral Λ m' = njlGapIntegral Λ mDyn := by
    have hmul : g * njlGapIntegral Λ m' = g * njlGapIntegral Λ mDyn := by
      rw [hm'_gap, hmDyn_gap]
    exact mul_left_cancel₀ hg.ne' hmul
  exact hanti.injOn hm'_pos hmDyn_pos heq

/-- **Passarino–Veltman Integrand Reduction (`MA₁₁`)**:
Unifies the quadratic loop numerators directly into the shifted gap scalar plus explicit `q²`
Goldstone (`+ 4 m²` / `- 4 m²` Higgs) polarization numerators. -/
theorem passarinoVeltman_njl_integrand_identities
    (kSq kDotQ qSq mSq : ℝ)
    (hDp : kSq + kDotQ - qSq / 4 + mSq ≠ 0)
    (hDm : kSq - kDotQ - qSq / 4 + mSq ≠ 0) :
    let Dplus := kSq + kDotQ - qSq / 4 + mSq
    let Dminus := kSq - kDotQ - qSq / 4 + mSq
    (kSq + qSq / 4 + mSq) / (Dplus * Dminus) =
      (1 / 2 : ℝ) * (1 / Dplus + 1 / Dminus) + (qSq / 2) / (Dplus * Dminus) ∧
    (kSq + qSq / 4 - mSq) / (Dplus * Dminus) =
      (1 / 2 : ℝ) * (1 / Dplus + 1 / Dminus) + ((qSq - 4 * mSq) / 2) / (Dplus * Dminus) := by
  intro Dplus Dminus
  have hsum : (1 / 2 : ℝ) * (1 / Dplus + 1 / Dminus) =
      (kSq - qSq / 4 + mSq) / (Dplus * Dminus) := by
    rw [eq_div_iff (mul_ne_zero hDp hDm)]
    calc
      (1 / 2 : ℝ) * (1 / Dplus + 1 / Dminus) * (Dplus * Dminus)
          = (1 / 2 : ℝ) * (Dplus⁻¹ * (Dplus * Dminus) + Dminus⁻¹ * (Dminus * Dplus)) := by
            simp only [one_div]; ring
      _ = (1 / 2 : ℝ) * (Dminus + Dplus) := by
            rw [← mul_assoc Dplus⁻¹, inv_mul_cancel₀ hDp, one_mul,
              ← mul_assoc Dminus⁻¹, inv_mul_cancel₀ hDm, one_mul]
      _ = kSq - qSq / 4 + mSq := by
            dsimp only [Dplus, Dminus]; ring
  constructor
  · rw [hsum, ← add_div]
    congr 1
    ring
  · rw [hsum, ← add_div]
    congr 1
    ring

/-- **Unconditional Supercritical NJL Goldstone & Collective Higgs Pole Theorem (`MA₁₁`)**:
Assuming **only** cutoff `0 < Λ`, supercritical coupling `1 < g * Λ²`, and form-factor scale `0 < Δ`
(discharging all `hgap`, `hm`, `hJ` hypotheses):
there exists a unique positive dynamical fermion mass `0 < mDyn` solving `g * njlGapIntegral Λ mDyn = 1`,
and for `Igap := njlGapIntegral Λ mDyn` and `Jq := njlFormFactorIntegral Λ Δ`, `0 < Jq`,
`njlInvPropagatorP g Igap Jq qSq = 0 ↔ qSq = 0`, and
`njlInvPropagatorS g Igap Jq mDyn qSq = 0 ↔ qSq = (2 * mDyn) ^ 2` with positive ghost-free
derivative slope `HasDerivAt ... (g * Jq / 2) ((2 * mDyn) ^ 2)`. -/
theorem njl_supercritical_unconditional_goldstone_and_higgs_poles
    {Λ g Δ : ℝ} (hΛ : 0 < Λ) (hsuper : 1 < g * Λ ^ 2) (hΔ : 0 < Δ) :
    ∃ mDyn : ℝ, 0 < mDyn ∧
      g * njlGapIntegral Λ mDyn = 1 ∧
      0 < njlFormFactorIntegral Λ Δ ∧
      (∀ qSq : ℝ,
        njlInvPropagatorP g (njlGapIntegral Λ mDyn) (njlFormFactorIntegral Λ Δ) qSq = 0 ↔
          qSq = 0) ∧
      (∀ qSq : ℝ,
        njlInvPropagatorS g (njlGapIntegral Λ mDyn) (njlFormFactorIntegral Λ Δ) mDyn qSq = 0 ↔
          qSq = (2 * mDyn) ^ 2) ∧
      HasDerivAt
        (njlInvPropagatorS g (njlGapIntegral Λ mDyn) (njlFormFactorIntegral Λ Δ) mDyn)
        (g * njlFormFactorIntegral Λ Δ / 2) ((2 * mDyn) ^ 2) ∧
      0 < g * njlFormFactorIntegral Λ Δ / 2 := by
  have hg : 0 < g := by nlinarith [sq_pos_of_pos hΛ, hsuper]
  obtain ⟨mDyn, ⟨hm_pos, hgap⟩, _⟩ := njl_supercritical_gap_solution_exists_unique hΛ hsuper
  have hJq_pos : 0 < njlFormFactorIntegral Λ Δ := (njlFormFactorIntegral_eval_and_pos hΛ hΔ).2
  have hpoles := dynamical_electroweak_goldstone_and_boundstate_higgs_poles hg hJq_pos hm_pos hgap
  exact ⟨mDyn, hm_pos, hgap, hJq_pos, fun qSq => (hpoles.1 qSq).2,
    fun qSq => (hpoles.2.1 qSq).2, hpoles.2.2.1, hpoles.2.2.2.1⟩

end MA11_DynamicalBoundStateHiggs

/-! ## Archetype `MA₁₂`: Local Dirac Weyl Spin-Connection Cancellation & On-Shell Traceless `T_{μν}` -/

section MA12_ConformalStressEnergyTrace

/-- `d`-dimensional Maxwell energy-momentum trace `(4 - d) F² / 4 = F² - (d / 4) F²`. -/
def maxwellStressTrace (d Fsq : ℝ) : ℝ :=
  Fsq - (d / 4) * Fsq

/-- Euler–Lagrange equation of motion for the conformally coupled scalar with Yukawa coupling:
`Box S + (1/6) R S - 4 λ S³ + h ψ̄ψ = 0`. -/
def conformalScalarFieldEq (boxS R S lam h psibarPsi : ℝ) : ℝ :=
  boxS + (1 / 6 : ℝ) * R * S - 4 * lam * S ^ 3 + h * psibarPsi

/-- Diagonal/trace components of the combined 4D conformal matter stress-energy tensor
`T^{(M)}_μ + T^{(ψ)}_μ + T^{(S)}_μ` including Maxwell, Yukawa-Dirac, improved `-1/6 ∇²(S²)`
Callan–Coleman–Jackiw improvement, Einstein-conformal `G_{μν} S² / 6`, and quartic `-λ S⁴ g_{μν}`. -/
def conformalMatterStress4 (ε : Fin 4 → ℝ) (emDiag : Fin 4 → ℝ) (psiDiag : Fin 4 → ℝ)
    (dS : Fin 4 → ℝ) (ddS : Fin 4 → ℝ) (RicDiag : Fin 4 → ℝ) (R S lam : ℝ) (μ : Fin 4) : ℝ :=
  emDiag μ + psiDiag μ +
    (2 / 3 : ℝ) * (dS μ) ^ 2 - (1 / 6 : ℝ) * diagEntry4 ε μ μ * (∑ α : Fin 4, ε α * (dS α) ^ 2) -
    (1 / 3 : ℝ) * S * ddS μ + (1 / 3 : ℝ) * diagEntry4 ε μ μ * S * (∑ α : Fin 4, ε α * ddS α) -
    (1 / 6 : ℝ) * S ^ 2 * (RicDiag μ - (1 / 2 : ℝ) * diagEntry4 ε μ μ * R) -
    diagEntry4 ε μ μ * lam * S ^ 4

/-- **Local Dirac Weyl Covariance & Curved-Spacetime On-Shell Traceless Stress-Energy (`MA₁₂`)**:
1. Under local rescaling `ψ(x) ↦ exp(w β(x)) ψ(x)`, `HasDerivAt` yields the product rule
   `exp(w β(x)) (ψ'(x) + w β'(x) ψ(x))`; adding the Weyl spin-connection shift
   `((d - 1)/2) β'(x) (exp(w β(x)) ψ(x))` cancels `β'(x)` identically **iff** `w = -(d - 1) / 2`
   (giving uniquely `w = -3 / 2` in `d = 4`);
2. For non-null Maxwell invariant `Fsq ≠ 0`, `maxwellStressTrace d Fsq = 0 ↔ d = 4`;
3. Across any 4D signature (`ε_μ² = 1`), with traceless Maxwell tensor (`∑ μ, ε μ em_μ = 0`),
   on-shell Yukawa-Dirac trace `h S ψ̄ψ`, Ricci scalar `∑ μ, ε μ Ric_μ = R`, and d'Alembertian
   `∑ μ, ε μ ddS_μ = boxS`, the exact trace `∑ μ, ε μ T_μ` factors as
   `S * conformalScalarFieldEq boxS R S lam h psibarPsi`, vanishing identically on-shell (`= 0`);
4. Consequently, on a conformally flat vacuum (`boxS = 0`, `S ≠ 0`), vanishing trace locks the
   dynamically induced cosmological term `4 λ S⁴ = (1/6) R S² + tr_matter`. -/
theorem local_dirac_weyl_covariance_and_traceless_conformal_stress_energy :
    (∀ (β : ℝ → ℝ) (ψ : ℝ → ℂ) (x β' : ℝ) (ψ' : ℂ) (w d : ℝ),
      HasDerivAt β β' x → HasDerivAt ψ ψ' x →
      HasDerivAt (fun y : ℝ => Complex.exp ((w * β y : ℝ) : ℂ) * ψ y)
        (Complex.exp ((w * β x : ℝ) : ℂ) * (ψ' + ((w * β' : ℝ) : ℂ) * ψ x)) x ∧
      Complex.exp ((w * β x : ℝ) : ℂ) * (ψ' + ((w * β' : ℝ) : ℂ) * ψ x) +
          ((((d - 1) / 2 * β' : ℝ) : ℂ)) * (Complex.exp ((w * β x : ℝ) : ℂ) * ψ x) =
        Complex.exp ((w * β x : ℝ) : ℂ) *
          (ψ' + ((((w + (d - 1) / 2) * β' : ℝ) : ℂ)) * ψ x) ∧
      ((∀ β' : ℝ, ((w + (d - 1) / 2) * β' : ℝ) = 0) ↔ w = -(d - 1) / 2) ∧
      ((-(4 - 1 : ℝ) / 2) = -(3 / 2 : ℝ))) ∧
    (∀ d Fsq : ℝ, Fsq ≠ 0 → (maxwellStressTrace d Fsq = 0 ↔ d = 4)) ∧
    (∀ (ε emDiag psiDiag dS ddS RicDiag : Fin 4 → ℝ), (∀ μ : Fin 4, ε μ * ε μ = 1) →
      ∀ (R S lam h psibarPsi boxS : ℝ),
      (∑ μ : Fin 4, ε μ * emDiag μ = 0) →
      (∑ μ : Fin 4, ε μ * psiDiag μ = h * S * psibarPsi) →
      (∑ μ : Fin 4, ε μ * RicDiag μ = R) →
      (∑ μ : Fin 4, ε μ * ddS μ = boxS) →
      ∑ μ : Fin 4, ε μ *
          conformalMatterStress4 ε emDiag psiDiag dS ddS RicDiag R S lam μ =
        S * conformalScalarFieldEq boxS R S lam h psibarPsi) ∧
    (∀ (R S lam trMatter : ℝ),
      S * ((1 / 6 : ℝ) * R * S - 4 * lam * S ^ 3) + trMatter = 0 →
      4 * lam * S ^ 4 = (1 / 6 : ℝ) * R * S ^ 2 + trMatter) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro β ψ x β' ψ' w d hβ hψ
    have hphase : HasDerivAt (fun y : ℝ => ((w * β y : ℝ) : ℂ)) ((w * β' : ℝ) : ℂ) x := by
      convert (hβ.const_mul w).ofReal_comp using 1
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp ((w * β y : ℝ) : ℂ))
        (Complex.exp ((w * β x : ℝ) : ℂ) * ((w * β' : ℝ) : ℂ)) x := hphase.cexp
    have hprod : HasDerivAt (fun y : ℝ => Complex.exp ((w * β y : ℝ) : ℂ) * ψ y)
        (Complex.exp ((w * β x : ℝ) : ℂ) * (ψ' + ((w * β' : ℝ) : ℂ) * ψ x)) x := by
      refine (hexp.mul hψ).congr_deriv ?_
      ring
    have halg : Complex.exp ((w * β x : ℝ) : ℂ) * (ψ' + ((w * β' : ℝ) : ℂ) * ψ x) +
          ((((d - 1) / 2 * β' : ℝ) : ℂ)) * (Complex.exp ((w * β x : ℝ) : ℂ) * ψ x) =
        Complex.exp ((w * β x : ℝ) : ℂ) *
          (ψ' + ((((w + (d - 1) / 2) * β' : ℝ) : ℂ)) * ψ x) := by
      push_cast
      ring
    have hiff : (∀ β' : ℝ, (w + (d - 1) / 2) * β' = 0) ↔ w = -(d - 1) / 2 := by
      constructor
      · intro hall
        have h1 := hall 1
        linarith
      · intro hw β'
        rw [hw]
        ring
    exact ⟨hprod, halg, hiff, by norm_num⟩
  · intro d Fsq hF
    unfold maxwellStressTrace
    have hfac : Fsq - d / 4 * Fsq = ((4 - d) / 4) * Fsq := by ring
    rw [hfac, mul_eq_zero, or_iff_left hF]
    constructor <;> intro h <;> linarith
  · intro ε emDiag psiDiag dS ddS RicDiag hε R S lam h psibarPsi boxS hem hpsi hRic hbox
    have h_tr_g : ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = 4 := by
      calc
        ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = ∑ _μ : Fin 4, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro μ _; simp [diagEntry4, hε μ]
        _ = 4 := by norm_num
    have hsplit : ∀ μ : Fin 4,
        ε μ * conformalMatterStress4 ε emDiag psiDiag dS ddS RicDiag R S lam μ =
          ε μ * emDiag μ + ε μ * psiDiag μ +
          (2 / 3 : ℝ) * (ε μ * (dS μ) ^ 2) -
          (1 / 6 : ℝ) * (ε μ * diagEntry4 ε μ μ) * (∑ α : Fin 4, ε α * (dS α) ^ 2) -
          (1 / 3 : ℝ) * S * (ε μ * ddS μ) +
          (1 / 3 : ℝ) * (ε μ * diagEntry4 ε μ μ) * S * (∑ α : Fin 4, ε α * ddS α) -
          (1 / 6 : ℝ) * S ^ 2 * (ε μ * RicDiag μ - (1 / 2 : ℝ) * (ε μ * diagEntry4 ε μ μ) * R) -
          (ε μ * diagEntry4 ε μ μ) * lam * S ^ 4 := by
      intro μ
      unfold conformalMatterStress4
      ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    rw [hem, hpsi, hRic, hbox, h_tr_g]
    unfold conformalScalarFieldEq
    ring
  · intro R S lam trMatter hzero
    linear_combination -hzero

/-- Symmetrized Belinfante Yukawa–Dirac stress-energy tensor
`T^{(ψ)}_{μν} = (1/2)(K_{μν} + K_{νμ}) - (1/4) g_{μν} (tr(K) - h S ψ̄ψ)`. -/
def diracYukawaStressTensor4 (ε : Fin 4 → ℝ) (kinMat : Matrix (Fin 4) (Fin 4) ℝ)
    (h S psibarPsi : ℝ) (μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (kinMat μ ν + kinMat ν μ) -
    (1 / 4 : ℝ) * diagEntry4 ε μ ν * ((∑ α : Fin 4, ε α * kinMat α α) - h * S * psibarPsi)

/-- Trace of `diracYukawaStressTensor4` across any 4D signature (`ε_μ² = 1`) and reduction on the
Dirac equation `∑ α, ε α * kinMat α α = h S ψ̄ψ`. -/
theorem diracYukawaStressTensor4_symm_and_trace
    (ε : Fin 4 → ℝ) (hε : ∀ μ : Fin 4, ε μ * ε μ = 1)
    (kinMat : Matrix (Fin 4) (Fin 4) ℝ) (h S psibarPsi : ℝ) :
    (∀ μ ν : Fin 4, diracYukawaStressTensor4 ε kinMat h S psibarPsi μ ν =
      diracYukawaStressTensor4 ε kinMat h S psibarPsi ν μ) ∧
    (∑ μ : Fin 4, ε μ * diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ = h * S * psibarPsi) ∧
    ((∑ α : Fin 4, ε α * kinMat α α = h * S * psibarPsi) →
      ∀ μ ν : Fin 4, diracYukawaStressTensor4 ε kinMat h S psibarPsi μ ν =
        (1 / 2 : ℝ) * (kinMat μ ν + kinMat ν μ)) := by
  have hsymm : ∀ μ ν : Fin 4,
      diracYukawaStressTensor4 ε kinMat h S psibarPsi μ ν =
        diracYukawaStressTensor4 ε kinMat h S psibarPsi ν μ := by
    intro μ ν
    unfold diracYukawaStressTensor4 diagEntry4
    have hdiag_sym : (if μ = ν then ε μ else 0) = if ν = μ then ε ν else 0 := by
      by_cases h1 : μ = ν
      · subst h1; simp
      · simp [h1, Ne.symm h1]
    rw [hdiag_sym, add_comm (kinMat μ ν) (kinMat ν μ)]
  have htr_g : ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = 4 := by
    calc
      ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = ∑ _μ : Fin 4, (1 : ℝ) :=
        Finset.sum_congr rfl fun μ _ => by simp [diagEntry4, hε μ]
      _ = 4 := by norm_num
  have htr : ∑ μ : Fin 4, ε μ * diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ =
      h * S * psibarPsi := by
    let Ktr := ∑ α : Fin 4, ε α * kinMat α α
    have hsplit : ∀ μ : Fin 4,
        ε μ * diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ =
          (ε μ * kinMat μ μ) - (1 / 4 : ℝ) * (ε μ * diagEntry4 ε μ μ) * (Ktr - h * S * psibarPsi) := by
      intro μ
      unfold diracYukawaStressTensor4
      dsimp only [Ktr]
      have hhalf : (1 / 2 : ℝ) * 2 = 1 := by norm_num
      rw [mul_sub, ← two_mul (kinMat μ μ), ← mul_assoc (1 / 2 : ℝ) 2 (kinMat μ μ), hhalf, one_mul,
        ← mul_assoc (ε μ), mul_left_comm (ε μ) (1 / 4 : ℝ) (diagEntry4 ε μ μ)]
    simp only [hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, htr_g]
    change Ktr - (1 / 4 : ℝ) * 4 * (Ktr - h * S * psibarPsi) = h * S * psibarPsi
    have hquar : (1 / 4 : ℝ) * 4 = 1 := by norm_num
    rw [hquar, one_mul, sub_sub_cancel]
  refine ⟨hsymm, htr, ?_⟩
  intro hDirac μ ν
  unfold diracYukawaStressTensor4
  rw [hDirac, sub_self, mul_zero, sub_zero]

/-- **Constructive 4D Conformal Total Stress-Energy Trace Theorem (`MA₁₂` Trace Premise Closure)**:
Directly plugs `maxwellStressTensor4`, `diracYukawaStressTensor4`, `ricciContract4`, and
`ricciScalar4` into `conformalMatterStress4` with **zero** trace assumptions on `emDiag`, `psiDiag`,
or `RicDiag`: the trace identically equals
`S * conformalScalarFieldEq (∑ μ, ε μ * ddS μ) (ricciScalar4 ε Riem) S lam h psibarPsi`
and vanishes identically iff `S = 0` or the conformal scalar EOM holds. -/
theorem constructive_4d_conformal_total_stress_trace_identity
    (ε : Fin 4 → ℝ) (hε : ∀ μ : Fin 4, ε μ * ε μ = 1)
    (F kinMat : Matrix (Fin 4) (Fin 4) ℝ)
    (dS ddS : Fin 4 → ℝ) (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (S lam h psibarPsi : ℝ) :
    let trTot := ∑ μ : Fin 4, ε μ * conformalMatterStress4 ε
        (fun μ => maxwellStressTensor4 ε F μ μ)
        (fun μ => diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ)
        dS ddS (fun μ => ricciContract4 ε Riem μ μ) (ricciScalar4 ε Riem) S lam μ
    let eqS := conformalScalarFieldEq (∑ μ : Fin 4, ε μ * ddS μ)
        (ricciScalar4 ε Riem) S lam h psibarPsi
    trTot = S * eqS ∧ (trTot = 0 ↔ S = 0 ∨ eqS = 0) := by
  intro trTot eqS
  have hem := (maxwellStressTensor4_symm_and_trace_zero ε hε F).2
  have hpsi := (diracYukawaStressTensor4_symm_and_trace ε hε kinMat h S psibarPsi).2.1
  have hRic : ∑ μ : Fin 4, ε μ * ricciContract4 ε Riem μ μ = ricciScalar4 ε Riem := rfl
  have hfac : trTot = S * eqS :=
    local_dirac_weyl_covariance_and_traceless_conformal_stress_energy.2.2.1
      ε (fun μ => maxwellStressTensor4 ε F μ μ)
      (fun μ => diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ)
      dS ddS (fun μ => ricciContract4 ε Riem μ μ) hε
      (ricciScalar4 ε Riem) S lam h psibarPsi (∑ μ : Fin 4, ε μ * ddS μ)
      hem hpsi hRic rfl
  refine ⟨hfac, ?_⟩
  rw [hfac, mul_eq_zero]

end MA12_ConformalStressEnergyTrace

/-! ## Archetype Registrations (`MA₉`–`MA₁₂`) -/

section ArchetypeRegistrations

/-- Proved `TypedArchetype` for `MA₉`: PT Stokes-wedge Gaussian integrability iff `cos(2 θ) < 0`,
all-loop 4D Weyl power-counting `weylSuperficialDegree = 4`, and 4D UV `IntegrableOn` loop closure. -/
def archMA9PTStokesWedgeAndWeylUV : TypedArchetype Unit .proved where
  name := `archMA9PTStokesWedgeAndWeylUV
  phase := 9
  claim := fun _ =>
    (∀ b θ : ℝ, 0 < b →
      (MeasureTheory.Integrable (ghostStokesIntegrand b θ) ↔ Real.cos (2 * θ) < 0)) ∧
    (∀ b : ℝ, 0 < b →
      ¬ MeasureTheory.Integrable (ghostStokesIntegrand b 0) ∧
      MeasureTheory.Integrable (ghostStokesIntegrand b (Real.pi / 2)) ∧
      ∫ y : ℝ, Real.exp (-b * y ^ 2) = Real.sqrt (Real.pi / b)) ∧
    (∀ G : ConnectedFeynmanGraph,
      fgLoops G - 1 = fgEdges G - fgVertices G ∧
      weylSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 4 ∧
      einsteinSuperficialDegree (fgLoops G) (fgVertices G) (fgEdges G) = 2 * fgLoops G + 2) ∧
    (∀ Λ m₁ m₂ : ℝ, 0 < Λ →
      MeasureTheory.IntegrableOn (weylBubbleUVIntegrand m₁ m₂) (Set.Ioi Λ) ∧
      ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (1 : ℝ)) (Set.Ioi Λ) ∧
      ¬ MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (3 : ℝ)) (Set.Ioi Λ))
  evidence := fun _ =>
    let h := pt_stokes_wedge_gaussian_and_weyl_uv_convergence
    ⟨h.2.1,
     fun b hb => ⟨(h.2.2.1 b hb).2.1, (h.2.2.1 b hb).2.2.1, (h.2.2.1 b hb).2.2.2.2.1⟩,
     connectedFeynmanGraph_euler_and_weyl_degree,
     h.2.2.2.2⟩

/-- Proved `TypedArchetype` for `MA₁₀`: Mannheim–Kazanas geodesic orbital velocity law,
dark-matter-free Keplerian excess, transition radius, and exact Baryonic Tully–Fisher `v⁴` law. -/
def archMA10MannheimKazanasRotationCurve : TypedArchetype Unit .proved where
  name := `archMA10MannheimKazanasRotationCurve
  phase := 10
  claim := fun _ =>
    (∀ c Nstar βstar γstar γ₀ κ r : ℝ, r ≠ 0 →
      (c ^ 2 * r / 2) * deriv (mannheimKazanasPotential 1 (Nstar * βstar) (Nstar * γstar + γ₀) κ) r =
        mkCircularVelocitySq c (Nstar * βstar) (Nstar * γstar + γ₀) κ r) ∧
    (∀ c Bstar Gtot r : ℝ, 0 < c → 0 < Bstar → 0 < Gtot → 0 < r →
      c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ≤ mkCircularVelocitySq c Bstar Gtot 0 r ∧
      (mkCircularVelocitySq c Bstar Gtot 0 r = c ^ 2 * Real.sqrt (2 * Bstar * Gtot) ↔
        r = mkTransitionRadius Bstar Gtot) ∧
      (mkCircularVelocitySq c Bstar Gtot 0 (mkTransitionRadius Bstar Gtot)) ^ 2 =
        2 * c ^ 4 * Bstar * Gtot) ∧
    (∀ c Gtot κ r : ℝ, 0 < c → 0 < Gtot → 0 < κ →
      (deriv (fun x : ℝ => (Gtot * c ^ 2 / 2) * x - κ * c ^ 2 * x ^ 2) r = 0 ↔
        r = Gtot / (4 * κ)))
  evidence := fun _ =>
    let h := mannheim_kazanas_galactic_rotation_geodesic_and_tully_fisher
    ⟨h.1,
     fun c Bstar Gtot r hc hB hG hr => (h.2.2.1 c Bstar Gtot r hc hB hG hr).2,
     fun c Gtot κ r hc hG hκ => (h.2.2.2 c Gtot κ r hc hG hκ).2⟩

/-- Proved `TypedArchetype` for `MA₁₁`: unconditional supercritical 1-loop NJL gap existence &
uniqueness (`g * njlGapIntegral Λ mDyn = 1`), positive form-factor integral `njlFormFactorIntegral`,
massless Goldstone pole, ghost-free dynamical bound-state Higgs pole `M_H = 2 m_dyn`, and `γ_θ = -1`
sub-threshold dressing. -/
def archMA11DynamicalBoundStateHiggs : TypedArchetype Unit .proved where
  name := `archMA11DynamicalBoundStateHiggs
  phase := 11
  claim := fun _ =>
    (∀ {Λ g Δ : ℝ}, 0 < Λ → 1 < g * Λ ^ 2 → 0 < Δ →
      ∃ mDyn : ℝ, 0 < mDyn ∧
        g * njlGapIntegral Λ mDyn = 1 ∧
        0 < njlFormFactorIntegral Λ Δ ∧
        (∀ qSq : ℝ,
          njlInvPropagatorP g (njlGapIntegral Λ mDyn) (njlFormFactorIntegral Λ Δ) qSq = 0 ↔
            qSq = 0) ∧
        (∀ qSq : ℝ,
          njlInvPropagatorS g (njlGapIntegral Λ mDyn) (njlFormFactorIntegral Λ Δ) mDyn qSq = 0 ↔
            qSq = (2 * mDyn) ^ 2) ∧
        0 < g * njlFormFactorIntegral Λ Δ / 2) ∧
    (∀ {g Igap Jq mDyn : ℝ}, 0 < g → 0 < Jq → 0 < mDyn → g * Igap = 1 →
      (∀ ΔA : ℝ, 0 < ΔA → ΔA < 4 * mDyn ^ 2 →
        njlDressedInvPropagatorS g Igap Jq mDyn ΔA (4 * mDyn ^ 2 - ΔA) = 0))
  evidence := fun _ =>
    ⟨fun hΛ hsuper hΔ =>
      let hw := njl_supercritical_unconditional_goldstone_and_higgs_poles hΛ hsuper hΔ
      ⟨hw.choose, hw.choose_spec.1, hw.choose_spec.2.1, hw.choose_spec.2.2.1,
        hw.choose_spec.2.2.2.1, hw.choose_spec.2.2.2.2.1, hw.choose_spec.2.2.2.2.2.2⟩,
     fun hg hJ hm hgap ΔA h0 hlt =>
       (@dynamical_electroweak_goldstone_and_boundstate_higgs_poles _ _ _ _ hg hJ hm hgap
         |>.2.2.2.2.2 ΔA h0 hlt (4 * _ ^ 2 - ΔA)).1.mpr rfl⟩

/-- Proved `TypedArchetype` for `MA₁₂`: local `HasDerivAt` Dirac Weyl spin-connection
cancellation (`w = -3/2` in `d = 4`), Maxwell trace iff `d = 4`, and constructive 4D
Maxwell + Yukawa–Dirac + scalar on-shell trace identity (`constructive_4d_conformal_total_stress_trace_identity`). -/
def archMA12ConformalStressEnergyTrace : TypedArchetype Unit .proved where
  name := `archMA12ConformalStressEnergyTrace
  phase := 12
  claim := fun _ =>
    (∀ (β : ℝ → ℝ) (ψ : ℝ → ℂ) (x β' : ℝ) (ψ' : ℂ) (w d : ℝ),
      HasDerivAt β β' x → HasDerivAt ψ ψ' x →
      Complex.exp ((w * β x : ℝ) : ℂ) * (ψ' + ((w * β' : ℝ) : ℂ) * ψ x) +
          ((((d - 1) / 2 * β' : ℝ) : ℂ)) * (Complex.exp ((w * β x : ℝ) : ℂ) * ψ x) =
        Complex.exp ((w * β x : ℝ) : ℂ) *
          (ψ' + ((((w + (d - 1) / 2) * β' : ℝ) : ℂ)) * ψ x) ∧
      ((∀ β' : ℝ, ((w + (d - 1) / 2) * β' : ℝ) = 0) ↔ w = -(d - 1) / 2)) ∧
    (∀ d Fsq : ℝ, Fsq ≠ 0 → (maxwellStressTrace d Fsq = 0 ↔ d = 4)) ∧
    (∀ (ε : Fin 4 → ℝ), (∀ μ : Fin 4, ε μ * ε μ = 1) →
      ∀ (F kinMat : Matrix (Fin 4) (Fin 4) ℝ)
        (dS ddS : Fin 4 → ℝ) (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
        (S lam h psibarPsi : ℝ),
      ∑ μ : Fin 4, ε μ * conformalMatterStress4 ε
          (fun μ => maxwellStressTensor4 ε F μ μ)
          (fun μ => diracYukawaStressTensor4 ε kinMat h S psibarPsi μ μ)
          dS ddS (fun μ => ricciContract4 ε Riem μ μ) (ricciScalar4 ε Riem) S lam μ =
        S * conformalScalarFieldEq (∑ μ : Fin 4, ε μ * ddS μ) (ricciScalar4 ε Riem) S lam h psibarPsi)
  evidence := fun _ =>
    let h := local_dirac_weyl_covariance_and_traceless_conformal_stress_energy
    ⟨fun β ψ x β' ψ' w d hβ hψ =>
      let hw := h.1 β ψ x β' ψ' w d hβ hψ
      ⟨hw.2.1, hw.2.2.1⟩,
     h.2.1,
     fun ε hε F kinMat dS ddS Riem S lam h psibarPsi =>
       (constructive_4d_conformal_total_stress_trace_identity ε hε F kinMat dS ddS Riem S lam h psibarPsi).1⟩

#register_archetype archMA9PTStokesWedgeAndWeylUV
#audit_archetype archMA9PTStokesWedgeAndWeylUV
#register_archetype archMA10MannheimKazanasRotationCurve
#audit_archetype archMA10MannheimKazanasRotationCurve
#register_archetype archMA11DynamicalBoundStateHiggs
#audit_archetype archMA11DynamicalBoundStateHiggs
#register_archetype archMA12ConformalStressEnergyTrace
#audit_archetype archMA12ConformalStressEnergyTrace

end ArchetypeRegistrations

end InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
