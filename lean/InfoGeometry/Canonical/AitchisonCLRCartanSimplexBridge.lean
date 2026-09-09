/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Quantum.DikinBlahutOrbits

noncomputable section

namespace InfoGeometry.Canonical.AitchisonCLRCartanSimplexBridge

open Real
open InfoGeometry.Quantum.DikinBlahutOrbits

set_option linter.unusedVariables false

/-!
# Aitchison CLR Simplex & Cartan Subalgebra Symmetric Space Bridge

This module formalizes the canonical geometric relationship between the
**Aitchison Centered Log-Ratio (CLR)** simplex $\Delta^{D-1}$, the **Cartan Subalgebra**
$\mathfrak{a} \subset \mathfrak{sl}(D, \mathbb{R})$ of the symmetric space $\operatorname{SL}(D, \mathbb{R})/\operatorname{SO}(D)$,
and the **Tripartite Symmetric Space Trinity**:

1. **The Aitchison CLR Projection**:
   $\xi_i = \ln(p_i) - \frac{1}{D} \sum_{k=1}^D \ln(p_k)$ projects $\Delta^{D-1}$ isometrically
   onto the zero-sum hyperplane $U = \{ \boldsymbol{\xi} \in \mathbb{R}^D \mid \sum \xi_i = 0 \}$,
   which is the Cartan subalgebra $\mathfrak{a} \subset \mathfrak{sl}(D, \mathbb{R})$ ($\operatorname{tr}(X) = 0$).

2. **The 1-Simplex ($\Delta^1$) Binary Model**:
   For $p \in (0, 1)$, $\mathbf{p} = (p, 1-p)$:
   - Logit: $\ell = \ln(p / (1-p))$.
   - CLR coordinates: $\boldsymbol{\xi} = (\frac{1}{2}\ell, -\frac{1}{2}\ell)$.
   - Zero-sum property: $\xi_1 + \xi_2 = 0$.

3. **The Triad Metric Identity Certified in Lean 4**:
   On $\Delta^1$, the Dikin barrier Hessian $b''(p)$, the Aitchison metric $g_{\text{Aitchison}}(p)$,
   and the Fisher-Rao metric $g_{\text{FR}}(p)$ satisfy the exact algebraic relation:
     $$b''(p) = 2 g_{\text{Aitchison}}(p) - 2 g_{\text{FR}}(p)$$
     $$\frac{1}{p^2} + \frac{1}{(1-p)^2} = \frac{1}{p^2(1-p)^2} - \frac{2}{p(1-p)}$$

4. **Weyl Group Reflection**:
   The survival-loss reflection $p \mapsto 1-p$ acts as the non-trivial reflection
   $\boldsymbol{\xi} \mapsto -\boldsymbol{\xi}$ in the Weyl group $\mathbb{Z}_2 = S_2$.

5. **Dikin Ellipsoid Confinement**:
   Self-concordant Dikin ellipsoids $\mathcal{E}(p, r) \subset (0, 1)$ isolate the simplex
   interior from boundary collisions under Sinkhorn transport.
-/

/-! ## 1. The 1-Simplex Binary Model & CLR Coordinates -/

/-- The log-odds / logit function on the open unit interval $(0, 1)$. -/
def logit (p : ℝ) : ℝ :=
  Real.log (p / (1 - p))

/-- The first CLR coordinate on the binary simplex $\Delta^1$: $\xi_1 = \frac{1}{2} \operatorname{logit}(p)$. -/
def clr1 (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logit p

/-- The second CLR coordinate on the binary simplex $\Delta^1$: $\xi_2 = -\frac{1}{2} \operatorname{logit}(p)$. -/
def clr2 (p : ℝ) : ℝ :=
  - (1 / 2 : ℝ) * logit p

/-- 🏆 THEOREM 1 (Zero-Sum Hyperplane / Cartan Subalgebra Condition):
    The CLR coordinates on $\Delta^1$ satisfy $\xi_1 + \xi_2 = 0$, identically projecting
    the probability vector onto the Cartan subalgebra $\mathfrak{a} \subset \mathfrak{sl}(2, \mathbb{R})$. -/
theorem clr_zero_sum (p : ℝ) :
    clr1 p + clr2 p = 0 := by
  unfold clr1 clr2
  ring

/-! ## 2. The Triad Metric Identity on the 1-Simplex -/

/-- The Dikin log-barrier Hessian on the 1-simplex: $b''(p) = 1/p^2 + 1/(1-p)^2$. -/
def dikinBarrierHessian (p : ℝ) : ℝ :=
  1 / p ^ 2 + 1 / (1 - p) ^ 2

/-- The Aitchison metric on the 1-simplex: $g_{\text{Aitchison}}(p) = 1 / (2 p^2 (1-p)^2)$. -/
def aitchisonMetric (p : ℝ) : ℝ :=
  1 / (2 * p ^ 2 * (1 - p) ^ 2)

/-- The Fisher-Rao metric on the 1-simplex: $g_{\text{FR}}(p) = 1 / (p (1-p))$. -/
def fisherRaoMetric (p : ℝ) : ℝ :=
  1 / (p * (1 - p))

/-- 🏆 THEOREM 2 (The Triad Metric Identity Certified):
    On the 1-simplex $\Delta^1$, the Dikin barrier Hessian decomposes into the Aitchison
    Cartan metric and the spherical Fisher-Rao metric:
      $$b''(p) = 2 g_{\text{Aitchison}}(p) - 2 g_{\text{FR}}(p)$$
      $$\frac{1}{p^2} + \frac{1}{(1-p)^2} = \frac{1}{p^2(1-p)^2} - \frac{2}{p(1-p)}$$ -/
theorem triad_metric_identity (p : ℝ) (hp : p ≠ 0) (h1p : 1 - p ≠ 0) :
    dikinBarrierHessian p = 2 * aitchisonMetric p - 2 * fisherRaoMetric p := by
  unfold dikinBarrierHessian aitchisonMetric fisherRaoMetric
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have h1p2 : (1 - p) ^ 2 ≠ 0 := pow_ne_zero 2 h1p
  field_simp [hp, h1p, hp2, h1p2]
  ring

/-- 🏆 THEOREM 3 (Aitchison vs. Fisher-Rao Conformal Scaling):
    The Aitchison metric is conformal to the Fisher-Rao metric by the inverse variance factor:
      $g_{\text{Aitchison}}(p) = \frac{1}{2 p (1-p)} g_{\text{FR}}(p)$. -/
theorem aitchison_conformal_fisher_rao (p : ℝ) (hp : p ≠ 0) (h1p : 1 - p ≠ 0) :
    aitchisonMetric p = (1 / (2 * p * (1 - p))) * fisherRaoMetric p := by
  unfold aitchisonMetric fisherRaoMetric
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have h1p2 : (1 - p) ^ 2 ≠ 0 := pow_ne_zero 2 h1p
  field_simp [hp, h1p, hp2, h1p2]

/-! ## 3. Weyl Group Reflection on the Cartan Subalgebra -/

/-- 🏆 THEOREM 4 (Weyl Reflection on the 1-Simplex):
    Under the survival-loss swap $p \mapsto 1 - p$, the logit flips sign:
      $\operatorname{logit}(1 - p) = - \operatorname{logit}(p)$.
    Consequently, the CLR vector undergoes the non-trivial Weyl reflection:
      $(\xi_1, \xi_2) \mapsto (-\xi_1, -\xi_2) = (\xi_2, \xi_1)$. -/
theorem weyl_reflection_logit (p : ℝ) (hp : 0 < p) (h1p : p < 1) :
    logit (1 - p) = - logit p := by
  unfold logit
  have hp_pos : 0 < p := hp
  have h1p_pos : 0 < 1 - p := by linarith
  have h_sub : 1 - (1 - p) = p := by ring
  rw [h_sub]
  have h_div_inv : (1 - p) / p = (p / (1 - p))⁻¹ := by
    rw [inv_div]
  rw [h_div_inv]
  rw [Real.log_inv]

/-- 🏆 THEOREM 5 (Weyl Action on CLR Coordinates):
    The swap $p \mapsto 1-p$ exchanges the two CLR coordinates:
      $\operatorname{clr}_1(1-p) = \operatorname{clr}_2(p)$ and
      $\operatorname{clr}_2(1-p) = \operatorname{clr}_1(p)$. -/
theorem weyl_action_clr (p : ℝ) (hp : 0 < p) (h1p : p < 1) :
    clr1 (1 - p) = clr2 p ∧ clr2 (1 - p) = clr1 p := by
  have h_refl := weyl_reflection_logit p hp h1p
  constructor
  · unfold clr1 clr2
    rw [h_refl]
    ring
  · unfold clr1 clr2
    rw [h_refl]
    ring

/-! ## 4. Dikin Ellipsoid Interior Confinement of the Simplex -/

/-- 🏆 THEOREM 6 (Dikin Confinement on the Statistical Simplex):
    Within the Dikin ellipsoid $\mathcal{E}(p, r)$ with radius $r < 1$,
    any updated probability vector $y$ remains strictly positive: $y > 0$.
    This guarantees that the Sinkhorn defect flow never hits the boundary of the simplex. -/
theorem dikin_simplex_interior_confinement (p y r : ℝ) (hp : 0 < p) (hr_nonneg : 0 ≤ r) (hr_lt : r < 1)
    (h_in : InDikinEllipsoid p y r) :
    0 < y :=
  dikin_ellipsoid_strictly_positive p y r hp hr_nonneg hr_lt h_in

end InfoGeometry.Canonical.AitchisonCLRCartanSimplexBridge
