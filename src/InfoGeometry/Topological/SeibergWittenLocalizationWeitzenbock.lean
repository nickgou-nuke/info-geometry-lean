/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Seiberg–Witten BRST Localization, Bochner–Weitzenböck Square Completion, & Positive Scalar Curvature Vanishing

Target: `InfoGeometry/Topological/SeibergWittenLocalizationWeitzenbock.lean`

This module epistemically compiles Wave 18 (Section 148) from
`1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` (Turn 329):

1. **Witten Topological Twisting BRST Localization (`sw_equation_from_brst_localization`):**
   - For the topologically twisted self-dual 2-form fermion $\chi_{\mu\nu}$ with BRST
     variation $Q\chi = F^+ - \sigma(\Phi)$, vanishing at a BRST fixed point ($Q\chi = 0$)
     is equivalent to the Seiberg–Witten monopole equation $F^+ = \sigma(\Phi)$.
2. **Bochner–Weitzenböck Action Square Completion (`weitzenbock_bochner_action_completion`):**
   - Proves the exact algebraic completion of squares relating the self-dual gauge +
     spinor functional to the topological coupling $4 F^+ \sigma(\Phi)$ when
     $\sigma(\Phi)^2 = \|\Phi\|^4$.
3. **Full Seiberg–Witten Weitzenböck Vanishing Theorem (`positive_scalar_curvature_vanishes_sw_moduli`):**
   - Over any strictly ordered commutative ring `R`, if $0 \le \|\nabla_A\Phi\|^2$,
     $0 \le \|\Phi\|^2$, and $0 < R_{\mathrm{scal}}$, then non-positivity of the full
     Bochner–Weitzenböck functional
     $$4\|\nabla_A\Phi\|^2 + 2(F^+ - \sigma(\Phi))^2 + R_{\mathrm{scal}}\|\Phi\|^2 + 2\|\Phi\|^4 \le 0$$
     forces $\|\Phi\|^2 = 0$, $\|\nabla_A\Phi\|^2 = 0$, and $F^+ = \sigma(\Phi)$ simultaneously.
4. **Negative Scalar Curvature BPS Condensate Bound (`negative_scalar_curvature_bps_condensate_law`):**
   - At a non-trivial BPS monopole ($\nabla_A\Phi = 0$, $F^+ = \sigma(\Phi)$, $\|\Phi\|^2 > 0$),
     vanishing of the Weitzenböck functional forces $2\|\Phi\|^2 = -R_{\mathrm{scal}}$
     and $R_{\mathrm{scal}} < 0$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Cohomological & Weitzenböck Theorems (`[kernel_verified]`):**
  - `sw_equation_from_brst_localization`, `weitzenbock_bochner_action_completion`,
    `positive_scalar_curvature_vanishes_sw_moduli`, and
    `negative_scalar_curvature_bps_condensate_law`.
* **BUCKET 2 — Eliminated Certificate Wrappers (Zero Remaining):**
  - `SeibergWittenWeitzenbockCertificate : Prop` from Turn 329 is eliminated.
* **BUCKET 3 — Infinite-Dimensional Sobolev Gauge Moduli Space (`[bucket_3_open_debt]`):**
  - Uhlenbeck–Taubes compactness and Fredholm index theory on $L^2_k(\Omega^1 \oplus S^+)$
    over smooth 4-manifolds remain outside this algebraic ordered-ring scope.
-/

namespace InfoGeometry.Topological.SeibergWittenWeitzenbock

section AlgebraicLocalization

variable {R : Type*} [CommRing R]

/-- BRST variation $Q\chi = F^+ - \sigma(\Phi)$ of the topologically twisted self-dual
2-form fermion $\chi_{\mu\nu}$. -/
def brstQ_chi (F_plus sigma_Phi : R) : R :=
  F_plus - sigma_Phi

/-- **Witten Topological Twisting BRST Localization (`sw_equation_from_brst_localization`):**
Vanishing of the BRST variation `brstQ_chi F_plus sigma_Phi = 0` is strictly equivalent
to the Seiberg–Witten monopole equation $F^+ = \sigma(\Phi)$. -/
theorem sw_equation_from_brst_localization (F_plus sigma_Phi : R) :
    brstQ_chi F_plus sigma_Phi = 0 ↔ F_plus = sigma_Phi := by
  unfold brstQ_chi
  exact sub_eq_zero

/-- Full Bochner–Weitzenböck Seiberg–Witten functional (scaled by 4 for ring exactness):
$$\mathcal{S}_{\mathrm{BW}}(\|\nabla_A\Phi\|^2, F^+, \sigma(\Phi), R_{\mathrm{scal}}, \|\Phi\|^2)
  = 4\|\nabla_A\Phi\|^2 + 2(F^+ - \sigma(\Phi))^2 + R_{\mathrm{scal}}\|\Phi\|^2 + 2\|\Phi\|^4.$$ -/
def bochnerWeitzenbockAction (nablaPhiSq F_plus sigma_Phi R_scal normPhiSq : R) : R :=
  4 * nablaPhiSq + 2 * (F_plus - sigma_Phi) ^ 2 +
    R_scal * normPhiSq + 2 * (normPhiSq * normPhiSq)

/-- **Bochner–Weitzenböck Square Completion (`weitzenbock_bochner_action_completion`):**
Whenever the quadratic spinor form satisfies the Clifford norm identity
$\sigma(\Phi)^2 = (\|\Phi\|^2)^2$, the full Bochner–Weitzenböck functional expands as
$$4\|\nabla_A\Phi\|^2 + 2(F^+)^2 - 4 F^+\sigma(\Phi) + R_{\mathrm{scal}}\|\Phi\|^2 + 4\|\Phi\|^4.$$ -/
theorem weitzenbock_bochner_action_completion
    (nablaPhiSq F_plus sigma_Phi R_scal normPhiSq : R)
    (h_clifford : sigma_Phi ^ 2 = normPhiSq * normPhiSq) :
    bochnerWeitzenbockAction nablaPhiSq F_plus sigma_Phi R_scal normPhiSq =
      4 * nablaPhiSq + 2 * F_plus ^ 2 - 4 * F_plus * sigma_Phi +
        R_scal * normPhiSq + 4 * (normPhiSq * normPhiSq) := by
  unfold bochnerWeitzenbockAction
  calc 4 * nablaPhiSq + 2 * (F_plus - sigma_Phi) ^ 2 +
        R_scal * normPhiSq + 2 * (normPhiSq * normPhiSq)
    _ = 4 * nablaPhiSq + 2 * F_plus ^ 2 - 4 * F_plus * sigma_Phi +
          2 * sigma_Phi ^ 2 + R_scal * normPhiSq + 2 * (normPhiSq * normPhiSq) := by ring
    _ = 4 * nablaPhiSq + 2 * F_plus ^ 2 - 4 * F_plus * sigma_Phi +
          2 * (normPhiSq * normPhiSq) + R_scal * normPhiSq + 2 * (normPhiSq * normPhiSq) := by
        rw [h_clifford]
    _ = 4 * nablaPhiSq + 2 * F_plus ^ 2 - 4 * F_plus * sigma_Phi +
          R_scal * normPhiSq + 4 * (normPhiSq * normPhiSq) := by ring

end AlgebraicLocalization

section OrderedWeitzenbockVanishing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Positive Scalar Curvature Vanishing of the Full Seiberg–Witten Moduli Space
(`positive_scalar_curvature_vanishes_sw_moduli`):**
Over any strictly ordered commutative ring `R`, if $0 \le \|\nabla_A\Phi\|^2$,
$0 \le \|\Phi\|^2$, $0 < R_{\mathrm{scal}}$, and
$\mathcal{S}_{\mathrm{BW}}(\|\nabla_A\Phi\|^2, F^+, \sigma(\Phi), R_{\mathrm{scal}}, \|\Phi\|^2) \le 0$,
then simultaneously:
1. $\|\Phi\|^2 = 0$ (no monopole condensate),
2. $\|\nabla_A\Phi\|^2 = 0$ (parallel spinor gradient vanishes),
3. $F^+ = \sigma(\Phi)$ (exact self-dual curvature localization). -/
theorem positive_scalar_curvature_vanishes_sw_moduli
    (nablaPhiSq F_plus sigma_Phi R_scal normPhiSq : R)
    (h_nabla : 0 ≤ nablaPhiSq)
    (h_phi : 0 ≤ normPhiSq)
    (h_R : 0 < R_scal)
    (h_action : bochnerWeitzenbockAction nablaPhiSq F_plus sigma_Phi R_scal normPhiSq ≤ 0) :
    normPhiSq = 0 ∧ nablaPhiSq = 0 ∧ F_plus = sigma_Phi := by
  unfold bochnerWeitzenbockAction at h_action
  have h1 : 0 ≤ 4 * nablaPhiSq := by linarith [h_nabla]
  have h_diff_sq : 0 ≤ (F_plus - sigma_Phi) ^ 2 := sq_nonneg (F_plus - sigma_Phi)
  have h2 : 0 ≤ 2 * (F_plus - sigma_Phi) ^ 2 := by linarith [h_diff_sq]
  have h_phi_sq : 0 ≤ normPhiSq * normPhiSq := mul_self_nonneg normPhiSq
  have h3 : 0 ≤ 2 * (normPhiSq * normPhiSq) := by linarith [h_phi_sq]
  have h4 : 0 ≤ R_scal * normPhiSq := mul_nonneg (le_of_lt h_R) h_phi
  have h_Rphi_le : R_scal * normPhiSq ≤ 0 := by linarith
  have h_Rphi_zero : R_scal * normPhiSq = 0 := le_antisymm h_Rphi_le h4
  have h_phi_zero : normPhiSq = 0 := by
    rcases mul_eq_zero.mp h_Rphi_zero with hR0 | hPhi0
    · linarith
    · exact hPhi0
  have h_nabla_zero : nablaPhiSq = 0 := by
    rw [h_phi_zero] at h_action
    linarith
  have h_diff_sq_le : (F_plus - sigma_Phi) ^ 2 ≤ 0 := by
    rw [h_phi_zero, h_nabla_zero] at h_action
    linarith
  have h_diff_sq_zero : (F_plus - sigma_Phi) ^ 2 = 0 := le_antisymm h_diff_sq_le h_diff_sq
  have h_F_eq : F_plus = sigma_Phi := sub_eq_zero.mp (sq_eq_zero_iff.mp h_diff_sq_zero)
  exact ⟨h_phi_zero, h_nabla_zero, h_F_eq⟩

/-- **Negative Scalar Curvature BPS Monopole Condensate Law
(`negative_scalar_curvature_bps_condensate_law`):**
At a BPS solution ($\|\nabla_A\Phi\|^2 = 0$ and $F^+ = \sigma(\Phi)$) with strictly
positive monopole condensate $\|\Phi\|^2 > 0$, vanishing of `bochnerWeitzenbockAction`
forces $2\|\Phi\|^2 = -R_{\mathrm{scal}}$ and strictly negative scalar curvature
$R_{\mathrm{scal}} < 0$. -/
theorem negative_scalar_curvature_bps_condensate_law
    (F_plus sigma_Phi R_scal normPhiSq : R)
    (h_bps : F_plus = sigma_Phi)
    (h_phi_pos : 0 < normPhiSq)
    (h_zero : bochnerWeitzenbockAction 0 F_plus sigma_Phi R_scal normPhiSq = 0) :
    2 * normPhiSq = -R_scal ∧ R_scal < 0 := by
  unfold bochnerWeitzenbockAction at h_zero
  rw [h_bps] at h_zero
  have h_prod : (R_scal + 2 * normPhiSq) * normPhiSq = 0 := by
    linear_combination h_zero
  have h_sum_zero : R_scal + 2 * normPhiSq = 0 := by
    rcases mul_eq_zero.mp h_prod with hSum | hPhi0
    · exact hSum
    · linarith [h_phi_pos]
  refine ⟨by linarith [h_sum_zero], by linarith [h_sum_zero, h_phi_pos]⟩

end OrderedWeitzenbockVanishing

end InfoGeometry.Topological.SeibergWittenWeitzenbock
