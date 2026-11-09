/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

/-!
# Temperley–Lieb Idempotent Identities and Peirce-Shell Trace Consequences

This module proves finite algebraic identities over an associative ring `B` (`[Ring B]`).
It does not construct a von Neumann crossed product, a Connes–Takesaki dual action, or a new
trace. Its trace result is conditional on an explicitly supplied cyclic trace.

* `TL1` (`temperley_lieb_commutative_collapse`):
  **The Socratic Collapse Theorem** — proves that if two Temperley–Lieb idempotents
  `e₁² = e₁, e₂² = e₂` satisfying `e₁ e₂ e₁ = τ e₁` and `e₂ e₁ e₂ = τ e₂` commute
  (`e₁ e₂ = e₂ e₁`), then `e₁ e₂ = τ e₁ = τ e₂` and `(τ - τ²) e₁ = (τ - τ²) e₂ = 0`.
  In particular, if `τ` is invertible and the idempotents are distinct, they cannot commute.
* `TL2` (`non_commutative_temperley_lieb_curvature`):
  **Non-Commutative Temperley–Lieb Spin Curvature** — decomposes `2 e₁ e₂ = Metric_TL + Sigma_TL`
  and `2 e₂ e₁ = Metric_TL - Sigma_TL` where `Sigma_TL = [e₁, e₂]` and `Metric_TL = {e₁, e₂}`,
  proving corner annihilation `e₁ Sigma_TL e₁ = e₂ Sigma_TL e₂ = 0` and Jordan compression
  `e₁ Metric_TL e₁ = 2 τ e₁`, `e₂ Metric_TL e₂ = 2 τ e₂`.
* `TL3` (`universal_halmos_two_projection_and_quantum_tripotency`):
  **Universal Halmos–Temperley–Lieb identities** — for *any* two idempotents
  `e₁² = e₁, e₂² = e₂` in *any* associative ring `B` (with zero extra hypotheses), let
  `H = e₁ - e₂` and `Sigma_TL = [e₁, e₂]`:
  1. **Universal Quartic-Tripotency Defect Law:** `(e₁ - e₂)⁴ - (e₁ - e₂)² = [e₁, e₂]²`
     (`H⁴ - H² = Sigma_TL²`), proving that the exact obstruction to `H⁴ = H²` is the square of
     the non-commutative braid commutator `[e₁, e₂]²`!
  2. **Universal Anticommutativity (`Cl(1,1)` Braid Pair):** `{H, Sigma_TL} = H Sigma_TL + Sigma_TL H = 0`.
  3. **Universal Centrality of `H²` and `Sigma_TL²`:** `[e₁, H²] = [e₂, H²] = [e₁, Sigma_TL²] = [e₂, Sigma_TL²] = 0`.
  4. **Quantum-Deformed Tripotent Modular Law under Temperley–Lieb (`e₁ e₂ e₁ = τ e₁, e₂ e₁ e₂ = τ e₂`):**
     `H³ = (1 - τ) H` and `Sigma_TL² = -τ H²`.
* `TL4` (`peirce_inner_derivation_shell_weights`):
  On orthogonal horizons, `H = P₁ - P₂` has `H³ = H`; the named Peirce shells are eigenvectors
  of the inner derivation `ad_H`. This is a finite ring identity, not a crossed-product result.
* `TL5` (`cyclic_trace_vanishes_on_peirce_shells`):
  For any supplied cyclic
  trace `tr : CyclicTrace B M`, because `N_{+1} = [H, N_{+1}]`, `N_{-1} = [N_{-1}, H]`,
  `N_{+2} = [P₁, N_{+2}]`, and `N_{-2} = [N_{-2}, P₁]`, all four off-diagonal modular shells
  have zero trace, and the full Para-Kähler metric
  has the same trace as its step-1 component.
* `waist_commutes_with_horizon_difference` derives commutation with `P₁ - P₂` from the two
  horizon-commutation results in the existing IKKT owner.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.TemperleyLiebCrossedProductAndGrandUnificationPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IKKTLaxHolographicDarkCondensatePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

universe u v
variable {B : Type u} [Ring B]

/-! ### Temperley–Lieb collapse under a commutativity hypothesis -/

/-- **Node `𝔗𝔏₁` (`temperley_lieb_commutative_collapse`)**:
In any associative ring `B`, if two Temperley–Lieb idempotents `e₁² = e₁, e₂² = e₂` satisfying
`e₁ e₂ e₁ = τ e₁` and `e₂ e₁ e₂ = τ e₂` commute (`e₁ e₂ = e₂ e₁`), then:
1. `e₁ * e₂ = τ * e₁`,
2. `e₁ * e₂ = τ * e₂`,
3. `(τ - τ²) * e₁ = 0` and `(τ - τ²) * e₂ = 0`,
4. `τ * (e₁ - e₂) = 0`.
Thus if `τ` is a unit and `e₁ ≠ e₂`, the commutativity hypothesis is impossible. This is a
ring-level implication; no Jones-index interpretation is part of this theorem. -/
theorem temperley_lieb_commutative_collapse
    (e1 e2 tau : B)
    (h_idem1 : e1 * e1 = e1)
    (h_idem2 : e2 * e2 = e2)
    (h_TL1 : e1 * e2 * e1 = tau * e1)
    (h_TL2 : e2 * e1 * e2 = tau * e2)
    (h_commutative_flaw : e1 * e2 = e2 * e1) :
    e1 * e2 = tau * e1 ∧
    e1 * e2 = tau * e2 ∧
    (tau - tau * tau) * e1 = 0 ∧
    (tau - tau * tau) * e2 = 0 ∧
    tau * (e1 - e2) = 0 := by
  have h_step1 : e1 * e2 = tau * e1 := by
    calc e1 * e2 = (e1 * e1) * e2 := by rw [h_idem1]
      _ = e1 * (e1 * e2)          := by rw [mul_assoc]
      _ = e1 * (e2 * e1)          := by rw [h_commutative_flaw]
      _ = e1 * e2 * e1            := by rw [← mul_assoc]
      _ = tau * e1                := h_TL1
  have h_step2 : e1 * e2 = tau * e2 := by
    calc e1 * e2 = e2 * e1        := h_commutative_flaw
      _ = (e2 * e2) * e1          := by rw [h_idem2]
      _ = e2 * (e2 * e1)          := by rw [mul_assoc]
      _ = e2 * (e1 * e2)          := by rw [← h_commutative_flaw]
      _ = e2 * e1 * e2            := by rw [← mul_assoc]
      _ = tau * e2                := h_TL2
  have h_step3 : (tau - tau * tau) * e1 = 0 := by
    have h_eq : tau * e1 = (tau * tau) * e1 := by
      calc tau * e1 = e1 * e2    := by rw [← h_step1]
        _ = e1 * (e2 * e2)       := by rw [h_idem2]
        _ = (e1 * e2) * e2       := by rw [← mul_assoc]
        _ = (tau * e1) * e2      := by rw [h_step1]
        _ = tau * (e1 * e2)      := by rw [mul_assoc]
        _ = tau * (tau * e1)     := by rw [h_step1]
        _ = (tau * tau) * e1     := by rw [← mul_assoc]
    calc (tau - tau * tau) * e1 = tau * e1 - (tau * tau) * e1 := by rw [sub_mul]
      _ = tau * e1 - tau * e1                                 := by rw [← h_eq]
      _ = 0                                                   := by abel
  have h_step4 : (tau - tau * tau) * e2 = 0 := by
    have h_eq : tau * e2 = (tau * tau) * e2 := by
      calc tau * e2 = e1 * e2    := by rw [← h_step2]
        _ = (e1 * e1) * e2       := by rw [h_idem1]
        _ = e1 * (e1 * e2)       := by rw [mul_assoc]
        _ = e1 * (tau * e2)      := by rw [h_step2]
        _ = e1 * (e1 * e2)       := by rw [← h_step2]
        _ = (e1 * e2) * e1       := by rw [h_commutative_flaw, ← mul_assoc, h_commutative_flaw]
        _ = (tau * e2) * e1      := by rw [h_step2]
        _ = tau * (e2 * e1)      := by rw [mul_assoc]
        _ = tau * (e1 * e2)      := by rw [← h_commutative_flaw]
        _ = tau * (tau * e2)     := by rw [h_step2]
        _ = (tau * tau) * e2     := by rw [← mul_assoc]
    calc (tau - tau * tau) * e2 = tau * e2 - (tau * tau) * e2 := by rw [sub_mul]
      _ = tau * e2 - tau * e2                                 := by rw [← h_eq]
      _ = 0                                                   := by abel
  have h_step5 : tau * (e1 - e2) = 0 := by
    rw [mul_sub, ← h_step1, ← h_step2, sub_self]
  exact ⟨h_step1, h_step2, h_step3, h_step4, h_step5⟩

/-! ### Noncommutative Temperley–Lieb commutator and anticommutator identities -/

/-- Temperley–Lieb spin curvature bivector `Σ_TL = [e₁, e₂]`. -/
def Sigma_TL (e1 e2 : B) : B := comm e1 e2

/-- Temperley–Lieb metric anticommutator `Metric_TL = {e₁, e₂}`. -/
def Metric_TL (e1 e2 : B) : B := anticomm e1 e2

/-- **Node `𝔗𝔏₂` (`non_commutative_temperley_lieb_curvature`)**:
When the boundary crossings do not commute (`[e₁, e₂] ≠ 0`), they split into the metric
anticommutator `Metric_TL = {e₁, e₂}` and the Temperley–Lieb spin curvature `Sigma_TL = [e₁, e₂]`,
with `e₁ Sigma_TL e₁ = e₂ Sigma_TL e₂ = 0` and `e₁ Metric_TL e₁ = 2 τ e₁`, `e₂ Metric_TL e₂ = 2 τ e₂`. -/
theorem non_commutative_temperley_lieb_curvature
    (e1 e2 tau : B)
    (h_idem1 : e1 * e1 = e1)
    (h_idem2 : e2 * e2 = e2)
    (h_TL1 : e1 * e2 * e1 = tau * e1)
    (h_TL2 : e2 * e1 * e2 = tau * e2) :
    let sTL := Sigma_TL e1 e2
    let mTL := Metric_TL e1 e2
    2 • (e1 * e2) = mTL + sTL ∧
    2 • (e2 * e1) = mTL - sTL ∧
    e1 * sTL * e1 = 0 ∧
    e2 * sTL * e2 = 0 ∧
    e1 * mTL * e1 = 2 • (tau * e1) ∧
    e2 * mTL * e2 = 2 • (tau * e2) := by
  have h1' : e1 * (e1 * e2) = e1 * e2 := by rw [← mul_assoc, h_idem1]
  have h2' : e2 * (e2 * e1) = e2 * e1 := by rw [← mul_assoc, h_idem2]
  dsimp only [Sigma_TL, Metric_TL, comm, anticomm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring
  · noncomm_ring
  · calc (e1 * (e1 * e2 - e2 * e1)) * e1
      _ = (e1 * (e1 * e2)) * e1 - (e1 * e2 * e1) * e1 := by noncomm_ring
      _ = (e1 * e2 * e1) - (e1 * e2 * e1) * e1        := by rw [h1', mul_assoc]
      _ = tau * e1 - tau * (e1 * e1)                  := by rw [h_TL1, mul_assoc]
      _ = 0                                           := by rw [h_idem1, sub_self]
  · calc (e2 * (e1 * e2 - e2 * e1)) * e2
      _ = (e2 * e1 * e2) * e2 - (e2 * (e2 * e1)) * e2 := by noncomm_ring
      _ = (e2 * e1 * e2) * e2 - (e2 * e1 * e2)        := by rw [h2', mul_assoc]
      _ = tau * (e2 * e2) - tau * e2                  := by rw [h_TL2, mul_assoc]
      _ = 0                                           := by rw [h_idem2, sub_self]
  · calc (e1 * (e1 * e2 + e2 * e1)) * e1
      _ = (e1 * (e1 * e2)) * e1 + (e1 * e2 * e1) * e1 := by noncomm_ring
      _ = (e1 * e2 * e1) + (e1 * e2 * e1) * e1        := by rw [h1', mul_assoc]
      _ = tau * e1 + tau * (e1 * e1)                  := by rw [h_TL1, mul_assoc]
      _ = 2 • (tau * e1)                              := by rw [h_idem1, two_nsmul]
  · calc (e2 * (e1 * e2 + e2 * e1)) * e2
      _ = (e2 * e1 * e2) * e2 + (e2 * (e2 * e1)) * e2 := by noncomm_ring
      _ = (e2 * e1 * e2) * e2 + (e2 * e1 * e2)        := by rw [h2', mul_assoc]
      _ = tau * (e2 * e2) + tau * e2                  := by rw [h_TL2, mul_assoc]
      _ = 2 • (tau * e2)                              := by rw [h_idem2, two_nsmul]

/-! ### Universal two-idempotent defect identities -/

/-- **Node `𝔗𝔏₃a` (`universal_halmos_two_projection_defect_and_clifford_pair`)**:
For *any* two idempotents `e₁² = e₁, e₂² = e₂` in *any* associative ring `B` (with zero extra
assumptions), let `H = e₁ - e₂` and `Sigma_TL = [e₁, e₂]`:
1. `H² + Metric_TL e1 e2 = e1 + e2`,
2. **Universal Quartic-Tripotency Defect Law:** `H⁴ - H² = Sigma_TL²` (`(e₁ - e₂)⁴ - (e₁ - e₂)² = [e₁, e₂]²`),
3. **Universal Clifford Anticommutativity:** `{H, Sigma_TL} = H * Sigma_TL + Sigma_TL * H = 0`,
4. **Universal Centrality:** `[e₁, H²] = 0`, `[e₂, H²] = 0`, `[e₁, Sigma_TL²] = 0`, `[e₂, Sigma_TL²] = 0`. -/
theorem universal_halmos_two_projection_defect_and_clifford_pair
    (e1 e2 : B)
    (h1 : e1 * e1 = e1) (h2 : e2 * e2 = e2) :
    let H   := e1 - e2
    let H2  := H * H
    let H4  := H2 * H2
    let sTL := Sigma_TL e1 e2
    let mTL := Metric_TL e1 e2
    H2 + mTL = e1 + e2 ∧
    H4 - H2 = sTL * sTL ∧
    anticomm H sTL = 0 ∧
    comm e1 H2 = 0 ∧
    comm e2 H2 = 0 ∧
    comm e1 (sTL * sTL) = 0 ∧
    comm e2 (sTL * sTL) = 0 := by
  have h1' : ∀ W : B, e1 * (e1 * W) = e1 * W := fun W => by rw [← mul_assoc, h1]
  have h2' : ∀ W : B, e2 * (e2 * W) = e2 * W := fun W => by rw [← mul_assoc, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Sigma_TL, Metric_TL, comm, anticomm]
    simp only [sub_mul, mul_sub, mul_assoc, h1, h2, h1', h2']
    abel

/-- **Node `𝔗𝔏₃b` (`temperley_lieb_quantum_deformed_tripotent_modular_law`)**:
When `e₁² = e₁, e₂² = e₂` satisfy the Temperley–Lieb relations `e₁ e₂ e₁ = τ e₁` and
`e₂ e₁ e₂ = τ e₂` (with `τ` commuting with `e₁, e₂`), the difference `H = e₁ - e₂` and
curvature `Sigma_TL = [e₁, e₂]` obey the **Quantum-Deformed Tripotent Modular Law**:
1. `H * (H * H) = (1 - τ) * H` (`H³ = (1 - τ) H`),
2. `Sigma_TL * Sigma_TL = - (τ * (H * H))` (`[e₁, e₂]² = -τ H²`),
3. `(H * H) * (H * H) = (1 - τ) * (H * H)` (`H⁴ = (1 - τ) H²`). -/
theorem temperley_lieb_quantum_deformed_tripotent_modular_law
    (e1 e2 tau : B)
    (h1 : e1 * e1 = e1) (h2 : e2 * e2 = e2)
    (h_TL1 : e1 * e2 * e1 = tau * e1)
    (h_TL2 : e2 * e1 * e2 = tau * e2)
    (h_tau1 : e1 * tau = tau * e1)
    (h_tau2 : e2 * tau = tau * e2) :
    let H   := e1 - e2
    let H2  := H * H
    let sTL := Sigma_TL e1 e2
    H * H2 = (1 - tau) * H ∧
    sTL * sTL = - (tau * H2) ∧
    H2 * H2 = (1 - tau) * H2 := by
  intro H H2 sTL
  have h1' : ∀ W : B, e1 * (e1 * W) = e1 * W := fun W => by rw [← mul_assoc, h1]
  have h2' : ∀ W : B, e2 * (e2 * W) = e2 * W := fun W => by rw [← mul_assoc, h2]
  have h_TL1_assoc : e1 * (e2 * e1) = tau * e1 := by rw [← mul_assoc, h_TL1]
  have h_TL2_assoc : e2 * (e1 * e2) = tau * e2 := by rw [← mul_assoc, h_TL2]
  have h_tau1' : ∀ W : B, e1 * (tau * W) = tau * (e1 * W) := fun W => by
    rw [← mul_assoc, h_tau1, mul_assoc]
  have h_tau2' : ∀ W : B, e2 * (tau * W) = tau * (e2 * W) := fun W => by
    rw [← mul_assoc, h_tau2, mul_assoc]
  have h_H3 : H * H2 = (1 - tau) * H := by
    dsimp only [H, H2]
    simp only [sub_mul, mul_sub, one_mul, h1, h2, h1', h2', h_TL1_assoc, h_TL2_assoc]
    abel
  have h_sTL2 : sTL * sTL = - (tau * H2) := by
    dsimp only [sTL, Sigma_TL, comm, H2, H]
    simp only [sub_mul, mul_sub, mul_assoc, h1, h2, h1', h2',
               h_TL1_assoc, h_TL2_assoc, h_tau1', h_tau2']
    abel
  have h_H4 : H2 * H2 = (1 - tau) * H2 := by
    calc H2 * H2 = (H * H2) * H := by dsimp only [H2]; noncomm_ring
      _ = ((1 - tau) * H) * H   := by rw [h_H3]
      _ = (1 - tau) * H2        := by dsimp only [H2]; noncomm_ring
  exact ⟨h_H3, h_sTL2, h_H4⟩

/-! ### Inner-derivation weights on Peirce shells -/

/-- For orthogonal idempotents, the inner derivation `ad_H` acts on the explicitly defined
Peirce shells with weights `±1` and `±2`. This is not a crossed-product construction. -/
lemma peirce_inner_derivation_shell_weights
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let H      := H_weyl P1 P2
    let N_pos1 := N_pos1_3 P1 P2 X
    let N_neg1 := N_neg1_3 P1 P2 Y
    let v1     := V1_weyl3 P1 P2 X Y
    H * (H * H) = H ∧
    comm H N_pos1 = N_pos1 ∧
    comm H N_neg1 = - N_neg1 ∧
    comm H (N_pos1 * N_pos1) = 2 • (N_pos1 * N_pos1) ∧
    comm H (N_neg1 * N_neg1) = - (2 • (N_neg1 * N_neg1)) ∧
    comm H v1 = 0 := by
  have h7 := node7_log_radial_modular_time_and_five_graded_weyl_invariance P1 P2 X Y h1 h2 h12 h21
  exact ⟨h7.2.1, h7.2.2.2.2.1, h7.2.2.2.2.2.1,
         h7.2.2.2.2.2.2.1, h7.2.2.2.2.2.2.2.1, h7.2.2.2.2.2.2.2.2.1⟩

/-! ### Cyclic-trace vanishing on commutator-supported Peirce shells -/

/-- For a supplied cyclic trace `tr : CyclicTrace B M` (`[AddCommGroup M]`) on the 3-horizon
system `(P₁, P₀, P₂)`:
1. The step-1 waves are exact modular commutators:
   `N_{+1} = [H, N_{+1}]` and `N_{-1} = [N_{-1}, H]`,
2. The step-2 contact shells are exact horizon commutators:
   `N_{+2} = [P₁, N_{+2}]` and `N_{-2} = [N_{-2}, P₁]`,
3. Consequently, **all four commutator-supported Peirce shells have zero trace**
   (`tr(N_{+1}) = 0`, `tr(N_{-1}) = 0`, `tr(N_{+2}) = 0`, `tr(N_{-2}) = 0`),
4. **Trace Equality under the supplied cyclic trace:** The trace of the full 5-entry Para-Kähler metric `V_PK`
   equals the trace of the modular-invariant step-1 metric `V₁`:
   `tr.tr (V_PK3 P1 P2 X Y) = tr.tr (V1_weyl3 P1 P2 X Y)`. -/
lemma cyclic_trace_vanishes_on_peirce_shells
    {M : Type v} [AddCommGroup M] (tr : CyclicTrace B M)
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let H   := H_weyl P1 P2
    let np1 := N_pos1_3 P1 P2 X
    let nm1 := N_neg1_3 P1 P2 Y
    let np2 := np1 * np1
    let nm2 := nm1 * nm1
    let v1  := V1_weyl3 P1 P2 X Y
    let vPK := V_PK3 P1 P2 X Y
    np1 = comm H np1 ∧
    nm1 = comm nm1 H ∧
    np2 = comm P1 np2 ∧
    nm2 = comm nm2 P1 ∧
    tr.tr np1 = 0 ∧
    tr.tr nm1 = 0 ∧
    tr.tr np2 = 0 ∧
    tr.tr nm2 = 0 ∧
    tr.tr vPK = tr.tr v1 := by
  intro H np1 nm1 np2 nm2 v1 vPK
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0     := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0     := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h_np1 : np1 = comm H np1 := by
    dsimp only [np1, H, H_weyl, N_pos1_3, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_nm1 : nm1 = comm nm1 H := by
    dsimp only [nm1, H, H_weyl, N_neg1_3, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_np2 : np2 = comm P1 np2 := by
    dsimp only [np2, np1, N_pos1_3, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_nm2 : nm2 = comm nm2 P1 := by
    dsimp only [nm2, nm1, N_neg1_3, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_np1 : tr.tr np1 = 0 := by rw [h_np1]; exact trace_comm_zero tr H np1
  have h_tr_nm1 : tr.tr nm1 = 0 := by rw [h_nm1]; exact trace_comm_zero tr nm1 H
  have h_tr_np2 : tr.tr np2 = 0 := by rw [h_np2]; exact trace_comm_zero tr P1 np2
  have h_tr_nm2 : tr.tr nm2 = 0 := by rw [h_nm2]; exact trace_comm_zero tr nm2 P1
  have h_vPK_eq : vPK = v1 + np2 + nm2 :=
    (fundamental_weyl_to_parakahler_metric_bridge P1 P2 X Y h1 h2 h12 h21).1
  have h_tr_vPK : tr.tr vPK = tr.tr v1 := by
    rw [h_vPK_eq, map_add, map_add, h_tr_np2, h_tr_nm2, add_zero, add_zero]
  exact ⟨h_np1, h_nm1, h_np2, h_nm2,
         h_tr_np1, h_tr_nm1, h_tr_np2, h_tr_nm2, h_tr_vPK⟩

/-! ### A focused Peirce consequence for the dark-waist corner -/

/-- Dark-waist corner element `P₀ C P₀`, where `P₀ = 1 - P₁ - P₂`. -/
def V_waist (P1 P2 C : B) : B := (1 - P1 - P2) * C * (1 - P1 - P2)

/-- If `P₁` and `P₂` are orthogonal idempotents, every element supported in their
complementary Peirce corner commutes with their difference. The proof uses the two
separate corner-commutation results from the IKKT owner and additivity of commutators. -/
lemma waist_commutes_with_horizon_difference
    (P1 P2 C : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    comm (H_weyl P1 P2) (V_waist P1 P2 C) = 0 := by
  have hWaist := dark_matter_waist_condensate_and_constructive_temperley_lieb
    P1 P2 P1 P2 0 0 C h1 h2 h12 h21 h1 h2
  have hP1 : comm P1 (V_waist P1 P2 C) = 0 := by
    simpa [V_waist, P0_waist] using hWaist.2.1
  have hP2 : comm P2 (V_waist P1 P2 C) = 0 := by
    simpa [V_waist, P0_waist] using hWaist.2.2.1
  have hCommSub :
      comm (P1 - P2) (V_waist P1 P2 C) =
        comm P1 (V_waist P1 P2 C) - comm P2 (V_waist P1 P2 C) := by
    unfold comm
    noncomm_ring
  change comm (P1 - P2) (V_waist P1 P2 C) = 0
  rw [hCommSub, hP1, hP2]
  simp

end InfoGeometry.OperatorAlgebra.PeirceSpine.TemperleyLiebCrossedProductAndGrandUnificationPoset
