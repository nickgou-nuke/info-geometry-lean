/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.CayleyDicksonEmbedding

noncomputable section

namespace InfoGeometry.Canonical.ArnoldParaKahlerBCFW

open InfoGeometry.Canonical.ArnoldCohenBCFWBridge
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
open InfoGeometry.Canonical.AlbertCayleyDickson

set_option linter.unusedVariables false

/-!
# Arnold-Form Identity and Algebraic Consequences

This module specializes abstract para-complex and exterior-form identities.
It does not construct a scattering amplitude, an on-shell shift, or a physical
residue. Historical API names refer only to the propositions in their Lean types:

1. **Abstract three-term identity**:
   The coefficient relation in `LogarithmicOneFormData` implies the cyclic
   exterior-form identity.

2. **Arnold-shaped relation**:
   This equation is abstract; no Orlik–Solomon quotient or Maurer-Cartan
   flatness is asserted here.

3. **Algebraic rearrangement (not physical on-shell factorization)**:
   The cyclic identity is rearranged into an equality of exterior-form
   products; no physical residue is represented.

4. **Supplied square-zero equations ($S_\pm^2 = 0$)**:
   These are explicit premises when transported; they are not inferred from
   Plücker or Minkowski mass-shell data.

5. **Élie Cartan Doubling Invariance**:
   The canonical inclusion $\operatorname{cdEmbed}$ into the split Cayley-Dickson tower
   preserves multiplication and transports square-zero equations.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The abstract coefficient relation yields the cyclic exterior-form identity. -/
theorem arnold_cohen_maurer_cartan_flatness
    (alg : ExteriorFormAlgebra (R := R) M)
    (dz : ℕ → M) (data : LogarithmicOneFormData (R := R) dz) (i j k : ℕ) :
    alg.wedge (data.form dz i j) (data.form dz j k) +
    alg.wedge (data.form dz j k) (data.form dz k i) +
    alg.wedge (data.form dz k i) (data.form dz i j) = 0 :=
  maurer_cartan_arnold_resolution alg dz data i j k

/-- Theorem 2 (Algebraic rearrangement of the Arnold-shaped identity):
    This is an equality in the abstract exterior-form carrier, not a physical
    residue factorization:
      $\omega_{ij} \wedge \omega_{jk} = - (\omega_{jk} \wedge \omega_{ki} + \omega_{ki} \wedge \omega_{ij})$. -/
theorem bcfw_collinear_factorization
    (alg : ExteriorFormAlgebra (R := R) M)
    (dz : ℕ → M) (data : LogarithmicOneFormData (R := R) dz) (i j k : ℕ) :
    alg.wedge (data.form dz i j) (data.form dz j k) =
      - (alg.wedge (data.form dz j k) (data.form dz k i) +
         alg.wedge (data.form dz k i) (data.form dz i j)) :=
  maurer_cartan_bcfw_factorization alg dz data i j k

/-- Alternation makes each abstract form generator square to zero. -/
theorem log_form_nilpotent
    (alg : ExteriorFormAlgebra (R := R) M)
    (dz : ℕ → M) (data : LogarithmicOneFormData (R := R) dz) (i j : ℕ) :
    alg.wedge (data.form dz i j) (data.form dz i j) = 0 :=
  log_form_wedge_self alg dz data i j

/-- 🏆 THEOREM 5 (Split Cayley-Dickson Preservation of Chiral Nilpotency):
    Under the Élie Cartan / Cayley-Dickson doubling embedding `cdEmbed`,
    the supplied square-zero elements remain square-zero in the doubled split algebra.
    This transport statement does not identify them with on-shell generators:
      $\operatorname{cdEmbed}(S_\pm)^2 = 0$. -/
theorem cdEmbed_preserves_chiral_nilpotency [StarRing R]
    (S_plus S_minus : R) (h_plus : S_plus * S_plus = 0)
    (h_minus : S_minus * S_minus = 0) :
    AlbertStep.mul (cdEmbed (γ := (1 : R)) S_plus) (cdEmbed (γ := (1 : R)) S_plus) = 0 ∧
    AlbertStep.mul (cdEmbed (γ := (1 : R)) S_minus) (cdEmbed (γ := (1 : R)) S_minus) = 0 := by
  constructor
  · rw [← cdEmbed_mul, h_plus, cdEmbed_zero]
  · rw [← cdEmbed_mul, h_minus, cdEmbed_zero]

section OperatorParaKahlerAmariMaurerCartanBridge

open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- **Theorem 6 (Operator Para-Kähler, Amari-Chentsov Cubic Skewness, & Maurer-Cartan Chiral Anomaly Master Bridge)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`) and commutative scalar ring $R$ (`[CommRing R]`):
    1. Fundamental Para-Kähler Compatibility & Chiral Anomaly Residue:
       $\Gamma * g(v, w) = \omega(v, w)$, $\Gamma * \omega(v, w) = g(v, w)$, and
       $\mathrm{opZornTrace}(\omega(v, w)) = w \cdot v - v \cdot w$.
    2. Amari-Chentsov Cubic Skewness Tensor:
       $[[L_-(w), L_+(v)], L_+(v)] = L_+\!\bigl((v \cdot w) \cdot_L v + v \cdot_R (w \cdot v)\bigr)$.
    3. Maurer-Cartan Grade Decomposition & Anomaly-Driven Grade-3 Square:
       $\Theta(v_1, v_2) = L_+(v_2 - v_1) - L_-(v_1 \times_{\mathrm{skew}} v_2)$ and
       $\Theta(v_1, v_2) * \Theta(v_1, v_2) = \langle (v_2 - v_1) \cdot (v_1 \times_{\mathrm{skew}} v_2), 0, 0, (v_1 \times_{\mathrm{skew}} v_2) \cdot (v_2 - v_1) \rangle$.
    4. Commutative Vanishing vs. Noncommutative Self-Associator Flow:
       Over any commutative ring $R$, $\Theta(u_1, u_2) * \Theta(u_1, u_2) = 0$ identically, whereas over
       a noncommutative ring $A$, the self-associator $[\Theta, \Theta, \Theta]$ equals the anomaly-driven
       Heisenberg-Dirac commutator $[D_{\mathrm{anom}}, \Theta]$. -/
theorem operator_paraKahler_amari_maurerCartan_master_bridge
    (u₁ u₂ : OpVec3 R) (v w v₁ v₂ : OpVec3 A) :
    let g := opParaKahlerMetric v w
    let ω := opParaKahlerSymplectic v w
    let Θ := opMaurerCartanForm v₁ v₂
    let Δv := v₂ - v₁
    let τ₁₂ := OpVec3.skewCross v₁ v₂
    let D_anom := opCartanDiag (OpVec3.dot Δv τ₁₂) (OpVec3.dot τ₁₂ Δv)
    (opZornGamma * g = ω ∧
     opZornGamma * ω = g ∧
     opZornTrace ω = OpVec3.dot w v - OpVec3.dot v w) ∧
    opCommutator (opCommutator (opLightconeRayMinus w) (opLightconeRayPlus v)) (opLightconeRayPlus v) =
      opLightconeRayPlus
        (OpVec3.leftScale (OpVec3.dot v w) v + OpVec3.rightScale v (OpVec3.dot w v)) ∧
    (Θ = opLightconeRayPlus Δv - opLightconeRayMinus τ₁₂ ∧
     Θ * Θ = D_anom) ∧
    (opMaurerCartanForm u₁ u₂ * opMaurerCartanForm u₁ u₂ = 0 ∧
     opAssociator Θ Θ Θ = opCommutator D_anom Θ) := by
  have hPK := opParaKahler_triplet_compatibility_and_anomaly_residue v w
  have hAC := amariChentsov_cubic_skewness_tensor v w
  have hMC := opMaurerCartanForm_grade_hierarchy_and_anomaly_generation v₁ v₂
  have hComm := opMaurerCartan_commutative_vanishing_and_dual_hierarchy u₁ u₂ v w w
  have hFlow := opMaurerCartan_cube_and_self_associator_emergent_flow v₁ v₂ v w w w
  exact ⟨⟨hPK.2.2.1, hPK.2.2.2.1, hPK.2.2.2.2.1⟩,
         hAC.1,
         ⟨hMC.1, hMC.2.1⟩,
         ⟨hComm.1, hFlow.2.2.1⟩⟩

/-- **Theorem 7 (Nucleus Leibniz Derivations, BKM Modular Metric, Erlangen Flag States, Killing Lie Algebra, & Noether Supercharge Master Bridge)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`):
    1. Exact Leibniz Product Rule for Nucleus Modular Derivations on Opposite-Chirality Lightcone Rays:
       $\delta_{\rho_+, \rho_-}(L_+(v) * L_-(w)) = \delta_{\rho_+, \rho_-}(L_+(v)) * L_-(w) + L_+(v) * \delta_{\rho_+, \rho_-}(L_-(w))$.
    2. BKM Modular Metric & KMS Leibniz Conservation:
       $G_{\mathrm{BKM}}(\rho; v, w) + G_{\mathrm{BKM}}^{\mathrm{dual}}(\rho; v, w) = \delta_{\rho_+, \rho_-}(g(v, w))$.
    3. Erlangen Homogeneous Flag State Idempotence & Symmetry Group Action:
       $\Pi_{\mathrm{hom}}(v) * \Pi_{\mathrm{hom}}(v) = \Pi_{\mathrm{hom}}(v)$ and
       $e_{11} * \bigl((U_+(v_1) * \Pi_{\mathrm{hom}}(v_2)) * U_+(-v_1)\bigr) = \Pi_{\mathrm{hom}}(v_1 + v_2)$.
    4. Killing Lie Algebra Homomorphism & Noether Supercharge Conservation:
       $[\delta_{D_1}, \delta_{D_2}](X) = \delta_{[D_1, D_2]}(X)$ and
       $[H_{\mathrm{mod}}(v, w), J(v, w)] = [J(v, w), J(v, w), J(v, w)]$. -/
theorem operator_bkm_erlangen_killing_noether_master_bridge
    (ρ_plus ρ_minus σ_plus σ_minus u q : A)
    (v w v₁ v₂ : OpVec3 A) (X Y : OpZornMatrix A) :
    let D₁ := opCartanDiag ρ_plus ρ_minus
    let D₂ := opCartanDiag σ_plus σ_minus
    let Lp := opLightconeRayPlus v
    let Lm := opLightconeRayMinus w
    let H_mod := emergentModularHamiltonian v w
    let J := opKasparovZornJ v w
    opModularDeriv ρ_plus ρ_minus (Lp * Lm) =
      opModularDeriv ρ_plus ρ_minus Lp * Lm + Lp * opModularDeriv ρ_plus ρ_minus Lm ∧
    opBKMMetric ρ_plus ρ_minus v w + opBKMMetricDual ρ_plus ρ_minus v w =
      opModularDeriv ρ_plus ρ_minus (opParaKahlerMetric v w) ∧
    (homogeneousFlagState v * homogeneousFlagState v = homogeneousFlagState v ∧
     opPeircePlus * ((opUnipotentUpper v₁ * homogeneousFlagState v₂) * opUnipotentUpper (-v₁)) =
       homogeneousFlagState (v₁ + v₂)) ∧
    opCommutator D₁ (opCommutator D₂ X) - opCommutator D₂ (opCommutator D₁ X) =
      opCommutator (opCommutator D₁ D₂) X ∧
    (opCommutator H_mod (Lp * Lm) = opCommutator H_mod Lp * Lm + Lp * opCommutator H_mod Lm ∧
     opCommutator H_mod J = opAssociator J J J) := by
  have hLeib := opModularDeriv_nucleus_and_exact_leibniz_rule (opCartanDiag ρ_plus ρ_minus) X Y v w ρ_plus ρ_minus
  have hBKM := opBKMMetric_coords_and_kms_leibniz_conservation ρ_plus ρ_minus v w X Y
  have hFlag := homogeneousFlagState_orbit_idempotence_and_group_action v v₁ v₂
  have hKill := killing_nucleus_derivation_lie_homomorphism ρ_plus ρ_minus σ_plus σ_minus X
  have hNoether := noetherSupercharges_emergent_modular_hamiltonian_and_conservation v w u q
  exact ⟨hLeib.2.2.2.2.1,
         hBKM.2.1,
         ⟨hFlag.2.2.1, hFlag.2.2.2.2⟩,
         hKill.2,
         ⟨hNoether.2.2.2.1, hNoether.2.2.2.2.1⟩⟩

/-- **Theorem 8 (5-Graded Kantor-Koecher-Tits Contact Structure & Associative Heisenberg Nilradicals Master Bridge)**:
    Over ANY noncommutative operator ring $A$ (`[Ring A]`):
    1. Step-2 Heisenberg-Contact Grading & Exact Termination at Grade $\pm 2$:
       $E_{+1}(y_1, z_1) * E_{+1}(y_2, z_2) = E_{+2}(\omega_\perp(y_1, z_1; y_2, z_2))$ and
       $E_{+1}(y, z) * E_{+2}(\xi) = 0$.
    2. Associativity of the 5-Graded Positive Nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$:
       $\mathrm{opAssociator}\;N_1\;N_2\;N_3 = 0$.
    3. Associative Heisenberg Group Law & Exact Two-Sided Group Inversion on $\exp(\mathcal{N}_+)$:
       $H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2) = H_+(y_1 + y_2, z_1 + z_2, \xi_1 + \xi_2 + \omega_\perp(y_1, z_1; y_2, z_2))$,
       $\mathrm{opAssociator}\;H_1\;H_2\;H_3 = 0$, and $H_1 * H_+(-y_1, -z_1, -\xi_1) = 1$.
    4. Opposite-Grade Contact Couplings into $\mathcal{G}_0$ & Contact Adjoint Lowering $\mathcal{G}_{+1} \times \mathcal{G}_{-2} \to \mathcal{G}_{-1}$:
       $E_{-2}(\eta) * E_{+2}(\xi) = \mathrm{opGradeZero}\;(-\eta \xi)\;0$ and
       $E_{+1}(y, z) * E_{-2}(\eta) = E_{-1}(z \eta + \eta z, -(y \eta + \eta y))$. -/
theorem operator_five_graded_kantor_koecher_contact_master_bridge
    (y z y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ ξ η : A) :
    let N₁ := opHeisenbergNilPlus y₁ z₁ ξ₁
    let N₂ := opHeisenbergNilPlus y₂ z₂ ξ₂
    let N₃ := opHeisenbergNilPlus y₃ z₃ ξ₃
    let H₁ := opHeisenbergGroupPlus y₁ z₁ ξ₁
    let H₂ := opHeisenbergGroupPlus y₂ z₂ ξ₂
    let H₃ := opHeisenbergGroupPlus y₃ z₃ ξ₃
    (opGradePlus1 y₁ z₁ * opGradePlus1 y₂ z₂ =
       opGradePlus2 (opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
     opGradePlus1 y z * opGradePlus2 ξ = 0) ∧
    opAssociator N₁ N₂ N₃ = 0 ∧
    (H₁ * H₂ =
       opHeisenbergGroupPlus (y₁ + y₂) (z₁ + z₂)
         (ξ₁ + ξ₂ + opContactSymplecticForm y₁ z₁ y₂ z₂) ∧
     opAssociator H₁ H₂ H₃ = 0 ∧
     H₁ * opHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) = 1) ∧
    (opGradeMinus2 η * opGradePlus2 ξ = opGradeZero (-η * ξ) 0 ∧
     opGradePlus1 y z * opGradeMinus2 η =
       opGradeMinus1 (z * η + η * z) (-(y * η + η * y))) := by
  have hStep := fiveGraded_step_two_heisenberg_and_termination y z y₁ z₁ y₂ z₂ ξ ξ₁ ξ₂ η η η
  have hHeis := heisenbergNilPlus_associativity_and_group_law y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃
  have hOpp := fiveGraded_opposite_grade_couplings y z y₁ z₁ y₂ z₂ ξ η
  exact ⟨⟨hStep.1, hStep.2.2.1⟩,
         hHeis.2.2.2.1,
         ⟨hHeis.2.2.2.2.1, hHeis.2.2.2.2.2.1, hHeis.2.2.2.2.2.2⟩,
         ⟨hOpp.1, hOpp.2.2.2⟩⟩

end OperatorParaKahlerAmariMaurerCartanBridge

end InfoGeometry.Canonical.ArnoldParaKahlerBCFW
