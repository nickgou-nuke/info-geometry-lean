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

end OperatorParaKahlerAmariMaurerCartanBridge

end InfoGeometry.Canonical.ArnoldParaKahlerBCFW
