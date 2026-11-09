/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineGranularExtensions
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineHistoricalFrontiers
import InfoGeometry.OperatorAlgebra.PeirceSpine.TemperleyLiebCrossedProductAndGrandUnificationPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.VietaSusyKatoDissipationAndGaloisGolayPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.YoshizawaGradientFlowInfoGeometryPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorMoebiusTetractysFlowPoset
import InfoGeometry.Canonical.Arxiv251107015ModelBundleSeibergWittenPoset

/-!
# Three-Horizon Differential Square, Peirce-Corner Invariance, Finite Peirce Dilation,
# and Double-Bracket / Para-Kähler / Jordan-Boundary Unification

This module proves three synthesis theorems over an associative ring `B` (`[Ring B]`):
1. `three_horizon_d_tot_sq_on_weyl_dilation`: relates the square of the defined three-horizon
   differential to the commutator of the finite Peirce metric and proves that adding the waist
   corner term leaves that commutator unchanged.
2. `de_haro_seiberg_witten_finite_peirce_dilation_bridge`: links the three-horizon Peirce corner
   decomposition, transitive Seiberg–Witten monodromy across the waist (`[N₁₀, N₀₂] = N₁₂`),
   monopole/dyon corner orthogonality (`Q₁₀ Q₂₀ = Q₂₀ Q₁₀ = 0`), a finite Peirce-corner dilation
   identity (`U(r, r⁻¹) U(r⁻¹, r) = 1` under stated corner equations), and cyclic-trace shell
   vanishing (`τ(V_PK3) = τ(V1_weyl3)`).
3. `master_global_peirce_spine_and_model_bundle_coagulation`: combines the three-horizon differential
   square, waist holonomy trace decomposition (`τ(V₀) = τ(Q₁₀) + τ(Q₂₀)`), Brockett–Souriau balance,
   Amari `α = ±1` exterior flatness, and Jordan-nilpotent boundary defect (`T² - T = N`).

BUCKET 1: PROVED FINITE/ALGEBRAIC IDENTITIES OVER `[Ring B]`
- `d_tot3`
- `three_horizon_d_tot_sq_on_weyl_dilation`

BUCKET 2: CONDITIONAL IDENTITIES FROM EXPLICIT PREMISES
- `de_haro_seiberg_witten_finite_peirce_dilation_bridge`
- `master_global_peirce_spine_and_model_bundle_coagulation`

BUCKET 3: OPEN CLOSURE DEBT
- Re-exported through `InfoGeometry.OperatorAlgebra.PeirceSpine`; continuum gradient-flow ODE
  integration and smooth moduli manifold blow-ups are not constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MasterPeirceSpineUnification

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IKKTLaxHolographicDarkCondensatePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineGranularExtensions
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineHistoricalFrontiers
open InfoGeometry.OperatorAlgebra.PeirceSpine.TemperleyLiebCrossedProductAndGrandUnificationPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.YoshizawaGradientFlowInfoGeometryPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorMoebiusTetractysFlowPoset
open InfoGeometry.Canonical.Arxiv251107015ModelBundleSeibergWittenPoset

universe u v
variable {B : Type u} [Ring B]
variable {M : Type v} [AddCommGroup M]

/-- Total 3-horizon odd differential `d_tot3 = d_out3 + d_in3 = d_sum3`. -/
def d_tot3 (P1 P2 X Y Z : B) : B :=
  d_sum3 P1 P2 X Y Z

/-- **3-Horizon Parabolic Differential Square Law (`three_horizon_d_tot_sq_on_weyl_dilation`)**:
On any two orthogonal idempotents `P₁² = P₁, P₂² = P₂, P₁ P₂ = P₂ P₁ = 0`, the total odd
differential `d_tot3` climbs the 5-graded tower starting from `H_weyl = P₁ - P₂` and its
square equals the commutator of the full 5-entry Para-Kähler metric `V_PK3` with `H_weyl`,
which remains invariant under adding the dark waist condensate `V_waist = P₀ C₀ P₀`:
1. `d_tot3(H_weyl) = -(N_{+1} - N_{-1})`,
2. `d_tot3(d_tot3(H_weyl)) = [V_PK3, H_weyl] = -2 • (N_{+1}² - N_{-1}²)`,
3. `[V_PK3 + V_waist, H_weyl] = [V_PK3, H_weyl] = d_tot3(d_tot3(H_weyl))`. -/
lemma three_horizon_d_tot_sq_on_weyl_dilation
    (P1 P2 X Y C0 : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let Hw  := H_weyl P1 P2
    let np1 := N_pos1_3 P1 P2 X
    let nm1 := N_neg1_3 P1 P2 Y
    let np2 := np1 * np1
    let nm2 := nm1 * nm1
    let vPK := V_PK3 P1 P2 X Y
    let vW  := V_waist P1 P2 C0
    d_tot3 P1 P2 X Y Hw = - (np1 - nm1) ∧
    d_tot3 P1 P2 X Y (d_tot3 P1 P2 X Y Hw) = comm vPK Hw ∧
    comm vPK Hw = - (2 • (np2 - nm2)) ∧
    comm (vPK + vW) Hw = comm vPK Hw := by
  intro Hw np1 nm1 np2 nm2 vPK vW
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0     := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0     := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h_step1 : d_tot3 P1 P2 X Y Hw = - (np1 - nm1) := by
    dsimp only [d_tot3, d_sum3, d_out3, d_in3, Psi_out3, Psi_in3, parConj3, S_par3, P_hor3,
                Hw, H_weyl, np1, nm1, N_pos1_3, N_neg1_3,
                ParabolicMaurerCartanAndBruhatTransportPoset.P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hP_hor := P_hor3_idem h1 h2 h12 h21
  have h_out := Psi_out3_eq_N_plus h1 h2 h12 h21 X Y
  have h_in  := Psi_in3_eq_N_minus h1 h2 h12 h21 X Y
  have h_step2 : d_tot3 P1 P2 X Y (d_tot3 P1 P2 X Y Hw) = comm vPK Hw := by
    dsimp only [d_tot3, d_sum3, d_out3, d_in3, parConj3, S_par3, vPK, V_PK3, comm, anticomm]
    rw [h_out, h_in]
    amari_peirce_nf hP_hor
  have h_vPK_eq : vPK = V1_weyl3 P1 P2 X Y + np2 + nm2 :=
    (fundamental_weyl_to_parakahler_metric_bridge P1 P2 X Y h1 h2 h12 h21).1
  have h7 := node7_log_radial_modular_time_and_five_graded_weyl_invariance P1 P2 X Y h1 h2 h12 h21
  have h_v1_0 : comm Hw (V1_weyl3 P1 P2 X Y) = 0 := h7.2.2.2.2.2.2.2.2.1
  have h_np2  : comm Hw np2 = 2 • np2 := h7.2.2.2.2.2.2.1
  have h_nm2  : comm Hw nm2 = - (2 • nm2) := h7.2.2.2.2.2.2.2.1
  have h_comm_Hw_vPK : comm Hw vPK = 2 • np2 - 2 • nm2 := by
    rw [h_vPK_eq, comm_add_right, comm_add_right, h_v1_0, h_np2, h_nm2]
    abel
  have h_skew : comm vPK Hw = - comm Hw vPK := by unfold comm; abel
  have h_step3 : comm vPK Hw = - (2 • (np2 - nm2)) := by
    rw [h_skew, h_comm_Hw_vPK]
    abel
  have h_vW : comm vW Hw = 0 := by
    dsimp only [vW, V_waist, Hw, H_weyl,
                ParabolicMaurerCartanAndBruhatTransportPoset.P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_add : comm (vPK + vW) Hw = comm vPK Hw + comm vW Hw := by
    unfold comm; noncomm_ring
  have h_step4 : comm (vPK + vW) Hw = comm vPK Hw := by
    rw [h_add, h_vW, add_zero]
  exact ⟨h_step1, h_step2, h_step3, h_step4⟩

/-- **De Haro Model Bundle and Finite Peirce Dilation Bridge
(`de_haro_seiberg_witten_finite_peirce_dilation_bridge`)**:
Links the three-horizon model-bundle corner decomposition, Seiberg–Witten transitive waist
monodromy and monopole/dyon corner orthogonality, the finite Peirce-corner dilation
`U(r, r⁻¹) = P₁ r P₁ + P₀ + P₂ r⁻¹ P₂`, and cyclic-trace shell vanishing:
1. `waistProjector P1 P2 = P0_waist P1 P2`,
2. Transitive monodromy `[N₁₀, N₀₂] = P₁ X P₀ Y P₂` and nilpotency `N₁₀² = N₀₂² = 0`,
3. Monopole/dyon corner orthogonality `Q₁₀ Q₂₀ = 0`, `Q₂₀ Q₁₀ = 0`, `[Q₁₀, Q₂₀] = 0`,
4. Corner conjugation: `U * (P₀ W P₀) * U⁻¹ = P₀ W P₀`,
   `U * (P₁ X P₀) * U⁻¹ = P₁ r P₁ X P₀`, `U * (P₁ Z P₂) * U⁻¹ = P₁ r P₁ Z P₂ r P₂`, and
   `U * U⁻¹ = 1` when `P₁ r P₁ r⁻¹ P₁ = P₁` and `P₂ r⁻¹ P₂ r P₂ = P₂`,
5. Cyclic-trace equality across dual holonomies `tr.tr Q₁₀ = tr.tr Q₀₁` and Para-Kähler metric
   trace collapse `tr.tr (V_PK3 P1 P2 X Y) = tr.tr (V1_weyl3 P1 P2 X Y)`. -/
theorem de_haro_seiberg_witten_finite_peirce_dilation_bridge
    (tr : CyclicTrace B M)
    (P1 P2 r rinv W X Y Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0   := waistProjector P1 P2
    let N10  := QuasiDuality P1 P0 X
    let N02  := QuasiDuality P0 P2 Y
    let N12  := P1 * X * P0 * Y * P2
    let Q10  := ExactDualityHolonomy P1 P0 X Y
    let Q01  := ExactDualityHolonomy P0 P1 Y X
    let Q10m := Q10_monopole P1 P2 X Y
    let Q20d := Q20_dyon P1 P2 X Y
    let U    := threeHorizonCornerScaling P1 P2 r rinv
    let Uinv := threeHorizonCornerScaling P1 P2 rinv r
    P0 = P0_waist P1 P2 ∧
    N10 * N10 = 0 ∧
    N02 * N02 = 0 ∧
    ringCommutator N10 N02 = N12 ∧
    Q10m * Q20d = 0 ∧
    Q20d * Q10m = 0 ∧
    ringCommutator Q10m Q20d = 0 ∧
    U * (P0 * W * P0) * Uinv = P0 * W * P0 ∧
    U * (P1 * X * P0) * Uinv = P1 * r * P1 * X * P0 ∧
    U * (P1 * Z * P2) * Uinv = P1 * r * P1 * Z * P2 * r * P2 ∧
    (P1 * r * P1 * rinv * P1 = P1 → P2 * rinv * P2 * r * P2 = P2 → U * Uinv = 1) ∧
    tr.tr Q10 = tr.tr Q01 ∧
    tr.tr (V_PK3 P1 P2 X Y) = tr.tr (V1_weyl3 P1 P2 X Y) := by
  have h_qd := quasi_duality_nilpotency_and_transitive_monodromy P1 P2 X Y h1 h2 h12 h21
  have h_md := monopole_dyon_orthogonality P1 P2 X Y h1 h2 h12 h21
  have h_ct := threeHorizonCornerScaling_transition_action P1 P2 r rinv W X Z h1 h2 h12 h21
  have h_eq := exact_duality_and_theoretical_equivalence tr.tr tr.cyclic P1 P2 X Y h1 h2 h12 h21
  have h_tr := cyclic_trace_vanishes_on_peirce_shells tr P1 P2 X Y h1 h2 h12 h21
  exact ⟨rfl,
         h_qd.1, h_qd.2.1, h_qd.2.2.1,
         h_md.2.2.1, h_md.2.2.2.1, h_md.2.2.2.2,
         h_ct.1, h_ct.2.1, h_ct.2.2,
         fun hr1 hr2 => threeHorizonCornerScaling_mul_right_inverse P1 P2 r rinv h1 h2 h12 h21 hr1 hr2,
         h_eq.2.2,
         h_tr.2.2.2.2.2.2.2.2⟩

/-- **Global Peirce-Spine, Hodge Triality, De Haro Model-Bundle, Yoshizawa Gradient-Flow,
and Operator Möbius / Steinberg / Cyclotomic Synthesis**
(`master_global_peirce_spine_and_model_bundle_coagulation`):
Unites the three-horizon differential square, waist holonomy trace balance, Brockett–Souriau
double-bracket lock, Amari `α = ±1` dual flatness, Jordan-nilpotent boundary defect,
Tetractys `𝔰𝔩₂(B)` Casimir, universal Steinberg braid defect, and 4-way linear diamond of `1 - J⁴`
over `[Ring B]`. -/
theorem master_global_peirce_spine_and_model_bundle_coagulation
    (tr : CyclicTrace B M)
    (P1 P2 N X Y Z C0 : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0)
    (hN2 : N * N = 0) (hP1N : P1 * N = N) (hNP1 : N * P1 = N) :
    (d_tot3 P1 P2 X Y (d_tot3 P1 P2 X Y (H_weyl P1 P2)) =
      comm (V_PK3 P1 P2 X Y + V_waist P1 P2 C0) (H_weyl P1 P2)) ∧
    (tr.tr (V0_semiclassical P1 P2 X Y) =
      tr.tr (Q10_monopole P1 P2 X Y) + tr.tr (Q20_dyon P1 P2 X Y)) ∧
    (- brockettIrrotational (J_mc P1 X Y) (Phi_v P1 X Y) +
      2 • souriauRotational (Sigma_sp P1 X Y) (Phi_v P1 X Y) = 0) ∧
    (d_alpha P1 X Y 1 (d_alpha P1 X Y 1 Z) = 0) ∧
    (d_alpha P1 X Y (-1) (d_alpha P1 X Y (-1) Z) = 0) ∧
    (jordanPerturbedProjector P1 N * jordanPerturbedProjector P1 N -
      jordanPerturbedProjector P1 N = N) ∧
    ((jordanPerturbedProjector P1 N - 1) * (jordanPerturbedProjector P1 N - 1) * P1 = 0) ∧
    (casimirTetractys P1 X Y = 3 • V_met P1 X Y) ∧
    (parabolicFlowPlus P1 X 1 * parabolicFlowMinus P1 Y (-1) * parabolicFlowPlus P1 X 1 =
      J_mc P1 X Y + (1 - V_met P1 X Y) * parabolicFlowPlus P1 X 1) ∧
    ((1 - J_mc P1 X Y) * (1 + J_mc P1 X Y) * (1 - Phi_v P1 X Y) * (1 + Phi_v P1 X Y) =
      1 - (J_mc P1 X Y * J_mc P1 X Y) * (J_mc P1 X Y * J_mc P1 X Y)) := by
  have h_dtot := three_horizon_d_tot_sq_on_weyl_dilation P1 P2 X Y C0 h1 h2 h12 h21
  have h_dh :=
    three_horizon_modular_weights_and_cyclic_trace_balance
      tr.tr tr.cyclic P1 P2 X Y Z h1 h2 h12 h21
  have h_bs := brockett_double_bracket_and_souriau_dewitt_centrifugal_lock P1 X Y h1
  have h_one_comm : ∀ W : B, (1 : B) * W = W * 1 := fun W => by rw [one_mul, mul_one]
  have h_amari := indefinite_parakahler_dc_potential_and_amari_alpha_curvature P1 X Y 1 Z h1 h_one_comm
  have h_jordan := birkhoff_boundary_jordan_nilpotent_split_and_master_synthesis P1 N X h1 hN2 hP1N hNP1
  have h_moeb := tetractys_is_sl2_moebius_lie_algebra P1 X Y h1
  have h_stein := universal_modular_steinberg_braid_defect P1 X Y h1
  have h_diam := operator_factorization_diamond_in_pure_ring P1 X Y h1
  exact ⟨h_dtot.2.1.trans h_dtot.2.2.2.symm,
         h_dh.2.2.2.2.2.2.2.2.2.2.2,
         h_bs.2.2.2.2.2.2.2.1,
         h_amari.2.2.2.2.2.2.2.2.1,
         h_amari.2.2.2.2.2.2.2.2.2,
         h_jordan.2.2.2.1,
         h_jordan.2.2.2.2.2.1,
         h_moeb.2.2.2.2.2.2.2.2.2.2.2.2.2,
         h_stein.2.2.2.1,
         h_diam.2.2⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.MasterPeirceSpineUnification
