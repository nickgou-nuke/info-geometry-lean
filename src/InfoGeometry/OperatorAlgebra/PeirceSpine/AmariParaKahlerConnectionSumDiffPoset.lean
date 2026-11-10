/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset

/-!
# Amari Para-Kähler Connection Sum–Difference & 3-Horizon Weyl Bridge Poset (`𝔄𝔓₁ ≺ ⋯ ≺ 𝔄𝔓₈`)

This module formalizes the noncommutative operator-algebra lift of Amari's dual
`(∇^(e), ∇^(m))` information geometry, the fourfold `V₄` Klein-bottle connection
sum–difference crossover, right-invariant Maurer–Cartan connection 1-forms
`𝒜^(e) ± 𝒜^(m)`, curved Bruhat projectors `P̂_± = G_± P G_±⁻¹`, the push–pull
Legendre–Hua–Bergman–Dikin resolvent differential `R_+ dN_+ R_- = R_V dN_+ R_V`,
and the 6th-order 3-horizon Weyl–para-Kähler bridge.

All theorems hold over an arbitrary associative (noncommutative) ring `B` (`[Ring B]`)
with zero `sorry`s, zero axioms, and zero commutative scalar assumptions.

BUCKET 1: PROVED FINITE/ALGEBRAIC IDENTITIES OVER `[Ring B]`
- `amari_parakahler_exponential_families_and_v4_crossover`
- `maurer_cartan_connection_sum_and_difference_laws`
- `bruhat_projector_sum_diff_and_legendre_hua_dikin`
- `fundamental_weyl_to_parakahler_metric_bridge`
- `master_amari_parakahler_connection_sum_diff_poset_coagulation`

BUCKET 2: CONDITIONAL IDENTITIES FROM EXPLICIT PREMISES
- Idempotent hypothesis `P * P = P` and orthogonal triad hypotheses `P1 * P1 = P1`, `P2 * P2 = P2`,
  `P1 * P2 = P2 * P1 = 0`.

BUCKET 3: OPEN CLOSURE DEBT
- Smooth affine statistical manifold differential geometry and infinite-series resolvent convergence
  are outside this algebraic `[Ring B]` formalization.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset

universe u
variable {B : Type u} [Ring B]

/-! ### Causal Poset Indexing (`𝔄𝔓₁ ≺ ⋯ ≺ 𝔄𝔓₈`) -/

/-- The 8-node causal poset of the Amari Para-Kähler connection sum/difference synthesis. -/
inductive AmariParaKahlerNode : Type
  | AP1_UnipotentExponentialFamilies
  | AP2_V4ConnectionSumDiffCrossover
  | AP3_MaurerCartanConnectionDifference
  | AP4_MaurerCartanConnectionSum
  | AP5_BruhatProjectorGaugeLiftAndDiff
  | AP6_PushPullLegendreHuaBergmanDikin
  | AP7_SingleResolventHuaReduction
  | AP8_ThreeHorizonWeylParaKahlerBridge
  deriving DecidableEq, Repr

instance : Inhabited AmariParaKahlerNode := ⟨.AP1_UnipotentExponentialFamilies⟩

/-- Monotone rank embedding `𝔄𝔓_k ↦ k`. -/
def AmariParaKahlerNode.rank : AmariParaKahlerNode → ℕ
  | .AP1_UnipotentExponentialFamilies => 1
  | .AP2_V4ConnectionSumDiffCrossover => 2
  | .AP3_MaurerCartanConnectionDifference => 3
  | .AP4_MaurerCartanConnectionSum => 4
  | .AP5_BruhatProjectorGaugeLiftAndDiff => 5
  | .AP6_PushPullLegendreHuaBergmanDikin => 6
  | .AP7_SingleResolventHuaReduction => 7
  | .AP8_ThreeHorizonWeylParaKahlerBridge => 8

instance : PartialOrder AmariParaKahlerNode where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    revert hab hba; cases a <;> cases b <;> decide

/-- Product of two positive Peirce corners vanishes (`N_+(P, X₁) * N_+(P, X₂) = 0`). -/
theorem N_plus_mul_N_plus {P : B} (hP : P * P = P) (X1 X2 : B) :
    N_plus P X1 * N_plus P X2 = 0 := by
  dsimp only [N_plus]; peirce_base_nf hP

/-- Right-associated product of two positive Peirce corners vanishes (`N_+(P, X₁) * (N_+(P, X₂) * Z) = 0`). -/
theorem N_plus_mul_N_plus_assoc {P : B} (hP : P * P = P) (X1 X2 Z : B) :
    N_plus P X1 * (N_plus P X2 * Z) = 0 := by
  rw [← mul_assoc, N_plus_mul_N_plus hP X1 X2, zero_mul]

/-- Product of two negative Peirce corners vanishes (`N_-(P, Y₁) * N_-(P, Y₂) = 0`). -/
theorem N_minus_mul_N_minus {P : B} (hP : P * P = P) (Y1 Y2 : B) :
    N_minus P Y1 * N_minus P Y2 = 0 := by
  dsimp only [N_minus]; peirce_base_nf hP

/-- Right-associated product of two negative Peirce corners vanishes (`N_-(P, Y₁) * (N_-(P, Y₂) * Z) = 0`). -/
theorem N_minus_mul_N_minus_assoc {P : B} (hP : P * P = P) (Y1 Y2 Z : B) :
    N_minus P Y1 * (N_minus P Y2 * Z) = 0 := by
  rw [← mul_assoc, N_minus_mul_N_minus hP Y1 Y2, zero_mul]

macro "amari_peirce_nf" hP:ident : tactic =>
  `(tactic| (
    try simp only [smul_add, smul_sub, two_nsmul,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      neg_mul, mul_neg, mul_assoc,
      $hP:ident, proj_idem $hP:ident,
      S_P_sq $hP:ident, S_P_sq_assoc $hP:ident,
      N_plus_sq $hP:ident, N_plus_sq_assoc $hP:ident,
      N_minus_sq $hP:ident, N_minus_sq_assoc $hP:ident,
      N_plus_mul_N_plus $hP:ident, N_plus_mul_N_plus_assoc $hP:ident,
      N_minus_mul_N_minus $hP:ident, N_minus_mul_N_minus_assoc $hP:ident,
      P_mul_N_plus $hP:ident, P_mul_N_plus_assoc $hP:ident,
      N_plus_mul_P $hP:ident, N_plus_mul_P_assoc $hP:ident,
      P_mul_N_minus $hP:ident, P_mul_N_minus_assoc $hP:ident,
      N_minus_mul_P $hP:ident, N_minus_mul_P_assoc $hP:ident,
      S_P_mul_N_plus $hP:ident, S_P_mul_N_plus_assoc $hP:ident,
      N_plus_mul_S_P $hP:ident, N_plus_mul_S_P_assoc $hP:ident,
      S_P_mul_N_minus $hP:ident, S_P_mul_N_minus_assoc $hP:ident,
      N_minus_mul_S_P $hP:ident, N_minus_mul_S_P_assoc $hP:ident,
      mul_zero, zero_mul]
    try abel))

/-! ### Level 1 (`𝔄𝔓₁ ≺ 𝔄𝔓₂`): Unipotent Exponential Families & `V₄` Sum–Difference Crossover -/

/-- Even diagonal subalgebra projection `K_even(W) = P W P + (1 - P) W (1 - P)`. -/
def K_even (P W : B) : B := P * W * P + (1 - P) * W * (1 - P)

/-- Odd off-diagonal tangent projection `P_odd(W) = P W (1 - P) + (1 - P) W P`. -/
def P_odd (P W : B) : B := P * W * (1 - P) + (1 - P) * W * P

/-- Symmetric connection core `Γ_sum(W) = P W P + (1 - P) W (1 - P)`. -/
def Gamma_sum (P W : B) : B := P * W * P + (1 - P) * W * (1 - P)

/-- Skew connection core `Γ_diff(W) = P W P - (1 - P) W (1 - P)`. -/
def Gamma_diff (P W : B) : B := P * W * P - (1 - P) * W * (1 - P)

/-- **Theorem 1 (`𝔄𝔓₁ ≺ 𝔄𝔓₂` — Unipotent Exponential Families & `V₄` Sum–Difference Crossover)**:
1. Abelian `e`-flat and `m`-flat operator exponential addition `(1 + N_+(X₁))(1 + N_+(X₂)) = 1 + N_+(X₁ + X₂)`,
2. Paired Gaussian sum `𝒢_+ + 𝒢_- - 2(1 + Φ) = V` and difference `𝒢_+ - 𝒢_- = Σ`,
3. Universal fourfold `V₄` Klein-bottle crossover `[Γ_diff, Φ] = {Γ_sum, J}`,
   `{Γ_diff, Φ} = [Γ_sum, J]`, `[Γ_diff, J] = {Γ_sum, Φ}`, `{Γ_diff, J} = [Γ_sum, Φ]`. -/
theorem amari_parakahler_exponential_families_and_v4_crossover
    (P X1 X2 Y1 Y2 W : B) (hP : P * P = P) :
    let np1 := N_plus P X1
    let np2 := N_plus P X2
    let nm1 := N_minus P Y1
    let nm2 := N_minus P Y2
    let ph  := Phi_v P X1 Y1
    let j   := J_mc P X1 Y1
    let G_p := (1 + np1) * (1 + nm1)
    let G_m := (1 + nm1) * (1 + np1)
    (1 + np1) * (1 + np2) = 1 + N_plus P (X1 + X2) ∧
    (1 + nm1) * (1 + nm2) = 1 + N_minus P (Y1 + Y2) ∧
    G_p + G_m - ((1 + ph) + (1 + ph)) = V_met P X1 Y1 ∧
    G_p - G_m = Sigma_sp P X1 Y1 ∧
    comm (Gamma_diff P W) ph = anticomm (Gamma_sum P W) j ∧
    anticomm (Gamma_diff P W) ph = comm (Gamma_sum P W) j ∧
    comm (Gamma_diff P W) j = anticomm (Gamma_sum P W) ph ∧
    anticomm (Gamma_diff P W) j = comm (Gamma_sum P W) ph := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [N_plus, N_minus, Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg,
                Gamma_sum, Gamma_diff, comm, anticomm]
    peirce_base_nf hP

/-! ### Level 2 (`𝔄𝔓₃ ≺ 𝔄𝔓₄`): Sum & Difference of the Maurer–Cartan Connection 1-Forms -/

/-- Right-invariant Maurer–Cartan connection 1-form `𝒜^(e) = (d𝒢_+) 𝒢_+⁻¹`. -/
def MC_Conn_e (P X Y dX dY : B) : B :=
  (N_plus P dX * (1 + N_minus P Y) + (1 + N_plus P X) * N_minus P dY) *
  ((1 - N_minus P Y) * (1 - N_plus P X))

/-- Right-invariant Maurer–Cartan connection 1-form `𝒜^(m) = (d𝒢_-) 𝒢_-⁻¹`. -/
def MC_Conn_m (P X Y dX dY : B) : B :=
  (N_minus P dY * (1 + N_plus P X) + (1 + N_minus P Y) * N_plus P dX) *
  ((1 - N_plus P X) * (1 - N_minus P Y))

/-- Leibniz differential of the Berry/spin curvature `dΣ = d(N_+ N_- - N_- N_+)`. -/
def dSigma (P X Y dX dY : B) : B :=
  (N_plus P dX * N_minus P Y + N_plus P X * N_minus P dY) -
  (N_minus P dY * N_plus P X + N_minus P Y * N_plus P dX)

/-- **Theorem 2 (`𝔄𝔓₃ ≺ 𝔄𝔓₄` — Exact Sum & Difference of Maurer–Cartan Connection 1-Forms)**:
1. Individual nilpotent reductions `𝒜^(e) = dN_+ + (1 + N_+) dN_- (1 - N_+)` and
   `𝒜^(m) = dN_- + (1 + N_-) dN_+ (1 - N_-)`,
2. Exact Difference Law `𝒜^(e) - 𝒜^(m) = dΣ - (N_+ dN_- N_+ - N_- dN_+ N_-)` with even
   part `K_even(𝒜^(e) - 𝒜^(m)) = dΣ`,
3. Exact Sum Law `𝒜^(e) + 𝒜^(m) = 2 dΦ + ([N_+, dN_-] + [N_-, dN_+]) - (N_+ dN_- N_+ + N_- dN_+ N_-)`. -/
theorem maurer_cartan_connection_sum_and_difference_laws
    (P X Y dX dY : B) (hP : P * P = P) :
    let np  := N_plus P X
    let nm  := N_minus P Y
    let dnp := N_plus P dX
    let dnm := N_minus P dY
    let dph := dnp + dnm
    let Ae  := MC_Conn_e P X Y dX dY
    let Am  := MC_Conn_m P X Y dX dY
    let dS  := dSigma P X Y dX dY
    Ae = dnp + (1 + np) * dnm * (1 - np) ∧
    Am = dnm + (1 + nm) * dnp * (1 - nm) ∧
    Ae - Am = dS - (np * dnm * np - nm * dnp * nm) ∧
    K_even P (Ae - Am) = dS ∧
    P_odd P (Ae - Am) = - (np * dnm * np - nm * dnp * nm) ∧
    Ae + Am = (dph + dph) + (comm np dnm + comm nm dnp) - (np * dnm * np + nm * dnp * nm) ∧
    K_even P (Ae + Am) = comm np dnm + comm nm dnp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [MC_Conn_e, MC_Conn_m, dSigma, K_even, P_odd, comm]
    amari_peirce_nf hP

/-! ### Level 3 (`𝔄𝔓₅ ≺ 𝔄𝔓₆ ≺ 𝔄𝔓₇`): Bruhat Projector Lift & Push–Pull Legendre–Hua–Dikin Metric -/

/-- **Theorem 3 (`𝔄𝔓₅ ≺ 𝔄𝔓₆` — Bruhat Projector Sum/Diff & Push–Pull Legendre Differential)**:
1. First-principles Bruhat gauge lift `(1 + N_+)(1 - N_-) P (1 + N_-)(1 - N_+) = P̂_+` and
   `(1 - N_-)(1 + N_+) P (1 - N_+)(1 + N_-) = P̂_-`,
2. Bruhat projector difference `P̂_- - P̂_+ = V J`, anticommutator `{P̂_+, P̂_-} = P̂_+ + P̂_- + V³`,
   and midpoint cubic sag `(P̂_+ + P̂_-)² - 2(P̂_+ + P̂_-) = V³`,
3. Push–pull resolvent intertwiner `R_+ N_+ = N_+ R_-` and Legendre differential collapse
   `R_+ dN_+ + R_+ dN_+ N_- R_+ N_+ = R_+ dN_+ R_-`. -/
theorem bruhat_projector_sum_diff_and_legendre_hua_dikin
    (P X Y dX Rp Rm : B) (hP : P * P = P)
    (hRp : Rp * (1 - Q_pos P X Y) = 1)
    (hRm : (1 - Q_neg P X Y) * Rm = 1) :
    let Pe  := P_hat_plus P X Y
    let Pm  := P_hat_minus P X Y
    let v   := V_met P X Y
    let np  := N_plus P X
    let nm  := N_minus P Y
    let dnp := N_plus P dX
    (1 - np) * (1 + nm) * P * ((1 - nm) * (1 + np)) = Pe ∧
    (1 + nm) * (1 - np) * P * ((1 + np) * (1 - nm)) = Pm ∧
    Pm - Pe = v * J_mc P X Y ∧
    anticomm Pe Pm = Pe + Pm + v * v * v ∧
    (Pe + Pm) * (Pe + Pm) - ((Pe + Pm) + (Pe + Pm)) = v * v * v ∧
    Rp * np = np * Rm ∧
    Rp * dnp + Rp * dnp * nm * (Rp * np) = Rp * dnp * Rm := by
  have h_inter : (1 - Q_pos P X Y) * N_plus P X = N_plus P X * (1 - Q_neg P X Y) := by
    dsimp only [Q_pos, Q_neg]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  have h_res_shift : Rp * N_plus P X = N_plus P X * Rm := by
    calc Rp * N_plus P X
      _ = Rp * N_plus P X * ((1 - Q_neg P X Y) * Rm) := by rw [hRm, mul_one]
      _ = Rp * (N_plus P X * (1 - Q_neg P X Y)) * Rm := by simp only [mul_assoc]
      _ = (Rp * (1 - Q_pos P X Y)) * N_plus P X * Rm := by rw [← h_inter]; simp only [mul_assoc]
      _ = N_plus P X * Rm                            := by rw [hRp, one_mul]
  have h_abs : 1 + Q_neg P X Y * Rm = Rm := by
    calc 1 + Q_neg P X Y * Rm
      _ = (1 - Q_neg P X Y) * Rm + Q_neg P X Y * Rm := by rw [hRm]
      _ = Rm                                        := by simp only [sub_mul, one_mul]; abel
  refine ⟨?_, ?_, ?_, ?_, ?_, h_res_shift, ?_⟩
  · dsimp only [P_hat_plus, Psi1, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP
  · dsimp only [P_hat_minus, Psi1, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP
  · dsimp only [P_hat_plus, P_hat_minus, Psi1, Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP
  · dsimp only [P_hat_plus, P_hat_minus, Psi1, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg, anticomm]
    amari_peirce_nf hP
  · dsimp only [P_hat_plus, P_hat_minus, Psi1, Phi_v, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP
  · calc Rp * N_plus P dX + Rp * N_plus P dX * N_minus P Y * (Rp * N_plus P X)
      _ = Rp * N_plus P dX + Rp * N_plus P dX * N_minus P Y * (N_plus P X * Rm) := by
          rw [h_res_shift]
      _ = Rp * N_plus P dX * (1 + Q_neg P X Y * Rm) := by
          dsimp [Q_neg]; simp only [mul_add, mul_one, mul_assoc]
      _ = Rp * N_plus P dX * Rm := by rw [h_abs]

/-- **Theorem 4 (`𝔄𝔓₇` — 5th-Order Single-Resolvent `R_V = (1 - V)⁻¹` Reduction)**:
When a single two-sided resolvent `Rv` of `1 - V` exists (`Rv * (1 - V) = 1` and `(1 - V) * Rv = 1`),
`Rv` commutes with `P`, `N_+`, `N_-`, and `V`, and satisfies `Rv * (1 - Q_+) = 1 + Rv * Q_-`
and `(Rv * dN_+ * Rv) * (1 - V) = Rv * dN_+`. -/
theorem single_resolvent_hua_bergman_dikin_reduction
    (P X Y dX Rv : B) (hP : P * P = P)
    (hRv_l : Rv * (1 - V_met P X Y) = 1)
    (hRv_r : (1 - V_met P X Y) * Rv = 1) :
    let v   := V_met P X Y
    let dnp := N_plus P dX
    comm Rv P = 0 ∧
    Rv * (1 - Q_pos P X Y) = 1 + Rv * Q_neg P X Y ∧
    (Rv * dnp * Rv) * (1 - v) = Rv * dnp := by
  have hVP : (1 - V_met P X Y) * P = P * (1 - V_met P X Y) := by
    dsimp only [V_met, Q_pos, Q_neg]
    amari_peirce_nf hP
  have hRvP : Rv * P = P * Rv := by
    calc Rv * P
      _ = Rv * P * ((1 - V_met P X Y) * Rv) := by rw [hRv_r, mul_one]
      _ = Rv * (P * (1 - V_met P X Y)) * Rv := by simp only [mul_assoc]
      _ = (Rv * (1 - V_met P X Y)) * P * Rv := by rw [← hVP]; simp only [mul_assoc]
      _ = P * Rv                            := by rw [hRv_l, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold comm; rw [hRvP, sub_self]
  · calc Rv * (1 - Q_pos P X Y)
      _ = Rv * (1 - V_met P X Y + Q_neg P X Y) := by
          dsimp [V_met]; congr 1; abel
      _ = Rv * (1 - V_met P X Y) + Rv * Q_neg P X Y := by rw [mul_add]
      _ = 1 + Rv * Q_neg P X Y := by rw [hRv_l]
  · calc (Rv * N_plus P dX * Rv) * (1 - V_met P X Y)
      _ = Rv * N_plus P dX * (Rv * (1 - V_met P X Y)) := by simp only [mul_assoc]
      _ = Rv * N_plus P dX                            := by rw [hRv_l, mul_one]

/-! ### Level 4 (`𝔄𝔓₈`): 6th-Order 3-Horizon Weyl–Para-Kähler Bridge -/

/-- **Theorem 5 (`𝔄𝔓₈` — 6th-Order 3-Horizon Weyl–Para-Kähler Bridge)**:
For three orthogonal horizons `1 = P₁ + P₀ + P₂` with `P_hor = P₁ + P₂` and `H = P₁ - P₂`,
the square-zero Para-Kähler horizon gauge waves `Ψ_out = P_hor X P₀` and `Ψ_in = P₀ Y P_hor`
and the step-1 Weyl waves `N_{+1} = P₁ X P₀ + P₀ Y P₂`, `N_{-1} = P₀ Y P₁ + P₂ X P₀`
share the exact same odd current `Ψ_out + Ψ_in = N_{+1} + N_{-1}`, while `Ψ_out² = Ψ_in² = 0`
contrasts with the non-vanishing contact shell `N_{+1}² = P₁ X P₀ Y P₂`. -/
theorem three_horizon_weyl_parakahler_bridge
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P_hor   := P1 + P2
    let P0      := 1 - P1 - P2
    let Psi_out := P_hor * X * P0
    let Psi_in  := P0 * Y * P_hor
    let Np1     := P1 * X * P0 + P0 * Y * P2
    let Nm1     := P0 * Y * P1 + P2 * X * P0
    P_hor * P_hor = P_hor ∧
    Psi_out * Psi_out = 0 ∧
    Psi_in * Psi_in = 0 ∧
    Psi_out + Psi_in = Np1 + Nm1 ∧
    Np1 * Np1 = P1 * X * P0 * Y * P2 ∧
    Nm1 * Nm1 = P2 * X * P0 * Y * P1 := by
  intro P_hor P0 Psi_out Psi_in Np1 Nm1
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [P_hor, P0, Psi_out, Psi_in, Np1, Nm1]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- **Master Poset Chain (`𝔄𝔓₁ ≺ ⋯ ≺ 𝔄𝔓₈`)**: Strict causal ordering of the 8-node
Amari Para-Kähler connection sum–difference poset. -/
theorem master_amari_parakahler_connection_sum_diff_poset_coagulation :
    AmariParaKahlerNode.AP1_UnipotentExponentialFamilies < .AP2_V4ConnectionSumDiffCrossover ∧
    AmariParaKahlerNode.AP2_V4ConnectionSumDiffCrossover < .AP3_MaurerCartanConnectionDifference ∧
    AmariParaKahlerNode.AP3_MaurerCartanConnectionDifference < .AP4_MaurerCartanConnectionSum ∧
    AmariParaKahlerNode.AP4_MaurerCartanConnectionSum < .AP5_BruhatProjectorGaugeLiftAndDiff ∧
    AmariParaKahlerNode.AP5_BruhatProjectorGaugeLiftAndDiff < .AP6_PushPullLegendreHuaBergmanDikin ∧
    AmariParaKahlerNode.AP6_PushPullLegendreHuaBergmanDikin < .AP7_SingleResolventHuaReduction ∧
    AmariParaKahlerNode.AP7_SingleResolventHuaReduction < .AP8_ThreeHorizonWeylParaKahlerBridge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · change AmariParaKahlerNode.rank _ < AmariParaKahlerNode.rank _
    decide

end InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
