/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset

/-!
# Algebraic Operator Identities for Double-Bracket Flows, Indefinite Para-Kähler
# Connections, Sheet-Gramian Resolvents, Three-Horizon Monodromy, Coadjoint Trace
# Orthogonality, and Jordan-Nilpotent Boundary Splits

Over an arbitrary associative ring `B` (`[Ring B]`) and an additive commutative group `R`
(`[AddCommGroup R]`), this module establishes six families of noncommutative operator identities
corresponding to the algebraic backbone of gradient-flow information geometry (cf. S. Yoshizawa,
*Information Geometry of Gradient Flows*, arXiv:2608.21152):

1. **Brockett Double-Bracket Flow and Souriau–DeWitt Centrifugal Balance:**
   For any idempotent `P * P = P` and off-diagonal Peirce waves `N_+ = P X (1 - P)`,
   `N_- = (1 - P) Y P`, solder form `Φ = N_+ + N_-`, generator `J = N_+ - N_-`, metric
   `V = {N_+, N_-}`, and spin bivector `Σ = [N_+, N_-]`, the double-commutator operator
   `brockettIrrotational J Φ = [Φ, [Φ, J]] = 4 V J` balances twice the Souriau rotational
   precession `2 [Σ, Φ]`, while the centrifugal double commutator `[Σ, [Σ, Φ]] = 4 V² Φ`
   balances `V [J, [J, Φ]] = -4 V² Φ`.
2. **Indefinite Para-Kähler Difference-of-Squares and Amari `α`-Connection Curvature:**
   The sheet Gramians `Q_+ = N_+ N_-` and `Q_- = N_- N_+` are mutually orthogonal (`Q_+ Q_- = 0`,
   `Q_- Q_+ = 0`), split `V = Q_+ + Q_-` and `Σ = Q_+ - Q_-` with `V² = Σ² = Q_+² + Q_-²`,
   and induce exterior differentials `d_sum`, `d_diff` obeying `{d_sum, d_diff} = 0`,
   `d_sum²(Z) = [V, Z]`, `d_diff²(Z) = -[V, Z]`, and the universal `α`-connection curvature
   identity `d_α(d_α(Z)) = (1 - α²) [V, Z]` (vanishing at `α = ±1`).
3. **Sheet-Gramian Factorizations and Hua–Bergman–Dikin Resolvent Identities:**
   The factors `1 ± Q_+` and `1 ± Q_-` multiply to `1 ± V` and `1 ± Σ` with fourth-order
   product `(1 - V)(1 + V) = (1 - Σ)(1 + Σ) = 1 - J⁴`, while two-sided resolvents `Rp`, `Rm`,
   and `Rv` of `1 - Q_+`, `1 - Q_-`, and `1 - V` intertwine `N_+` and collapse the differential
   variation `Rp dN_+ + Rp dN_+ N_- Rp N_+ = Rp dN_+ Rm`.
4. **Three-Horizon Idempotent Resolution and Transitive Waist Monodromy:**
   For orthogonal idempotents `P₁`, `P₂` with complementary waist `P₀ = 1 - P₁ - P₂` and
   tripotent `H = P₁ - P₂` (`H³ = H`), the off-diagonal transitions `N₁₀ = P₁ X P₀` and
   `N₀₂ = P₀ Y P₂` are square-zero (`N₁₀² = N₀₂² = 0`) and their commutator across `P₀`
   generates the cross-horizon transition `[N₁₀, N₀₂] = P₁ X P₀ Y P₂`, while the monopole
   and dyon return holonomies are mutually orthogonal.
5. **Coadjoint Leaf Trace Orthogonality and Brockett Dissipation Pairing:**
   Under any cyclic additive trace `τ : CyclicTrace B R`, the Souriau rotational velocity
   `[Ω, ρ]` has zero trace pairing with every element `M` commuting with `ρ`, whereas the
   Brockett operator satisfies `⟨[ρ, [ρ, G]], G⟩_τ = -⟨[ρ, G], [ρ, G]⟩_τ` and is symmetric
   with respect to `⟨·, ·⟩_τ`.
6. **Non-Semisimple Jordan-Nilpotent Boundary Split:**
   For `T = P + N` with `P * P = P`, `N * N = 0`, and `P * N = N * P = N`, the idempotency
   defect is `T * T - T = N`, the Jordan radical satisfies `(T - P)² = 0`, and `(T - 1) P = N`
   is annihilated at second order `(T - 1)² P = 0`.

All results are exact ring identities over `[Ring B]`; no smooth manifold, analytic logarithm,
or birational blow-up scheme is assumed.

BUCKET 1: PROVED FINITE/ALGEBRAIC IDENTITIES OVER `[Ring B]`
- `brockett_double_bracket_and_souriau_dewitt_centrifugal_lock`
- `indefinite_parakahler_dc_potential_and_amari_alpha_curvature`
- `three_horizon_moduli_idempotents_and_transitive_monodromy`
- `birkhoff_boundary_jordan_nilpotent_split_and_master_synthesis`

BUCKET 2: CONDITIONAL IDENTITIES FROM EXPLICIT PREMISES
- `sheet_gramian_factorization_and_hua_bergman_dikin_resolvent` (from explicit two-sided resolvents)
- `kirillov_coadjoint_leaf_orthogonality_and_brockett_dissipation` (from a cyclic trace `τ`)

BUCKET 3: OPEN CLOSURE DEBT
- Continuum gradient-flow ODE integration, analytic matrix logarithm/determinant potentials,
  and birational blow-up schemes on smooth moduli manifolds are not constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.YoshizawaGradientFlowInfoGeometryPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset

universe u v
variable {B : Type u} [Ring B]
variable {R : Type v} [AddCommGroup R]

-- ============================================================================
-- 1. BROCKETT DOUBLE-BRACKET FLOW & SOURIAU–DEWITT CENTRIFUGAL LOCK
-- ============================================================================

/--
**Brockett–Souriau–DeWitt double-bracket theorem
(`brockett_double_bracket_and_souriau_dewitt_centrifugal_lock`):**
For any idempotent `P * P = P` and `X, Y : B` with `Φ = Phi_v P X Y`, `J = J_mc P X Y`,
`V = V_met P X Y`, and `Σ = Sigma_sp P X Y`:
1. **Split-Signature Clifford Squares and Brackets:**
   - `Φ * Φ = V`, `J * J = -V`, `Σ * Σ = V * V`,
   - `anticomm Φ J = 0` and `comm Φ J = -(2 • Σ)`,
2. **Brockett Irrotational Flow vs. Souriau Coriolis Precession:**
   - `souriauRotational Σ Φ = 2 • (V * J)`,
   - `- brockettIrrotational J Φ = -(4 • (V * J))`,
   - `- brockettIrrotational J Φ + 2 • souriauRotational Σ Φ = 0`,
3. **Centrifugal Double-Commutator Push vs. Parabolic Well Pull:**
   - `brockettIrrotational Φ Σ = 4 • (V * V * Φ)`,
   - `V * brockettIrrotational Φ J = -(4 • (V * V * Φ))`,
   - `brockettIrrotational Φ Σ + V * brockettIrrotational Φ J = 0`.
-/
theorem brockett_double_bracket_and_souriau_dewitt_centrifugal_lock
    (P X Y : B) (hP : P * P = P) :
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    ph * ph = v ∧
    j * j = -v ∧
    s * s = v * v ∧
    anticomm ph j = 0 ∧
    comm ph j = - (2 • s) ∧
    souriauRotational s ph = 2 • (v * j) ∧
    - brockettIrrotational j ph = - (4 • (v * j)) ∧
    - brockettIrrotational j ph + 2 • souriauRotational s ph = 0 ∧
    brockettIrrotational ph s = 4 • (v * v * ph) ∧
    v * brockettIrrotational ph j = - (4 • (v * v * ph)) ∧
    brockettIrrotational ph s + v * brockettIrrotational ph j = 0 := by
  have h4 := node4_rotating_ball_parabolic_entropy_well_and_dewitt_lock P X Y hP
  refine ⟨?_, ?_, ?_, ?_, ?_, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1⟩ <;>
  · dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

-- ============================================================================
-- 2. INDEFINITE PARA-KÄHLER DC SPLIT & AMARI α-CONNECTION CURVATURE
-- ============================================================================

/--
**Indefinite Para-Kähler and Amari `α`-curvature theorem
(`indefinite_parakahler_dc_potential_and_amari_alpha_curvature`):**
For any idempotent `P * P = P`, `X, Y, Z : B`, and central scalar `α : B` (`∀ W, α * W = W * α`):
1. **Orthogonal Sheet Gramians and Difference-of-Squares Decomposition:**
   - `Q_pos P X Y * Q_neg P X Y = 0` and `Q_neg P X Y * Q_pos P X Y = 0`,
   - `V_met P X Y * V_met P X Y = Q_pos P X Y * Q_pos P X Y + Q_neg P X Y * Q_neg P X Y`,
   - `V_met P X Y * Sigma_sp P X Y = Q_pos P X Y * Q_pos P X Y - Q_neg P X Y * Q_neg P X Y`,
2. **Split-Clifford `Cl(1,1)` Exterior Differentials:**
   - `d_sum P X Y (d_sum P X Y Z) = comm (V_met P X Y) Z`,
   - `d_diff P X Y (d_diff P X Y Z) = - comm (V_met P X Y) Z`,
   - `d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z) = 0`,
3. **Universal Amari `α`-Connection Curvature and `α = ±1` Dual Flatness:**
   - `d_alpha P X Y α (d_alpha P X Y α Z) = (1 - α * α) * comm (V_met P X Y) Z`,
   - `d_alpha P X Y 1 (d_alpha P X Y 1 Z) = 0`,
   - `d_alpha P X Y (-1) (d_alpha P X Y (-1) Z) = 0`.
-/
theorem indefinite_parakahler_dc_potential_and_amari_alpha_curvature
    (P X Y α Z : B) (hP : P * P = P) (hα : ∀ W : B, α * W = W * α) :
    let qp := Q_pos P X Y
    let qm := Q_neg P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    qp * qm = 0 ∧
    qm * qp = 0 ∧
    v * v = qp * qp + qm * qm ∧
    v * s = qp * qp - qm * qm ∧
    d_sum P X Y (d_sum P X Y Z) = comm v Z ∧
    d_diff P X Y (d_diff P X Y Z) = - comm v Z ∧
    d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z) = 0 ∧
    d_alpha P X Y α (d_alpha P X Y α Z) = (1 - α * α) * comm v Z ∧
    d_alpha P X Y 1 (d_alpha P X Y 1 Z) = 0 ∧
    d_alpha P X Y (-1) (d_alpha P X Y (-1) Z) = 0 := by
  have h6_α := (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure P X Y α Z Z Z hP hα)
  have h_one_comm : ∀ W : B, (1 : B) * W = W * 1 := fun W => by rw [one_mul, mul_one]
  have h_neg_one_comm : ∀ W : B, (-1 : B) * W = W * (-1) := fun W => by noncomm_ring
  have h6_pos := (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure P X Y 1 Z Z Z hP h_one_comm).2.2.2.2.2.2.2.2.2.2.1
  have h6_neg := (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure P X Y (-1) Z Z Z hP h_neg_one_comm).2.2.2.2.2.2.2.2.2.2.1
  have h_flat_pos : d_alpha P X Y 1 (d_alpha P X Y 1 Z) = 0 := by
    rw [h6_pos, mul_one, sub_self, zero_mul]
  have h_flat_neg : d_alpha P X Y (-1) (d_alpha P X Y (-1) Z) = 0 := by
    have h_sq : (-1 : B) * (-1 : B) = 1 := by noncomm_ring
    rw [h6_neg, h_sq, sub_self, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h6_α.2.2.2.2.2.2.2.2.1, h6_α.2.2.2.2.2.2.2.2.2.2.1, h_flat_pos, h_flat_neg⟩ <;>
  · dsimp only [V_met, Sigma_sp, Q_pos, Q_neg, d_sum, d_diff, d_plus, d_minus, chiralConj, comm]
    amari_peirce_nf hP

-- ============================================================================
-- 3. SHEET-GRAMIAN FACTORIZATION & HUA–BERGMAN–DIKIN RESOLVENT
-- ============================================================================

/--
**Sheet-Gramian factorization and Hua–Bergman–Dikin resolvent theorem
(`sheet_gramian_factorization_and_hua_bergman_dikin_resolvent`):**
For any idempotent `P * P = P` and `X, Y, dX : B`, together with sheet resolvents `Rp`, `Rm`
and metric resolvent `Rv`:
1. **Four-Way Bott / Sheet-Gramian Factorizations:**
   - `(1 - Q_pos P X Y) * (1 - Q_neg P X Y) = 1 - V_met P X Y`,
   - `(1 + Q_pos P X Y) * (1 + Q_neg P X Y) = 1 + V_met P X Y`,
   - `(1 - Q_pos P X Y) * (1 + Q_neg P X Y) = 1 - Sigma_sp P X Y`,
   - `(1 + Q_pos P X Y) * (1 - Q_neg P X Y) = 1 + Sigma_sp P X Y`,
   - `(1 - V_met P X Y) * (1 + V_met P X Y) = 1 - J_mc P X Y * J_mc P X Y * J_mc P X Y * J_mc P X Y`,
   - `(1 - Sigma_sp P X Y) * (1 + Sigma_sp P X Y) = 1 - J_mc P X Y * J_mc P X Y * J_mc P X Y * J_mc P X Y`,
2. **Hua–Bergman–Dikin Resolvent Intertwining and Differential Collapse:**
   - `Rp * N_plus P X = N_plus P X * Rm`,
   - `Rp * N_plus P dX + Rp * N_plus P dX * N_minus P Y * (Rp * N_plus P X) = Rp * N_plus P dX * Rm`,
   - `comm Rv P = 0`,
   - `(Rv * N_plus P dX * Rv) * (1 - V_met P X Y) = Rv * N_plus P dX`.
-/
theorem sheet_gramian_factorization_and_hua_bergman_dikin_resolvent
    (P X Y dX Rp Rm Rv : B) (hP : P * P = P)
    (hRp : Rp * (1 - Q_pos P X Y) = 1)
    (hRm : (1 - Q_neg P X Y) * Rm = 1)
    (hRv_l : Rv * (1 - V_met P X Y) = 1)
    (hRv_r : (1 - V_met P X Y) * Rv = 1) :
    let qp  := Q_pos P X Y
    let qm  := Q_neg P X Y
    let v   := V_met P X Y
    let s   := Sigma_sp P X Y
    let j   := J_mc P X Y
    let np  := N_plus P X
    let nm  := N_minus P Y
    let dnp := N_plus P dX
    (1 - qp) * (1 - qm) = 1 - v ∧
    (1 + qp) * (1 + qm) = 1 + v ∧
    (1 - qp) * (1 + qm) = 1 - s ∧
    (1 + qp) * (1 - qm) = 1 + s ∧
    (1 - v) * (1 + v) = 1 - j * j * j * j ∧
    (1 - s) * (1 + s) = 1 - j * j * j * j ∧
    Rp * np = np * Rm ∧
    Rp * dnp + Rp * dnp * nm * (Rp * np) = Rp * dnp * Rm ∧
    comm Rv P = 0 ∧
    (Rv * dnp * Rv) * (1 - v) = Rv * dnp := by
  have h_bhd := bruhat_projector_sum_diff_and_legendre_hua_dikin P X Y dX Rp Rm hP hRp hRm
  have h_single := single_resolvent_hua_bergman_dikin_reduction P X Y dX Rv hP hRv_l hRv_r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h_bhd.2.2.2.2.2.1, h_bhd.2.2.2.2.2.2, h_single.1, h_single.2.2⟩ <;>
  · dsimp only [V_met, Sigma_sp, J_mc, Q_pos, Q_neg]
    amari_peirce_nf hP

-- ============================================================================
-- 4. THREE-HORIZON MODULI IDEMPOTENTS & TRANSITIVE WAIST MONODROMY
-- ============================================================================

/--
**Three-horizon idempotent frame and transitive monodromy theorem
(`three_horizon_moduli_idempotents_and_transitive_monodromy`):**
Given orthogonal idempotents `P₁² = P₁`, `P₂² = P₂`, `P₁ P₂ = P₂ P₁ = 0` with waist
`P₀ = P0_waist P1 P2 = 1 - P₁ - P₂` and Weyl generator `H = H_weyl P1 P2 = P₁ - P₂`:
1. **Three-Projector Partition and Tripotent Generator:**
   - `P₁ + P₀ + P₂ = 1`, `P₀ * P₀ = P₀`, and `H * (H * H) = H`,
2. **Square-Zero Quasi-Duality Jumps and Transitive Waist Monodromy:**
   - `block10 P1 P2 X * block10 P1 P2 X = 0` and `block02 P1 P2 Y * block02 P1 P2 Y = 0`,
   - `comm (block10 P1 P2 X) (block02 P1 P2 Y) = block12 P1 P2 (X * P₀ * Y)`,
3. **Monopole and Dyon Return-Holonomy Orthogonality:**
   - `(block10 P1 P2 X * block01 P1 P2 Y) * (block20 P1 P2 Y * block02 P1 P2 X) = 0`,
   - `(block20 P1 P2 Y * block02 P1 P2 X) * (block10 P1 P2 X * block01 P1 P2 Y) = 0`,
4. **Three-Horizon Brockett–Souriau Balance:**
   - `- brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) + 2 • souriauRotational (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) = 0`.
-/
theorem three_horizon_moduli_idempotents_and_transitive_monodromy
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0  := P0_waist P1 P2
    let H   := H_weyl P1 P2
    let N10 := block10 P1 P2 X
    let N02 := block02 P1 P2 Y
    let Q10 := block10 P1 P2 X * block01 P1 P2 Y
    let Q20 := block20 P1 P2 Y * block02 P1 P2 X
    P1 + P0 + P2 = 1 ∧
    P0 * P0 = P0 ∧
    H * (H * H) = H ∧
    N10 * N10 = 0 ∧
    N02 * N02 = 0 ∧
    comm N10 N02 = block12 P1 P2 (X * P0 * Y) ∧
    Q10 * Q20 = 0 ∧
    Q20 * Q10 = 0 ∧
    - brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) +
      2 • souriauRotational (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) = 0 := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0     := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0     := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h_frame := orthogonal_idempotents_induce_complementary_tripotent_frame P1 P2 h1 h2 h12 h21
  have h_rb := (three_horizon_rotating_ball_and_cl11_weitzenbock_calculus P1 P2 X Y 0 h1 h2 h12 h21).2.2.2.1
  have h_bs :
      - brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) +
        2 • souriauRotational (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) = 0 := by
    dsimp only [brockettIrrotational, souriauRotational]
    exact h_rb
  refine ⟨h_frame.1, h_frame.2.1, h_frame.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, h_bs⟩ <;>
  · dsimp only [block10, block01, block02, block20, block12, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 5. KIRILLOV COADJOINT LEAF ORTHOGONALITY & BROCKETT DISSIPATION
-- ============================================================================

/--
**Coadjoint leaf trace orthogonality and Brockett dissipation theorem
(`kirillov_coadjoint_leaf_orthogonality_and_brockett_dissipation`):**
Under any cyclic trace `τ : CyclicTrace B R`, for any `Ω, G, ρ, M, H, x : B` with `comm ρ M = 0`:
1. **Souriau Coadjoint Leaf Orthogonality:**
   - `tracePairing τ (souriauRotational Ω ρ) M = 0`,
   - `tracePairing τ (souriauRotational Ω ρ) ρ = 0`,
2. **Metriplectic Trace Splitting and Brockett Dissipation Pairing:**
   - `tracePairing τ (metriplecticFlow Ω G ρ) H = tracePairing τ Ω (comm ρ H) - tracePairing τ (comm ρ G) (comm ρ H)`,
   - `tracePairing τ (brockettIrrotational G ρ) G = - tracePairing τ (comm ρ G) (comm ρ G)`,
3. **Double-Commutator Trace Symmetry:**
   - `tracePairing τ (comm Ω (comm Ω x)) H = tracePairing τ x (comm Ω (comm Ω H))`.
-/
theorem kirillov_coadjoint_leaf_orthogonality_and_brockett_dissipation
    (τ : CyclicTrace B R) (Ω G ρ M H x : B) (hM : comm ρ M = 0) :
    tracePairing τ (souriauRotational Ω ρ) M = 0 ∧
    tracePairing τ (souriauRotational Ω ρ) ρ = 0 ∧
    tracePairing τ (metriplecticFlow Ω G ρ) H =
      tracePairing τ Ω (comm ρ H) - tracePairing τ (comm ρ G) (comm ρ H) ∧
    tracePairing τ (brockettIrrotational G ρ) G =
      - tracePairing τ (comm ρ G) (comm ρ G) ∧
    tracePairing τ (comm Ω (comm Ω x)) H =
      tracePairing τ x (comm Ω (comm Ω H)) := by
  have h2 := node2_souriau_brockett_trace_foliation_and_twin_bimodule τ 0 0 0 x Ω G ρ H M hM
  have h2_zero := (node2_souriau_brockett_trace_foliation_and_twin_bimodule τ 0 0 0 x 0 G ρ G M hM).2.2.2.2.1
  have h_diss :
      tracePairing τ (brockettIrrotational G ρ) G =
        - tracePairing τ (comm ρ G) (comm ρ G) := by
    have h_met0 : metriplecticFlow 0 G ρ = brockettIrrotational G ρ := by
      dsimp only [metriplecticFlow, souriauRotational, comm]
      simp only [zero_mul, mul_zero, sub_self, zero_add]
    have h_tr0 : tracePairing τ 0 (comm ρ G) = 0 := by
      dsimp only [tracePairing]; rw [zero_mul, map_zero]
    rw [h_met0, h_tr0, zero_sub] at h2_zero
    exact h2_zero
  exact ⟨h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h_diss, h2.2.2.2.2.2⟩

-- ============================================================================
-- 6. BIRKHOFF BOUNDARY JORDAN-NILPOTENT SPLIT & MASTER SYNTHESIS
-- ============================================================================

/-- Non-semisimple Jordan-perturbed projector `T = P + N`. -/
def jordanPerturbedProjector (P N : B) : B := P + N

/--
**Jordan-nilpotent boundary split theorem
(`birkhoff_boundary_jordan_nilpotent_split_and_master_synthesis`):**
For an idempotent `P * P = P` and a commuting square-zero nilpotent `N` absorbed by `P`
(`N * N = 0`, `P * N = N`, `N * P = N`), the Jordan-perturbed operator
`T = jordanPerturbedProjector P N = P + N` satisfies:
1. **Semisimple Idempotent Annihilation vs. Non-Semisimple Jordan Defect:**
   - `P * (P - 1) = 0` and `(P - 1) * P = 0`,
   - `(T - P) * (T - P) = 0`,
   - `T * T - T = N`,
2. **Rank-2 Generalized Eigenspace Annihilation at Eigenvalue `1`:**
   - `(T - 1) * P = N`,
   - `(T - 1) * (T - 1) * P = 0`,
3. **Brockett Double-Bracket Expansion on `T = P + N`:**
   - `brockettIrrotational X T = brockettIrrotational X P + comm P (comm N X) + comm N (comm P X) + brockettIrrotational X N`.
-/
theorem birkhoff_boundary_jordan_nilpotent_split_and_master_synthesis
    (P N X : B)
    (hP : P * P = P)
    (hN2 : N * N = 0)
    (hPN : P * N = N)
    (hNP : N * P = N) :
    let T := jordanPerturbedProjector P N
    P * (P - 1) = 0 ∧
    (P - 1) * P = 0 ∧
    (T - P) * (T - P) = 0 ∧
    T * T - T = N ∧
    (T - 1) * P = N ∧
    (T - 1) * (T - 1) * P = 0 ∧
    brockettIrrotational X T =
      brockettIrrotational X P + comm P (comm N X) +
        comm N (comm P X) + brockettIrrotational X N := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_sub, mul_one, hP, sub_self]
  · rw [sub_mul, one_mul, hP, sub_self]
  · dsimp only [jordanPerturbedProjector]
    have h_sub : P + N - P = N := by abel
    rw [h_sub, hN2]
  · dsimp only [jordanPerturbedProjector]
    calc (P + N) * (P + N) - (P + N)
        = P * P + P * N + N * P + N * N - (P + N) := by noncomm_ring
      _ = P + N + N + 0 - (P + N) := by rw [hP, hPN, hNP, hN2]
      _ = N := by abel
  · dsimp only [jordanPerturbedProjector]
    calc (P + N - 1) * P = P * P + N * P - P := by noncomm_ring
      _ = P + N - P := by rw [hP, hNP]
      _ = N := by abel
  · dsimp only [jordanPerturbedProjector]
    have h_step1 : (P + N - 1) * P = N := by
      calc (P + N - 1) * P = P * P + N * P - P := by noncomm_ring
        _ = P + N - P := by rw [hP, hNP]
        _ = N := by abel
    calc (P + N - 1) * (P + N - 1) * P
        = (P + N - 1) * ((P + N - 1) * P) := by rw [mul_assoc]
      _ = (P + N - 1) * N := by rw [h_step1]
      _ = P * N + N * N - N := by noncomm_ring
      _ = N + 0 - N := by rw [hPN, hN2]
      _ = 0 := by abel
  · dsimp only [jordanPerturbedProjector, brockettIrrotational, comm]
    noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine.YoshizawaGradientFlowInfoGeometryPoset
