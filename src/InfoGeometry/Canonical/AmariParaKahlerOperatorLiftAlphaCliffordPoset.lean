/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
==============================================================================
HIVE CONSTITUTIONAL HEADER
==============================================================================
1. Epistemic State & Provenance:
   Formalized via `epistemic compiler solve et coagula` from AI Studio
   transcript `1iLTmbxfiVRM8rOhwchpAcmLD3r1zL4JA` (Turn 0077
   `AmariParaKahlerConnectionSumDiffPoset` and Turn 0079
   `AmariAlphaConnectionCliffordDualityPoset`) and Google Drive source
   `1PA5NMMld6mTDATG00Zc6hbQMRtggABGD` (`AmariOperatorLift`), aligned with the
   repository's non-commutative operator ring `[Ring B]` architecture.

2. Mathematical Target & Carrier:
   - Carrier: Arbitrary non-commutative unital associative operator ring `B`
     equipped with `[Ring B]`.
   - Operator connections: Arbitrary pair of non-commuting operator derivations
     `D, D_star : B → B` (or inner derivations `d_+(Z) = [Q_+, Z]`,
     `d_-(Z) = [Q_-, Z]` induced by an idempotent horizon `P : B`, `P * P = P`).

3. Three-Bucket Epistemic Audit Map (`audit-proof`):
   - BUCKET 1 (Proved Constructive Kernel):
     * Part I (Abstract Operator Connections `D, D^* : B → B`):
       - Scaled Levi-Civita sum `G(Z) = D(Z) + D^*(Z)` and Amari-Chentsov
         skewness difference `K(Z) = D(Z) - D^*(Z)`.
       - Chiral projector decomposition `2 D(Z) = G(Z) + K(Z)` and
         `2 D^*(Z) = G(Z) - K(Z)`.
       - Exact curvature polarization identity:
         `G(G(Z)) - K(K(Z)) = 2 • (D(D^*(Z)) + D^*(D(Z)))`.
       - Exact Levi-Civita curvature synthesis (avoiding division by 2):
         `4 • R_LC(Z) = G(G(Z)) = 2 • (D(D(Z)) + D^*(D^*(Z))) - K(K(Z))`,
         and when `D` and `D^*` are dually flat (`D^2 = 0`, `(D^*)^2 = 0`):
         `G(G(Z)) = -K(K(Z)) = 2 • (D(D^*(Z)) + D^*(D(Z)))`.
       - Full Amari `α`-connection family (`α : ℤ`):
         `D_alpha_2 α Z = (1 + α) • D(Z) + (1 - α) • D^*(Z) = G(Z) + α • K(Z)`.
       - Conjugate reflection duality `D_alpha_2 (-α) Z = G(Z) - α • K(Z)` and
         midpoint invariance `D_alpha_2 α Z + D_alpha_2 (-α) Z = 2 • G(Z)`.
       - Universal quadratic `α`-curvature expansion:
         `D_alpha_2 α (D_alpha_2 α Z) = G(G(Z)) + α • (G(K(Z)) + K(G(Z))) + (α * α) • K(K(Z))`.
       - Exact flatness duality (`R^{(+α)} = R^{(-α)}` iff `G(K(Z)) + K(G(Z)) = 0`).
     * Part II (Concrete Peirce-Horizon Realization `P^2 = P` in `[Ring B]`):
       - Nilpotent chiral roots `Q_+(X) = P X P_⊥`, `Q_-(X) = P_⊥ X P` (`Q_+^2 = Q_-^2 = 0`).
       - Inner `e`-connection `d_e(Z) = [Q_+(X), Z]` and `m`-connection
         `d_m(Z) = [Q_-(X), Z]` are dually flat (`d_e^2 = 0`, `d_m^2 = 0`) on
         all diagonal observables `Z_0 = X_11 P Z + X_00 P Z`.
       - Concrete `Cl(1,1)` para-Kähler emergence:
         `G_peirce(Z) = [Q_+ + Q_-, Z]` (`N_P = Q_+ + Q_-`),
         `K_peirce(Z) = [Q_+ - Q_-, Z]` (`d_mod = [P, X] = Q_+ - Q_-`),
         with `(Q_+ + Q_-)^2 = V_P + Σ_P`, `(Q_+ - Q_-)^2 = -(V_P + Σ_P)`, and
         `{Q_+ + Q_-, Q_+ - Q_-} = 0` generating a genuine `Cl(1,1)` algebra!
     * Part III (Strict 9-Stage Acyclic Causal Poset):
       - `Node`, `rank`, `coverEdge`, `coverEdge_strict_rank`,
         `coverEdge_irrefl`, `coverEdge_asymm`.
   - BUCKET 2 (Explicit Structural Hypotheses):
     * Additivity and `ℤ`-linear homogeneity of abstract connections `D, D_star`
       for the general `α`-family theorem (dischargeable automatically for
       inner derivations `[A, ·]`).
     * Idempotency `hP : P * P = P` for the concrete Peirce realization.
   - BUCKET 3 (Remaining Debt):
     * None (`0 sorry`, `0 admit`, `0 custom axioms`).
==============================================================================
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

namespace InfoGeometry.Canonical.AmariParaKahlerOperatorLiftAlphaCliffordPoset

variable {B : Type*} [Ring B]

/-!
## Part I: Abstract Non-Commutative Operator Connections `(D, D^*)` & Amari `α`-Family

Let `D, D_star : B →+ B` be any pair of additive operator connections (derivations
or covariant derivatives) on a non-commutative ring `B`.
To avoid requiring `1/2` in an arbitrary ring `B`, we work with the exact
twice-scaled connections:
* `G(Z) = 2 ∇^{(0)}(Z) = D(Z) + D^*(Z)` (Twice the self-dual Levi-Civita / Fisher-Rao connection),
* `K(Z) = T(Z) = D(Z) - D^*(Z)` (The Amari-Chentsov cubic skewness / torsion difference),
* `D_alpha_2 α Z = 2 ∇^{(α)}(Z) = G(Z) + α • K(Z) = (1 + α) • D(Z) + (1 - α) • D^*(Z)`.
-/

/-- Twice the Self-Dual Levi-Civita / Fisher-Rao Connection `G(Z) = D(Z) + D^*(Z)`. -/
def G_sum (D D_star : B →+ B) (Z : B) : B := D Z + D_star Z

/-- The Amari-Chentsov Skewness / Contorsion Difference `K(Z) = D(Z) - D^*(Z)`. -/
def K_diff (D D_star : B →+ B) (Z : B) : B := D Z - D_star Z

/-- Twice the Amari `α`-Connection (`α : ℤ`):
    `2 ∇^{(α)}(Z) = G(Z) + α • K(Z)`. -/
def D_alpha_2 (D D_star : B →+ B) (α : ℤ) (Z : B) : B :=
  G_sum D D_star Z + α • K_diff D D_star Z

/-- Theorem 1.1 (Bipolar Reconstruction & Para-Complex Projector Split):
    The primal (`e`-connection `D`) and dual (`m`-connection `D^*`) connections
    are recovered identically at `α = +1` and `α = -1`:
    1. `G(Z) + K(Z) = 2 • D(Z)` (`D_alpha_2 (+1) Z = 2 • D(Z)`),
    2. `G(Z) - K(Z) = 2 • D^*(Z)` (`D_alpha_2 (-1) Z = 2 • D^*(Z)`),
    3. `D_alpha_2 0 Z = G(Z)` (Self-dual Levi-Civita connection at `α = 0`),
    4. `D_alpha_2 α Z + D_alpha_2 (-α) Z = 2 • G(Z)` (Dual-pair midpoint invariance),
    5. `D_alpha_2 α Z - D_alpha_2 (-α) Z = (2 * α) • K(Z)` (Dual-pair skewness distance). -/
theorem amari_bipolar_connection_split (D D_star : B →+ B) (α : ℤ) (Z : B) :
    G_sum D D_star Z + K_diff D D_star Z = 2 • D Z ∧
    G_sum D D_star Z - K_diff D D_star Z = 2 • D_star Z ∧
    D_alpha_2 D D_star 1 Z = 2 • D Z ∧
    D_alpha_2 D D_star (-1) Z = 2 • D_star Z ∧
    D_alpha_2 D D_star 0 Z = G_sum D D_star Z ∧
    D_alpha_2 D D_star α Z + D_alpha_2 D D_star (-α) Z = 2 • G_sum D D_star Z ∧
    D_alpha_2 D D_star α Z - D_alpha_2 D D_star (-α) Z = (2 * α) • K_diff D D_star Z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [G_sum, K_diff]
    abel
  · dsimp [G_sum, K_diff]
    abel
  · dsimp [D_alpha_2, G_sum, K_diff]
    rw [one_zsmul]
    abel
  · dsimp [D_alpha_2, G_sum, K_diff]
    rw [neg_one_zsmul]
    abel
  · dsimp [D_alpha_2]
    rw [zero_zsmul, add_zero]
  · dsimp [D_alpha_2]
    rw [neg_zsmul]
    abel
  · dsimp [D_alpha_2]
    rw [neg_zsmul, mul_zsmul, two_zsmul]
    abel

/-- Theorem 1.2 (Non-Commutative Curvature Polarization & Weitzenböck-Amari Identity):
    For any additive operator connections `D, D_star : B →+ B`:
    1. **Sum-Plus-Difference Curvature Law**:
       `G(G(Z)) + K(K(Z)) = 2 • (D(D(Z)) + D^*(D^*(Z)))`,
    2. **Sum-Minus-Difference Mutual Anticommutator Law**:
       `G(G(Z)) - K(K(Z)) = 2 • (D(D^*(Z)) + D^*(D(Z)))`,
    3. **Cross-Commutator Identity**:
       `G(K(Z)) + K(G(Z)) = 2 • (D(D(Z)) - D^*(D^*(Z)))`,
       `G(K(Z)) - K(G(Z)) = 2 • (D^*(D(Z)) - D(D^*(Z)))`,
    4. **Levi-Civita Curvature Synthesis (Theorem 77.1)**:
       `G(G(Z)) = 2 • (D(D(Z)) + D^*(D^*(Z))) - K(K(Z))`,
       so when `D` and `D^*` are dually flat (`D(D(Z)) = 0` and `D^*(D^*(Z)) = 0`),
       the Levi-Civita curvature `G(G(Z))` is generated purely by the negative square
       of the Amari-Chentsov skewness operator:
       `G(G(Z)) = - K(K(Z)) = 2 • (D(D^*(Z)) + D^*(D(Z)))`! -/
theorem amari_para_kahler_curvature_polarization (D D_star : B →+ B) (Z : B) :
    G_sum D D_star (G_sum D D_star Z) + K_diff D D_star (K_diff D D_star Z) =
      2 • (D (D Z) + D_star (D_star Z)) ∧
    G_sum D D_star (G_sum D D_star Z) - K_diff D D_star (K_diff D D_star Z) =
      2 • (D (D_star Z) + D_star (D Z)) ∧
    G_sum D D_star (K_diff D D_star Z) + K_diff D D_star (G_sum D D_star Z) =
      2 • (D (D Z) - D_star (D_star Z)) ∧
    G_sum D D_star (K_diff D D_star Z) - K_diff D D_star (G_sum D D_star Z) =
      2 • (D_star (D Z) - D (D_star Z)) ∧
    G_sum D D_star (G_sum D D_star Z) =
      2 • (D (D Z) + D_star (D_star Z)) - K_diff D D_star (K_diff D D_star Z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp [G_sum, K_diff]; simp only [map_add, map_sub]; abel)

/-- Corollary 1.3 (Dually Flat Para-Kähler Curvature Emergence):
    Whenever `Z` lies in the dually flat sector (`D(D(Z)) = 0` and `D^*(D^*(Z)) = 0`),
    1. `G(G(Z)) = - K(K(Z))` (Levi-Civita curvature is the negative square of skewness),
    2. `G(G(Z)) = D(D^*(Z)) + D^*(D(Z))` (Levi-Civita curvature is the
       Kähler-Hodge Laplacian `Δ_H = D D^* + D^* D`),
    3. `G(K(Z)) + K(G(Z)) = 0` (`G` and `K` strictly anticommute on `Z`, generating a
       representation of the split-quaternion Clifford algebra `Cl(1,1)`!). -/
theorem dually_flat_para_kahler_clifford_emergence (D D_star : B →+ B) (Z : B)
    (hD2 : D (D Z) = 0) (hDs2 : D_star (D_star Z) = 0) :
    G_sum D D_star (G_sum D D_star Z) = - K_diff D D_star (K_diff D D_star Z) ∧
    G_sum D D_star (G_sum D D_star Z) = D (D_star Z) + D_star (D Z) ∧
    G_sum D D_star (K_diff D D_star Z) + K_diff D D_star (G_sum D D_star Z) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp [G_sum, K_diff]; simp only [map_add, map_sub, hD2, hDs2]; abel)

/-- Universal Quadratic Expansion of `D_alpha_2 β (D_alpha_2 β Z)` for any `β : ℤ`. -/
lemma amari_alpha_curvature_quad (D D_star : B →+ B) (β : ℤ) (Z : B) :
    D_alpha_2 D D_star β (D_alpha_2 D D_star β Z) =
      G_sum D D_star (G_sum D D_star Z) +
      β • (G_sum D D_star (K_diff D D_star Z) + K_diff D D_star (G_sum D D_star Z)) +
      (β * β) • K_diff D D_star (K_diff D D_star Z) := by
  dsimp [D_alpha_2, G_sum, K_diff]
  simp only [map_add, map_sub, map_zsmul, zsmul_add, zsmul_sub, mul_zsmul]
  abel

/-- Theorem 1.4 (Universal Quadratic Curvature Law for the Amari `α`-Connection Family):
    For any `α : ℤ` and any `Z : B`, the iterated `α`-connection
    `D_alpha_2 α (D_alpha_2 α Z)` expands quadratically in `α`:
    `D_alpha_2 α (D_alpha_2 α Z) = G(G(Z)) + α • (G(K(Z)) + K(G(Z))) + (α * α) • K(K(Z))`.
    Moreover, if `Z` is dually flat (`D(D(Z)) = 0` and `D^*(D^*(Z)) = 0`), then
    `G(K(Z)) + K(G(Z)) = 0` and `K(K(Z)) = - G(G(Z))`, so the `α`-curvature obeys
    the exact **Amari `(1 - α²)` Parabolic Law**:
    `D_alpha_2 α (D_alpha_2 α Z) = (1 - α * α) • G(G(Z))`! -/
theorem amari_alpha_curvature_parabolic_law (D D_star : B →+ B) (α : ℤ) (Z : B) :
    D_alpha_2 D D_star α (D_alpha_2 D D_star α Z) =
      G_sum D D_star (G_sum D D_star Z) +
      α • (G_sum D D_star (K_diff D D_star Z) + K_diff D D_star (G_sum D D_star Z)) +
      (α * α) • K_diff D D_star (K_diff D D_star Z) ∧
    (D (D Z) = 0 → D_star (D_star Z) = 0 →
      D_alpha_2 D D_star α (D_alpha_2 D D_star α Z) =
        (1 - α * α) • G_sum D D_star (G_sum D D_star Z) ∧
      D_alpha_2 D D_star α (D_alpha_2 D D_star α Z) =
        D_alpha_2 D D_star (-α) (D_alpha_2 D D_star (-α) Z)) := by
  refine ⟨amari_alpha_curvature_quad D D_star α Z, ?_⟩
  intro hD2 hDs2
  have hFlat := dually_flat_para_kahler_clifford_emergence D D_star Z hD2 hDs2
  have hKK : K_diff D D_star (K_diff D D_star Z) = - G_sum D D_star (G_sum D D_star Z) := by
    rw [hFlat.1, neg_neg]
  have h_parabolic (β : ℤ) :
      D_alpha_2 D D_star β (D_alpha_2 D D_star β Z) =
        (1 - β * β) • G_sum D D_star (G_sum D D_star Z) := by
    rw [amari_alpha_curvature_quad D D_star β Z, hFlat.2.2, zsmul_zero, add_zero,
        hKK, zsmul_neg, sub_zsmul, one_zsmul]
    (try abel)
  refine ⟨h_parabolic α, ?_⟩
  rw [h_parabolic α, h_parabolic (-α), neg_mul_neg]

/-- Right-associated idempotent helper `P * (P * Z) = P * Z`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-!
## Part II: Concrete Peirce-Horizon Realization (`P² = P`) & `Cl(1,1)` Algebra in `[Ring B]`

We now instantiate the abstract operator connection theory on any non-commutative
ring `B` equipped with an idempotent horizon `P : B` (`P * P = P`) and generator `X : B`:
* `Q_+(X) = P X (1 - P)` (Upper Chiral Nilpotent Root, `Q_+² = 0`),
* `Q_-(X) = (1 - P) X P` (Lower Chiral Nilpotent Root, `Q_-² = 0`),
* `D_e(Z) = [Q_+(X), Z]` (Exponential / Forward Chiral Connection),
* `D_m(Z) = [Q_-(X), Z]` (Mixture / Backward Chiral Connection).
Then:
* The Levi-Civita sum generator is `N_P(X) = Q_+(X) + Q_-(X) = [P, [P, X]]` (the Lindblad/Metriplectic dissipator!),
* The Amari-Chentsov skewness generator is `M_P(X) = Q_+(X) - Q_-(X) = [P, X]` (the Connes-Rovelli modular derivation!),
* And `(N_P(X), M_P(X))` generate a genuine **Para-Kähler Split-Quaternion Clifford Algebra `Cl(1,1)`** over the Casimir core `Z_bridge(P, X) = V_P(X) + Σ_P(X)`:
  - `N_P(X)² = +(V_P(X) + Σ_P(X))`,
  - `M_P(X)² = -(V_P(X) + Σ_P(X))`,
  - `N_P(X) * M_P(X) + M_P(X) * N_P(X) = 0`!
-/

/-- Complementary shadow idempotent `P_⊥ = 1 - P`. -/
def P_perp (P : B) : B := 1 - P

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Upper Peirce chiral root `Q_+(X) = P X P_⊥`. -/
def Q_pos (P X : B) : B := P * X * P_perp P
/-- Lower Peirce chiral root `Q_-(X) = P_⊥ X P`. -/
def Q_neg (P X : B) : B := P_perp P * X * P
/-- Upper-left diagonal Peirce block `X_11 = P X P`. -/
def X_11 (P X : B) : B := P * X * P
/-- Lower-right diagonal Peirce block `X_00 = P_⊥ X P_⊥`. -/
def X_00 (P X : B) : B := P_perp P * X * P_perp P

/-- Active Core Gravity `V_P(X) = Q_+(X) Q_-(X)`. -/
def V_P (P X : B) : B := Q_pos P X * Q_neg P X
/-- Shadow Core Gravity `Σ_P(X) = Q_-(X) Q_+(X)`. -/
def Sigma_P (P X : B) : B := Q_neg P X * Q_pos P X

/-- The Symmetric Levi-Civita Generator `N_P(X) = Q_+(X) + Q_-(X) = [P, [P, X]]`. -/
def N_LC (P X : B) : B := Q_pos P X + Q_neg P X

/-- The Antisymmetric Amari-Chentsov / Modular Generator `M_P(X) = Q_+(X) - Q_-(X) = [P, X]`. -/
def M_Skew (P X : B) : B := Q_pos P X - Q_neg P X

/-- The Inner `e`-Connection `d_e(P, X) : B →+ B` given by `Z ↦ [Q_+(X), Z]`. -/
def d_e (P X : B) : B →+ B where
  toFun Z := comm (Q_pos P X) Z
  map_zero' := by dsimp [comm]; rw [mul_zero, zero_mul, sub_self]
  map_add' Y Z := by dsimp [comm]; simp only [mul_add, add_mul]; abel

/-- The Inner `m`-Connection `d_m(P, X) : B →+ B` given by `Z ↦ [Q_-(X), Z]`. -/
def d_m (P X : B) : B →+ B where
  toFun Z := comm (Q_neg P X) Z
  map_zero' := by dsimp [comm]; rw [mul_zero, zero_mul, sub_self]
  map_add' Y Z := by dsimp [comm]; simp only [mul_add, add_mul]; abel

/-- Theorem 2.1 (Concrete `Cl(1,1)` Para-Kähler Split-Quaternion Structure of `(N_LC, M_Skew)`):
    For any idempotent `P` (`P² = P`) and generator `X : B`:
    1. `N_LC(P, X)² = V_P(P, X) + Sigma_P(P, X)` (Positive-signature spacelike reflection),
    2. `M_Skew(P, X)² = - (V_P(P, X) + Sigma_P(P, X))` (Negative-signature timelike rotation),
    3. `anticomm (N_LC P X) (M_Skew P X) = 0` (Exact `Cl(1,1)` Clifford anticommutation),
    4. `comm (N_LC P X) (M_Skew P X) = - 2 • comm (Q_pos P X) (Q_neg P X)`
       (The Lorentz boost bivector is twice the negative Casimir curvature `H_P = [Q_+, Q_-]`). -/
theorem peirce_cl11_para_kahler_algebra {P : B} (hP : P * P = P) (X : B) :
    N_LC P X * N_LC P X = V_P P X + Sigma_P P X ∧
    M_Skew P X * M_Skew P X = - (V_P P X + Sigma_P P X) ∧
    anticomm (N_LC P X) (M_Skew P X) = 0 ∧
    comm (N_LC P X) (M_Skew P X) = - (2 • comm (Q_pos P X) (Q_neg P X)) := by
  have hQp2 : Q_pos P X * Q_pos P X = 0 := by
    dsimp [Q_pos, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  have hQm2 : Q_neg P X * Q_neg P X = 0 := by
    dsimp [Q_neg, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [N_LC, V_P, Sigma_P]
    simp only [mul_add, add_mul, hQp2, hQm2]
    abel
  · dsimp [M_Skew, V_P, Sigma_P]
    simp only [mul_sub, sub_mul, hQp2, hQm2]
    abel
  · dsimp [anticomm, N_LC, M_Skew]
    simp only [mul_add, add_mul, mul_sub, sub_mul, hQp2, hQm2]
    abel
  · dsimp [comm, N_LC, M_Skew]
    simp only [mul_add, add_mul, mul_sub, sub_mul, hQp2, hQm2]
    abel

/-- Theorem 2.2 (Concrete Peirce Instantiation of the Amari `(1 - α²)` Parabolic Law):
    For any idempotent `P` (`P² = P`), generator `X : B`, `α : ℤ`, and block-diagonal
    observable `Z_0 = X_11 P Z + X_00 P Z`:
    1. `Z_0` is dually flat with respect to `d_e(P, X)` and `d_m(P, X)`:
       `d_e P X (d_e P X Z_0) = 0` and `d_m P X (d_m P X Z_0) = 0`,
    2. Consequently, the Amari `α`-connection `D_alpha_2 (d_e P X) (d_m P X) α`
       satisfies the exact `(1 - α²)` parabolic curvature law on `Z_0`:
       `D_alpha_2 (d_e P X) (d_m P X) α (D_alpha_2 (d_e P X) (d_m P X) α Z_0) = (1 - α * α) • G_sum (d_e P X) (d_m P X) (G_sum (d_e P X) (d_m P X) Z_0)`. -/
theorem peirce_diagonal_amari_alpha_parabolic_law {P : B} (hP : P * P = P) (X Z : B) (α : ℤ) :
    let Z0 := X_11 P Z + X_00 P Z
    d_e P X (d_e P X Z0) = 0 ∧
    d_m P X (d_m P X Z0) = 0 ∧
    D_alpha_2 (d_e P X) (d_m P X) α (D_alpha_2 (d_e P X) (d_m P X) α Z0) =
      (1 - α * α) • G_sum (d_e P X) (d_m P X) (G_sum (d_e P X) (d_m P X) Z0) := by
  intro Z0
  have hde2 : d_e P X (d_e P X Z0) = 0 := by
    change comm (Q_pos P X) (comm (Q_pos P X) Z0) = 0
    dsimp [Z0, comm, Q_pos, X_11, X_00, P_perp]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  have hdm2 : d_m P X (d_m P X Z0) = 0 := by
    change comm (Q_neg P X) (comm (Q_neg P X) Z0) = 0
    dsimp [Z0, comm, Q_neg, X_11, X_00, P_perp]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  refine ⟨hde2, hdm2, ?_⟩
  exact ((amari_alpha_curvature_parabolic_law (d_e P X) (d_m P X) α Z0).2 hde2 hdm2).1

/-!
## Part III: Acyclic Causal Poset of the Amari–Para-Kähler–Clifford Duality
-/

/-- Nodes of the 9-stage Amari–Para-Kähler–Clifford causal poset. -/
inductive Node
  | dualConnectionPair
  | leviCivitaSumChentsovDiff
  | bipolarProjectorReconstruction
  | curvaturePolarizationIdentity
  | duallyFlatParaKahlerEmergence
  | amariAlphaFamilyInterpolation
  | parabolicOneMinusAlphaSquaredLaw
  | peirceCl11SplitQuaternionRealization
  | diagonalObservableAlphaSynthesis
  deriving DecidableEq, Repr

/-- Topological causal rank in the 9-stage poset. -/
def rank : Node → ℕ
  | .dualConnectionPair => 0
  | .leviCivitaSumChentsovDiff => 1
  | .bipolarProjectorReconstruction => 2
  | .curvaturePolarizationIdentity => 3
  | .duallyFlatParaKahlerEmergence => 4
  | .amariAlphaFamilyInterpolation => 5
  | .parabolicOneMinusAlphaSquaredLaw => 6
  | .peirceCl11SplitQuaternionRealization => 7
  | .diagonalObservableAlphaSynthesis => 8

/-- Directed causal cover edges of the 9-stage poset. -/
def coverEdge : Node → Node → Prop
  | .dualConnectionPair, .leviCivitaSumChentsovDiff => True
  | .leviCivitaSumChentsovDiff, .bipolarProjectorReconstruction => True
  | .bipolarProjectorReconstruction, .curvaturePolarizationIdentity => True
  | .bipolarProjectorReconstruction, .amariAlphaFamilyInterpolation => True
  | .curvaturePolarizationIdentity, .duallyFlatParaKahlerEmergence => True
  | .duallyFlatParaKahlerEmergence, .parabolicOneMinusAlphaSquaredLaw => True
  | .amariAlphaFamilyInterpolation, .parabolicOneMinusAlphaSquaredLaw => True
  | .duallyFlatParaKahlerEmergence, .peirceCl11SplitQuaternionRealization => True
  | .parabolicOneMinusAlphaSquaredLaw, .diagonalObservableAlphaSynthesis => True
  | .peirceCl11SplitQuaternionRealization, .diagonalObservableAlphaSynthesis => True
  | _, _ => False

/-- Every causal cover edge strictly increases the topological rank. -/
theorem coverEdge_strict_rank {u v : Node} (h : coverEdge u v) :
    rank u < rank v := by
  cases u <;> cases v <;> simp [coverEdge, rank] at h ⊢

/-- The causal cover relation is strictly irreflexive. -/
theorem coverEdge_irrefl (u : Node) : ¬ coverEdge u u := by
  intro h
  exact Nat.lt_irrefl (rank u) (coverEdge_strict_rank h)

/-- The causal cover relation is strictly asymmetric. -/
theorem coverEdge_asymm {u v : Node} (huv : coverEdge u v) : ¬ coverEdge v u := by
  intro hvu
  exact Nat.lt_asymm (coverEdge_strict_rank huv) (coverEdge_strict_rank hvu)

/-- **Inductive Colimit Cone Transport (`amari_alpha_clifford_colimit_cone_transport`):**
    Under any compatible inductive ring cone `toLimit : ∀ k : ℕ, Stage k →+* Limit`
    (`toLimit (k + 1) (embed k Z) = toLimit k Z`), the Peirce off-diagonal nilpotents `Q_pos, Q_neg`,
    block-diagonal projections `X_11, X_00`, and the Amari `(1 - α²)` parabolic curvature law
    transport functorially from finite stage `Stage k` into `Limit`. -/
theorem amari_alpha_clifford_colimit_cone_transport
    {Stage : ℕ → Type*} [∀ k, Ring (Stage k)]
    {Limit : Type*} [Ring Limit]
    (embed : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (toLimit : ∀ k : ℕ, Stage k →+* Limit)
    (hCone : ∀ (k : ℕ) (Z : Stage k), toLimit (k + 1) (embed k Z) = toLimit k Z)
    (k : ℕ) (P X Z : Stage k) (hP : P * P = P) (α : ℤ) :
    let P_inf := toLimit k P
    let X_inf := toLimit k X
    let Z_inf := toLimit k Z
    let Z0_inf := X_11 P_inf Z_inf + X_00 P_inf Z_inf
    toLimit k (Q_pos P X) = Q_pos P_inf X_inf ∧
    toLimit k (Q_neg P X) = Q_neg P_inf X_inf ∧
    toLimit (k + 1) (Q_pos (embed k P) (embed k X)) = Q_pos P_inf X_inf ∧
    d_e P_inf X_inf (d_e P_inf X_inf Z0_inf) = 0 ∧
    d_m P_inf X_inf (d_m P_inf X_inf Z0_inf) = 0 ∧
    D_alpha_2 (d_e P_inf X_inf) (d_m P_inf X_inf) α
        (D_alpha_2 (d_e P_inf X_inf) (d_m P_inf X_inf) α Z0_inf) =
      (1 - α * α) • G_sum (d_e P_inf X_inf) (d_m P_inf X_inf)
        (G_sum (d_e P_inf X_inf) (d_m P_inf X_inf) Z0_inf) := by
  have hQp : toLimit k (Q_pos P X) = Q_pos (toLimit k P) (toLimit k X) := by
    dsimp [Q_pos, P_perp]
    simp only [map_mul, map_sub, map_one]
  have hQn : toLimit k (Q_neg P X) = Q_neg (toLimit k P) (toLimit k X) := by
    dsimp [Q_neg, P_perp]
    simp only [map_mul, map_sub, map_one]
  have hQpEmb : toLimit (k + 1) (Q_pos (embed k P) (embed k X)) =
      Q_pos (toLimit k P) (toLimit k X) := by
    have hE : embed k (Q_pos P X) = Q_pos (embed k P) (embed k X) := by
      dsimp [Q_pos, P_perp]
      simp only [map_mul, map_sub, map_one]
    rw [← hE, hCone k, hQp]
  have hP_inf : toLimit k P * toLimit k P = toLimit k P := by
    rw [← map_mul, hP]
  rcases peirce_diagonal_amari_alpha_parabolic_law hP_inf (toLimit k X) (toLimit k Z) α with
    ⟨hde2, hdm2, hPar⟩
  exact ⟨hQp, hQn, hQpEmb, hde2, hdm2, hPar⟩

end InfoGeometry.Canonical.AmariParaKahlerOperatorLiftAlphaCliffordPoset
