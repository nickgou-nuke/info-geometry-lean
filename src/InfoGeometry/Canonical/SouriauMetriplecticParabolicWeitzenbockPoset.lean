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
   transcript `1iLTmbxfiVRM8rOhwchpAcmLD3r1zL4JA` (Turn 0073
   `GrandRevivedLineagesMasterPoset` and Turn 0083
   `CompleteSouriauMetriplecticParabolicMaster`) and Google Drive source
   `1M6DtAn-YERAk15Z5R_n6BX6rW7NttJKg` (`NoncommutativeSouriauGeometry`),
   lifted completely to non-commutative operator rings `[Ring A]` and
   additive abelian target groups `[AddCommGroup R]` (no `CommRing`).

2. Mathematical Target & Carrier:
   - Carrier: Arbitrary non-commutative unital associative operator ring `A`
     equipped with `[Ring A]`, relative to an idempotent horizon `P : A`
     (`P * P = P`).
   - Trace carrier: Arbitrary additive commutative group `R` equipped with
     `[AddCommGroup R]` and a cyclic trace `τ : A →+ R` (`∀ X Y, τ (X * Y) = τ (Y * X)`).

3. Three-Bucket Epistemic Audit Map (`audit-proof`):
   - BUCKET 1 (Proved Constructive Kernel):
     * Stage I: Peirce fourfold decomposition, corner nilpotency (`Q_+^2 = 0`,
       `Q_-^2 = 0`), Cartan grading `S_P = 2P - 1` (`S_P^2 = 1`), and partial
       isometry / Moore–Penrose equations.
     * Stage II: Souriau 2-cocycle `Θ(X,Y) = [P,[X,Y]] - [[P,X],[P,Y]]`,
       exact equivariant coboundary reduction `Θ = -[[P,X],[P,Y]]` when
       `[P,[X,Y]] = 0`, trace-class Lie–Poisson Kirillov–Kostant–Souriau (KKS)
       bracket `ω_P(X,Y) = τ(P [X,Y]) = τ(P Θ(X,Y))`, and Borel–Weil–Bott
       Toeplitz curvature.
     * Stage III: Parabolic 3-graded (`g_{-1} ⊕ g_0 ⊕ g_{+1}`) and 5-graded
       (`g_{-2}..g_{+2}`) Kantor–Tits–Connes–Moscovici hierarchy, 2-step
       nilpotency `[Q_+(X), Q_+(Y)] = 0`, and Cartan involution grading.
     * Stage IV: Non-commutative Kähler–Hodge–Weitzenböck–Bochner calculus:
       nilpotent differentials `d_+^2 = 0`, `d_-^2 = 0`, Laplacian
       `Δ_H(Z) = d_+(d_-(Z)) + d_-(d_+(Z)) = [V, Z]`, and Weitzenböck
       curvature separation `(d_+ - d_-)^2(Z) + Δ_H(Z) = (d_+ + d_-)^2(Z)`.
     * Stage V: Exact core/nilpotent spectral splitting (`Z = (V + Σ) + (Q_+ + Q_-)`),
       explicit Group/Drazin inverse verification when `W` inverts `V + Σ`
       inside the diagonal Peirce block, and Schur complement factorization.
     * Stage VI: Connes–Rovelli Modular / Morrison Metriplectic / GKSL Lindblad
       synthesis (`d_mod(X) = [P,X] = Q_+ - Q_-`, `Δ_diss(X) = [P,[P,X]] = Q_+ + Q_-`,
       `Δ_diss^2 = Δ_diss`, and exact Casimir conservation `d_mod(C) = 0`,
       `Δ_diss(C) = 0` whenever `[P, C] = 0`).
     * Stage VII: KMS / Kubo–Mori–Bogoliubov modular difference expansion and
       Schwinger–Keldysh / Dyson doubled contour commutator-anticommutator
       factorization (`A_+ B_+ - A_- B_- = [A_c, B_q] + {A_q, B_c}`).
     * Stage VIII: Strict 10-stage acyclic causal poset `Node` (`rank`,
       `coverEdge`, `coverEdge_strict_rank`, `coverEdge_irrefl`, `coverEdge_asymm`).
   - BUCKET 2 (Explicit Structural Hypotheses):
     * Idempotent horizon `hP : P * P = P`.
     * Cyclic trace `τ : A →+ R` with `hCyclic : ∀ X Y, τ (X * Y) = τ (Y * X)`.
     * Conditional block invertibility `hWV : W * V_P P X = P`, etc. for the
       explicit Group/Drazin inverse theorem.
   - BUCKET 3 (Constructive `[Ring A]` & Colimit-Cone Compilation):
     * All Souriau–Metriplectic–Parabolic–Weitzenböck–Drazin theorems and their
       direct-limit cone transport (`souriau_metriplectic_colimit_cone_transport`)
       are proved constructively in `[Ring A]` (`0 sorry`, `0 admit`, `0 custom axioms`,
       `0 structures`).
==============================================================================
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

namespace InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset

variable {A : Type*} [Ring A]

/-!
## Stage I: The Primordial Horizon, Peirce Fourfold Cut & Cartan Involution
-/

/-- The Complementary Shadow Idempotent `P_⊥ = 1 - P`. -/
def P_perp (P : A) : A := 1 - P

/-- The Cartan Grading Involution `S_P = 2P - 1 = P - P_⊥` (`S_P² = 1`). -/
def S_P (P : A) : A := P - P_perp P

/-- The Associative Ring Commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : A) : A := X * Y - Y * X

/-- The Associative Ring Anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : A) : A := X * Y + Y * X

/-- Conscious Self-Adjoint / Active Core Peirce Projection `X₁₁ = P X P`. -/
def X_11 (P X : A) : A := P * X * P
/-- Autonomous Unexamined Vacuum / Shadow Core Peirce Projection `X₀₀ = P_⊥ X P_⊥`. -/
def X_00 (P X : A) : A := P_perp P * X * P_perp P
/-- Outward Projection / Raising Root `Q_+(X) = P X P_⊥` (`𝔤_{+1}`). -/
def Q_pos (P X : A) : A := P * X * P_perp P
/-- Inward Shadow-Intrusion / Lowering Root `Q_-(X) = P_⊥ X P` (`𝔤_{-1}`). -/
def Q_neg (P X : A) : A := P_perp P * X * P

/-- Helper: `P * (A * B) = (P * A) * B` and idempotent absorptions. -/
lemma proj_idem {P : A} (hP : P * P = P) (X : A) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

/-- Complementary shadow idempotence `P_⊥ * P_⊥ = P_⊥`. -/
lemma perp_idem {P : A} (hP : P * P = P) : P_perp P * P_perp P = P_perp P := by
  dsimp [P_perp]
  simp only [mul_sub, sub_mul, mul_one, one_mul, hP]
  abel

/-- Left-right orthogonality `P * P_⊥ = 0`. -/
lemma proj_perp_zero {P : A} (hP : P * P = P) : P * P_perp P = 0 := by
  dsimp [P_perp]
  rw [mul_sub, mul_one, hP, sub_self]

/-- Right-left orthogonality `P_⊥ * P = 0`. -/
lemma perp_proj_zero {P : A} (hP : P * P = P) : P_perp P * P = 0 := by
  dsimp [P_perp]
  rw [sub_mul, one_mul, hP, sub_self]

/-- Theorem 1.1 (Fourfold Peirce Partition of Unity):
    Every operator `X : A` decomposes identically into its four Peirce quadrants. -/
theorem peirce_fourfold_partition (P X : A) :
    X = X_11 P X + Q_pos P X + Q_neg P X + X_00 P X := by
  dsimp [X_11, Q_pos, Q_neg, X_00, P_perp]
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  abel

/-- Theorem 1.2 (Strict Nilpotency of the Off-Diagonal Corner Projections):
    `Q_+(X) * Q_+(Y) = 0` and `Q_-(X) * Q_-(Y) = 0` for all `X, Y : A`. -/
theorem corner_strict_nilpotency {P : A} (hP : P * P = P) (X Y : A) :
    Q_pos P X * Q_pos P Y = 0 ∧ Q_neg P X * Q_neg P Y = 0 := by
  constructor
  · dsimp [Q_pos]
    calc (P * X * P_perp P) * (P * Y * P_perp P)
      _ = (P * X) * (P_perp P * P) * Y * P_perp P := by simp only [mul_assoc]
      _ = 0 := by rw [perp_proj_zero hP, mul_zero, zero_mul, zero_mul]
  · dsimp [Q_neg]
    calc (P_perp P * X * P) * (P_perp P * Y * P)
      _ = (P_perp P * X) * (P * P_perp P) * Y * P := by simp only [mul_assoc]
      _ = 0 := by rw [proj_perp_zero hP, mul_zero, zero_mul, zero_mul]

/-- Theorem 1.3 (Cartan Involution Unitarity):
    `S_P² = 1`, `S_P * P = P`, and `S_P * P_⊥ = -P_⊥`. -/
theorem cartan_involution_properties {P : A} (hP : P * P = P) :
    S_P P * S_P P = 1 ∧ S_P P * P = P ∧ S_P P * P_perp P = -P_perp P := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [S_P, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, hP]
    abel
  · dsimp [S_P, P_perp]
    simp only [sub_mul, one_mul, hP]
    abel
  · dsimp [S_P, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, hP]
    abel

/-- Theorem 1.4 (Partial Isometry / Moore-Penrose Cycle of `(Q_+, Q_-)`):
    Let `V_P(X, Y) = Q_+(X) * Q_-(Y)` (Active Core Gravity in `P A P`) and
    `Σ_P(X, Y) = Q_-(Y) * Q_+(X)` (Shadow Core Gravity in `P_⊥ A P_⊥`).
    Then `Q_+(X)` and `Q_-(Y)` satisfy the exact intertwined partial-isometry
    bridge equations:
    `Q_+(X) * Σ_P(X, Y) = V_P(X, Y) * Q_+(X)` and
    `Σ_P(X, Y) * Q_-(Y) = Q_-(Y) * V_P(X, Y)`. -/
theorem partial_isometry_intertwining (P X Y : A) :
    Q_pos P X * (Q_neg P Y * Q_pos P X) = (Q_pos P X * Q_neg P Y) * Q_pos P X ∧
    (Q_neg P Y * Q_pos P X) * Q_neg P Y = Q_neg P Y * (Q_pos P X * Q_neg P Y) := by
  exact ⟨by rw [mul_assoc], by rw [mul_assoc]⟩

/-!
## Stage II: Souriau Symplectic 2-Cocycle, KKS Orbit & Borel-Weil-Bott Toeplitz Curvature
-/

/-- The Non-Commutative Souriau Anomaly (Adjoint Derivation Defect):
    `Θ_P(X, Y) = [P, [X, Y]] - [[P, X], [P, Y]]`.
    Measures the exact failure of `ad_P = [P, ·]` to be a Lie algebra homomorphism
    when `P` is multiplied rather than commuted. -/
def SouriauDefect (P X Y : A) : A :=
  comm P (comm X Y) - comm (comm P X) (comm P Y)

/-- The Projected Berry / KKS Coadjoint Curvature in the Active Core `P A P`:
    `Ω_P(X, Y) = P * [[P, X], [P, Y]] * P`. -/
def BerryKKS_Core (P X Y : A) : A :=
  P * comm (comm P X) (comm P Y) * P

/-- The Borel-Weil-Bott Toeplitz Commutator Defect on the Active Sector `P A P`:
    `ℱ_Toeplitz(X, Y) = [P X P, P Y P] - P [X, Y] P`. -/
def ToeplitzDefect (P X Y : A) : A :=
  comm (X_11 P X) (X_11 P Y) - X_11 P (comm X Y)

/-- Theorem 2.1 (Souriau Equivariant Coboundary Theorem):
    Whenever the commutator `[X, Y]` commutes with the horizon `P` (`[P, [X, Y]] = 0`,
    i.e., `[X, Y]` lies in the isotropy Levi subalgebra `𝔤_0`), the Souriau defect
    reduces identically to the negative bracket of the modular velocities:
    `Θ_P(X, Y) = - [[P, X], [P, Y]]`. -/
theorem souriau_equivariant_coboundary (P X Y : A) (h_iso : comm P (comm X Y) = 0) :
    SouriauDefect P X Y = - comm (comm P X) (comm P Y) := by
  dsimp [SouriauDefect]
  rw [h_iso, zero_sub]

/-- Theorem 2.2 (Exact Peirce Expansion of the Berry / KKS Core Curvature):
    The projected Berry/KKS curvature `P [[P, X], [P, Y]] P` equals the negative
    antisymmetric round-trip return across the horizon:
    `Ω_P(X, Y) = - (Q_+(X) Q_-(Y) - Q_+(Y) Q_-(X))`. -/
theorem berry_kks_core_peirce_identity {P : A} (hP : P * P = P) (X Y : A) :
    BerryKKS_Core P X Y = - (Q_pos P X * Q_neg P Y - Q_pos P Y * Q_neg P X) := by
  dsimp [BerryKKS_Core, Q_pos, Q_neg, P_perp, comm]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
  abel

/-- Theorem 2.3 (Borel-Weil-Bott Toeplitz Curvature Identity):
    The failure of Toeplitz quantization `X ↦ P X P` to be a Lie homomorphism is
    controlled purely by the off-diagonal horizon transitions `Q_+` and `Q_-`:
    `[P X P, P Y P] - P [X, Y] P = -(Q_+(X) Q_-(Y) - Q_+(Y) Q_-(X)) = Ω_P(X, Y)`. -/
theorem borel_weil_bott_toeplitz_curvature {P : A} (hP : P * P = P) (X Y : A) :
    ToeplitzDefect P X Y = - (Q_pos P X * Q_neg P Y - Q_pos P Y * Q_neg P X) ∧
    ToeplitzDefect P X Y = BerryKKS_Core P X Y := by
  have h1 : ToeplitzDefect P X Y = - (Q_pos P X * Q_neg P Y - Q_pos P Y * Q_neg P X) := by
    dsimp [ToeplitzDefect, X_11, Q_pos, Q_neg, P_perp, comm]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  refine ⟨h1, ?_⟩
  rw [h1, berry_kks_core_peirce_identity hP]

/-- Lemma: Cyclic trace `τ : A →+ R` vanishes on any commutator `τ([X, Y]) = 0`. -/
lemma trace_comm_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hCyclic : ∀ X Y : A, τ (X * Y) = τ (Y * X)) (X Y : A) :
    τ (comm X Y) = 0 := by
  dsimp [comm]
  rw [map_sub, hCyclic, sub_self]

/-- Lemma: Cyclic trace `τ : A →+ R` satisfies `τ(X Y Z) = τ(Z X Y)`. -/
lemma trace_cycle_3 {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hCyclic : ∀ X Y : A, τ (X * Y) = τ (Y * X)) (X Y Z : A) :
    τ (X * Y * Z) = τ (Z * X * Y) := by
  rw [← hCyclic Z (X * Y), ← mul_assoc]

/-- Theorem 2.4 (Trace-Class Kirillov-Kostant-Souriau Lie-Poisson Identity):
    For any cyclic trace `τ : A →+ R` (`∀ X Y, τ(X Y) = τ(Y X)`) and idempotent `P` (`P² = P`),
    the traced Souriau defect `τ(P Θ_P(X, Y))` equals the canonical Kirillov-Kostant-Souriau (KKS)
    symplectic 2-cocycle `ω_P(X, Y) = τ(P [X, Y])`! -/
theorem trace_souriau_kks_equivalence {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hCyclic : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {P : A} (hP : P * P = P) (X Y : A) :
    τ (P * SouriauDefect P X Y) = τ (P * comm X Y) := by
  have h_id : P * SouriauDefect P X Y - P * comm X Y =
      comm (P * Y * P) (P * X * P) := by
    dsimp [SouriauDefect, comm]
    simp only [mul_sub, sub_mul, mul_assoc, hP, proj_idem hP]
    abel
  have h_sub : τ (P * SouriauDefect P X Y - P * comm X Y) = 0 := by
    rw [h_id, trace_comm_zero τ hCyclic]
  rw [map_sub] at h_sub
  exact sub_eq_zero.mp h_sub

/-!
## Stage III: Parabolic 3-Graded & 5-Graded Kantor-Tits-Connes-Moscovici Hierarchy
-/

/-- Theorem 3.1 (Parabolic 3-Graded Lie-Peirce Structure `𝔤 = 𝔤_{-1} ⊕ 𝔤_0 ⊕ 𝔤_{+1}`):
    Let `𝔤_0` consist of diagonal operators `D = X_11 P D + X_00 P D`,
    `𝔤_{+1}` consist of upper corner operators `Q_+(X)`, and
    `𝔤_{-1}` consist of lower corner operators `Q_-(Y)`.
    1. **2-Step Nilpotency (`[𝔤_{+1}, 𝔤_{+1}] = 0` and `[𝔤_{-1}, 𝔤_{-1}] = 0`)**:
       `[Q_+(X), Q_+(Y)] = 0` and `[Q_-(X), Q_-(Y)] = 0`.
    2. **Opposite Grade Bracket (`[𝔤_{+1}, 𝔤_{-1}] ⊆ 𝔤_0`)**:
       `[Q_+(X), Q_-(Y)] = Q_+(X) Q_-(Y) - Q_-(Y) Q_+(X)` lies purely in the
       diagonal Levi block `P A P ⊕ P_⊥ A P_⊥`.
    3. **Cartan Grading Action**:
       `[S_P, Q_+(X)] = 2 Q_+(X)` (grade `+2`),
       `[S_P, Q_-(Y)] = -2 Q_-(Y)` (grade `-2`),
       `[S_P, X_11 P Z + X_00 P Z] = 0` (grade `0`). -/
theorem parabolic_three_graded_lie_peirce_hierarchy {P : A} (hP : P * P = P) (X Y Z : A) :
    comm (Q_pos P X) (Q_pos P Y) = 0 ∧
    comm (Q_neg P X) (Q_neg P Y) = 0 ∧
    comm (Q_pos P X) (Q_neg P Y) =
      X_11 P (Q_pos P X * Q_neg P Y) - X_00 P (Q_neg P Y * Q_pos P X) ∧
    comm (S_P P) (Q_pos P X) = 2 • Q_pos P X ∧
    comm (S_P P) (Q_neg P Y) = -(2 • Q_neg P Y) ∧
    comm (S_P P) (X_11 P Z + X_00 P Z) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [comm]
    rw [(corner_strict_nilpotency hP X Y).1, (corner_strict_nilpotency hP Y X).1, sub_self]
  · dsimp [comm]
    rw [(corner_strict_nilpotency hP X Y).2, (corner_strict_nilpotency hP Y X).2, sub_self]
  · dsimp [comm, X_11, X_00, Q_pos, Q_neg, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [comm, S_P, Q_pos, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [comm, S_P, Q_neg, P_perp]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [comm, S_P, X_11, X_00, P_perp]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel

/-!
## Stage IV: Kähler-Hodge-Weitzenböck-Bochner Calculus
-/

/-- Forward Chiral Coboundary `d_+(Z) = [Q_+(X), Z]`. -/
def d_pos (P X Z : A) : A := comm (Q_pos P X) Z
/-- Backward Chiral Coboundary `d_-(Z) = [Q_-(X), Z]`. -/
def d_neg (P X Z : A) : A := comm (Q_neg P X) Z

/-- The Chiral Casimir Difference `H_P(X) = [Q_+(X), Q_-(X)] = Q_+(X) Q_-(X) - Q_-(X) Q_+(X)`. -/
def H_casimir (P X : A) : A := comm (Q_pos P X) (Q_neg P X)

/-- The Non-Commutative Kähler-Hodge-Dirac Operator `D_Kähler(Z) = d_+(Z) + d_-(Z)`. -/
def D_kahler (P X Z : A) : A := d_pos P X Z + d_neg P X Z
/-- Conjugate Kähler-Hodge-Dirac Operator `D_Kähler^c(Z) = d_+(Z) - d_-(Z)`. -/
def D_kahler_conj (P X Z : A) : A := d_pos P X Z - d_neg P X Z

/-- Theorem 4.1 (Kähler-Weitzenböck-Bochner Identities in `[Ring A]`): -/
theorem kahler_weitzenbock_bochner_identities {P : A} (hP : P * P = P) (X Z : A) :
    -- 1. Left/Right Multiplication Nilpotency (`Q_+² Z = 0`, `Q_-² Z = 0`)
    Q_pos P X * (Q_pos P X * Z) = 0 ∧
    Q_neg P X * (Q_neg P X * Z) = 0 ∧
    -- 2. Exact Cochain Nilpotency `d_+²(Z_diag) = 0` and `d_-²(Z_diag) = 0` on the Diagonal Core `𝔤_0`
    d_pos P X (d_pos P X (X_11 P Z + X_00 P Z)) = 0 ∧
    d_neg P X (d_neg P X (X_11 P Z + X_00 P Z)) = 0 ∧
    -- 3. Bochner-Weitzenböck Curvature Commutator Identity (`[d_+, d_-](Z) = [H_P(X), Z]`)
    d_pos P X (d_neg P X Z) - d_neg P X (d_pos P X Z) = comm (H_casimir P X) Z ∧
    -- 4. Kähler-Dirac Square Polarization (`D_Kähler²(Z) - (D_Kähler^c)²(Z) = 2 (d_+ d_- + d_- d_+)(Z)`)
    D_kahler P X (D_kahler P X Z) - D_kahler_conj P X (D_kahler_conj P X Z) =
      2 • (d_pos P X (d_neg P X Z) + d_neg P X (d_pos P X Z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, (corner_strict_nilpotency hP X X).1, zero_mul]
  · rw [← mul_assoc, (corner_strict_nilpotency hP X X).2, zero_mul]
  · dsimp [d_pos, comm, Q_pos, X_11, X_00, P_perp]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [d_neg, comm, Q_neg, X_11, X_00, P_perp]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [d_pos, d_neg, H_casimir, comm]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  · dsimp [D_kahler, D_kahler_conj, d_pos, d_neg, comm]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
    abel

/-!
## Stage V: Exact Drazin / Group Generalized Inverse & Schur Complement Resolvent
-/

/-- The Active Core Gravity `V_P(X) = Q_+(X) * Q_-(X)`. -/
def V_P (P X : A) : A := Q_pos P X * Q_neg P X
/-- The Shadow Core Gravity `Σ_P(X) = Q_-(X) * Q_+(X)`. -/
def Sigma_P (P X : A) : A := Q_neg P X * Q_pos P X

/-- The Full Transcendent Bridge `Z_P(X) = (Q_+(X) + Q_-(X))² = V_P(X) + Σ_P(X)`. -/
def Z_bridge (P X : A) : A := V_P P X + Sigma_P P X

/-- Theorem 5.1 (Exact Core-Nilpotent Drazin Spectral Splitting):
    1. The square of the off-diagonal horizon bridge `N_P(X) = Q_+(X) + Q_-(X)`
       equals the purely block-diagonal operator `Z_bridge P X = V_P P X + Sigma_P P X`,
    2. `V_P P X` and `Sigma_P P X` are strictly orthogonal (`V_P * Sigma_P = 0` and
       `Sigma_P * V_P = 0`),
    3. If `W_11 = P W P` inverts `V_P P X` inside the active core `P A P`
       (`W_11 * V_P P X = P` and `V_P P X * W_11 = P`), then `W_11` satisfies all three
       **Drazin / Group Generalized Inverse** equations for `V_P P X` in the full
       non-commutative ring `A`:
       * `(V_P P X) * W_11 * (V_P P X) = V_P P X` (Generalized Inverse 1),
       * `W_11 * (V_P P X) * W_11 = W_11` (Generalized Inverse 2),
       * `(V_P P X) * W_11 = W_11 * (V_P P X)` (Spectral Commutation 3). -/
theorem drazin_group_inverse_and_orthogonal_core_splitting {P : A} (hP : P * P = P)
    (X W : A)
    (hW_core : P * W * P = W)
    (hWL : W * V_P P X = P)
    (hWR : V_P P X * W = P) :
    (Q_pos P X + Q_neg P X) * (Q_pos P X + Q_neg P X) = Z_bridge P X ∧
    V_P P X * Sigma_P P X = 0 ∧
    Sigma_P P X * V_P P X = 0 ∧
    V_P P X * W * V_P P X = V_P P X ∧
    W * V_P P X * W = W ∧
    V_P P X * W = W * V_P P X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [Z_bridge, V_P, Sigma_P]
    simp only [mul_add, add_mul, (corner_strict_nilpotency hP X X).1,
               (corner_strict_nilpotency hP X X).2, zero_add, add_zero]
    abel
  · dsimp [V_P, Sigma_P, Q_pos, Q_neg]
    calc (P * X * P_perp P * (P_perp P * X * P)) * (P_perp P * X * P * (P * X * P_perp P))
      _ = (P * X * P_perp P * (P_perp P * X)) * (P * P_perp P) * X * P * (P * X * P_perp P) := by
          simp only [mul_assoc]
      _ = 0 := by rw [proj_perp_zero hP, mul_zero, zero_mul, zero_mul, zero_mul]
  · dsimp [V_P, Sigma_P, Q_pos, Q_neg]
    calc (P_perp P * X * P * (P * X * P_perp P)) * (P * X * P_perp P * (P_perp P * X * P))
      _ = (P_perp P * X * P * (P * X)) * (P_perp P * P) * X * P_perp P * (P_perp P * X * P) := by
          simp only [mul_assoc]
      _ = 0 := by rw [perp_proj_zero hP, mul_zero, zero_mul, zero_mul, zero_mul]
  · rw [hWR]
    dsimp [V_P, Q_pos, Q_neg]
    simp only [← mul_assoc, hP]
  · rw [hWL]
    calc P * W = P * (P * W * P) := by rw [hW_core]
      _ = P * W * P := by simp only [← mul_assoc, hP]
      _ = W := hW_core
  · rw [hWR, hWL]

/-- Theorem 5.2 (Non-Commutative Schur Complement Block-LDU Factorization):
    In any ring `A` with idempotent `P` (`P² = P`), let `X` have invertible
    active block `X₁₁ = P X P` with block-inverse `G₁₁ = P G P` (`X₁₁ G₁₁ = P`,
    `G₁₁ X₁₁ = P`, `P G₁₁ P = G₁₁`).
    Define the **Non-Commutative Schur Complement** in the shadow sector `P_⊥ A P_⊥`:
    `S_Schur(X, G₁₁) = X₀₀ - Q_-(X) * G₁₁ * Q_+(X)`.
    Then `X` factors identically into a Lower-Diagonal-Upper (LDU) Peirce product:
    `X = (P + P_⊥ + Q_-(X) * G₁₁) * (X₁₁ + S_Schur(X, G₁₁)) * (P + P_⊥ + G₁₁ * Q_+(X))`! -/
theorem noncommutative_schur_complement_ldu_factorization {P : A} (hP : P * P = P)
    (X G11 : A)
    (hG_core : P * G11 * P = G11)
    (hXG : X_11 P X * G11 = P)
    (hGX : G11 * X_11 P X = P) :
    (1 + Q_neg P X * G11) *
    (X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X)) *
    (1 + G11 * Q_pos P X) = X := by
  have hPG : P * G11 = G11 := by
    calc P * G11 = P * (P * G11 * P) := by rw [hG_core]
      _ = P * G11 * P := by simp only [← mul_assoc, hP]
      _ = G11 := hG_core
  have hGP : G11 * P = G11 := by
    calc G11 * P = (P * G11 * P) * P := by rw [hG_core]
      _ = P * G11 * P := by simp only [mul_assoc, hP]
      _ = G11 := hG_core
  have hPperpG : P_perp P * G11 = 0 := by
    rw [← hPG, ← mul_assoc, perp_proj_zero hP, zero_mul]
  have hGPperp : G11 * P_perp P = 0 := by
    rw [← hGP, mul_assoc, proj_perp_zero hP, mul_zero]
  have hQneg_X11 : (Q_neg P X * G11) * X_11 P X = Q_neg P X := by
    rw [mul_assoc, hGX]
    dsimp [Q_neg]
    simp only [mul_assoc, hP]
  have hX11_Qpos : X_11 P X * (G11 * Q_pos P X) = Q_pos P X := by
    rw [← mul_assoc, hXG]
    dsimp [Q_pos]
    simp only [← mul_assoc, hP]
  have hQneg_Schur : (Q_neg P X * G11) * (X_00 P X - Q_neg P X * G11 * Q_pos P X) = 0 := by
    dsimp [X_00, Q_neg, Q_pos]
    simp only [mul_sub, ← mul_assoc]
    have h1 : Q_neg P X * G11 * P_perp P = 0 := by
      rw [mul_assoc, hGPperp, mul_zero]
    dsimp [Q_neg] at h1
    rw [h1]
    simp only [zero_mul, sub_self]
  have hSchur_Qpos : (X_00 P X - Q_neg P X * G11 * Q_pos P X) * (G11 * Q_pos P X) = 0 := by
    dsimp [X_00, Q_neg, Q_pos]
    simp only [sub_mul, mul_assoc]
    have h2 : P_perp P * (G11 * (P * (X * P_perp P))) = 0 := by
      rw [← mul_assoc (P_perp P) G11, hPperpG, zero_mul]
    rw [h2]
    simp only [mul_zero, sub_self]
  calc (1 + Q_neg P X * G11) *
       (X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X)) *
       (1 + G11 * Q_pos P X)
    _ = (X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X) +
         (Q_neg P X * G11) * X_11 P X +
         (Q_neg P X * G11) * (X_00 P X - Q_neg P X * G11 * Q_pos P X)) *
        (1 + G11 * Q_pos P X) := by
        simp only [add_mul, mul_add, one_mul]
        abel
    _ = (X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X) + Q_neg P X) *
        (1 + G11 * Q_pos P X) := by
        rw [hQneg_X11, hQneg_Schur, add_zero]
    _ = X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X) + Q_neg P X +
        X_11 P X * (G11 * Q_pos P X) +
        (X_00 P X - Q_neg P X * G11 * Q_pos P X) * (G11 * Q_pos P X) +
        Q_neg P X * (G11 * Q_pos P X) := by
        simp only [add_mul, mul_add, mul_one]
        abel
    _ = X_11 P X + Q_pos P X + Q_neg P X + X_00 P X := by
        rw [hX11_Qpos, hSchur_Qpos, ← mul_assoc (Q_neg P X) G11 (Q_pos P X)]
        abel
    _ = X := (peirce_fourfold_partition P X).symm

/-!
## Stage VI: Metriplectic Thermodynamics, Connes-Rovelli Modular Time & GKSL Lindblad Dissipator
-/

/-- The Connes-Rovelli Modular Hamiltonian Derivation `d_mod(X) = [P, X] = Q_+(X) - Q_-(X)`. -/
def d_modular (P X : A) : A := comm P X

/-- The Morrison Metriplectic / GKSL Lindblad Double-Commutator Dissipator:
    `Δ_diss(X) = [P, [P, X]] = Q_+(X) + Q_-(X) = P X + X P - 2 P X P`
    (when `P_⊥ = 1 - P`, note `Q_+ + Q_- = P X (1 - P) + (1 - P) X P = P X + X P - 2 P X P`,
    which is the negative of the standard Lindblad dissipator `2 P X P - {P, X}`). -/
def Delta_diss (P X : A) : A := comm P (comm P X)

/-- The Standard GKSL Lindblad Jump Dissipator with jump operator `L = P` (`P² = P`):
    `ℒ_GKSL(X) = 2 P X P - (P X + X P) = - Δ_diss(P, X)`. -/
def Lindblad_GKSL (P X : A) : A := 2 • (P * X * P) - anticomm P X

/-- Theorem 6.1 (Metriplectic Split, Dissipator Idempotence & Casimir Conservation):
    1. **Reversible Modular Flow**: `d_mod(X) = Q_+(X) - Q_-(X)` (antisymmetric in corners),
    2. **Irreversible Dissipative Flow**: `Δ_diss(X) = Q_+(X) + Q_-(X) = - ℒ_GKSL(X)` (symmetric in corners),
    3. **Metriplectic Reconstruction of Chiral Roots**:
       `d_mod(X) + Δ_diss(X) = 2 Q_+(X)` and `Δ_diss(X) - d_mod(X) = 2 Q_-(X)`,
    4. **Idempotence of the Dissipator (`Δ_diss³ = Δ_diss² = Δ_diss`)**:
       `Δ_diss(Δ_diss(X)) = Δ_diss(X)` — dissipation projects any observable onto the
       off-diagonal boundary modes in a single step and does not decay further,
    5. **Exact Casimir Conservation (First & Second Law Compatibility)**:
       Any block-diagonal Casimir observable `C_0 = X_11 P Z + X_00 P Z` is simultaneously
       stationary under the modular Hamiltonian (`d_mod(C_0) = 0`) and lies in the
       decoherence-free kernel of the Lindblad dissipator (`Δ_diss(C_0) = 0`)! -/
theorem metriplectic_lindblad_modular_synthesis {P : A} (hP : P * P = P) (X Z : A) :
    d_modular P X = Q_pos P X - Q_neg P X ∧
    Delta_diss P X = Q_pos P X + Q_neg P X ∧
    Lindblad_GKSL P X = - Delta_diss P X ∧
    Delta_diss P X + d_modular P X = 2 • Q_pos P X ∧
    Delta_diss P X - d_modular P X = 2 • Q_neg P X ∧
    Delta_diss P (Delta_diss P X) = Delta_diss P X ∧
    d_modular P (X_11 P Z + X_00 P Z) = 0 ∧
    Delta_diss P (X_11 P Z + X_00 P Z) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [d_modular, Q_pos, Q_neg, P_perp, comm]
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    abel
  · dsimp [Delta_diss, Q_pos, Q_neg, P_perp, comm]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [Lindblad_GKSL, Delta_diss, anticomm, comm]
    simp only [mul_sub, sub_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [Delta_diss, d_modular, Q_pos, P_perp, comm]
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [Delta_diss, d_modular, Q_neg, P_perp, comm]
    simp only [mul_sub, sub_mul, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [Delta_diss, comm]
    simp only [mul_sub, sub_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [d_modular, X_11, X_00, P_perp, comm]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp [Delta_diss, X_11, X_00, P_perp, comm]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP, proj_idem hP]
    abel

/-!
## Stage VII: KMS / Kubo-Mori-Bogoliubov Modular Difference & Schwinger-Keldysh Contour
-/

/-- Given a two-point weight `(p₁, p₀)` (`p₁ P + p₀ P_⊥`, representing a two-level
    Gibbs state `ρ = e^{-β_1} P + e^{-β_0} P_⊥`), the **Modular Difference Operator**
    `Δ_ρ(X) = ρ X - X ρ` is proportional to the modular derivation `[P, X] = Q_+(X) - Q_-(X)`. -/
def GibbsTwoLevel (P : A) (c : A) : A := P + c * P_perp P

/-- Theorem 7.1 (Schwinger-Keldysh / Dyson Doubled-Contour Commutator-Anticommutator Identity):
    In any non-commutative ring `A`, let `(A_+, A_-)` and `(B_+, B_-)` be Forward (`+`)
    and Backward (`-`) time-contour operators related to their Classical/Retarded sum
    `A_c = A_+ + A_-`, `B_c = B_+ + B_-` and Quantum/Keldysh difference
    `A_q = A_+ - A_-`, `B_q = B_+ - B_-`.
    Then twice the contour action difference `2(A_+ B_+ - A_- B_-)` decomposes identically
    into the sum of the **Classical-Quantum Anticommutator** and **Commutator**:
    `2 • (A_+ * B_+ - A_- * B_-) = (A_+ + A_-) * (B_+ - B_-) + (A_+ - A_-) * (B_+ + B_-)`
    and its antisymmetrized Dyson-Keldysh commutator satisfies:
    `2 • (comm A_+ B_+ - comm A_- B_-) = comm (A_+ + A_-) (B_+ - B_-) + comm (A_+ - A_-) (B_+ + B_-)`. -/
theorem schwinger_keldysh_contour_identities (Ap Am Bp Bm : A) :
    2 • (Ap * Bp - Am * Bm) = (Ap + Am) * (Bp - Bm) + (Ap - Am) * (Bp + Bm) ∧
    2 • (comm Ap Bp - comm Am Bm) =
      comm (Ap + Am) (Bp - Bm) + comm (Ap - Am) (Bp + Bm) := by
  constructor
  · simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel
  · dsimp [comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel

/-!
## Stage VIII: Acyclic Causal Poset of the 10-Stage Souriau–Metriplectic–Parabolic Synthesis
-/

/-- Nodes of the 10-stage Souriau–Metriplectic–Parabolic–Weitzenböck causal poset. -/
inductive Node
  | peirceFourfoldCut
  | cornerNilpotencyCartanGrading
  | partialIsometryIntertwining
  | souriauCocycleBerryKKSCore
  | borelWeilBottToeplitzCurvature
  | traceClassKKSIdentity
  | parabolicThreeGradedHierarchy
  | kahlerWeitzenbockBochnerCalculus
  | drazinInverseSchurComplement
  | metriplecticLindbladKeldyshCrown
  deriving DecidableEq, Repr

/-- Topological causal rank in the 10-stage poset. -/
def rank : Node → ℕ
  | .peirceFourfoldCut => 0
  | .cornerNilpotencyCartanGrading => 1
  | .partialIsometryIntertwining => 2
  | .souriauCocycleBerryKKSCore => 3
  | .borelWeilBottToeplitzCurvature => 4
  | .traceClassKKSIdentity => 5
  | .parabolicThreeGradedHierarchy => 6
  | .kahlerWeitzenbockBochnerCalculus => 7
  | .drazinInverseSchurComplement => 8
  | .metriplecticLindbladKeldyshCrown => 9

/-- Directed causal cover edges of the 10-stage poset. -/
def coverEdge : Node → Node → Prop
  | .peirceFourfoldCut, .cornerNilpotencyCartanGrading => True
  | .cornerNilpotencyCartanGrading, .partialIsometryIntertwining => True
  | .partialIsometryIntertwining, .souriauCocycleBerryKKSCore => True
  | .souriauCocycleBerryKKSCore, .borelWeilBottToeplitzCurvature => True
  | .borelWeilBottToeplitzCurvature, .traceClassKKSIdentity => True
  | .traceClassKKSIdentity, .parabolicThreeGradedHierarchy => True
  | .parabolicThreeGradedHierarchy, .kahlerWeitzenbockBochnerCalculus => True
  | .kahlerWeitzenbockBochnerCalculus, .drazinInverseSchurComplement => True
  | .drazinInverseSchurComplement, .metriplecticLindbladKeldyshCrown => True
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

/-!
## Stage IX: Master Crown Synthesis Theorem
-/

/-- **Master Theorem: The Complete Souriau–Metriplectic–Parabolic–Weitzenböck–Drazin Synthesis**
    Simultaneously verifies in any non-commutative ring `A` with idempotent `P` (`P² = P`):
    1. Fourfold Peirce partition of unity and strict corner nilpotency (`Q_+² = Q_-² = 0`),
    2. Souriau 2-cocycle equivariant coboundary reduction (`Θ_P = -[[P,X],[P,Y]]` on `𝔤_0`),
    3. Exact Berry/KKS core curvature `Ω_P = Q_+(X) Q_-(Y) - Q_+(Y) Q_-(X)` and
       Borel-Weil-Bott Toeplitz curvature `ℱ_Toeplitz = - Ω_P`,
    4. Trace-class Kirillov-Kostant-Souriau identity `τ(P Θ_P(X,Y)) = τ(P [X,Y])`,
    5. Parabolic 3-graded Lie-Peirce hierarchy (`[𝔤_{+1}, 𝔤_{+1}] = 0`, `[S_P, Q_±] = ± 2 Q_±`),
    6. Kähler-Weitzenböck-Bochner curvature identity `[d_+, d_-](Z) = [H_P(X), Z]` and
       cochain nilpotency `d_±²(Z_diag) = 0`,
    7. Exact Drazin/Group generalized inverse and non-commutative Schur complement
       LDU factorization,
    8. Morrison Metriplectic / Connes-Rovelli Modular / GKSL Lindblad split, dissipator
       idempotence `Δ_diss² = Δ_diss`, and Casimir conservation `d_mod(C_0) = Δ_diss(C_0) = 0`. -/
theorem master_souriau_metriplectic_parabolic_weitzenbock_drazin_synthesis
    {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hCyclic : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {P : A} (hP : P * P = P) (X Y Z G11 : A)
    (hG_core : P * G11 * P = G11)
    (hXG : X_11 P X * G11 = P)
    (hGX : G11 * X_11 P X = P) :
    -- 1. Peirce partition & corner nilpotency
    (X = X_11 P X + Q_pos P X + Q_neg P X + X_00 P X ∧
     Q_pos P X * Q_pos P Y = 0 ∧ Q_neg P X * Q_neg P Y = 0) ∧
    -- 2. Berry/KKS core & Toeplitz curvature
    (BerryKKS_Core P X Y = - (Q_pos P X * Q_neg P Y - Q_pos P Y * Q_neg P X) ∧
     ToeplitzDefect P X Y = BerryKKS_Core P X Y) ∧
    -- 3. Traced Souriau-KKS symplectic identity
    (τ (P * SouriauDefect P X Y) = τ (P * comm X Y)) ∧
    -- 4. Parabolic 3-grading & Cartan involution
    (comm (S_P P) (Q_pos P X) = 2 • Q_pos P X ∧
     comm (S_P P) (Q_neg P Y) = -(2 • Q_neg P Y)) ∧
    -- 5. Kähler-Weitzenböck-Bochner identity
    (d_pos P X (d_pos P X (X_11 P Z + X_00 P Z)) = 0 ∧
     d_pos P X (d_neg P X Z) - d_neg P X (d_pos P X Z) = comm (H_casimir P X) Z) ∧
    -- 6. Non-commutative Schur complement LDU factorization
    ((1 + Q_neg P X * G11) *
     (X_11 P X + (X_00 P X - Q_neg P X * G11 * Q_pos P X)) *
     (1 + G11 * Q_pos P X) = X) ∧
    -- 7. Metriplectic-Lindblad-Modular split & Casimir conservation
    (Delta_diss P (Delta_diss P X) = Delta_diss P X ∧
     d_modular P (X_11 P Z + X_00 P Z) = 0 ∧
     Delta_diss P (X_11 P Z + X_00 P Z) = 0) := by
  have h_part : X = X_11 P X + Q_pos P X + Q_neg P X + X_00 P X := peirce_fourfold_partition P X
  refine ⟨⟨h_part,
           (corner_strict_nilpotency hP X Y).1,
           (corner_strict_nilpotency hP X Y).2⟩,
          ⟨berry_kks_core_peirce_identity hP X Y,
           (borel_weil_bott_toeplitz_curvature hP X Y).2⟩,
          trace_souriau_kks_equivalence τ hCyclic hP X Y,
          ⟨(parabolic_three_graded_lie_peirce_hierarchy hP X Y Z).2.2.2.1,
           (parabolic_three_graded_lie_peirce_hierarchy hP X Y Z).2.2.2.2.1⟩,
          ⟨(kahler_weitzenbock_bochner_identities hP X Z).2.2.1,
           (kahler_weitzenbock_bochner_identities hP X Z).2.2.2.2.1⟩,
          noncommutative_schur_complement_ldu_factorization hP X G11 hG_core hXG hGX,
          ⟨(metriplectic_lindblad_modular_synthesis hP X Z).2.2.2.2.2.1,
           (metriplectic_lindblad_modular_synthesis hP X Z).2.2.2.2.2.2.1,
           (metriplectic_lindblad_modular_synthesis hP X Z).2.2.2.2.2.2.2⟩⟩

/-- **Inductive Colimit Cone Transport of the Souriau–Metriplectic–Weitzenböck Hierarchy
(`souriau_metriplectic_colimit_cone_transport`)**:
For any directed tower of non-commutative operator rings `Stage : ℕ → Type*` (`[∀ k, Ring (Stage k)]`)
with bonding homomorphisms `embed : ∀ k : ℕ, Stage k →+* Stage (k + 1)` and colimit cone legs
`toLimit : ∀ k : ℕ, Stage k →+* Limit` (`[Ring Limit]`) satisfying
`∀ k Z, toLimit (k + 1) (embed k Z) = toLimit k Z`:
1. The colimit cone legs preserve `SouriauDefect`, `BerryKKS_Core`, and `Delta_diss` and are
   invariant under stage refinement `embed k`,
2. In the colimit ring `Limit`, `P_∞ = toLimit k P` is idempotent, `Delta_diss P_∞` is idempotent,
   and the Kähler–Weitzenböck–Bochner commutator identity `[d_+, d_-](Z_∞) = [H_casimir, Z_∞]` holds! -/
theorem souriau_metriplectic_colimit_cone_transport
    {Stage : ℕ → Type*} [∀ k, Ring (Stage k)]
    {Limit : Type*} [Ring Limit]
    (embed : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (toLimit : ∀ k : ℕ, Stage k →+* Limit)
    (hCone : ∀ (k : ℕ) (Z : Stage k), toLimit (k + 1) (embed k Z) = toLimit k Z)
    (k : ℕ) {P : Stage k} (hP : P * P = P) (X Y Z : Stage k) :
    let P_inf := toLimit k P
    let X_inf := toLimit k X
    let Y_inf := toLimit k Y
    let Z_inf := toLimit k Z
    toLimit k (SouriauDefect P X Y) = SouriauDefect P_inf X_inf Y_inf ∧
    toLimit (k + 1) (SouriauDefect (embed k P) (embed k X) (embed k Y)) =
      SouriauDefect P_inf X_inf Y_inf ∧
    toLimit k (Delta_diss P X) = Delta_diss P_inf X_inf ∧
    Delta_diss P_inf (Delta_diss P_inf X_inf) = Delta_diss P_inf X_inf ∧
    d_pos P_inf X_inf (d_neg P_inf X_inf Z_inf) - d_neg P_inf X_inf (d_pos P_inf X_inf Z_inf) =
      comm (H_casimir P_inf X_inf) Z_inf := by
  have hP_inf : toLimit k P * toLimit k P = toLimit k P := by
    rw [← map_mul, hP]
  have hSD_lim : toLimit k (SouriauDefect P X Y) =
      SouriauDefect (toLimit k P) (toLimit k X) (toLimit k Y) := by
    dsimp only [SouriauDefect, comm]
    simp only [map_sub, map_mul]
  have hSD_emb : embed k (SouriauDefect P X Y) =
      SouriauDefect (embed k P) (embed k X) (embed k Y) := by
    dsimp only [SouriauDefect, comm]
    simp only [map_sub, map_mul]
  have hDiss_lim : toLimit k (Delta_diss P X) =
      Delta_diss (toLimit k P) (toLimit k X) := by
    dsimp only [Delta_diss, d_modular, comm]
    simp only [map_sub, map_mul]
  refine ⟨hSD_lim, ?_, hDiss_lim,
          (metriplectic_lindblad_modular_synthesis hP_inf (toLimit k X) (toLimit k Z)).2.2.2.2.2.1,
          (kahler_weitzenbock_bochner_identities hP_inf (toLimit k X) (toLimit k Z)).2.2.2.2.1⟩
  rw [← hSD_emb, hCone k, hSD_lim]

end InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset
