/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# Three-Horizon Peirce Corner Subalgebras, Off-Diagonal Bimodule Transitions,
# Parity Conjugation Invariants, and Five-Grade Resolution

Over an associative ring `B` (`[Ring B]`), two orthogonal idempotents `P1`, `P2` and their
complementary waist idempotent `P0 = 1 - P1 - P2` organize `B` into a five-graded Peirce
architecture:

1. **Three-Idempotent Frame and Tripotent Generator:**
   `P1 + P0 + P2 = 1`, `P0 * P0 = P0`, pairwise orthogonality `P_i * P_j = 0` (`i ≠ j`),
   tripotence `H * (H * H) = H` for `H = P1 - P2`, and reconstruction of the three idempotents
   from `(1, H, H²)`: `2 • P1 = H² + H`, `2 • P2 = H² - H`, `P0 = 1 - H²`.
2. **Diagonal Peirce Corner Subalgebras and Direct-Sum Commutator Splitting:**
   The three diagonal corners `block11 P1 Z = P1 * Z * P1`, `block00 P1 P2 Z = P0 * Z * P0`,
   and `block22 P2 Z = P2 * Z * P2` are closed under multiplication and Lie commutation
   `souriauRotational`, annihilate each other on both sides, and split the grade-zero commutator
   `souriauRotational (zeroGradeSector P1 P2 Ω) (zeroGradeSector P1 P2 ρ)` into the direct sum
   of the three corner commutators.
3. **Off-Diagonal Step-`±1` Bimodule Transitions and Brockett Double Commutator:**
   Sandwiching by the step-`±1` operators `N_{+1} = P1 * X * P0 + P0 * X * P2` and
   `N_{-1} = P0 * Y * P1 + P2 * Y * P0` maps waist elements `block00` into the boundary corners
   `block11` and `block22` and vice versa, shifts `ad H` eigenvalues by `±1`, and satisfies the
   Brockett double-commutator identity `brockettIrrotational J_PK Φ_odd = 2 • [Σ_PK, Φ_odd]`.
4. **Parity Reflection `S_par = 2 H² - 1`, Corner/Metric Invariance, and Trace Conservation:**
   Conjugation `parConj3 P1 P2 Z = S_par * Z * S_par` is an involution that fixes every diagonal
   corner (`block11`, `block00`, `block22`, `zeroGradeSector`), negates the step-`±1` operators
   (`N_{+1}`, `N_{-1}`, `Φ_odd`), preserves the Para-Kähler metric `V_PK3`, spin bivector
   `Σ_PK3`, and Weyl step-1 metric `V1_weyl3`, and preserves any cyclic trace `τ : CyclicTrace B R`.
5. **Five-Grade Peirce Resolution and Unit Maurer–Cartan Identities:**
   Every `Z : B` decomposes into five `ad H`-weight components (`-2, -1, 0, +1, +2`), while
   bichiral exterior transport satisfies `{d_out3, d_in3}(Z) = [V_PK3, Z]` and unit gauge frames
   `g : Bˣ` obey the Maurer–Cartan structural equation `D(θ_L(g)) + θ_L(g)² = g⁻¹ D²(g)`.

All statements are algebraic identities over `[Ring B]`; no topological manifold, analytic bundle,
or modular group action on the upper half-plane is assumed.

BUCKET 1: PROVED FINITE/ALGEBRAIC IDENTITIES OVER `[Ring B]`
- `peirceCorner`, `peirceTransition`, `peirceTransition_compose`, `peirceTransition_orthogonal_compose`
- `orthogonal_idempotents_induce_complementary_tripotent_frame`
- `peirce_corner_subalgebras_and_grade_zero_commutator_split`
- `step_one_peirce_corner_sandwich_and_brockett_commutator`

BUCKET 2: CONDITIONAL IDENTITIES FROM EXPLICIT PREMISES
- `parity_conjugation_invariants_and_cyclic_trace_conservation` (from cyclic trace `τ : CyclicTrace B R`)
- `five_grade_peirce_resolution_and_unit_maurer_cartan` (from unit gauge frames `g : Bˣ`)

BUCKET 3: OPEN CLOSURE DEBT
- Topological moduli bundles and analytic upper-half-plane modular actions are not constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes
open InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset

universe u v
variable {B : Type u} [Ring B]
variable {R : Type v} [AddCommGroup R]

/-! ### Algebraic fibers and transition spaces

These definitions formalize corners and directed Peirce transitions in the given
ring. They do not assert that a moduli space, topological bundle, or duality group
has been constructed. -/

/-- The (possibly nonunital as a subring of `B`) Peirce corner `e B e`. -/
def peirceCorner (e : B) : NonUnitalSubring B where
  carrier := {x | e * x = x ∧ x * e = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change e * x = x ∧ x * e = x at hx
    change e * y = y ∧ y * e = y at hy
    constructor <;> simp [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2]
  neg_mem' := by
    intro x hx
    change e * x = x ∧ x * e = x at hx
    constructor <;> simp [mul_neg, neg_mul, hx.1, hx.2]
  mul_mem' := by
    intro x y hx hy
    change e * x = x ∧ x * e = x at hx
    change e * y = y ∧ y * e = y at hy
    constructor
    · rw [← mul_assoc, hx.1]
    · rw [mul_assoc, hy.2]

/-- A directed Peirce transition from the `f` corner to the `e` corner. -/
def peirceTransition (e f : B) : AddSubgroup B where
  carrier := {x | e * x = x ∧ x * f = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change e * x = x ∧ x * f = x at hx
    change e * y = y ∧ y * f = y at hy
    constructor <;> simp [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2]
  neg_mem' := by
    intro x hx
    change e * x = x ∧ x * f = x at hx
    constructor <;> simp [mul_neg, neg_mul, hx.1, hx.2]

/-- Composition of composable Peirce transitions is a Peirce transition. -/
theorem peirceTransition_compose {e f g x y : B}
    (hx : x ∈ peirceTransition e f) (hy : y ∈ peirceTransition f g) :
    x * y ∈ peirceTransition e g := by
  change e * x = x ∧ x * f = x at hx
  change f * y = y ∧ y * g = y at hy
  change e * (x * y) = x * y ∧ (x * y) * g = x * y
  constructor
  · rw [← mul_assoc, hx.1]
  · rw [mul_assoc, hy.2]

/-- Transitions separated by orthogonal middle corners compose to zero. -/
theorem peirceTransition_orthogonal_compose {e f g h x y : B}
    (hx : x ∈ peirceTransition e f) (hy : y ∈ peirceTransition g h)
    (hfg : f * g = 0) : x * y = 0 := by
  change e * x = x ∧ x * f = x at hx
  change g * y = y ∧ y * h = y at hy
  calc
    x * y = (x * f) * (g * y) := by rw [hx.2, hy.1]
    _ = x * (f * g) * y := by simp [mul_assoc]
    _ = 0 := by rw [hfg]; simp

/-- The idempotent `e` acts as the identity on its Peirce corner. -/
theorem peirceCorner_idempotent_identity {e : B} (he : e * e = e) :
    e ∈ peirceCorner e := by
  change e * e = e ∧ e * e = e
  exact ⟨he, he⟩

/-- Right-associated idempotent and orthogonality rewrite helpers for `P₁, P₂`. -/
private theorem peirce_nf_helpers {P1 P2 : B}
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    (∀ M, P1 * (P1 * M) = P1 * M) ∧
    (∀ M, P2 * (P2 * M) = P2 * M) ∧
    (∀ M, P1 * (P2 * M) = 0) ∧
    (∀ M, P2 * (P1 * M) = 0) :=
  ⟨fun M => by rw [← mul_assoc, h1],
   fun M => by rw [← mul_assoc, h2],
   fun M => by rw [← mul_assoc, h12, zero_mul],
   fun M => by rw [← mul_assoc, h21, zero_mul]⟩

-- ============================================================================
-- 1. COMPLEMENTARY IDEMPOTENT FRAME AND TRIPOTENT GENERATOR H = P₁ - P₂
-- ============================================================================

/--
**Algebraic frame theorem (`orthogonal_idempotents_induce_complementary_tripotent_frame`):**
Given orthogonal idempotents `P₁² = P₁`, `P₂² = P₂`, `P₁ P₂ = P₂ P₁ = 0` with complementary
waist `P₀ = P0_waist P1 P2 = 1 - P₁ - P₂` and generator `H = H_weyl P1 P2 = P₁ - P₂`:
1. `P₁ + P₀ + P₂ = 1`, `P₀ * P₀ = P₀`, and `P₁ * P₀ = P₀ * P₁ = P₂ * P₀ = P₀ * P₂ = 0`,
2. `H * (H * H) = H`, `H * H = P_hor3 P1 P2`, and `P₀ = 1 - H * H`,
3. `H * P₁ = P₁`, `P₁ * H = P₁`, `H * P₀ = 0`, `P₀ * H = 0`, `H * P₂ = -P₂`, `P₂ * H = -P₂`,
4. `2 • P₁ = H * H + H` and `2 • P₂ = H * H - H`.
-/
theorem orthogonal_idempotents_induce_complementary_tripotent_frame
    (P1 P2 : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := P0_waist P1 P2
    let H := H_weyl P1 P2
    P1 + P0 + P2 = 1 ∧
    P0 * P0 = P0 ∧
    P1 * P0 = 0 ∧ P0 * P1 = 0 ∧
    P2 * P0 = 0 ∧ P0 * P2 = 0 ∧
    H * (H * H) = H ∧
    H * H = P_hor3 P1 P2 ∧
    P0 = 1 - H * H ∧
    H * P1 = P1 ∧ P1 * H = P1 ∧
    H * P0 = 0 ∧ P0 * H = 0 ∧
    H * P2 = -P2 ∧ P2 * H = -P2 ∧
    2 • P1 = H * H + H ∧
    2 • P2 = H * H - H := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_nf_helpers h1 h2 h12 h21
  refine ⟨by dsimp only [P0_waist]; abel,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [P0_waist, H_weyl, P_hor3, two_nsmul] <;>
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 2. DIAGONAL PEIRCE CORNER SUBALGEBRAS & DIRECT-SUM SPLITTING
-- ============================================================================

/--
**Diagonal corner theorem (`diagonal_peirce_corner_products_and_commutator_splitting`):**
The three diagonal Peirce corners `block11 P1`, `block00 P1 P2`, and `block22 P2` satisfy:
1. **Multiplicative and Lie (`souriauRotational`) closure inside each corner:**
   - `block11 P1 (block11 P1 A * block11 P1 C) = block11 P1 A * block11 P1 C`,
   - `block00 P1 P2 (block00 P1 P2 A * block00 P1 P2 C) = block00 P1 P2 A * block00 P1 P2 C`,
   - `block22 P2 (block22 P2 A * block22 P2 C) = block22 P2 A * block22 P2 C`,
   - `block11 P1 (souriauRotational (block11 P1 Ω) (block11 P1 ρ)) = souriauRotational (block11 P1 Ω) (block11 P1 ρ)`,
   - `block00 P1 P2 (souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ)) = souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ)`,
   - `block22 P2 (souriauRotational (block22 P2 Ω) (block22 P2 ρ)) = souriauRotational (block22 P2 Ω) (block22 P2 ρ)`,
2. **Mutual annihilation of products and commutators between distinct corners:**
   - `block11 P1 A * block00 P1 P2 C = 0`, `block00 P1 P2 C * block11 P1 A = 0`,
   - `block11 P1 A * block22 P2 C = 0`, `block22 P2 C * block11 P1 A = 0`,
   - `block00 P1 P2 A * block22 P2 C = 0`, `block22 P2 C * block00 P1 P2 A = 0`,
   - `comm (block11 P1 A) (block00 P1 P2 C) = 0`, `comm (block11 P1 A) (block22 P2 C) = 0`,
     `comm (block00 P1 P2 A) (block22 P2 C) = 0`,
3. **Direct-sum product and Souriau commutator splitting on `zeroGradeSector`:**
   - `zeroGradeSector P1 P2 A * zeroGradeSector P1 P2 C = block11 P1 A * block11 P1 C + block00 P1 P2 A * block00 P1 P2 C + block22 P2 A * block22 P2 C`,
   - `souriauRotational (zeroGradeSector P1 P2 Ω) (zeroGradeSector P1 P2 ρ) = souriauRotational (block11 P1 Ω) (block11 P1 ρ) + souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ) + souriauRotational (block22 P2 Ω) (block22 P2 ρ)`.
-/
theorem diagonal_peirce_corner_products_and_commutator_splitting
    (P1 P2 A C Ω ρ : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    block11 P1 (block11 P1 A * block11 P1 C) = block11 P1 A * block11 P1 C ∧
    block00 P1 P2 (block00 P1 P2 A * block00 P1 P2 C) = block00 P1 P2 A * block00 P1 P2 C ∧
    block22 P2 (block22 P2 A * block22 P2 C) = block22 P2 A * block22 P2 C ∧
    block11 P1 (souriauRotational (block11 P1 Ω) (block11 P1 ρ)) =
      souriauRotational (block11 P1 Ω) (block11 P1 ρ) ∧
    block00 P1 P2 (souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ)) =
      souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ) ∧
    block22 P2 (souriauRotational (block22 P2 Ω) (block22 P2 ρ)) =
      souriauRotational (block22 P2 Ω) (block22 P2 ρ) ∧
    block11 P1 A * block00 P1 P2 C = 0 ∧
    block00 P1 P2 C * block11 P1 A = 0 ∧
    block11 P1 A * block22 P2 C = 0 ∧
    block22 P2 C * block11 P1 A = 0 ∧
    block00 P1 P2 A * block22 P2 C = 0 ∧
    block22 P2 C * block00 P1 P2 A = 0 ∧
    comm (block11 P1 A) (block00 P1 P2 C) = 0 ∧
    comm (block11 P1 A) (block22 P2 C) = 0 ∧
    comm (block00 P1 P2 A) (block22 P2 C) = 0 ∧
    zeroGradeSector P1 P2 A * zeroGradeSector P1 P2 C =
      block11 P1 A * block11 P1 C +
      block00 P1 P2 A * block00 P1 P2 C +
      block22 P2 A * block22 P2 C ∧
    souriauRotational (zeroGradeSector P1 P2 Ω) (zeroGradeSector P1 P2 ρ) =
      souriauRotational (block11 P1 Ω) (block11 P1 ρ) +
      souriauRotational (block00 P1 P2 Ω) (block00 P1 P2 ρ) +
      souriauRotational (block22 P2 Ω) (block22 P2 ρ) := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_nf_helpers h1 h2 h12 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only [zeroGradeSector, block11, block00, block22, P0_waist,
                souriauRotational, comm]
    try simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc,
                   h1, h2, h12, h21, h1', h2', h12', h21', mul_zero, zero_mul]
    try abel

-- ============================================================================
-- 3. OFF-DIAGONAL STEP-±1 TRANSITION BIMODULES & BROCKETT SHIFT
-- ============================================================================

/--
**Step transition theorem (`off_diagonal_peirce_sandwich_transitions_and_brockett_identity`):**
The off-diagonal step-`±1` transition operators `N_{+1} = N_pos1_3 P1 P2 X` and
`N_{-1} = N_neg1_3 P1 P2 Y` transport elements between the three diagonal Peirce corners:
1. **Waist-to-Boundary Sandwich Transport (`block00 → block11` and `block00 → block22`):**
   - `N_{+1} * block00 P1 P2 W * N_{-1} = block11 P1 (X * block00 P1 P2 W * Y)`,
   - `N_{-1} * block00 P1 P2 W * N_{+1} = block22 P2 (Y * block00 P1 P2 W * X)`,
2. **Boundary-to-Waist Sandwich Transport (`block11, block22 → block00`):**
   - `N_{-1} * block11 P1 A * N_{+1} = block00 P1 P2 (Y * block11 P1 A * X)`,
   - `N_{+1} * block22 P2 C * N_{-1} = block00 P1 P2 (X * block22 P2 C * Y)`,
3. **Two-Step Boundary-to-Boundary Transport (`block22 → block11` and `block11 → block22`):**
   - `(N_{+1} * N_{+1}) * block22 P2 C * (N_{-1} * N_{-1}) = block11 P1 (X * P0_waist P1 P2 * X * block22 P2 C * Y * P0_waist P1 P2 * Y)`,
   - `(N_{-1} * N_{-1}) * block11 P1 A * (N_{+1} * N_{+1}) = block22 P2 (Y * P0_waist P1 P2 * Y * block11 P1 A * X * P0_waist P1 P2 * X)`,
4. **Weyl Weight Shift (`±1`) and Brockett Cross-Leaf Double Commutator:**
   - `comm (H_weyl P1 P2) N_{+1} = N_{+1}`,
   - `comm (H_weyl P1 P2) N_{-1} = - N_{-1}`,
   - `brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) = 2 • comm (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y)`.
-/
theorem off_diagonal_peirce_sandwich_transitions_and_brockett_identity
    (P1 P2 X Y W A C : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let np1 := N_pos1_3 P1 P2 X
    let nm1 := N_neg1_3 P1 P2 Y
    let P0 := P0_waist P1 P2
    np1 * block00 P1 P2 W * nm1 = block11 P1 (X * block00 P1 P2 W * Y) ∧
    nm1 * block00 P1 P2 W * np1 = block22 P2 (Y * block00 P1 P2 W * X) ∧
    nm1 * block11 P1 A * np1 = block00 P1 P2 (Y * block11 P1 A * X) ∧
    np1 * block22 P2 C * nm1 = block00 P1 P2 (X * block22 P2 C * Y) ∧
    (np1 * np1) * block22 P2 C * (nm1 * nm1) =
      block11 P1 (X * P0 * X * block22 P2 C * Y * P0 * Y) ∧
    (nm1 * nm1) * block11 P1 A * (np1 * np1) =
      block22 P2 (Y * P0 * Y * block11 P1 A * X * P0 * X) ∧
    comm (H_weyl P1 P2) np1 = np1 ∧
    comm (H_weyl P1 P2) nm1 = - nm1 ∧
    brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) =
      2 • comm (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_nf_helpers h1 h2 h12 h21
  have h_rb := (three_horizon_rotating_ball_and_cl11_weitzenbock_calculus P1 P2 X Y 0 h1 h2 h12 h21).2.2.2.1
  have h_brockett :
      brockettIrrotational (J_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) =
        2 • comm (Sigma_PK3 P1 P2 X Y) (Phi_odd3 P1 P2 X Y) := by
    dsimp only [brockettIrrotational]
    exact neg_add_eq_zero.mp h_rb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_brockett⟩ <;>
    dsimp only [N_pos1_3, N_neg1_3, block11, block00, block22, P0_waist, H_weyl, comm] <;>
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 4. PARITY REFLECTION S_par = 2 H² - 1, METRIC & TRACE INVARIANCE
-- ============================================================================

/--
**Parity theorem (`parity_conjugation_fixes_corners_and_preserves_cyclic_trace`):**
Under the parity involution `Spar = S_par3 P1 P2 = 2(P₁ + P₂) - 1` and its conjugation
`parConj3 P1 P2 Z = Spar * Z * Spar`:
1. **Involution and Horizon/Waist Eigenvalues:**
   - `Spar * Spar = 1`,
   - `Spar * P₁ = P₁`, `P₁ * Spar = P₁`, `Spar * P₂ = P₂`, `P₂ * Spar = P₂`,
   - `Spar * P0_waist P1 P2 = - P0_waist P1 P2`, `P0_waist P1 P2 * Spar = - P0_waist P1 P2`,
   - `parConj3 P1 P2 (H_weyl P1 P2) = H_weyl P1 P2`,
2. **Pointwise Fixation of All Three Diagonal Corners vs. Sign Reversal of Off-Diagonal Steps:**
   - `parConj3 P1 P2 (block11 P1 Z) = block11 P1 Z`,
   - `parConj3 P1 P2 (block00 P1 P2 Z) = block00 P1 P2 Z`,
   - `parConj3 P1 P2 (block22 P2 Z) = block22 P2 Z`,
   - `parConj3 P1 P2 (zeroGradeSector P1 P2 Z) = zeroGradeSector P1 P2 Z`,
   - `parConj3 P1 P2 (N_pos1_3 P1 P2 X) = - N_pos1_3 P1 P2 X`,
   - `parConj3 P1 P2 (N_neg1_3 P1 P2 Y) = - N_neg1_3 P1 P2 Y`,
   - `parConj3 P1 P2 (Phi_odd3 P1 P2 X Y) = - Phi_odd3 P1 P2 X Y`,
3. **Invariance of the Para-Kähler Metric, Spin Bivector, and Step-1 Metric:**
   - `parConj3 P1 P2 (V_PK3 P1 P2 X Y) = V_PK3 P1 P2 X Y`,
   - `parConj3 P1 P2 (Sigma_PK3 P1 P2 X Y) = Sigma_PK3 P1 P2 X Y`,
   - `parConj3 P1 P2 (V1_weyl3 P1 P2 X Y) = V1_weyl3 P1 P2 X Y`,
4. **Cyclic Trace and Casimir Commutator Conservation:**
   - For any `τ : CyclicTrace B R`, `τ.tr (parConj3 P1 P2 Z) = τ.tr Z` and
     `τ.tr (comm (V_PK3 P1 P2 X Y) Z) = 0`.
-/
theorem parity_conjugation_fixes_corners_and_preserves_cyclic_trace
    (τ : CyclicTrace B R)
    (P1 P2 X Y Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let Spar := S_par3 P1 P2
    let P0 := P0_waist P1 P2
    Spar * Spar = 1 ∧
    Spar * P1 = P1 ∧ P1 * Spar = P1 ∧
    Spar * P2 = P2 ∧ P2 * Spar = P2 ∧
    Spar * P0 = - P0 ∧ P0 * Spar = - P0 ∧
    parConj3 P1 P2 (H_weyl P1 P2) = H_weyl P1 P2 ∧
    parConj3 P1 P2 (block11 P1 Z) = block11 P1 Z ∧
    parConj3 P1 P2 (block00 P1 P2 Z) = block00 P1 P2 Z ∧
    parConj3 P1 P2 (block22 P2 Z) = block22 P2 Z ∧
    parConj3 P1 P2 (zeroGradeSector P1 P2 Z) = zeroGradeSector P1 P2 Z ∧
    parConj3 P1 P2 (N_pos1_3 P1 P2 X) = - N_pos1_3 P1 P2 X ∧
    parConj3 P1 P2 (N_neg1_3 P1 P2 Y) = - N_neg1_3 P1 P2 Y ∧
    parConj3 P1 P2 (Phi_odd3 P1 P2 X Y) = - Phi_odd3 P1 P2 X Y ∧
    parConj3 P1 P2 (V_PK3 P1 P2 X Y) = V_PK3 P1 P2 X Y ∧
    parConj3 P1 P2 (Sigma_PK3 P1 P2 X Y) = Sigma_PK3 P1 P2 X Y ∧
    parConj3 P1 P2 (V1_weyl3 P1 P2 X Y) = V1_weyl3 P1 P2 X Y ∧
    τ.tr (parConj3 P1 P2 Z) = τ.tr Z ∧
    τ.tr (comm (V_PK3 P1 P2 X Y) Z) = 0 := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_nf_helpers h1 h2 h12 h21
  have h_Spar_sq : S_par3 P1 P2 * S_par3 P1 P2 = 1 := by
    dsimp only [S_par3, P_hor3]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_conj : τ.tr (parConj3 P1 P2 Z) = τ.tr Z := by
    dsimp only [parConj3]
    rw [τ.cyclic (S_par3 P1 P2 * Z) (S_par3 P1 P2), ← mul_assoc, h_Spar_sq, one_mul]
  have h_tr_comm : τ.tr (comm (V_PK3 P1 P2 X Y) Z) = 0 := by
    dsimp only [comm]
    rw [map_sub τ.tr, τ.cyclic (V_PK3 P1 P2 X Y) Z, sub_self]
  refine ⟨h_Spar_sq,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          h_tr_conj, h_tr_comm⟩ <;>
    dsimp only [parConj3, S_par3, P_hor3, P0_waist, H_weyl,
                zeroGradeSector, block11, block00, block22,
                N_pos1_3, N_neg1_3, Phi_odd3, Psi_out3, Psi_in3,
                V_PK3, Sigma_PK3, V1_weyl3, comm, anticomm] <;>
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- Five-grade Peirce components
-- ============================================================================

/-- Grade `-2` Peirce component `P₂ Z P₁`. -/
def gradeNeg2 (P1 P2 Z : B) : B := block21 P1 P2 Z

/-- Grade `-1` Peirce component `P₀ Z P₁ + P₂ Z P₀`. -/
def gradeNeg1 (P1 P2 Z : B) : B := block01 P1 P2 Z + block20 P1 P2 Z

/-- Grade `0` Peirce component `P₁ Z P₁ + P₀ Z P₀ + P₂ Z P₂` (sum of the three diagonal corners). -/
def gradeZero (P1 P2 Z : B) : B := zeroGradeSector P1 P2 Z

/-- Grade `+1` Peirce component `P₁ Z P₀ + P₀ Z P₂`. -/
def gradePos1 (P1 P2 Z : B) : B := block10 P1 P2 Z + block02 P1 P2 Z

/-- Grade `+2` Peirce component `P₁ Z P₂`. -/
def gradePos2 (P1 P2 Z : B) : B := block12 P1 P2 Z

end InfoGeometry.OperatorAlgebra.PeirceSpine.DeHaroModelBundleDualityPoset
