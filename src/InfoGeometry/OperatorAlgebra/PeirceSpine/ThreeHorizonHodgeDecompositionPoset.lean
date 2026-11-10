/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

/-!
# Three-Horizon Peirce Decomposition and Weyl Grades

Over an associative ring `B`, an orthogonal pair of idempotents `P1`, `P2` determines the
complementary idempotent `P0 = 1 - P1 - P2`. The file proves finite Peirce-corner reconstruction,
annihilation of the `P0` corner by the boundary idempotents, the three sector projections and
their Weyl-grade identities, and conditional cyclic-trace vanishing.

The file also constructs the 2-step nilpotent corner cochain differential (`d² = 0`), proves
formal cyclic-trace adjointness (integration by parts) of the step differentials and formal
self-adjointness of `peirceStepLaplacian`, and establishes the complete three-sector algebraic
Hodge–Peirce projector decomposition (`E_0 + E_+ + E_- = id`, `E_i ∘ E_j = δ_{ij} E_i`).

Causal order of the formal claims:
1. Orthogonal idempotents give the complementary Peirce corner and nine-corner reconstruction.
2. The complementary corner is annihilated by the two boundary idempotents.
3. The three grouped corner maps are orthogonal projections and their corners have weights
   `0, ±1, ±2` for `ad (P1 - P2)`; the step commutators of the waist corner land in the
   corresponding grouped sectors.
4. Under a cyclic trace, off-diagonal and cross-sector pairings listed in the theorem vanish.
5. If an element commutes with a commutator generator, its trace pairings with that commutator
   vanish in both orders.
6. The step differentials satisfy formal cyclic-trace skew-adjointness, the step Laplacian is
   formally self-adjoint under the cyclic trace pairing, and the grade-1 corner commutator acts
   as a 2-step nilpotent cochain differential (`d² = 0`) across the waist.

BUCKET 1: PROVED FINITE/ALGEBRAIC IDENTITIES OVER `[Ring B]`
- `peirce_nine_block_decomposition`
- `peirce_waist_corner_boundary_annihilation`
- `peirce_complement_triad`
- `peirce_grade_sector_projectors`
- `peirce_corner_weyl_weights`
- `three_sector_algebraic_hodge_peirce_cochain_and_formal_adjoint`

BUCKET 2: CONDITIONAL IDENTITIES FROM EXPLICIT PREMISES
- `cyclicTrace_tr_corner_eq_zero` (from cyclic trace `τ : CyclicTrace B R`)
- `peirce_grade_trace_pairing_vanishes` (from cyclic trace `τ : CyclicTrace B R`)
- `cyclic_trace_closed_commutator_pairing_zero` (from cyclic trace and closedness hypothesis)
- `peirce_corner_asymmetry_and_step_commutator_jacobi` (from cyclic trace `τ : CyclicTrace B R`)

BUCKET 3: CONSTRUCTIVE `[Ring B]` COMPILATION
- Every 3-horizon Peirce 9-block decomposition, corner cochain differential (`d² = 0`), and
  formal cyclic-trace Laplacian self-adjointness law is compiled into division-free `[Ring B]`
  operator identities with zero custom wrapper structures and zero `rfl` aliases.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

universe u v
variable {B : Type u} [Ring B]
variable {R : Type v} [AddCommGroup R]

/-- For any idempotent `P² = P` and any element `Q` with `Q * P = 0`, the cyclic trace of the
off-diagonal corner `P * M * Q` vanishes identically for all `M : B`:
$$\tau(P M Q) = \tau(P \cdot (P M Q)) = \tau((P M Q) \cdot P) = \tau(P M (Q P)) = \tau(0) = 0.$$ -/
theorem cyclicTrace_tr_corner_eq_zero (τ : CyclicTrace B R)
    (P Q M : B) (hP : P * P = P) (hQP : Q * P = 0) :
    τ.tr (P * M * Q) = 0 := by
  have h1 : P * M * Q = P * (P * M * Q) := by
    rw [← mul_assoc, ← mul_assoc, hP]
  have h2 : (P * M * Q) * P = 0 := by
    rw [mul_assoc, hQP, mul_zero]
  rw [h1, τ.cyclic P (P * M * Q), h2, map_zero τ.tr]

-- ============================================================================
-- 0. THE 9 PEIRCE BLOCKS & 3 HODGE SECTORS ACROSS (P₁, P₀, P₂)
-- ============================================================================

/-- Diagonal Peirce corner `(1,1)`, of Weyl grade zero. -/
def block11 (P1 Z : B) : B := P1 * Z * P1

/-- Diagonal Peirce corner `(0,0)`, of Weyl grade zero. -/
def block00 (P1 P2 Z : B) : B := P0_waist P1 P2 * Z * P0_waist P1 P2

/-- Diagonal Peirce corner `(2,2)`, of Weyl grade zero. -/
def block22 (P2 Z : B) : B := P2 * Z * P2

/-- Peirce corner `(1,0)`, of Weyl grade `+1`. -/
def block10 (P1 P2 Z : B) : B := P1 * Z * P0_waist P1 P2

/-- Peirce corner `(0,2)`, of Weyl grade `+1`. -/
def block02 (P1 P2 Z : B) : B := P0_waist P1 P2 * Z * P2

/-- Peirce corner `(1,2)`, of Weyl grade `+2`. -/
def block12 (P1 P2 Z : B) : B := P1 * Z * P2

/-- Peirce corner `(0,1)`, of Weyl grade `-1`. -/
def block01 (P1 P2 Z : B) : B := P0_waist P1 P2 * Z * P1

/-- Peirce corner `(2,0)`, of Weyl grade `-1`. -/
def block20 (P1 P2 Z : B) : B := P2 * Z * P0_waist P1 P2

/-- Peirce corner `(2,1)`, of Weyl grade `-2`. -/
def block21 (P1 P2 Z : B) : B := P2 * Z * P1

/-- **Zero-Grade Sector (Grade $0$):**
Sum of the three diagonal Peirce blocks `P₁ Z P₁ + P₀ Z P₀ + P₂ Z P₂`. -/
def zeroGradeSector (P1 P2 Z : B) : B :=
  block11 P1 Z + block00 P1 P2 Z + block22 P2 Z

/-- **Positive-Grade Sector (Grades $+1, +2$):**
Sum of the three upper-triangular Peirce blocks `P₁ Z P₀ + P₀ Z P₂ + P₁ Z P₂`. -/
def positiveGradeSector (P1 P2 Z : B) : B :=
  block10 P1 P2 Z + block02 P1 P2 Z + block12 P1 P2 Z

/-- **Negative-Grade Sector (Grades $-1, -2$):**
Sum of the three lower-triangular Peirce blocks `P₀ Z P₁ + P₂ Z P₀ + P₂ Z P₁`. -/
def negativeGradeSector (P1 P2 Z : B) : B :=
  block01 P1 P2 Z + block20 P1 P2 Z + block21 P1 P2 Z

/-- **Positive-step commutator `Z ↦ [N_{+1}, Z]`** for the grade-$+1$ operator `N_{+1}`. -/
def positiveStepCommutator (P1 P2 X Z : B) : B :=
  comm (N_pos1_3 P1 P2 X) Z

/-- **Negative-step commutator `Z ↦ [N_{-1}, Z]`** for the grade-$-1$ operator `N_{-1}`. -/
def negativeStepCommutator (P1 P2 Y Z : B) : B :=
  comm (N_neg1_3 P1 P2 Y) Z

/-- Composition through a matching Peirce corner contracts the middle idempotent. -/
theorem peirce_corner_compose (P Q X Y R : B) (hQ : Q * Q = Q) :
    (P * X * Q) * (Q * Y * R) = P * X * Q * Y * R := by
  rw [show (P * X * Q) * (Q * Y * R) = P * X * (Q * Q) * Y * R by noncomm_ring, hQ]

/-- Distinct orthogonal middle corners force a product of Peirce blocks to vanish. -/
theorem peirce_corner_mismatch_zero (P Q R X Y S : B) (hQR : Q * R = 0) :
    (P * X * Q) * (R * Y * S) = 0 := by
  rw [show (P * X * Q) * (R * Y * S) = P * X * (Q * R) * Y * S by noncomm_ring,
      hQR, mul_zero, zero_mul, zero_mul]

-- ============================================================================
-- 1. THE PEIRCE 9-BLOCK COMPLETENESS & THREE-SECTOR RESOLUTION THEOREM
-- ============================================================================

/--
**Theorem 1 (`peirce_nine_block_decomposition`): Complete 9-Block & 3-Grade Peirce Resolution across `(P₁, P₀, P₂)`:**
If `P₁² = P₁, P₂² = P₂, P₁ P₂ = P₂ P₁ = 0` and `P₀ = 1 - P₁ - P₂`, then for every `Z : B`:
1. `P₁ + P₀ + P₂ = 1`, `P₀ * P₀ = P₀`, and `P₁ * P₀ = 0 = P₀ * P₁ = P₂ * P₀ = P₀ * P₂`,
2. The sum of the 9 Peirce blocks reconstructs `Z` identically:
   `Z₁₁ + Z₀₀ + Z₂₂ + Z₁₀ + Z₀₂ + Z₁₂ + Z₀₁ + Z₂₀ + Z₂₁ = Z`,
3. The sum of the zero-, positive-, and negative-grade sectors reconstructs `Z` identically:
   `zeroGradeSector P1 P2 Z + positiveGradeSector P1 P2 Z + negativeGradeSector P1 P2 Z = Z`.
-/
theorem peirce_nine_block_decomposition
    (P1 P2 : B) (Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let Z11 := P1 * Z * P1
    let Z00 := P0 * Z * P0
    let Z22 := P2 * Z * P2
    let Z10 := P1 * Z * P0
    let Z02 := P0 * Z * P2
    let Z12 := P1 * Z * P2
    let Z01 := P0 * Z * P1
    let Z20 := P2 * Z * P0
    let Z21 := P2 * Z * P1
    P1 + P0 + P2 = 1 ∧
    P0 * P0 = P0 ∧
    Z11 + Z00 + Z22 + Z10 + Z02 + Z12 + Z01 + Z20 + Z21 = Z ∧
    zeroGradeSector P1 P2 Z + positiveGradeSector P1 P2 Z + negativeGradeSector P1 P2 Z = Z := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  refine ⟨by abel, ?_, ?_, ?_⟩
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · dsimp only [zeroGradeSector, positiveGradeSector, negativeGradeSector,
                block11, block00, block22, block10, block02, block12,
                block01, block20, block21, P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 2. THE DARK CONDENSATE (HARMONIC WAIST) ANNIHILATION THEOREM
-- ============================================================================

/--
**Theorem 2 (`peirce_waist_corner_boundary_annihilation`): Boundary annihilation of the waist corner:**
The waist-corner element `W₀ := P₀ * W * P₀` is annihilated by `P₁` and `P₂` on either side:
multiplying `W₀` by `P₁` or `P₂` on either the left or right yields `0` identically,
its boundary sandwiches vanish (`P₁ * W₀ * P₁ = 0`, `P₂ * W₀ * P₂ = 0`), and it and therefore commutes with `P₁`, `P₂`, and `H_weyl = P₁ - P₂`.
-/
theorem peirce_waist_corner_boundary_annihilation
    (P1 P2 W : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let W0 := P0 * W * P0
    P1 * W0 = 0 ∧ W0 * P1 = 0 ∧
    P2 * W0 = 0 ∧ W0 * P2 = 0 ∧
    P1 * W0 * P1 = 0 ∧ P2 * W0 * P2 = 0 ∧
    comm P1 W0 = 0 ∧ comm P2 W0 = 0 ∧
    comm (H_weyl P1 P2) W0 = 0 := by
  have h1'  : ∀ X, P1 * (P1 * X) = P1 * X := fun X => by rw [← mul_assoc, h1]
  have h2'  : ∀ X, P2 * (P2 * X) = P2 * X := fun X => by rw [← mul_assoc, h2]
  have h12' : ∀ X, P1 * (P2 * X) = 0 := fun X => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ X, P2 * (P1 * X) = 0 := fun X => by rw [← mul_assoc, h21, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · unfold comm
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · unfold comm
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · unfold comm H_weyl
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 3. THREE-SECTOR PROJECTOR ALGEBRA & 5-GRADED EIGENVALUE SPECTRUM
-- ============================================================================

/-- Right-associated idempotent and orthogonality rewrite helpers for `P₁, P₂`. -/
private theorem peirce_grade_nf {P1 P2 : B}
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    (∀ M, P1 * (P1 * M) = P1 * M) ∧
    (∀ M, P2 * (P2 * M) = P2 * M) ∧
    (∀ M, P1 * (P2 * M) = 0) ∧
    (∀ M, P2 * (P1 * M) = 0) := by
  exact ⟨fun M => by rw [← mul_assoc, h1],
          fun M => by rw [← mul_assoc, h2],
          fun M => by rw [← mul_assoc, h12, zero_mul],
          fun M => by rw [← mul_assoc, h21, zero_mul]⟩

/-- The complement `P₀ = 1 - P₁ - P₂` completes an orthogonal idempotent triad. -/
theorem peirce_complement_triad
    (P1 P2 : B) (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := P0_waist P1 P2
    P0 * P0 = P0 ∧ P1 * P0 = 0 ∧ P0 * P1 = 0 ∧
      P2 * P0 = 0 ∧ P0 * P2 = 0 ∧ P1 + P0 + P2 = 1 := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_grade_nf h1 h2 h12 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, by dsimp only [P0_waist]; abel⟩ <;>
    dsimp only [P0_waist] <;>
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- The three grouped Peirce-sector maps are idempotent and pairwise orthogonal. -/
theorem peirce_grade_sector_projectors
    (P1 P2 Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    zeroGradeSector P1 P2 (zeroGradeSector P1 P2 Z) = zeroGradeSector P1 P2 Z ∧
    positiveGradeSector P1 P2 (positiveGradeSector P1 P2 Z) = positiveGradeSector P1 P2 Z ∧
    negativeGradeSector P1 P2 (negativeGradeSector P1 P2 Z) = negativeGradeSector P1 P2 Z ∧
    zeroGradeSector P1 P2 (positiveGradeSector P1 P2 Z) = 0 ∧
    positiveGradeSector P1 P2 (zeroGradeSector P1 P2 Z) = 0 ∧
    zeroGradeSector P1 P2 (negativeGradeSector P1 P2 Z) = 0 ∧
    negativeGradeSector P1 P2 (zeroGradeSector P1 P2 Z) = 0 ∧
    positiveGradeSector P1 P2 (negativeGradeSector P1 P2 Z) = 0 ∧
    negativeGradeSector P1 P2 (positiveGradeSector P1 P2 Z) = 0 := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_grade_nf h1 h2 h12 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [zeroGradeSector, positiveGradeSector, negativeGradeSector,
      block11, block00, block22, block10, block02, block12,
      block01, block20, block21, P0_waist]
  all_goals parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- Each Peirce corner is an eigenvector for `ad (P1 - P2)` with weight `0`, `±1`, or `±2`. -/
theorem peirce_corner_weyl_weights
    (P1 P2 Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let Hw := H_weyl P1 P2
    comm Hw (block11 P1 Z) = 0 ∧
    comm Hw (block00 P1 P2 Z) = 0 ∧
    comm Hw (block22 P2 Z) = 0 ∧
    comm Hw (zeroGradeSector P1 P2 Z) = 0 ∧
    comm Hw (block10 P1 P2 Z) = block10 P1 P2 Z ∧
    comm Hw (block02 P1 P2 Z) = block02 P1 P2 Z ∧
    comm Hw (block12 P1 P2 Z) = 2 • block12 P1 P2 Z ∧
    comm Hw (block01 P1 P2 Z) = - block01 P1 P2 Z ∧
    comm Hw (block20 P1 P2 Z) = - block20 P1 P2 Z ∧
    comm Hw (block21 P1 P2 Z) = -(2 • block21 P1 P2 Z) := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_grade_nf h1 h2 h12 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [zeroGradeSector, positiveGradeSector, negativeGradeSector,
      block11, block00, block22, block10, block02, block12,
      block01, block20, block21, P0_waist, H_weyl, comm, two_nsmul]
  all_goals parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- The two step commutators of the waist corner lie in their corresponding grouped Peirce sectors. -/
theorem peirce_waist_step_commutator_sector
    (P1 P2 X Y W : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let W0 := block00 P1 P2 W
    let dW0 := positiveStepCommutator P1 P2 X W0
    let cW0 := negativeStepCommutator P1 P2 Y W0
    positiveGradeSector P1 P2 dW0 = dW0 ∧
    zeroGradeSector P1 P2 dW0 = 0 ∧
    negativeGradeSector P1 P2 dW0 = 0 ∧
    negativeGradeSector P1 P2 cW0 = cW0 ∧
    zeroGradeSector P1 P2 cW0 = 0 ∧
    positiveGradeSector P1 P2 cW0 = 0 := by
  obtain ⟨h1', h2', h12', h21'⟩ := peirce_grade_nf h1 h2 h12 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [zeroGradeSector, positiveGradeSector, negativeGradeSector,
      block11, block00, block22, block10, block02, block12,
      block01, block20, block21, positiveStepCommutator, negativeStepCommutator,
      N_pos1_3, N_neg1_3, P0_waist, H_weyl, comm, two_nsmul]
  all_goals parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

-- ============================================================================
-- 4. CYCLIC TRACE PAIRING VANISHING FOR PEIRCE SECTORS
-- ============================================================================

/--
**Theorem 4 (`peirce_grade_trace_pairing_vanishes`): Cyclic-trace vanishing from Peirce support:**
Under any cyclic trace functional `τ : CyclicTrace B R`:
1. **Positive-Grade/Waist Corner Pairing:**
   For `F = P₁ * A * P₀` and `W = P₀ * Z * P₀`,
   `W * F = 0` at the operator level, so both cyclic trace pairings vanish:
   `τ.tr (F * W) = 0` and `τ.tr (W * F) = 0`.
2. **Sector Trace Vanishing from Peirce Support:**
   - `τ.tr (positiveGradeSector P1 P2 Z) = 0` and `τ.tr (negativeGradeSector P1 P2 Z) = 0`,
   - `τ.tr (positiveGradeSector P1 P2 A * W_corner) = 0` and `τ.tr (W_corner * positiveGradeSector P1 P2 A) = 0`,
   - `τ.tr (positiveGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0` and
     `τ.tr (zeroGradeSector P1 P2 Z * positiveGradeSector P1 P2 A) = 0`,
   - `τ.tr (negativeGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0` and
     `τ.tr (zeroGradeSector P1 P2 Z * negativeGradeSector P1 P2 A) = 0`.
-/
theorem peirce_grade_trace_pairing_vanishes
    (τ : CyclicTrace B R)
    (P1 P2 A Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let F_corner := P1 * A * P0
    let W_corner := P0 * Z * P0
    W_corner * F_corner = 0 ∧
    τ.tr (F_corner * W_corner) = 0 ∧
    τ.tr (W_corner * F_corner) = 0 ∧
    τ.tr (positiveGradeSector P1 P2 Z) = 0 ∧
    τ.tr (negativeGradeSector P1 P2 Z) = 0 ∧
    τ.tr (positiveGradeSector P1 P2 A * W_corner) = 0 ∧
    τ.tr (W_corner * positiveGradeSector P1 P2 A) = 0 ∧
    τ.tr (positiveGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0 ∧
    τ.tr (zeroGradeSector P1 P2 Z * positiveGradeSector P1 P2 A) = 0 ∧
    τ.tr (negativeGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0 ∧
    τ.tr (zeroGradeSector P1 P2 Z * negativeGradeSector P1 P2 A) = 0 := by
  intro P0 F_corner W_corner
  have h1'  : ∀ M, P1 * (P1 * M) = P1 * M := fun M => by rw [← mul_assoc, h1]
  have h2'  : ∀ M, P2 * (P2 * M) = P2 * M := fun M => by rw [← mul_assoc, h2]
  have h12' : ∀ M, P1 * (P2 * M) = 0 := fun M => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ M, P2 * (P1 * M) = 0 := fun M => by rw [← mul_assoc, h21, zero_mul]
  have hP0 : P0 * P0 = P0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hP01 : P0 * P1 = 0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hP10 : P1 * P0 = 0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hP02 : P0 * P2 = 0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hP20 : P2 * P0 = 0 := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  -- Off-diagonal corner trace helper for all 6 off-diagonal pairs:
  have htr10 : ∀ M, τ.tr (P1 * M * P0) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P1 P0 M h1 hP01
  have htr02 : ∀ M, τ.tr (P0 * M * P2) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P0 P2 M hP0 hP20
  have htr12 : ∀ M, τ.tr (P1 * M * P2) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P1 P2 M h1 h21
  have htr01 : ∀ M, τ.tr (P0 * M * P1) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P0 P1 M hP0 hP10
  have htr20 : ∀ M, τ.tr (P2 * M * P0) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P2 P0 M h2 hP02
  have htr21 : ∀ M, τ.tr (P2 * M * P1) = 0 := fun M => cyclicTrace_tr_corner_eq_zero τ P2 P1 M h2 h12
  have h_WF : W_corner * F_corner = 0 := by
    dsimp only [W_corner, F_corner, P0]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_WF : τ.tr (W_corner * F_corner) = 0 := by
    rw [h_WF, map_zero τ.tr]
  have h_tr_FW : τ.tr (F_corner * W_corner) = 0 := by
    rw [τ.cyclic F_corner W_corner, h_tr_WF]
  have h_tr_E : ∀ M, τ.tr (positiveGradeSector P1 P2 M) = 0 := by
    intro M
    dsimp only [positiveGradeSector, block10, block02, block12]
    change τ.tr (P1 * M * P0 + P0 * M * P2 + P1 * M * P2) = 0
    rw [map_add τ.tr, map_add τ.tr, htr10, htr02, htr12, add_zero, add_zero]
  have h_tr_C : ∀ M, τ.tr (negativeGradeSector P1 P2 M) = 0 := by
    intro M
    dsimp only [negativeGradeSector, block01, block20, block21]
    change τ.tr (P0 * M * P1 + P2 * M * P0 + P2 * M * P1) = 0
    rw [map_add τ.tr, map_add τ.tr, htr01, htr20, htr21, add_zero, add_zero]
  have h_EW_in_E : positiveGradeSector P1 P2 A * W_corner = positiveGradeSector P1 P2 (positiveGradeSector P1 P2 A * W_corner) := by
    dsimp only [positiveGradeSector, block10, block02, block12, W_corner, P0, P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_EW : τ.tr (positiveGradeSector P1 P2 A * W_corner) = 0 := by
    rw [h_EW_in_E, h_tr_E]
  have h_tr_WE : τ.tr (W_corner * positiveGradeSector P1 P2 A) = 0 := by
    rw [τ.cyclic W_corner (positiveGradeSector P1 P2 A), h_tr_EW]
  have h_EH_in_E :
      positiveGradeSector P1 P2 A * zeroGradeSector P1 P2 Z =
        positiveGradeSector P1 P2 (positiveGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) := by
    dsimp only [positiveGradeSector, zeroGradeSector, block11, block00, block22,
                block10, block02, block12, P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_EH : τ.tr (positiveGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0 := by
    rw [h_EH_in_E, h_tr_E]
  have h_tr_HE : τ.tr (zeroGradeSector P1 P2 Z * positiveGradeSector P1 P2 A) = 0 := by
    rw [τ.cyclic (zeroGradeSector P1 P2 Z) (positiveGradeSector P1 P2 A), h_tr_EH]
  have h_CH_in_C :
      negativeGradeSector P1 P2 A * zeroGradeSector P1 P2 Z =
        negativeGradeSector P1 P2 (negativeGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) := by
    dsimp only [negativeGradeSector, zeroGradeSector, block11, block00, block22,
                block01, block20, block21, P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_tr_CH : τ.tr (negativeGradeSector P1 P2 A * zeroGradeSector P1 P2 Z) = 0 := by
    rw [h_CH_in_C, h_tr_C]
  have h_tr_HC : τ.tr (zeroGradeSector P1 P2 Z * negativeGradeSector P1 P2 A) = 0 := by
    rw [τ.cyclic (zeroGradeSector P1 P2 Z) (negativeGradeSector P1 P2 A), h_tr_CH]
  exact ⟨h_WF, h_tr_FW, h_tr_WF, h_tr_E Z, h_tr_C Z,
         h_tr_EW, h_tr_WE, h_tr_EH, h_tr_HE, h_tr_CH, h_tr_HC⟩

/--
**Theorem 5 (`cyclic_trace_closed_commutator_pairing_zero`): Vanishing trace pairings for a commutator with a commuting element:**
For any element `D : B` and any cyclic trace `τ : CyclicTrace B R`:
If `Ω` commutes with `D` (`comm D Ω = 0`), then `τ.tr (comm D A * Ω) = 0` and
`τ.tr (Ω * comm D A) = 0`.
-/
theorem cyclic_trace_closed_commutator_pairing_zero
    (τ : CyclicTrace B R) (D A Ω : B) (h_closed : comm D Ω = 0) :
    τ.tr (comm D A * Ω) = 0 ∧ τ.tr (Ω * comm D A) = 0 := by
  have h_expand : comm D A * Ω = D * (A * Ω) - A * (D * Ω) := by
    unfold comm; noncomm_ring
  have h_DΩ : D * Ω = Ω * D := sub_eq_zero.mp h_closed
  have h_assoc : (A * Ω) * D = A * (D * Ω) := by
    rw [h_DΩ]
    noncomm_ring
  have h_first : τ.tr (comm D A * Ω) = 0 := by
    rw [h_expand, map_sub τ.tr, τ.cyclic D (A * Ω), h_assoc, sub_self]
  have h_second : τ.tr (Ω * comm D A) = 0 := by
    rw [τ.cyclic Ω (comm D A), h_first]
  exact ⟨h_first, h_second⟩

-- ============================================================================
-- 5. THE PEIRCE STEP-COMMUTATOR LAPLACIAN AND ITS JACOBI IDENTITY
-- ============================================================================

/-- Anticommutator of the two graded commutator steps. This is an algebraic operator;
it is not a Hilbert-space Hodge Laplacian without additional differential and adjoint structure. -/
def peirceStepLaplacian (P1 P2 X Y Z : B) : B :=
  positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y Z) +
  negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X Z)

/--
**Peirce corner product asymmetry and step-commutator Jacobi identities:**
The ordered corner products differ, although the cyclic trace pairing vanishes:
1. **Right-Action Annihilation vs. Left-Action Dressing:**
   - `W_corner * F_corner = 0` (operator-level annihilation because `P₀ * P₁ = 0`),
   - `F_corner * W_corner = P₁ * A * W_corner` (a potentially nonzero ordered product in the positive Peirce sector),
   - `comm F_corner W_corner = P₁ * A * W_corner` (the commutator `[F_corner, W_corner]` is the dressed wave!).
2. **Step-commutator Jacobi decomposition:**
   - `[N_{+1}, [N_{-1}, Z]] - [N_{-1}, [N_{+1}, Z]] = [[N_{+1}, N_{-1}], Z]`,
   - If `W_corner` is closed and coclosed (`[N_{+1}, W_corner] = 0` and `[N_{-1}, W_corner] = 0`), then
     `peirceStepLaplacian P1 P2 X Y W_corner = 0` under the stated closedness hypotheses and
     `τ.tr (positiveStepCommutator P1 P2 X A * W_corner) = 0` and
     `τ.tr (negativeStepCommutator P1 P2 Y A * W_corner) = 0` for all `A : B`.
-/
theorem peirce_corner_asymmetry_and_step_commutator_jacobi
    (τ : CyclicTrace B R)
    (P1 P2 X Y A Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let F_corner := P1 * A * P0
    let W_corner := P0 * Z * P0
    -- 1. Operator-level asymmetry & commutator dressing:
    W_corner * F_corner = 0 ∧
    F_corner * W_corner = P1 * A * W_corner ∧
    comm F_corner W_corner = P1 * A * W_corner ∧
    -- 2. Jacobi identity for the two step-commutator operators:
    positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y Z) -
      negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X Z) =
      comm (comm (N_pos1_3 P1 P2 X) (N_neg1_3 P1 P2 Y)) Z ∧
    -- 3. Laplacian vanishing and cyclic-trace pairing for a corner element closed under both steps:
    (positiveStepCommutator P1 P2 X W_corner = 0 →
     negativeStepCommutator P1 P2 Y W_corner = 0 →
     peirceStepLaplacian P1 P2 X Y W_corner = 0 ∧
     τ.tr (positiveStepCommutator P1 P2 X A * W_corner) = 0 ∧
     τ.tr (negativeStepCommutator P1 P2 Y A * W_corner) = 0) := by
  have h1'  : ∀ M, P1 * (P1 * M) = P1 * M := fun M => by rw [← mul_assoc, h1]
  have h2'  : ∀ M, P2 * (P2 * M) = P2 * M := fun M => by rw [← mul_assoc, h2]
  have h12' : ∀ M, P1 * (P2 * M) = 0 := fun M => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ M, P2 * (P1 * M) = 0 := fun M => by rw [← mul_assoc, h21, zero_mul]
  have h_WF : (1 - P1 - P2) * Z * (1 - P1 - P2) * (P1 * A * (1 - P1 - P2)) = 0 := by
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_FW : (P1 * A * (1 - P1 - P2)) * ((1 - P1 - P2) * Z * (1 - P1 - P2)) =
      P1 * A * ((1 - P1 - P2) * Z * (1 - P1 - P2)) := by
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_comm : comm (P1 * A * (1 - P1 - P2)) ((1 - P1 - P2) * Z * (1 - P1 - P2)) =
      P1 * A * ((1 - P1 - P2) * Z * (1 - P1 - P2)) := by
    dsimp only [comm]
    rw [h_FW, h_WF, sub_zero]
  have h_jacobi :
      positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y Z) -
        negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X Z) =
        comm (comm (N_pos1_3 P1 P2 X) (N_neg1_3 P1 P2 Y)) Z := by
    dsimp only [positiveStepCommutator, negativeStepCommutator, comm]
    noncomm_ring
  refine ⟨h_WF, h_FW, h_comm, h_jacobi, fun hd hδ => ?_⟩
  have h_lap : peirceStepLaplacian P1 P2 X Y ((1 - P1 - P2) * Z * (1 - P1 - P2)) = 0 := by
    dsimp only [peirceStepLaplacian]
    rw [hδ, hd]
    dsimp only [positiveStepCommutator, negativeStepCommutator, comm]
    simp only [mul_zero, zero_mul, sub_self, add_zero]
  have h_tr_d : τ.tr (positiveStepCommutator P1 P2 X A * ((1 - P1 - P2) * Z * (1 - P1 - P2))) = 0 :=
    (cyclic_trace_closed_commutator_pairing_zero τ (N_pos1_3 P1 P2 X) A
      ((1 - P1 - P2) * Z * (1 - P1 - P2)) hd).1
  have h_tr_δ : τ.tr (negativeStepCommutator P1 P2 Y A * ((1 - P1 - P2) * Z * (1 - P1 - P2))) = 0 :=
    (cyclic_trace_closed_commutator_pairing_zero τ (N_neg1_3 P1 P2 Y) A
      ((1 - P1 - P2) * Z * (1 - P1 - P2)) hδ).1
  exact ⟨h_lap, h_tr_d, h_tr_δ⟩

-- ============================================================================
-- 6. ALGEBRAIC COCHAIN DIFFERENTIAL, FORMAL TRACE ADJOINT, AND HODGE-PEIRCE DECOMPOSITION
-- ============================================================================

/-- Nilpotent corner cochain differential `d_{10}(Z) = [P₁ X P₀, Z]`. -/
def cornerCochainDiff10 (P1 P2 X Z : B) : B :=
  comm (block10 P1 P2 X) Z

/--
**Theorem 6 (`three_sector_algebraic_hodge_peirce_cochain_and_formal_adjoint`):**
In any associative ring `[Ring B]` with orthogonal idempotents `P₁² = P₁, P₂² = P₂, P₁ P₂ = P₂ P₁ = 0`
and cyclic trace `τ : CyclicTrace B R`:
1. **Two-Step Cochain Nilpotency (`d² = 0` Across the Waist):**
   The corner generator `D₁₀ = block10 P1 P2 X` is square-zero (`D₁₀ * D₁₀ = 0`), maps the waist-to-boundary
   corner `block02 P1 P2 Y` onto the cross-horizon grade-2 corner `block12 P1 P2 (X * P₀ * Y)`,
   and annihilates it at the second cochain step:
   `cornerCochainDiff10 P1 P2 X (cornerCochainDiff10 P1 P2 X (block02 P1 P2 Y)) = 0`.
2. **Formal Cyclic-Trace Skew-Adjointness of Step Differentials & Self-Adjointness of the Step Laplacian:**
   - `τ.tr (positiveStepCommutator P1 P2 X A * Z) = - τ.tr (A * positiveStepCommutator P1 P2 X Z)`,
   - `τ.tr (negativeStepCommutator P1 P2 Y A * Z) = - τ.tr (A * negativeStepCommutator P1 P2 Y Z)`,
   - `τ.tr (peirceStepLaplacian P1 P2 X Y A * Z) = τ.tr (A * peirceStepLaplacian P1 P2 X Y Z)`.
3. **Complete Three-Sector Algebraic Hodge–Peirce Decomposition:**
   `Z = zeroGradeSector P1 P2 Z + positiveGradeSector P1 P2 Z + negativeGradeSector P1 P2 Z`.
-/
theorem three_sector_algebraic_hodge_peirce_cochain_and_formal_adjoint
    (τ : CyclicTrace B R)
    (P1 P2 X Y A Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := P0_waist P1 P2
    let D10 := block10 P1 P2 X
    D10 * D10 = 0 ∧
    cornerCochainDiff10 P1 P2 X (block02 P1 P2 Y) = block12 P1 P2 (X * P0 * Y) ∧
    cornerCochainDiff10 P1 P2 X (cornerCochainDiff10 P1 P2 X (block02 P1 P2 Y)) = 0 ∧
    τ.tr (positiveStepCommutator P1 P2 X A * Z) =
      - τ.tr (A * positiveStepCommutator P1 P2 X Z) ∧
    τ.tr (negativeStepCommutator P1 P2 Y A * Z) =
      - τ.tr (A * negativeStepCommutator P1 P2 Y Z) ∧
    τ.tr (peirceStepLaplacian P1 P2 X Y A * Z) =
      τ.tr (A * peirceStepLaplacian P1 P2 X Y Z) ∧
    Z = zeroGradeSector P1 P2 Z + positiveGradeSector P1 P2 Z + negativeGradeSector P1 P2 Z := by
  have h1'  : ∀ M, P1 * (P1 * M) = P1 * M := fun M => by rw [← mul_assoc, h1]
  have h2'  : ∀ M, P2 * (P2 * M) = P2 * M := fun M => by rw [← mul_assoc, h2]
  have h12' : ∀ M, P1 * (P2 * M) = 0 := fun M => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ M, P2 * (P1 * M) = 0 := fun M => by rw [← mul_assoc, h21, zero_mul]
  have h_comm_adj : ∀ D U V : B, τ.tr (comm D U * V) = - τ.tr (U * comm D V) := by
    intro D U V
    have h_lhs : comm D U * V = D * (U * V) - (U * D) * V := by
      unfold comm; noncomm_ring
    have h_rhs : U * comm D V = (U * D) * V - (U * V) * D := by
      unfold comm; noncomm_ring
    rw [h_lhs, h_rhs, map_sub τ.tr, map_sub τ.tr, τ.cyclic D (U * V)]
    abel
  have h_d_step1 : cornerCochainDiff10 P1 P2 X (block02 P1 P2 Y) =
      block12 P1 P2 (X * P0_waist P1 P2 * Y) := by
    dsimp only [cornerCochainDiff10, block10, block02, block12, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_d_step2 : cornerCochainDiff10 P1 P2 X (cornerCochainDiff10 P1 P2 X (block02 P1 P2 Y)) = 0 := by
    rw [h_d_step1]
    dsimp only [cornerCochainDiff10, block10, block12, P0_waist, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_pos_adj :
      τ.tr (positiveStepCommutator P1 P2 X A * Z) =
        - τ.tr (A * positiveStepCommutator P1 P2 X Z) :=
    h_comm_adj (N_pos1_3 P1 P2 X) A Z
  have h_neg_adj :
      τ.tr (negativeStepCommutator P1 P2 Y A * Z) =
        - τ.tr (A * negativeStepCommutator P1 P2 Y Z) :=
    h_comm_adj (N_neg1_3 P1 P2 Y) A Z
  have h_lap_adj :
      τ.tr (peirceStepLaplacian P1 P2 X Y A * Z) =
        τ.tr (A * peirceStepLaplacian P1 P2 X Y Z) := by
    dsimp only [peirceStepLaplacian]
    rw [add_mul, mul_add, map_add τ.tr, map_add τ.tr]
    have h_pn :
        τ.tr (positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y A) * Z) =
          τ.tr (A * negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X Z)) := by
      have h1_adj :
          τ.tr (positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y A) * Z) =
            - τ.tr (negativeStepCommutator P1 P2 Y A * positiveStepCommutator P1 P2 X Z) :=
        h_comm_adj (N_pos1_3 P1 P2 X) (negativeStepCommutator P1 P2 Y A) Z
      have h2_adj :
          τ.tr (negativeStepCommutator P1 P2 Y A * positiveStepCommutator P1 P2 X Z) =
            - τ.tr (A * negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X Z)) :=
        h_comm_adj (N_neg1_3 P1 P2 Y) A (positiveStepCommutator P1 P2 X Z)
      rw [h1_adj, h2_adj, neg_neg]
    have h_np :
        τ.tr (negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X A) * Z) =
          τ.tr (A * positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y Z)) := by
      have h1_adj :
          τ.tr (negativeStepCommutator P1 P2 Y (positiveStepCommutator P1 P2 X A) * Z) =
            - τ.tr (positiveStepCommutator P1 P2 X A * negativeStepCommutator P1 P2 Y Z) :=
        h_comm_adj (N_neg1_3 P1 P2 Y) (positiveStepCommutator P1 P2 X A) Z
      have h2_adj :
          τ.tr (positiveStepCommutator P1 P2 X A * negativeStepCommutator P1 P2 Y Z) =
            - τ.tr (A * positiveStepCommutator P1 P2 X (negativeStepCommutator P1 P2 Y Z)) :=
        h_comm_adj (N_pos1_3 P1 P2 X) A (negativeStepCommutator P1 P2 Y Z)
      rw [h1_adj, h2_adj, neg_neg]
    rw [h_pn, h_np, add_comm]
  refine ⟨?_, h_d_step1, h_d_step2, h_pos_adj, h_neg_adj, h_lap_adj, ?_⟩
  · dsimp only [block10, P0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  · exact Eq.symm (peirce_nine_block_decomposition P1 P2 Z h1 h2 h12 h21).2.2.2

end InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
