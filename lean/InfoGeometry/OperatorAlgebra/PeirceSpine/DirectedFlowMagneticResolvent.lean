/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockTriangularIntervention
import InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra
import InfoGeometry.SignedNetwork.RankedDAGResolvent

/-!
# Symmetric/Skew-Adjoint Corner Decomposition, Grading-Twisted Self-Adjoint Operators, and Three-Idempotent Step Resolvents

In an arbitrary non-commutative star-ring `B` equipped with a self-adjoint idempotent
`P` (`P * P = P`, `star P = P`):

1. **Symmetric and skew-adjoint decomposition (`symAdj`, `skewAdj`):**
   Every element `W : B` decomposes as `symAdj W + skewAdj W = (2 : ℤ) • W` into a
   self-adjoint component `W + star W` and a skew-adjoint component `W - star W`.
   On the upper Peirce corner `W = conePlus P A`, these recover `genPhi P A (star A)`
   and `genJ P A (star A)`, whose squares are `+genV P A (star A)` and `-genV P A (star A)`.
2. **Grading-twisted self-adjoint corner operator (`gradingTwistedAdj`, `gradingTwistedLaplacian`):**
   Twisting the upper corner and its adjoint by the grading involution `invS P = P - (1 - P)`
   produces `gradingTwistedAdj P A = invS P * conePlus P A + star (conePlus P A) * invS P`.
   The exact ordered identities are `gradingTwistedAdj = invS P * genJ` and
   `gradingTwistedAdj = -(genJ * invS P)`. The operator is self-adjoint and squares
   to `+genV P A (star A)`.
3. **Three-idempotent strictly upper-triangular step operator (`twoStepUpper`, `twoStepResolvent`):**
   For mutually orthogonal idempotents `P₁, P₂` and complementary idempotent
   `third P₁ P₂ = 1 - P₁ - P₂`, the step sum `T = P₁ A P₂ + P₂ C (1 - P₁ - P₂)` has
   square `P₁ A P₂ C (1 - P₁ - P₂)`, cube `0`, and two-sided inverse `1 + T + T * T`
   for `1 - T`, matching `RankedDAGResolvent.finiteGreen T 3`.
4. **Master causal poset synthesis (`stage_D15_directed_flow_magnetic_resolvent_and_block_intervention`):**
   Combines the star-corner decomposition, grading-twisted self-adjoint operator,
   three-idempotent step resolvent, and lower block-triangular compression invariance.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra (third)
open InfoGeometry.SignedNetwork.RankedDAGResolvent (finiteGreen finiteGreen_left_inverse finiteGreen_right_inverse)

variable {B : Type*} [Ring B]

/-! ### 1. Symmetric and skew-adjoint decomposition in a star-ring -/

section StarDecomposition

variable [StarRing B]

/-- Self-adjoint sum `W + star W`. -/
def symAdj (W : B) : B := W + star W

/-- Skew-adjoint difference `W - star W`. -/
def skewAdj (W : B) : B := W - star W

/-- Grading-twisted corner operator `S N₊(A) + N₊(A)⋆ S`. -/
def gradingTwistedAdj (P A : B) : B :=
  invS P * conePlus P A + star (conePlus P A) * invS P

/-- Difference operator `D - gradingTwistedAdj P A`. -/
def gradingTwistedLaplacian (P D A : B) : B :=
  D - gradingTwistedAdj P A

theorem symAdj_add_skewAdj (W : B) :
    symAdj W + skewAdj W = (2 : ℤ) • W := by
  unfold symAdj skewAdj
  noncomm_ring

theorem symAdj_sub_skewAdj (W : B) :
    symAdj W - skewAdj W = (2 : ℤ) • star W := by
  unfold symAdj skewAdj
  noncomm_ring

theorem star_symAdj (W : B) :
    star (symAdj W) = symAdj W := by
  unfold symAdj
  rw [star_add, star_star, add_comm]

theorem star_skewAdj (W : B) :
    star (skewAdj W) = -skewAdj W := by
  unfold skewAdj
  rw [star_sub, star_star, neg_sub]

variable {P : B} (hPs : star P = P)
include hPs

theorem symAdj_conePlus (A : B) :
    symAdj (conePlus P A) = genPhi P A (star A) := by
  unfold symAdj genPhi
  rw [star_conePlus hPs]

theorem skewAdj_conePlus (A : B) :
    skewAdj (conePlus P A) = genJ P A (star A) := by
  unfold skewAdj genJ
  rw [star_conePlus hPs]

theorem star_gradingTwistedAdj (A : B) :
    star (gradingTwistedAdj P A) = gradingTwistedAdj P A := by
  unfold gradingTwistedAdj
  rw [star_add, star_mul, star_mul, star_star, star_invS hPs, add_comm]

theorem star_gradingTwistedLaplacian {D : B} (hDs : star D = D) (A : B) :
    star (gradingTwistedLaplacian P D A) = gradingTwistedLaplacian P D A := by
  unfold gradingTwistedLaplacian
  rw [star_sub, hDs, star_gradingTwistedAdj hPs]

variable (hP : P * P = P)
include hP

theorem symAdj_conePlus_sq (A : B) :
    symAdj (conePlus P A) * symAdj (conePlus P A) = genV P A (star A) := by
  rw [symAdj_conePlus hPs]
  peirce_nf hP

theorem skewAdj_conePlus_sq (A : B) :
    skewAdj (conePlus P A) * skewAdj (conePlus P A) = -genV P A (star A) := by
  rw [skewAdj_conePlus hPs]
  peirce_nf hP

theorem skewAdj_mul_symAdj_conePlus (A : B) :
    skewAdj (conePlus P A) * symAdj (conePlus P A) = genSig P A (star A) := by
  rw [skewAdj_conePlus hPs, symAdj_conePlus hPs]
  peirce_nf hP

theorem gradingTwistedAdj_eq_genPhi (A : B) :
    gradingTwistedAdj P A = genPhi P A (star A) := by
  unfold gradingTwistedAdj
  rw [star_conePlus hPs]
  peirce_nf hP

theorem gradingTwistedAdj_eq_invS_mul_genJ (A : B) :
    gradingTwistedAdj P A = invS P * genJ P A (star A) := by
  unfold gradingTwistedAdj
  rw [star_conePlus hPs]
  peirce_nf hP

theorem gradingTwistedAdj_eq_neg_genJ_mul_invS (A : B) :
    gradingTwistedAdj P A = -(genJ P A (star A) * invS P) := by
  unfold gradingTwistedAdj
  rw [star_conePlus hPs]
  peirce_nf hP

theorem gradingTwistedAdj_sq (A : B) :
    gradingTwistedAdj P A * gradingTwistedAdj P A = genV P A (star A) := by
  rw [gradingTwistedAdj_eq_invS_mul_genJ hPs hP]
  peirce_nf hP

theorem anticomm_invS_gradingTwistedAdj (A : B) :
    anticomm (invS P) (gradingTwistedAdj P A) = 0 := by
  rw [gradingTwistedAdj_eq_invS_mul_genJ hPs hP]
  peirce_nf hP

theorem comm_gradingTwistedAdj_genV (A : B) :
    comm (gradingTwistedAdj P A) (genV P A (star A)) = 0 := by
  rw [gradingTwistedAdj_eq_invS_mul_genJ hPs hP]
  peirce_nf hP

end StarDecomposition

/-! ### 2. Three-idempotent strictly upper-triangular step operator and resolvent -/

section ThreeIdempotentResolvent

/-- Two-step strictly upper-triangular operator across `P₁`, `P₂`, and `third P₁ P₂ = 1 - P₁ - P₂`. -/
def twoStepUpper (P₁ P₂ A C : B) : B :=
  P₁ * A * P₂ + P₂ * C * third P₁ P₂

/-- Unipotent polynomial resolvent `1 + T + T * T` for a two-step upper operator `T`. -/
def twoStepResolvent (P₁ P₂ A C : B) : B :=
  1 + twoStepUpper P₁ P₂ A C + twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C

private theorem zero_mul_right {X Y : B} (h : X * Y = 0) (Z : B) : X * (Y * Z) = 0 := by
  rw [← mul_assoc, h, zero_mul]

variable {P₁ P₂ : B} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
  (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
include h1 h2 h12 h21

/-- The square of `twoStepUpper` isolates the two-hop path `P₁ A P₂ C (1 - P₁ - P₂)`. -/
theorem twoStepUpper_sq (A C : B) :
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C =
      P₁ * A * P₂ * C * third P₁ P₂ := by
  unfold twoStepUpper third
  simp only [add_mul, mul_add, sub_mul, mul_sub, mul_one, mul_assoc,
    P_mul_P' h1, P_mul_P' h2,
    zero_mul_right h12, zero_mul_right h21,
    mul_zero]
  abel

/-- Any three-hop product of `twoStepUpper` vanishes identically. -/
theorem twoStepUpper_mul_sq_zero (A C : B) :
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C = 0 := by
  rw [twoStepUpper_sq h1 h2 h12 h21]
  unfold twoStepUpper third
  simp only [mul_add, sub_mul, mul_sub, mul_one, mul_assoc,
    P_mul_P' h1, P_mul_P' h2,
    zero_mul_right h12, zero_mul_right h21,
    mul_zero]
  abel

/-- Cube nilpotency `T ^ 3 = 0` in power notation, feeding `RankedDAGResolvent.finiteGreen`. -/
theorem twoStepUpper_pow_three_zero (A C : B) :
    twoStepUpper P₁ P₂ A C ^ 3 = 0 := by
  have hpow : twoStepUpper P₁ P₂ A C ^ 3 =
      twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C := by
    noncomm_ring
  rw [hpow, twoStepUpper_mul_sq_zero h1 h2 h12 h21]

omit h1 h2 h12 h21 in
/-- `twoStepResolvent` coincides definitionally with the 3-term truncated Neumann series `finiteGreen T 3`. -/
theorem twoStepResolvent_eq_finiteGreen (A C : B) :
    twoStepResolvent P₁ P₂ A C = finiteGreen (twoStepUpper P₁ P₂ A C) 3 := by
  unfold twoStepResolvent finiteGreen
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  noncomm_ring

/-- Left inverse identity `(1 - T) * (1 + T + T²) = 1`. -/
theorem twoStepResolvent_left_inv (A C : B) :
    (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 := by
  rw [twoStepResolvent_eq_finiteGreen]
  exact finiteGreen_left_inverse (twoStepUpper P₁ P₂ A C) 3 (twoStepUpper_pow_three_zero h1 h2 h12 h21 A C)

/-- Right inverse identity `(1 + T + T²) * (1 - T) = 1`. -/
theorem twoStepResolvent_right_inv (A C : B) :
    twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 := by
  rw [twoStepResolvent_eq_finiteGreen]
  exact finiteGreen_right_inverse (twoStepUpper P₁ P₂ A C) 3 (twoStepUpper_pow_three_zero h1 h2 h12 h21 A C)

end ThreeIdempotentResolvent

/-! ### 3. Stage D₁₅ Master Synthesis across the Peirce Spine -/

section MasterSynthesis

/-- Bilateral compression by `1 - Q` (with `P * Q = Q * P = 0`) leaves the `11` block of `blockLower` invariant. -/
theorem idempotentCompression_blockLower_peirce11
    {P Q : B} (hP : P * P = P) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (F L D : B) :
    peirce11 P (idempotentCompression Q (blockLower P F L D)) = peirce11 P F := by
  rw [idempotentCompression_peirce11 hPQ hQP, blockLower_peirce11 hP]

variable [StarRing B]

/-- **Stage D₁₅ Master Synthesis Theorem:**
Unifies the symmetric/skew-adjoint star decomposition, the grading-twisted self-adjoint
corner operator and Laplacian, the three-idempotent step resolvent `(1 - T) G = G (1 - T) = 1`,
and the lower block-triangular compression invariance of the `11` Peirce corner. -/
theorem stage_D15_directed_flow_magnetic_resolvent_and_block_intervention
    {P P₁ P₂ Q : B}
    (hP : P * P = P) (hPs : star P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (A C D F L W : B) :
    -- 1. Symmetric and skew-adjoint decomposition:
    symAdj W + skewAdj W = (2 : ℤ) • W ∧
    star (symAdj W) = symAdj W ∧
    star (skewAdj W) = -skewAdj W ∧
    symAdj (conePlus P A) = genPhi P A (star A) ∧
    skewAdj (conePlus P A) = genJ P A (star A) ∧
    skewAdj (conePlus P A) * skewAdj (conePlus P A) = -genV P A (star A) ∧
    -- 2. Grading-twisted self-adjoint operator & Laplacian:
    gradingTwistedAdj P A = invS P * genJ P A (star A) ∧
    gradingTwistedAdj P A = -(genJ P A (star A) * invS P) ∧
    star (gradingTwistedAdj P A) = gradingTwistedAdj P A ∧
    (star D = D → star (gradingTwistedLaplacian P D A) = gradingTwistedLaplacian P D A) ∧
    gradingTwistedAdj P A * gradingTwistedAdj P A = genV P A (star A) ∧
    -- 3. Three-idempotent 2-hop composition, 3-hop vanishing, & two-sided resolvent:
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C =
      P₁ * A * P₂ * C * third P₁ P₂ ∧
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C = 0 ∧
    (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
    twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 ∧
    -- 4. Block-lower upper-right vanishing and `11`-block compression invariance:
    P * blockLower P F L D * (1 - P) = 0 ∧
    peirce11 P (idempotentCompression Q (blockLower P F L D)) = peirce11 P F :=
  ⟨symAdj_add_skewAdj W,
   star_symAdj W,
   star_skewAdj W,
   symAdj_conePlus hPs A,
   skewAdj_conePlus hPs A,
   skewAdj_conePlus_sq hPs hP A,
   gradingTwistedAdj_eq_invS_mul_genJ hPs hP A,
   gradingTwistedAdj_eq_neg_genJ_mul_invS hPs hP A,
   star_gradingTwistedAdj hPs A,
   fun hDs => star_gradingTwistedLaplacian hPs hDs A,
   gradingTwistedAdj_sq hPs hP A,
   twoStepUpper_sq h1 h2 h12 h21 A C,
   twoStepUpper_mul_sq_zero h1 h2 h12 h21 A C,
   twoStepResolvent_left_inv h1 h2 h12 h21 A C,
   twoStepResolvent_right_inv h1 h2 h12 h21 A C,
   blockLower_upper_right hP F L D,
   idempotentCompression_blockLower_peirce11 hP hPQ hQP F L D⟩

end MasterSynthesis

end InfoGeometry.OperatorAlgebra.PeirceSpine
