/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized

/-!
# Cyclotomic polynomial evaluations on the Peirce generators

These are finite polynomial identities in the associative operator ring. The
cyclotomic labels do not assert spectral, analytic zeta, or number-theoretic
interpretations.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The polynomial `X² + X + 1`, evaluated without commuting the ambient ring. -/
def cyclotomicThree (X : B) : B := X * X + X + 1

/-- The polynomial `X² - X + 1`, evaluated without commuting the ambient ring. -/
def cyclotomicSix (X : B) : B := X * X - X + 1

/-- Universal ordered polynomial identities for the third and sixth
cyclotomic polynomials in one element of an associative ring. The factors are
kept in the displayed order; no commutativity of the ambient ring is assumed.
-/
theorem cyclotomic_three_six_polynomial_identities (X : B) :
    cyclotomicSix X = X * X - X + 1 ∧
    cyclotomicThree X = X * X + X + 1 ∧
    cyclotomicThree X - cyclotomicSix X = (2 : ℤ) • X ∧
    (X - 1) * cyclotomicThree X = X * X * X - 1 ∧
    (X + 1) * cyclotomicSix X = X * X * X + 1 ∧
    cyclotomicThree X * cyclotomicSix X = cyclotomicThree (X * X) ∧
    (X - 1) * (X + 1) * cyclotomicThree X * cyclotomicSix X =
      (X * X * X) * (X * X * X) - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cyclotomicThree, cyclotomicSix] <;> noncomm_ring

/-- The complementary chiral transfer element `(1 - P) - J`. -/
def peirceTransferJComplement (P A C : B) : B := (1 - P) - genJ P A C

/-- The signed chiral transfer element `-(P + J)`. -/
def cubeRootOp (P A C : B) : B := -(P + genJ P A C)

/-- The complementary signed chiral transfer element `-(1 - P) + J`. -/
def cubeRootOpConj (P A C : B) : B := -(1 - P) + genJ P A C

/-- The primary odd generator `Φ` viewed as the zeroth reflection channel in A59. -/
def s3Refl0 (P A C : B) : B := genPhi P A C

/-- The first rotated odd reflection channel `cubeRootOp * Φ`. -/
def s3Refl1 (P A C : B) : B := cubeRootOp P A C * genPhi P A C

/-- The second rotated odd reflection channel `cubeRootOpConj * Φ`. -/
def s3Refl2 (P A C : B) : B := cubeRootOpConj P A C * genPhi P A C

variable {P : B} (hP : P * P = P)
include hP

/-- The two cyclotomic evaluations at `J` are the ordered Cayley--Weyl pair. -/
theorem weyl_cyclotomic_evaluations (A C : B) :
    cyclotomicThree (genJ P A C) = weylJ P A C ∧
    cyclotomicSix (genJ P A C) = weylJInv P A C ∧
    weylJ P A C * weylJInv P A C = cyclotomicSix (genV P A C) := by
  simp only [cyclotomicThree, cyclotomicSix, weylJ, weylJInv]
  peirce_nf hP
  simp

/-- The second Cayley--Weyl polynomial is a genuine two-sided inverse of the
first exactly on the idempotent-defect-zero locus of `V`. -/
theorem weyl_pair_inverse_iff_metric_idempotent (A C : B) :
    (weylJ P A C * weylJInv P A C = 1 ∧
      weylJInv P A C * weylJ P A C = 1) ↔
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genV P A C) = 0 := by
  have h₁ := (archetype_A16_cayley_weyl_steinberg_reflection hP A C).1
  have h₂ := (archetype_A16_cayley_weyl_steinberg_reflection hP A C).2.1
  have hp : weylJ P A C * weylJInv P A C - 1 =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (genV P A C) := by
    simpa [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect] using h₁
  have hq : weylJInv P A C * weylJ P A C - 1 =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (genV P A C) := by
    simpa [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect] using h₂
  constructor
  · rintro ⟨hleft, hright⟩
    rw [← hp, hleft]
    simp
  · intro hd
    constructor
    · exact sub_eq_zero.mp (by rw [hp, hd])
    · exact sub_eq_zero.mp (by rw [hq, hd])

/-- Cyclotomic factors at `Φ` multiply to the third polynomial at `V`. -/
theorem phi_cyclotomic_norm (A C : B) :
    cyclotomicThree (genPhi P A C) * cyclotomicSix (genPhi P A C) =
      genV P A C * genV P A C + genV P A C + 1 := by
  simp only [cyclotomicThree, cyclotomicSix]
  peirce_nf hP

/-- The degree-six polynomial of the Peirce transfer elements is the pair of
complementary Euler factors. -/
theorem transfer_cyclotomic_evaluations (A C : B) :
    cyclotomicSix (peirceTransfer P A C) = 1 + genV P A C ∧
    cyclotomicSix (peirceTransferJ P A C) = 1 - genV P A C := by
  simp only [cyclotomicSix, peirceTransfer, peirceTransferJ]
  constructor <;> peirce_nf hP

/-- Applying the defect again to the two transfer elements yields the two
opposite defect polynomials of the Peirce metric. -/
theorem transfer_second_defect_iterates (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (peirceTransfer P A C)) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (genV P A C) ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (peirceTransferJ P A C)) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefectBar (genV P A C) := by
  simp only [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect,
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefectBar,
    peirceTransfer, peirceTransferJ]
  constructor <;> peirce_nf hP

/-- Off-shell cyclotomic polynomial evaluations, cube factorizations, and
discriminant squares for the Peirce transfer and chiral transfer elements
(`A58`). These are polynomial identities in `B`; they equal roots of unity only
under an additional unit-shell hypothesis `genV P A C = 1`. -/
theorem archetype_A58_operator_cyclotomic_roots_and_discriminants (A C : B) :
    peirceTransferJ P A C + peirceTransferJComplement P A C = 1 ∧
    peirceTransferJ P A C * peirceTransferJComplement P A C = genV P A C ∧
    peirceTransferJComplement P A C * peirceTransferJ P A C = genV P A C ∧
    cyclotomicSix (peirceTransferJ P A C) = 1 - genV P A C ∧
    cyclotomicSix (peirceTransferJComplement P A C) = 1 - genV P A C ∧
    cubeRootOp P A C + cubeRootOpConj P A C = -1 ∧
    cubeRootOp P A C * cubeRootOpConj P A C = genV P A C ∧
    cyclotomicThree (cubeRootOp P A C) = 1 - genV P A C ∧
    cyclotomicThree (cubeRootOpConj P A C) = 1 - genV P A C ∧
    peirceTransferJ P A C * peirceTransferJ P A C * peirceTransferJ P A C + 1 =
      (peirceTransferJ P A C + 1) * (1 - genV P A C) ∧
    cubeRootOp P A C * cubeRootOp P A C * cubeRootOp P A C - 1 =
      (cubeRootOp P A C - 1) * (1 - genV P A C) ∧
    ((2 : ℤ) • peirceTransfer P A C - 1) * ((2 : ℤ) • peirceTransfer P A C - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    ((2 : ℤ) • peirceTransferJ P A C - 1) * ((2 : ℤ) • peirceTransferJ P A C - 1) =
      1 - (4 : ℤ) • genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirceTransfer, peirceTransferJ, peirceTransferJComplement,
      cubeRootOp, cubeRootOpConj, cyclotomicThree, cyclotomicSix];
     peirce_nf hP)

/-- Off-shell cyclic, braiding, and reflection-channel identities for
`cubeRootOp`, `cubeRootOpConj`, and `s3Refl0, s3Refl1, s3Refl2` (`A59`).
Off-shell, the products carry factors of `genV P A C` and `genV P A C * genV P A C`;
they specialize to `S₃` group relations on the unit shell `genV P A C = 1`. -/
theorem archetype_A59_s3_operator_cyclotomic_braiding_and_reflections (A C : B) :
    1 + cubeRootOp P A C + cubeRootOpConj P A C = 0 ∧
    cubeRootOp P A C * cubeRootOpConj P A C = genV P A C ∧
    cubeRootOpConj P A C * cubeRootOp P A C = genV P A C ∧
    cubeRootOp P A C * cubeRootOp P A C - cubeRootOpConj P A C =
      1 - genV P A C ∧
    cubeRootOpConj P A C * cubeRootOpConj P A C - cubeRootOp P A C =
      1 - genV P A C ∧
    genPhi P A C * cubeRootOp P A C =
      cubeRootOpConj P A C * genPhi P A C ∧
    genPhi P A C * cubeRootOpConj P A C =
      cubeRootOp P A C * genPhi P A C ∧
    s3Refl0 P A C + s3Refl1 P A C + s3Refl2 P A C = 0 ∧
    s3Refl1 P A C * s3Refl1 P A C = genV P A C * genV P A C ∧
    s3Refl2 P A C * s3Refl2 P A C = genV P A C * genV P A C ∧
    s3Refl0 P A C * s3Refl1 P A C = genV P A C * cubeRootOpConj P A C ∧
    s3Refl1 P A C * s3Refl0 P A C = genV P A C * cubeRootOp P A C ∧
    s3Refl0 P A C * s3Refl2 P A C = genV P A C * cubeRootOp P A C ∧
    s3Refl2 P A C * s3Refl0 P A C = genV P A C * cubeRootOpConj P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cubeRootOp, cubeRootOpConj, s3Refl0, s3Refl1, s3Refl2];
     peirce_nf hP)

/-- Centrality of `genV`, Tetraktys decomposition, and homogenized-channel
evaluations on the `S₃` reflection channels (`A60`, with the corrected `-2 Σ`
and `-16 V² Σ` signs on `s3Refl1 - s3Refl2`). -/
theorem archetype_A60_s3_klein_four_decomposition_and_tomography (A C : B) :
    comm (genV P A C) (cubeRootOp P A C) = 0 ∧
    comm (genV P A C) (cubeRootOpConj P A C) = 0 ∧
    comm (genV P A C) (s3Refl1 P A C) = 0 ∧
    comm (genV P A C) (s3Refl2 P A C) = 0 ∧
    cubeRootOp P A C - cubeRootOpConj P A C =
      -invS P - (2 : ℤ) • genJ P A C ∧
    s3Refl1 P A C + s3Refl2 P A C = -genPhi P A C ∧
    s3Refl1 P A C - s3Refl2 P A C =
      -genJ P A C - (2 : ℤ) • genSig P A C ∧
    hProjV P A C (s3Refl1 P A C) = 0 ∧
    hProjV P A C (s3Refl2 P A C) = 0 ∧
    hProjPhi P A C (s3Refl1 P A C + s3Refl2 P A C) =
      -((8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    hProjJ P A C (s3Refl1 P A C - s3Refl2 P A C) =
      -((8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) ∧
    hProjSig P A C (s3Refl1 P A C - s3Refl2 P A C) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genSig P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cubeRootOp, cubeRootOpConj, s3Refl1, s3Refl2,
      hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig];
     peirce_nf hP)

/-- Explicit Peirce-cone/chirality decomposition, squares (`V` vs `V²`), and
anticommutator (`V - 2 • V²`) of the three `S₃` reflection channels (`M₅`). -/
theorem s3Refl_components_squares_and_anticomm (A C : B) :
    s3Refl1 P A C = -conePlus P A - genSig P A C ∧
    s3Refl2 P A C = -coneMinus P C + genSig P A C ∧
    s3Refl0 P A C * s3Refl0 P A C = genV P A C ∧
    s3Refl1 P A C * s3Refl1 P A C = genV P A C * genV P A C ∧
    s3Refl2 P A C * s3Refl2 P A C = genV P A C * genV P A C ∧
    anticomm (s3Refl1 P A C) (s3Refl2 P A C) =
      genV P A C - (2 : ℤ) • (genV P A C * genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [s3Refl0, s3Refl1, s3Refl2, cubeRootOp, cubeRootOpConj];
     peirce_nf hP)

/-! ### Stage M₅: scaled chiral array identities -/

/-- Threefold scaled homogenized channel maps. -/
def scaledHProjV3   (P A C X : B) : B := (3 : ℤ) • hProjV P A C X
def scaledHProjPhi3 (P A C X : B) : B := (3 : ℤ) • hProjPhi P A C X
def scaledHProjJ3   (P A C X : B) : B := (3 : ℤ) • hProjJ P A C X
def scaledHProjSig3 (P A C X : B) : B := (3 : ℤ) • hProjSig P A C X

/-- Six explicitly defined chiral column operators. -/
def chiralArrayColumnWeight : Fin 6 → B → B → B → B → B
  | ⟨0, _⟩, P, _, _, Y => P * Y
  | ⟨1, _⟩, P, _, _, Y => (1 - P) * Y
  | ⟨2, _⟩, P, A, C, Y => -cubeRootOp P A C * (P * Y)
  | ⟨3, _⟩, P, A, C, Y => -cubeRootOpConj P A C * ((1 - P) * Y)
  | ⟨4, _⟩, P, A, C, Y => (P - genJ P A C * P) * Y
  | ⟨5, _⟩, P, A, C, Y => (1 - P + genJ P A C * (1 - P)) * Y

/-- Entry `(r, c)` of the finite chiral array. -/
def chiralArrayEntry (r : Fin 4) (c : Fin 6) (P A C X : B) : B :=
  chiralArrayColumnWeight c P A C (homogenizedChannel P A C r X)

/-- Sum across the six columns of row `r`. -/
def chiralArrayRowSum (r : Fin 4) (P A C X : B) : B :=
  chiralArrayEntry r 0 P A C X + chiralArrayEntry r 1 P A C X +
  chiralArrayEntry r 2 P A C X + chiralArrayEntry r 3 P A C X +
  chiralArrayEntry r 4 P A C X + chiralArrayEntry r 5 P A C X

/-- **Stage M₅ (`stage_M5_scaled_chiral_array_identities`)**:
1. The four row sums over the six defined chiral columns equal the threefold-scaled
   homogenized channels `scaledHProjV3`, `scaledHProjPhi3`, `scaledHProjJ3`, and `scaledHProjSig3`.
2. Alternating column differences recover the grading involution `invS P` and chiral current
   `2 • genJ` on every row `r : Fin 4`.
3. The grand sum of the array entries equals `24 • (V² * X)`.
4. The row-zero response to the displayed sum of operators equals
   `24 • (V² * V)`. This is an operator identity; no code or error-correction
   structure is asserted. -/
theorem stage_M5_scaled_chiral_array_identities
    (A C X : B) (r : Fin 4) :
    chiralArrayRowSum 0 P A C X = scaledHProjV3 P A C X ∧
    chiralArrayRowSum 1 P A C X = scaledHProjPhi3 P A C X ∧
    chiralArrayRowSum 2 P A C X = scaledHProjJ3 P A C X ∧
    chiralArrayRowSum 3 P A C X = scaledHProjSig3 P A C X ∧
    chiralArrayEntry r 0 P A C X - chiralArrayEntry r 1 P A C X =
      invS P * homogenizedChannel P A C r X ∧
    (chiralArrayEntry r 2 P A C X - chiralArrayEntry r 4 P A C X) +
      (chiralArrayEntry r 5 P A C X - chiralArrayEntry r 3 P A C X) =
      (2 : ℤ) • (genJ P A C * homogenizedChannel P A C r X) ∧
    chiralArrayRowSum 0 P A C X + chiralArrayRowSum 1 P A C X +
      chiralArrayRowSum 2 P A C X + chiralArrayRowSum 3 P A C X =
      (24 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    chiralArrayRowSum 0 P A C
      (genV P A C + conjPlus P A (genPhi P A C) +
       conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C) * genV P A C) := by
  have hColSum : ∀ Y : B,
      chiralArrayColumnWeight 0 P A C Y + chiralArrayColumnWeight 1 P A C Y +
      chiralArrayColumnWeight 2 P A C Y + chiralArrayColumnWeight 3 P A C Y +
      chiralArrayColumnWeight 4 P A C Y + chiralArrayColumnWeight 5 P A C Y =
      (3 : ℤ) • Y := by
    intro Y
    simp only [chiralArrayColumnWeight, cubeRootOp, cubeRootOpConj]
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hColSum (hProjV P A C X)
  · exact hColSum (hProjPhi P A C X)
  · exact hColSum (hProjJ P A C X)
  · exact hColSum (hProjSig P A C X)
  · simp only [chiralArrayEntry, chiralArrayColumnWeight, invS, sub_mul]
  · simp only [chiralArrayEntry, chiralArrayColumnWeight, cubeRootOp, cubeRootOpConj]
    peirce_nf hP
  · rw [show chiralArrayRowSum 0 P A C X = (3 : ℤ) • hProjV P A C X from
          hColSum (hProjV P A C X),
        show chiralArrayRowSum 1 P A C X = (3 : ℤ) • hProjPhi P A C X from
          hColSum (hProjPhi P A C X),
        show chiralArrayRowSum 2 P A C X = (3 : ℤ) • hProjJ P A C X from
          hColSum (hProjJ P A C X),
        show chiralArrayRowSum 3 P A C X = (3 : ℤ) • hProjSig P A C X from
          hColSum (hProjSig P A C X)]
    have h8 := (archetype_A13_homogenized_projectors hP A C X).1
    calc
      (3 : ℤ) • hProjV P A C X + (3 : ℤ) • hProjPhi P A C X +
          (3 : ℤ) • hProjJ P A C X + (3 : ℤ) • hProjSig P A C X =
        (3 : ℤ) • (hProjV P A C X + hProjPhi P A C X +
          hProjJ P A C X + hProjSig P A C X) := by abel
      _ = (3 : ℤ) • ((8 : ℤ) • ((genV P A C * genV P A C) * X)) := by rw [h8]
      _ = (24 : ℤ) • ((genV P A C * genV P A C) * X) := by rw [smul_smul]; norm_num
  · rw [show chiralArrayRowSum 0 P A C
          (genV P A C + conjPlus P A (genPhi P A C) +
           conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) =
        (3 : ℤ) • hProjV P A C
          (genV P A C + conjPlus P A (genPhi P A C) +
           conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) from
        hColSum _]
    simp only [hProjV, derivSqPhi, derivSqJ, derivSqSig, conjPlus, conjMinus,
      s3Refl1, s3Refl2, cubeRootOp, cubeRootOpConj]
    peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
