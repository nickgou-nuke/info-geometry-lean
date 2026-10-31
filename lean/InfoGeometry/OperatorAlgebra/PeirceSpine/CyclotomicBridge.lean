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

end InfoGeometry.OperatorAlgebra.PeirceSpine
