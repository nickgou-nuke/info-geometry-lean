/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect

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

end InfoGeometry.OperatorAlgebra.PeirceSpine
