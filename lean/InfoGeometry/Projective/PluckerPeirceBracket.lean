/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset
import InfoGeometry.Projective.KleinQuadric
import Mathlib.Data.Matrix.Basis

/-!
# Ordered Peirce brackets and a Plücker coefficient realization

An orthogonal pair of idempotents in an associative ring determines the existing
complementary corner `P0_waist P1 P2 = 1 - P1 - P2`. Products of two sums of
the `(1,0)` and `(0,2)` Peirce blocks retain exactly the composable path through
that corner. Their commutator is its ordered antisymmetrization.

For matrices on `Fin 3`, the explicit map
`step r ρ = Matrix.single 0 1 r + Matrix.single 1 2 ρ` realizes this two-step
pattern. Its commutator coefficient is `r * σ - s * ρ`, with this multiplication
order valid even for a noncommutative coefficient ring.

For the existing `KleinQuadric.Plucker6` coordinates over a commutative ring,
the source's anonymous-index coordinate assignment is
`(r,s,h,σ,ρ,η) = (P.p03,P.p13,P.p23,-P.p12,-P.p02,P.p01)`.
The Klein equation gives the concrete matrix identity
`comm (step P.p03 (-P.p02)) (step P.p13 (-P.p12)) =
  Matrix.single 0 2 (P.p23 * P.p01)`, namely coefficient `h * η`.
This is a compatibility formula for the displayed coefficient map. It does not
identify arbitrary Peirce corners with six scalar Plücker coordinates.
-/

namespace InfoGeometry.Projective.PluckerPeirceBracket

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset

section Peirce

variable {B : Type*} [Ring B]

/-- Only the path from the first boundary through the complementary corner to
the second boundary survives in a product of two positive-step sums. -/
theorem peirce_two_step_product
    (P1 P2 r ρ s σ : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    (block10 P1 P2 r + block02 P1 P2 ρ) *
        (block10 P1 P2 s + block02 P1 P2 σ) =
      block12 P1 P2 (r * P0_waist P1 P2 * σ) := by
  let P0 := P0_waist P1 P2
  obtain ⟨h0, _h10, h01, h20, _h02, _hsum⟩ :=
    peirce_complement_triad P1 P2 h1 h2 h12 h21
  have hAC : (P1 * r * P0) * (P1 * s * P0) = 0 :=
    peirce_corner_mismatch_zero P1 P0 P1 r s P0 h01
  have hAD : (P1 * r * P0) * (P0 * σ * P2) = P1 * r * P0 * σ * P2 :=
    peirce_corner_compose P1 P0 r σ P2 h0
  have hBC : (P0 * ρ * P2) * (P1 * s * P0) = 0 :=
    peirce_corner_mismatch_zero P0 P2 P1 ρ s P0 h21
  have hBD : (P0 * ρ * P2) * (P0 * σ * P2) = 0 :=
    peirce_corner_mismatch_zero P0 P2 P0 ρ σ P2 h20
  change (P1 * r * P0 + P0 * ρ * P2) *
      (P1 * s * P0 + P0 * σ * P2) = P1 * (r * P0 * σ) * P2
  simp only [add_mul, mul_add, hAC, hAD, hBC, hBD, zero_add, add_zero]
  simp only [mul_assoc]

/-- The positive-step commutator is the ordered difference of the two
composable paths. The complementary projector remains between the inputs. -/
theorem peirce_two_step_commutator
    (P1 P2 r ρ s σ : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    comm (block10 P1 P2 r + block02 P1 P2 ρ)
        (block10 P1 P2 s + block02 P1 P2 σ) =
      block12 P1 P2
        (r * P0_waist P1 P2 * σ - s * P0_waist P1 P2 * ρ) := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  rw [peirce_two_step_product P1 P2 r ρ s σ h1 h2 h12 h21,
    peirce_two_step_product P1 P2 s σ r ρ h1 h2 h12 h21]
  simp only [block12, mul_sub, sub_mul]

end Peirce

section Matrix

variable {R : Type*} [Ring R]

/-- The explicit two-step upper-triangular matrix on `Fin 3`. -/
def step (r ρ : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.single 0 1 r + Matrix.single 1 2 ρ

/-- Matrix-unit multiplication contracts the unique matching middle index. -/
theorem step_mul (r ρ s σ : R) :
    step r ρ * step s σ = Matrix.single 0 2 (r * σ) := by
  simp [step, add_mul, mul_add, Matrix.single_mul_single_of_ne]

/-- The matrix commutator records the ordered antisymmetrized coefficient. -/
theorem step_commutator (r ρ s σ : R) :
    comm (step r ρ) (step s σ) = Matrix.single 0 2 (r * σ - s * ρ) := by
  rw [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, step_mul, step_mul]
  simp only [sub_eq_add_neg, Matrix.single_neg, ← Matrix.single_add]

end Matrix

section Klein

variable {R : Type*} [CommRing R]

/-- In the source's ray-coordinate convention, the Klein equation identifies
the commutator coefficient `r * σ - s * ρ` with `h * η`. -/
theorem step_commutator_of_klein
    (P : KleinQuadric.Plucker6 R) (hP : KleinQuadric.Plucker6.kleinQ P = 0) :
    comm (step P.p03 (-P.p02)) (step P.p13 (-P.p12)) =
      Matrix.single 0 2 (P.p23 * P.p01) := by
  rw [step_commutator]
  apply congrArg (Matrix.single (0 : Fin 3) (2 : Fin 3))
  calc
    P.p03 * (-P.p12) - P.p13 * (-P.p02) =
        P.p23 * P.p01 - KleinQuadric.Plucker6.kleinQ P := by
      simp only [KleinQuadric.Plucker6.kleinQ]
      ring
    _ = P.p23 * P.p01 := by rw [hP, sub_zero]

end Klein

end InfoGeometry.Projective.PluckerPeirceBracket
