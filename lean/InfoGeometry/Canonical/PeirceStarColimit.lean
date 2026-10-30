/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceStarFunctoriality
import InfoGeometry.OperatorAlgebra.SquareZeroModeActions
import InfoGeometry.Canonical.RealStarColimitUniversal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Peirce star geometry in the existing real matrix colimit

The original finite matrix corners enter the existing `Cl(1,1)` tensor-tower
colimit through `ofStage`. Star-opposite corners and their Gram expression
are identified using the actual star-preserving inclusions. Independent
opposite corners give three representative real linear endomorphism actions;
their coefficients remain products in the noncommutative colimit algebra.

The last branch follows weighted modes and Gram expressions through the
actual one-step refinement and the existing universal map. Finite-stage
semidefiniteness uses the ordinary real matrix star. No order on the limit,
analytic completion, or strict gap is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.PeirceStarColimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.Core.PeirceStarFunctoriality
open InfoGeometry.OperatorAlgebra.SquareZeroModeActions
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.RealStarColimitUniversal

/-- Every finite real-matrix Gram weight is positive semidefinite, without
a commutation, square-zero, invertibility, or diagonalization hypothesis. -/
theorem stage_gram_posSemidef (n : ℕ) (x : Stage n) :
    Matrix.PosSemidef (x * star x + star x * x) := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.posSemidef_self_mul_conjTranspose x).add
      (Matrix.posSemidef_conjTranspose_mul_self x)

/-- The finite reflected star is carried to the reflected star of the actual
colimit representatives. -/
theorem ofStage_reflected_star (n : ℕ) (p x : Stage n) :
    ofStage n (reflection p * star x * reflection p) =
      reflection (ofStage n p) * star (ofStage n x) * reflection (ofStage n p) := by
  exact map_reflected_star (ofStage n) (ofStage_star n) p x

/-- The adjoint of a finite forward corner is the image of the opposite
corner with adjointed coefficient. -/
theorem ofStage_star_opposite_corner {n : ℕ} {p : Stage n}
    (hp : IsSelfAdjoint p) (a : Stage n) :
    ofStage n (component01 p (star a)) = star (ofStage n (component10 p a)) := by
  rw [← star_component10 hp a, ofStage_star]

/-- Both independent opposite matrix corners remain square-zero in the
actual colimit. -/
theorem ofStage_corner_pair_sq_zero {n : ℕ} {p : Stage n}
    (hp : IsIdempotentElem p) (a b : Stage n) :
    ofStage n (component10 p a) * ofStage n (component10 p a) = 0 ∧
      ofStage n (component01 p b) * ofStage n (component01 p b) = 0 := by
  constructor
  · exact limit_square_zero
      (peirce10_mul_peirce10_eq_zero p hp.eq (component10_mem p a) (component10_mem p a))
  · exact limit_square_zero
      (peirce01_mul_peirce01_eq_zero p hp.eq (component01_mem p b) (component01_mem p b))

/-- Mapping the finite signed reflection pairing gives the Gram sum of the
same forward corner in the noncommutative colimit. -/
theorem ofStage_negative_reflection_pairing {n : ℕ} {p : Stage n}
    (hp : IsStarProjection p) (a : Stage n) :
    let u := ofStage n (component10 p a)
    let r := reflection (ofStage n p);
    -((r * star u * r) * u + u * (r * star u * r)) =
      u * star u + star u * u := by
  dsimp only
  calc
    _ = ofStage n
        (-((reflection p * star (component10 p a) * reflection p) * component10 p a +
          component10 p a * (reflection p * star (component10 p a) * reflection p))) :=
      (map_reflection_pairing (ofStage n) (ofStage_star n) p (component10 p a)).symm
    _ = ofStage n
        (component10 p a * star (component10 p a) +
          star (component10 p a) * component10 p a) :=
      congrArg (ofStage n) (negative_reflection_pairing hp a)
    _ = _ := map_gram (ofStage n) (ofStage_star n) (component10 p a)

/-- The negative square of the native real inner derivation is intertwined
on every finite-stage input, not only on the distinguished modes. -/
theorem ofStage_neg_ad_sq (n : ℕ) (a x : Stage n) :
    ofStage n ((-((LieAlgebra.ad ℝ (Stage n) a) ^ 2)) x) =
      (-((LieAlgebra.ad ℝ Limit (ofStage n a)) ^ 2)) (ofStage n x) := by
  simpa only [pow_two, Module.End.mul_apply, LinearMap.neg_apply,
    LieAlgebra.ad_apply] using map_neg_ad_sq (ofStage n) a x

/-- A representative difference-mode action retains the full operator weight
after passage from the finite corners to the colimit. -/
theorem ofStage_neg_ad_sum_sq_difference {n : ℕ} {p : Stage n}
    (hp : IsIdempotentElem p) (a b : Stage n) :
    let u := ofStage n (component10 p a)
    let v := ofStage n (component01 p b)
    (-((LieAlgebra.ad ℝ Limit (u + v)) ^ 2)) (u - v) =
      -(4 • ((u * v + v * u) * (u - v))) := by
  dsimp only
  exact neg_ad_sum_sq_difference (R := ℝ)
    (ofStage_corner_pair_sq_zero hp a b).1 (ofStage_corner_pair_sq_zero hp a b).2

/-- The corresponding sum-mode action is the native real adjoint square of
the difference of the two colimit corners. -/
theorem ofStage_ad_difference_sq_sum {n : ℕ} {p : Stage n}
    (hp : IsIdempotentElem p) (a b : Stage n) :
    let u := ofStage n (component10 p a)
    let v := ofStage n (component01 p b)
    ((LieAlgebra.ad ℝ Limit (u - v)) ^ 2) (u + v) =
      -(4 • ((u * v + v * u) * (u + v))) := by
  dsimp only
  exact ad_difference_sq_sum (R := ℝ)
    (ofStage_corner_pair_sq_zero hp a b).1 (ofStage_corner_pair_sq_zero hp a b).2

/-- The symmetric mixed operator acts on the native bracket with its ordered
noncommutative weight. -/
theorem ofStage_neg_ad_symmetric_bracket {n : ℕ} {p : Stage n}
    (hp : IsIdempotentElem p) (a b : Stage n) :
    let u := ofStage n (component10 p a)
    let v := ofStage n (component01 p b)
    (-(LieAlgebra.ad ℝ Limit u * LieAlgebra.ad ℝ Limit v +
      LieAlgebra.ad ℝ Limit v * LieAlgebra.ad ℝ Limit u)) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  dsimp only
  exact neg_ad_symmetric_bracket (R := ℝ)
    (ofStage_corner_pair_sq_zero hp a b).1 (ofStage_corner_pair_sq_zero hp a b).2

/-- Refining both inputs by the actual tensor-identity map does not change
their weighted difference mode in the colimit. -/
theorem weighted_mode_refinement (n : ℕ) (u v : Stage n) :
    ofStage (n + 1)
        ((stageEmbed n u * stageEmbed n v + stageEmbed n v * stageEmbed n u) *
          (stageEmbed n u - stageEmbed n v)) =
      ofStage n ((u * v + v * u) * (u - v)) := by
  simpa only [map_mul, map_add, map_sub] using
    ofStage_apply_bond n ((u * v + v * u) * (u - v))

/-- The Gram expression is independent of one-step representative refinement
because the actual bonding map preserves star. -/
theorem gram_refinement (n : ℕ) (u : Stage n) :
    ofStage (n + 1)
        (stageEmbed n u * star (stageEmbed n u) +
          star (stageEmbed n u) * stageEmbed n u) =
      ofStage n (u * star u + star u * u) := by
  simpa only [map_add, map_mul, stageEmbed_star] using
    ofStage_apply_bond n (u * star u + star u * u)

section UniversalReadback

variable {B : Type} [Ring B]

/-- The existing universal map reads the refined weighted mode as the
same ordered polynomial in its finite-stage cone leg. -/
theorem directLimitLift_refined_weighted_mode
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f) (n : ℕ) (u v : Stage n) :
    directLimitLift stageBond f hcone
        (ofStage (n + 1)
          ((stageEmbed n u * stageEmbed n v + stageEmbed n v * stageEmbed n u) *
            (stageEmbed n u - stageEmbed n v))) =
      (f n u * f n v + f n v * f n u) * (f n u - f n v) := by
  rw [weighted_mode_refinement]
  change f n ((u * v + v * u) * (u - v)) = _
  simp only [map_mul, map_add, map_sub]

variable [StarRing B]

/-- The refined finite Gram expression is read through the proven
star-preserving universal map, with the exact stagewise star hypothesis. -/
theorem directLimitLift_refined_gram
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f)
    (hstar : ∀ n (x : Stage n), f n (star x) = star (f n x))
    (n : ℕ) (u : Stage n) :
    directLimitLift stageBond f hcone
        (ofStage (n + 1)
          (stageEmbed n u * star (stageEmbed n u) +
            star (stageEmbed n u) * stageEmbed n u)) =
      f n u * star (f n u) + star (f n u) * f n u := by
  rw [gram_refinement]
  calc
    _ = directLimitLift stageBond f hcone
        (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u) := by
      congr 1
      simp only [map_add, map_mul, ofStage_star]
    _ = directLimitLift stageBond f hcone (ofStage n u) *
          star (directLimitLift stageBond f hcone (ofStage n u)) +
        star (directLimitLift stageBond f hcone (ofStage n u)) *
          directLimitLift stageBond f hcone (ofStage n u) :=
      directLimitLift_gram f hcone hstar (ofStage n u)
    _ = _ := rfl

end UniversalReadback

end InfoGeometry.Canonical.PeirceStarColimit
