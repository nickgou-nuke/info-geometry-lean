/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11ChiralityTransport
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

/-!
# The global chirality action on the Clifford operator colimit

The existing descended chirality ring endomorphism preserves the real scalar
map and star. Its involution law therefore gives an actual algebra equivalence
of `Cl11TensorTowerLimit.Limit`. No coherent global chirality element is needed.

The existing intrinsic graded adjoint is then an endomorphism of the whole
colimit module. The stage inclusions intertwine this action with the finite
chirality actions. Jordan--Wigner creation and annihilation charges give
nonzero square-zero endomorphisms; their mutual anticommutator is zero because
the coefficient CAR anticommutator is the central identity. The explicit
readouts on the opposite charge are both the identity element.

These are algebraic operator statements on the actual direct limit. The
annihilation-charge differential is not identified here with a Hilbert-space
adjoint, and no completion or spectral estimate is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl11GradedOperatorAction

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

theorem stageChiralityConj_involutive (n : ℕ) :
    Function.Involutive (stageChiralityConj n) := by
  intro X
  change globalChirality n * (globalChirality n * X * globalChirality n) *
    globalChirality n = X
  calc
    _ = (globalChirality n * globalChirality n) * X *
        (globalChirality n * globalChirality n) := by noncomm_ring
    _ = X := by rw [globalChirality_sq]; simp

/-- Finite chirality conjugation fixes the real scalar algebra map. -/
theorem stageChiralityConj_algebraMap (n : ℕ) (r : ℝ) :
    stageChiralityConj n (algebraMap ℝ (Stage n) r) =
      algebraMap ℝ (Stage n) r := by
  change globalChirality n * algebraMap ℝ (Stage n) r * globalChirality n =
    algebraMap ℝ (Stage n) r
  rw [← Algebra.commutes r (globalChirality n), mul_assoc,
    globalChirality_sq, mul_one]

/-- The finite parity maps as native real algebra equivalences. -/
def stageChiralityAlgEquiv (n : ℕ) : Stage n ≃ₐ[ℝ] Stage n where
  toFun := stageChiralityConj n
  invFun := stageChiralityConj n
  left_inv := stageChiralityConj_involutive n
  right_inv := stageChiralityConj_involutive n
  map_mul' := (stageChiralityConj n).map_mul
  map_add' := (stageChiralityConj n).map_add
  commutes' := stageChiralityConj_algebraMap n

/-- The descended parity fixes scalars on the existing colimit carrier. -/
theorem limitChiralityConj_algebraMap (r : ℝ) :
    limitChiralityConj (algebraMap ℝ Limit r) = algebraMap ℝ Limit r := by
  change limitChiralityConj (realAlgebraMap r) = realAlgebraMap r
  rw [realAlgebraMap_stage 0, limitChiralityConj_ofStage]
  exact congrArg (ofStage 0) (stageChiralityConj_algebraMap 0 r)

/-- The global parity, with its existing involution law and proved scalar law. -/
def limitChiralityAlgEquiv : Limit ≃ₐ[ℝ] Limit where
  toFun := limitChiralityConj
  invFun := limitChiralityConj
  left_inv := limitChiralityConj_involutive
  right_inv := limitChiralityConj_involutive
  map_mul' := limitChiralityConj.map_mul
  map_add' := limitChiralityConj.map_add
  commutes' := limitChiralityConj_algebraMap

/-- Chirality conjugation respects the matrix star at every finite stage. -/
theorem stageChiralityConj_star (n : ℕ) (X : Stage n) :
    stageChiralityConj n (star X) = star (stageChiralityConj n X) := by
  have hΓ : star (globalChirality n) = globalChirality n := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      InfoGeometry.Canonical.Cl55WittCAR.globalChirality_transpose n
  change globalChirality n * star X * globalChirality n =
    star (globalChirality n * X * globalChirality n)
  simp only [star_mul, hΓ, mul_assoc]

/-- The actual descended parity commutes with the quotient star. -/
theorem limitChiralityConj_star (X : Limit) :
    limitChiralityConj (star X) = star (limitChiralityConj X) := by
  induction X using DirectLimit.induction with
  | _ n A =>
    change limitChiralityConj (star (ofStage n A)) =
      star (limitChiralityConj (ofStage n A))
    rw [← ofStage_star, limitChiralityConj_ofStage,
      limitChiralityConj_ofStage, ← ofStage_star]
    exact congrArg (ofStage n) (stageChiralityConj_star n A)

/-- The faithful stage maps intertwine the finite and global graded actions. -/
theorem gradedAdjoint_intertwines_ofStage (n : ℕ) (Q : Stage n) :
    (gradedAdjoint limitChiralityAlgEquiv (ofStage n Q)).comp
        (ofStageStarAlgHom n).toAlgHom.toLinearMap =
      (ofStageStarAlgHom n).toAlgHom.toLinearMap.comp
        (gradedAdjoint (stageChiralityAlgEquiv n) Q) := by
  ext X
  change ofStage n Q * ofStage n X -
      limitChiralityConj (ofStage n X) * ofStage n Q =
    ofStage n (Q * X - (globalChirality n * X * globalChirality n) * Q)
  rw [limitChiralityConj_ofStage]
  simp only [map_sub, map_mul]

/-- A creation charge differentiates its same-site annihilation charge to one. -/
theorem gradedAdjoint_jwCreation_apply_jwAnnihilation (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k))
      (ofStage n (jwAnnihilation n k)) = 1 := by
  change ofStage n (jwCreation n k) * ofStage n (jwAnnihilation n k) -
    limitChiralityConj (ofStage n (jwAnnihilation n k)) *
      ofStage n (jwCreation n k) = 1
  rw [limitChiralityConj_jwAnnihilation, neg_mul, sub_neg_eq_add]
  simpa only [map_add, map_mul, map_one] using
    congrArg (ofStage n) (InfoGeometry.Canonical.Cl55WittCAR.same_site_car n k)

/-- The reverse same-site graded readout is also the identity element. -/
theorem gradedAdjoint_jwAnnihilation_apply_jwCreation (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k))
      (ofStage n (jwCreation n k)) = 1 := by
  change ofStage n (jwAnnihilation n k) * ofStage n (jwCreation n k) -
    limitChiralityConj (ofStage n (jwCreation n k)) *
      ofStage n (jwAnnihilation n k) = 1
  rw [limitChiralityConj_jwCreation, neg_mul, sub_neg_eq_add]
  simpa only [map_add, map_mul, map_one, add_comm] using
    congrArg (ofStage n) (InfoGeometry.Canonical.Cl55WittCAR.same_site_car n k)

/-- Creation gives a square-zero endomorphism on all of the colimit module. -/
theorem gradedAdjoint_jwCreation_square (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k)) *
      gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k)) = 0 := by
  rw [gradedAdjoint_square limitChiralityAlgEquiv
    limitChiralityConj_involutive _ (limitChiralityConj_jwCreation n k)]
  have hsq : ofStage n (jwCreation n k) * ofStage n (jwCreation n k) = 0 :=
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.creation_sq n k)
  rw [hsq]
  ext X
  simp

/-- Annihilation gives a square-zero endomorphism on all of the colimit module. -/
theorem gradedAdjoint_jwAnnihilation_square (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k)) *
      gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k)) = 0 := by
  rw [gradedAdjoint_square limitChiralityAlgEquiv
    limitChiralityConj_involutive _ (limitChiralityConj_jwAnnihilation n k)]
  have hsq : ofStage n (jwAnnihilation n k) * ofStage n (jwAnnihilation n k) = 0 :=
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.annihilation_sq n k)
  rw [hsq]
  ext X
  simp

/-- The coefficient CAR identity becomes zero inner curvature for the two actions. -/
theorem gradedAdjoint_jw_same_site_anticommute (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k)) *
        gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k)) +
      gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k)) *
        gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k)) = 0 := by
  rw [gradedAdjoint_mixed limitChiralityAlgEquiv limitChiralityConj_involutive
    _ _ (limitChiralityConj_jwCreation n k) (limitChiralityConj_jwAnnihilation n k)]
  have hcar :
      ofStage n (jwCreation n k) * ofStage n (jwAnnihilation n k) +
        ofStage n (jwAnnihilation n k) * ofStage n (jwCreation n k) = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (ofStage n) (InfoGeometry.Canonical.Cl55WittCAR.same_site_car n k)
  rw [hcar]
  ext X
  simp

/-- The creation differential is nonzero, witnessed by its CAR readout. -/
theorem gradedAdjoint_jwCreation_ne_zero (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k)) ≠ 0 := by
  intro h
  have hzero : (1 : Limit) = 0 := by
    simpa only [gradedAdjoint_jwCreation_apply_jwAnnihilation,
      LinearMap.zero_apply] using
      congrArg (fun T : Module.End ℝ Limit => T (ofStage n (jwAnnihilation n k))) h
  have hstage : (1 : Stage n) = 0 :=
    ofStage_injective n (by simpa only [map_one, map_zero] using hzero)
  exact one_ne_zero hstage

/-- The annihilation differential is nonzero, witnessed by its CAR readout. -/
theorem gradedAdjoint_jwAnnihilation_ne_zero (n : ℕ) (k : Fin n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwAnnihilation n k)) ≠ 0 := by
  intro h
  have hzero : (1 : Limit) = 0 := by
    simpa only [gradedAdjoint_jwAnnihilation_apply_jwCreation,
      LinearMap.zero_apply] using
      congrArg (fun T : Module.End ℝ Limit => T (ofStage n (jwCreation n k))) h
  have hstage : (1 : Stage n) = 0 :=
    ofStage_injective n (by simpa only [map_one, map_zero] using hzero)
  exact one_ne_zero hstage

end InfoGeometry.Clifford.Cl11GradedOperatorAction
