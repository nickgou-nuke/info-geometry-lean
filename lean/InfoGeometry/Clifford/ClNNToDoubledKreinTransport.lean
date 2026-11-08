/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge

/-!
# Finite-rank transport from algebraic `Cl(n,n)` to the real doubled Krein space

This owner transports the algebraic coordinate carrier and its full algebraic
dual to Euclidean coordinates.  Its Riesz equivalence is finite-rank and is
proved by the standard basis pairing; it is not an identification of an
infinite-dimensional algebraic dual with a Hilbert dual.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNToDoubledKreinTransport

open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein

variable (n : ℕ)

abbrev EucVector := EuclideanSpace ℝ (Fin n)

/-- The coordinate copy of `Fin n → ℝ` in the native `EuclideanSpace` API. -/
def toEuclidean : Vector n ≃ₗ[ℝ] EucVector n :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

/-- Finite-dimensional Riesz equivalence, transported from the coordinate
dual through the standard basis and the native Euclidean carrier. -/
def rieszEquiv : EucVector n ≃ₗ[ℝ] Module.Dual ℝ (EucVector n) :=
  (toEuclidean n).symm.trans <|
    (dualCoordinates n).symm.trans ((toEuclidean n).dualMap).symm

/-- The transported algebraic dual evaluates by the Euclidean inner product. -/
theorem rieszEquiv_apply_apply (x y : EucVector n) :
    rieszEquiv n x y = @inner ℝ (EucVector n) _ x y := by
  change (dualCoordinates n).symm ((toEuclidean n).symm x)
      ((toEuclidean n).symm y) = @inner ℝ (EucVector n) _ x y
  rw [← dualCoordinates_eval]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [toEuclidean, dotProduct, mul_comm]

/-- The coordinate algebraic dual, transported through the finite Euclidean
carrier, is linearly equivalent to that carrier. This is the inverse Riesz
direction, made explicit for the `Fin n → ℝ` dual used by `ClNN`. -/
def coordinateDualToEuclidean :
    Module.Dual ℝ (Vector n) ≃ₗ[ℝ] EucVector n :=
  ((toEuclidean n).dualMap).symm.trans (rieszEquiv n).symm

/-- The coordinate dual pairing is the Euclidean inner product after the
explicit dual-to-vector transport. -/
theorem coordinateDual_eval_eq_inner (x : Vector n)
    (φ : Module.Dual ℝ (Vector n)) :
    φ x = @inner ℝ (EucVector n) _ (toEuclidean n x)
      (coordinateDualToEuclidean n φ) := by
  let φE : Module.Dual ℝ (EucVector n) := ((toEuclidean n).dualMap).symm φ
  have hdual : φ x = φE (toEuclidean n x) := by
    simp [φE, LinearEquiv.dualMap_apply]
  have hriesz : rieszEquiv n (coordinateDualToEuclidean n φ) = φE := by
    simp [coordinateDualToEuclidean, φE]
  rw [hdual, ← hriesz]
  calc
    rieszEquiv n (coordinateDualToEuclidean n φ) (toEuclidean n x) =
        @inner ℝ (EucVector n) _ (coordinateDualToEuclidean n φ)
          (toEuclidean n x) :=
      rieszEquiv_apply_apply n (coordinateDualToEuclidean n φ)
        (toEuclidean n x)
    _ = @inner ℝ (EucVector n) _ (toEuclidean n x)
        (coordinateDualToEuclidean n φ) := real_inner_comm _ _

/-- Algebraic neutral phase space transported to the Euclidean phase-space
owner used by the doubled real Krein construction. -/
def toEuclideanPhase : Neutral n ≃ₗ[ℝ]
    PhaseSpaceCarrier (EucVector n) :=
  LinearEquiv.prodCongr (toEuclidean n) ((toEuclidean n).dualMap).symm

/-- The algebraic split form agrees exactly with the established doubled
Krein form after the native 45-degree realization. The factor `1/2` is the
repository's normalization in `canonicalNeutralFormUnscaled`. -/
theorem Qsplit_eq_doubledKrein_form (X : Neutral n) :
    TowerForm n (neutralToSplit n X) =
      (1 / 2 : ℝ) * hessian_indefinite_form
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n X))
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n X)) := by
  rcases X with ⟨x, φ⟩
  rw [Qsplit_neutralToSplit]
  rw [canonicalNeutralFormUnscaled_apply]
  change φ x = _
  calc
    φ x = canonicalNeutralFormUnscaled (E := EucVector n)
        (toEuclideanPhase n (x, φ)) := by
          simp [canonicalNeutralFormUnscaled_apply, toEuclideanPhase]
    _ = (1 / 2 : ℝ) * hessian_indefinite_form
          (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
            (toEuclideanPhase n (x, φ)))
          (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
            (toEuclideanPhase n (x, φ))) :=
        canonicalNeutralFormUnscaled_realizeToDoubledRho
          (E := EucVector n) (rieszEquiv n)
          (rieszEquiv_apply_apply n) (toEuclideanPhase n (x, φ))

/-- The primal/covector evaluation pairing is exactly the cross term of the
real doubled Krein bilinear form after the canonical finite-rank Riesz
transport. -/
theorem evaluation_eq_doubledKrein_cross
    (x : Vector n) (φ : Module.Dual ℝ (Vector n)) :
    φ x = hessian_indefinite_form
      (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
        (toEuclideanPhase n (x, 0)))
      (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
        (toEuclideanPhase n (0, φ))) := by
  calc
    φ x = canonicalNeutralBilin (E := EucVector n)
        (toEuclideanPhase n (x, 0)) (toEuclideanPhase n (0, φ)) := by
          simp [canonicalNeutralBilin_apply, toEuclideanPhase]
    _ = hessian_indefinite_form
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n (x, 0)))
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n (0, φ))) :=
      canonicalNeutralBilin_realizeToDoubledRho
        (E := EucVector n) (rieszEquiv n) (rieszEquiv_apply_apply n)
        (toEuclideanPhase n (x, 0)) (toEuclideanPhase n (0, φ))

end InfoGeometry.Clifford.ClNNToDoubledKreinTransport
