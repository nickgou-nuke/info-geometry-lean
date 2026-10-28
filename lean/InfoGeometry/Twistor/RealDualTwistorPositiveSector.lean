/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistorKreinBridge

/-!
# Positive real sectors in the genuine dual twistor carrier

The algebraic dual lift is self-adjoint for the neutral evaluation pairing.
It is not an algebra homomorphism on arbitrary noncommuting operators.
The positive graph is a separate, explicitly constructed sector: the
configuration projector is not identified with a Krein-sheet projector.
The constructed finite-dimensional real inner-product duality supplies the
normalization, and self-adjoint configuration operators preserve this graph.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealDualTwistorPositiveSector

open InfoGeometry.Krein
open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Twistor.RealDualTwistorKreinBridge

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Apply an operator to the primal leg and its actual dual to the covector leg. -/
def dualLift (A : Module.End ℝ V) : Module.End ℝ (Carrier V) :=
  A.prodMap A.dualMap

@[simp] theorem dualLift_apply (A : Module.End ℝ V) (p : Carrier V) :
    dualLift A p = (A p.1, p.2.comp A) := rfl

/-- Neutral adjointness does not require a positive inner product on `V`. -/
theorem dualLift_neutral_selfAdjoint (A : Module.End ℝ V) (p q : Carrier V) :
    neutralForm (dualLift A p) q = neutralForm p (dualLift A q) := rfl

/-- A single operator's square is respected despite reversal of general dual products. -/
theorem dualLift_mul_self (A : Module.End ℝ V) :
    dualLift A * dualLift A = dualLift (A * A) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · rfl
  · ext v
    rfl

theorem dualLift_idempotent (A : Module.End ℝ V) (hA : A * A = A) :
    dualLift A * dualLift A = dualLift A := by
  rw [dualLift_mul_self, hA]

theorem dualLift_commute_of_commute (A B : Module.End ℝ V)
    (hAB : A * B = B * A) : dualLift A * dualLift B = dualLift B * dualLift A := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · exact congrArg (fun T : Module.End ℝ V => T p.1) hAB
  · ext v
    change p.2 (B (A v)) = p.2 (A (B v))
    exact congrArg p.2 (congrArg (fun T : Module.End ℝ V => T v) hAB).symm

theorem dualLift_para (A : Module.End ℝ V) :
    dualLift A * para = para * dualLift A := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · rfl
  · ext v
    rfl

end Algebraic

section PositiveGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The positive graph is normalized to preserve the original inner product exactly. -/
def positiveEmbedding : E →ₗ[ℝ] Carrier E :=
  ((1 / 2 : ℝ) • (LinearMap.id : Module.End ℝ E)).prod
    (realInnerDuality (E := E)).toLinearMap

omit [CompleteSpace E] in
@[simp] theorem positiveEmbedding_apply (v : E) :
    positiveEmbedding v = ((1 / 2 : ℝ) • v, realInnerDuality v) := rfl

omit [CompleteSpace E] in
theorem positiveEmbedding_pairing (v w : E) :
    neutralForm (positiveEmbedding v) (positiveEmbedding w) = inner ℝ v w := by
  simp only [positiveEmbedding_apply, neutralForm_apply, realInnerDuality_apply,
    real_inner_smul_right]
  rw [real_inner_comm w v]
  ring

omit [CompleteSpace E] in
theorem positiveEmbedding_injective : Function.Injective (positiveEmbedding (E := E)) := by
  intro v w h
  apply (realInnerDuality (E := E)).injective
  exact congrArg Prod.snd h

omit [CompleteSpace E] in
theorem lightconeDoubled_positiveEmbedding (v : E) :
    lightconeDoubled realInnerDuality (positiveEmbedding v) = to_doubled v 0 := by
  rw [positiveEmbedding_apply, lightconeDoubled_apply]
  simp only [LinearEquiv.symm_apply_apply]
  apply DoubledSpace.ext <;> simp only [fst_to_doubled, snd_to_doubled] <;> module

omit [CompleteSpace E] in
/-- An explicit formula for the already-owned transported fundamental symmetry. -/
theorem fundamental_apply (p : Carrier E) :
    dualFundamentalSymmetry realInnerDuality p =
      ((1 / 2 : ℝ) • realInnerDuality.symm p.2, (2 : ℝ) • realInnerDuality p.1) := by
  change (lightconeDoubled realInnerDuality).symm
    (spectral_epsilon (lightconeDoubled realInnerDuality p)) = _
  rw [lightconeDoubled_apply, spectral_epsilon_to_doubled,
    lightconeDoubled_symm_apply]
  simp only [fst_to_doubled, snd_to_doubled]
  apply Prod.ext <;>
    simp only [map_add, map_sub, map_neg, map_smul, LinearEquiv.apply_symm_apply] <;>
    module

omit [CompleteSpace E] in
theorem fundamental_positiveEmbedding (v : E) :
    dualFundamentalSymmetry realInnerDuality (positiveEmbedding v) =
      positiveEmbedding v := by
  apply (lightconeDoubled realInnerDuality).injective
  simp only [dualFundamentalSymmetry_intertwines, lightconeDoubled_positiveEmbedding,
    spectral_epsilon_to_doubled, neg_zero]

theorem fundamental_neutral_selfAdjoint (p q : Carrier E) :
    neutralForm (dualFundamentalSymmetry realInnerDuality p) q =
      neutralForm p (dualFundamentalSymmetry realInnerDuality q) := by
  rw [neutralForm_symm (dualFundamentalSymmetry realInnerDuality p) q,
    neutralForm_fundamental_eq_positive, neutralForm_fundamental_eq_positive]
  change inner ℝ (lightconeDoubled realInnerDuality q)
      (lightconeDoubled realInnerDuality p) =
    inner ℝ (lightconeDoubled realInnerDuality p)
      (lightconeDoubled realInnerDuality q)
  exact real_inner_comm _ _

/-- The positive graph projector, kept distinct from configuration projections. -/
def positiveProjector : Module.End ℝ (Carrier E) :=
  (1 / 2 : ℝ) • (1 + dualFundamentalSymmetry realInnerDuality)

omit [CompleteSpace E] in
@[simp] theorem positiveProjector_apply (p : Carrier E) :
    positiveProjector p =
      (1 / 2 : ℝ) • (p + dualFundamentalSymmetry realInnerDuality p) := rfl

omit [CompleteSpace E] in
theorem positiveProjector_eq_embedding (p : Carrier E) :
    positiveProjector p = positiveEmbedding
      (p.1 + (1 / 2 : ℝ) • realInnerDuality.symm p.2) := by
  rw [positiveProjector_apply, fundamental_apply, positiveEmbedding_apply]
  apply Prod.ext
  · rfl
  · change (1 / 2 : ℝ) • (p.2 + (2 : ℝ) • realInnerDuality p.1) =
      realInnerDuality (p.1 + (1 / 2 : ℝ) • realInnerDuality.symm p.2)
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply]
    module

omit [CompleteSpace E] in
@[simp] theorem positiveProjector_positiveEmbedding (v : E) :
    positiveProjector (positiveEmbedding v) = positiveEmbedding v := by
  rw [positiveProjector_apply, fundamental_positiveEmbedding]
  module

omit [CompleteSpace E] in
theorem positiveProjector_idempotent :
    positiveProjector (E := E) * positiveProjector = positiveProjector := by
  apply LinearMap.ext
  intro p
  change positiveProjector (positiveProjector p) = positiveProjector p
  rw [positiveProjector_eq_embedding p, positiveProjector_positiveEmbedding]

theorem positiveProjector_neutral_selfAdjoint (p q : Carrier E) :
    neutralForm (positiveProjector p) q = neutralForm p (positiveProjector q) := by
  rw [positiveProjector_apply, positiveProjector_apply]
  simp only [map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [fundamental_neutral_selfAdjoint]

omit [CompleteSpace E] in
theorem positiveEmbedding_graph (v : E) :
    (positiveEmbedding v).2 = (2 : ℝ) • realInnerDuality (positiveEmbedding v).1 := by
  simp [positiveEmbedding_apply, map_smul, smul_smul]

omit [CompleteSpace E] in
theorem positiveProjector_fixed_iff_graph (p : Carrier E) :
    positiveProjector p = p ↔ p.2 = (2 : ℝ) • realInnerDuality p.1 := by
  constructor
  · intro hp
    rw [← hp, positiveProjector_eq_embedding]
    exact positiveEmbedding_graph _
  · intro hp
    have he : p = positiveEmbedding ((2 : ℝ) • p.1) := by
      apply Prod.ext
      · simp [positiveEmbedding_apply, smul_smul]
      · simpa [positiveEmbedding_apply, map_smul] using hp
    rw [he, positiveProjector_positiveEmbedding]

omit [CompleteSpace E] in
theorem positiveEmbedding_self_pos (v : E) (hv : v ≠ 0) :
    0 < neutralForm (positiveEmbedding v) (positiveEmbedding v) := by
  rw [positiveEmbedding_pairing]
  exact real_inner_self_pos.mpr hv

omit [CompleteSpace E] in
/-- Unit positive-graph states do not satisfy the independent ambitwistor-null constraint. -/
theorem positiveEmbedding_unit_not_incident (v : E) (hv : inner ℝ v v = 1) :
    ¬ Incident (positiveEmbedding v) := by
  intro h
  have hz := (incident_iff_neutral_self (positiveEmbedding v)).mp h
  rw [positiveEmbedding_pairing, hv] at hz
  norm_num at hz

end PositiveGraph

section SelfAdjointOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem realInnerDuality_dualMap (A : E →L[ℝ] E) (hA : A.adjoint = A) (v : E) :
    A.toLinearMap.dualMap (realInnerDuality v) = realInnerDuality (A v) := by
  ext w
  change inner ℝ v (A w) = inner ℝ (A v) w
  rw [← ContinuousLinearMap.adjoint_inner_left, hA]

theorem realInnerDuality_symm_dualMap (A : E →L[ℝ] E) (hA : A.adjoint = A)
    (φ : Module.Dual ℝ E) :
    realInnerDuality.symm (A.toLinearMap.dualMap φ) = A (realInnerDuality.symm φ) := by
  apply (realInnerDuality (E := E)).injective
  rw [LinearEquiv.apply_symm_apply, ← realInnerDuality_dualMap A hA,
    LinearEquiv.apply_symm_apply]

theorem dualLift_positiveEmbedding (A : E →L[ℝ] E) (hA : A.adjoint = A) (v : E) :
    dualLift A.toLinearMap (positiveEmbedding v) = positiveEmbedding (A v) := by
  rw [dualLift_apply, positiveEmbedding_apply, positiveEmbedding_apply]
  apply Prod.ext
  · exact map_smul A (1 / 2 : ℝ) v
  · exact realInnerDuality_dualMap A hA v

theorem dualLift_fundamental_commute (A : E →L[ℝ] E) (hA : A.adjoint = A) :
    dualLift A.toLinearMap * dualFundamentalSymmetry realInnerDuality =
      dualFundamentalSymmetry realInnerDuality * dualLift A.toLinearMap := by
  apply LinearMap.ext
  intro p
  change dualLift A.toLinearMap (dualFundamentalSymmetry realInnerDuality p) =
    dualFundamentalSymmetry realInnerDuality (dualLift A.toLinearMap p)
  simp only [dualLift_apply, fundamental_apply]
  apply Prod.ext
  · change A ((1 / 2 : ℝ) • realInnerDuality.symm p.2) =
      (1 / 2 : ℝ) • realInnerDuality.symm (A.toLinearMap.dualMap p.2)
    rw [map_smul, realInnerDuality_symm_dualMap A hA]
  · change A.toLinearMap.dualMap ((2 : ℝ) • realInnerDuality p.1) =
      (2 : ℝ) • realInnerDuality (A p.1)
    rw [map_smul, realInnerDuality_dualMap A hA]

theorem dualLift_positiveProjector_commute (A : E →L[ℝ] E) (hA : A.adjoint = A) :
    dualLift A.toLinearMap * positiveProjector =
      positiveProjector * dualLift A.toLinearMap := by
  apply LinearMap.ext
  intro p
  change dualLift A.toLinearMap (positiveProjector p) =
    positiveProjector (dualLift A.toLinearMap p)
  rw [positiveProjector_apply, positiveProjector_apply, map_smul, map_add]
  have h := congrArg (fun T : Module.End ℝ (Carrier E) => T p)
    (dualLift_fundamental_commute A hA)
  simpa only [Module.End.mul_apply] using
    congrArg (fun q : Carrier E => (1 / 2 : ℝ) • (dualLift A.toLinearMap p + q)) h

theorem positiveEmbedding_transition (A : E →L[ℝ] E) (hA : A.adjoint = A)
    (v w : E) :
    neutralForm (positiveEmbedding v) (dualLift A.toLinearMap (positiveEmbedding w)) =
      inner ℝ v (A w) := by
  rw [dualLift_positiveEmbedding A hA, positiveEmbedding_pairing]

theorem positiveEmbedding_eigen_iff (A : E →L[ℝ] E) (hA : A.adjoint = A)
    (v : E) (energy : ℝ) :
    dualLift A.toLinearMap (positiveEmbedding v) = energy • positiveEmbedding v ↔
      A v = energy • v := by
  rw [dualLift_positiveEmbedding A hA]
  constructor
  · intro h
    apply positiveEmbedding_injective
    rw [map_smul]
    exact h
  · intro h
    rw [h, map_smul]

end SelfAdjointOperators

end InfoGeometry.Twistor.RealDualTwistorPositiveSector
