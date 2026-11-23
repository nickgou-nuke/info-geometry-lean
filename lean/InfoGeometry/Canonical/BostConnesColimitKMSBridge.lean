/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.StarSubalgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Inductive-Limit KMS Bridge (`Cl11TensorTowerLimit` -> `BostConnesKMS`)

This module defines the higher-grade `Type`-valued bridge structures connecting
the algebraic inductive limit `InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit`
to a completed normed `⋆`-algebra, a continuous GNS Hilbert-space `⋆`-representation,
and modular/KMS time-evolution data (`CliffordTowerCompletion`,
`CliffordTowerGNSRepresentation`, `CliffordTowerModularKMSData`, and
`CliffordTowerKMSBridgeSystem`).

It provides:
1. Universal lift theorems from `Cl11TensorTowerLimit.Limit` into any
   `CliffordTowerCompletion` and `CliffordTowerGNSRepresentation`, plus Cauchy--Schwarz,
   isometry of modular conjugation `J`, centralizer traciality, and vector symmetry.
2. A constructive infinite-dimensional trace GNS witness (`traceKMSBridgeModel`)
   built from `Cl11TensorTower.normalizedTrace` on `UniformSpace.Completion TracePreHilbert`.
3. Conditional Bost--Connes KMS projection bridge theorems deriving the `n^{-β}`
   diagonal weights, off-diagonal vanishing, and `KMSProjectionState` normalization
   at `Re ζ(β)` for `1 < β`.
4. Explicit R5 separation theorems showing noncommutativity of `Limit` and that
   any `1 < β` Bost--Connes KMS shift requires `σ_imag ≠ AlgHom.id`.
-/

open scoped BigOperators InnerProductSpace Matrix Kronecker

noncomputable section

namespace InfoGeometry.Canonical.BostConnesColimitKMSBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.BostConnesKMS

/-! ## 1. Higher-grade bridge structures and derived operator theorems -/

/-- Topological/normed `⋆`-algebra completion of the `Cl(1,1)` inductive-limit tower. -/
structure CliffordTowerCompletion where
  Carrier : Type
  normedRing : NormedRing Carrier
  starRing : StarRing Carrier
  normedAlgebra : NormedAlgebra ℝ Carrier
  completeSpace : CompleteSpace Carrier
  continuousStar : ContinuousStar Carrier
  stageMap : ∀ n : ℕ, Stage n →+* Carrier
  stage_compat : ∀ (n : ℕ) (X : Stage n), stageMap (n + 1) (stageBond n X) = stageMap n X
  stage_star : ∀ (n : ℕ) (X : Stage n), stageMap n (star X) = star (stageMap n X)
  stage_algebraMap : ∀ (n : ℕ) (r : ℝ),
    stageMap n (algebraMap ℝ (Stage n) r) = algebraMap ℝ Carrier r

attribute [instance] CliffordTowerCompletion.normedRing
attribute [instance] CliffordTowerCompletion.starRing
attribute [instance] CliffordTowerCompletion.normedAlgebra
attribute [instance] CliffordTowerCompletion.completeSpace
attribute [instance] CliffordTowerCompletion.continuousStar

namespace CliffordTowerCompletion

/-- Universal ring homomorphism from `Cl11TensorTowerLimit.Limit` into a completion. -/
def limitHom (C : CliffordTowerCompletion) : Limit →+* C.Carrier :=
  directLimitLift stageBond C.stageMap C.stage_compat

@[simp]
theorem limitHom_ofStage (C : CliffordTowerCompletion) (n : ℕ) (X : Stage n) :
    C.limitHom (ofStage n X) = C.stageMap n X := by
  exact directLimitLift_of stageBond C.stageMap C.stage_compat n X

@[simp]
theorem limitHom_star (C : CliffordTowerCompletion) (x : Limit) :
    C.limitHom (star x) = star (C.limitHom x) := by
  induction x using DirectLimit.induction with
  | _ n X =>
      change C.limitHom (ofStage n (star X)) = star (C.limitHom (ofStage n X))
      rw [limitHom_ofStage, limitHom_ofStage, C.stage_star]

@[simp]
theorem limitHom_realAlgebraMap (C : CliffordTowerCompletion) (r : ℝ) :
    C.limitHom (realAlgebraMap r) = algebraMap ℝ C.Carrier r := by
  rw [realAlgebraMap_stage 0 r, limitHom_ofStage, C.stage_algebraMap]

@[simp]
theorem limitHom_smul (C : CliffordTowerCompletion) (r : ℝ) (x : Limit) :
    C.limitHom (r • x) = r • C.limitHom x := by
  have hsmul : r • x = realAlgebraMap r * x := Algebra.smul_def r x
  rw [hsmul, map_mul, limitHom_realAlgebraMap, ← Algebra.smul_def]

end CliffordTowerCompletion

/-- Continuous Hilbert-space `⋆`-representation with unit vacuum vector for a tower completion. -/
structure CliffordTowerGNSRepresentation (C : CliffordTowerCompletion) where
  Hilbert : Type
  normedGroup : NormedAddCommGroup Hilbert
  innerProduct : InnerProductSpace ℝ Hilbert
  completeHilbert : CompleteSpace Hilbert
  rep : C.Carrier →+* (Hilbert →L[ℝ] Hilbert)
  rep_continuous : Continuous rep
  rep_star : ∀ a : C.Carrier, rep (star a) = ContinuousLinearMap.adjoint (rep a)
  rep_smul : ∀ (r : ℝ) (a : C.Carrier), rep (r • a) = r • rep a
  vacuum : Hilbert
  vacuum_norm : ‖vacuum‖ = 1

attribute [instance] CliffordTowerGNSRepresentation.normedGroup
attribute [instance] CliffordTowerGNSRepresentation.innerProduct
attribute [instance] CliffordTowerGNSRepresentation.completeHilbert

namespace CliffordTowerGNSRepresentation

/-- Continuous vector state `a ↦ ⟪Ω, rep(a) Ω⟫_ℝ` on the completed tower. -/
def stateCLM {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C) :
    C.Carrier →L[ℝ] ℝ where
  toFun a := ⟪R.vacuum, R.rep a R.vacuum⟫_ℝ
  map_add' a b := by
    simp [map_add, inner_add_right]
  map_smul' r a := by
    simp [R.rep_smul, inner_smul_right]
  cont := by
    exact Continuous.inner continuous_const (R.rep_continuous.clm_apply continuous_const)

@[simp]
theorem stateCLM_apply {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C)
    (a : C.Carrier) :
    R.stateCLM a = ⟪R.vacuum, R.rep a R.vacuum⟫_ℝ :=
  rfl

/-- Pullback of the continuous GNS state to the algebraic direct limit `Limit`. -/
def limitState {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C) :
    Limit →ₗ[ℝ] ℝ where
  toFun x := R.stateCLM (C.limitHom x)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp [C.limitHom_smul, map_smul]

@[simp]
theorem limitState_apply {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C)
    (x : Limit) :
    R.limitState x = R.stateCLM (C.limitHom x) :=
  rfl

theorem stateCLM_one {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C) :
    R.stateCLM 1 = 1 := by
  rw [stateCLM_apply, map_one, one_apply_eq_self, real_inner_self_eq_norm_sq,
    R.vacuum_norm, one_pow]

theorem stateCLM_star_mul_self_nonneg {C : CliffordTowerCompletion}
    (R : CliffordTowerGNSRepresentation C) (a : C.Carrier) :
    0 ≤ R.stateCLM (star a * a) := by
  rw [stateCLM_apply, map_mul, R.rep_star]
  change 0 ≤ ⟪R.vacuum, (ContinuousLinearMap.adjoint (R.rep a)) (R.rep a R.vacuum)⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_nonneg

theorem stateCLM_star {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C)
    (a : C.Carrier) :
    R.stateCLM (star a) = R.stateCLM a := by
  rw [stateCLM_apply, stateCLM_apply, R.rep_star, ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm]

theorem stateCLM_cauchy_schwarz {C : CliffordTowerCompletion}
    (R : CliffordTowerGNSRepresentation C) (a b : C.Carrier) :
    (R.stateCLM (star a * b)) ^ 2 ≤ R.stateCLM (star a * a) * R.stateCLM (star b * b) := by
  rw [stateCLM_apply, stateCLM_apply, stateCLM_apply, map_mul, map_mul, map_mul,
    R.rep_star, R.rep_star]
  change (⟪R.vacuum, (ContinuousLinearMap.adjoint (R.rep a)) (R.rep b R.vacuum)⟫_ℝ) ^ 2 ≤
    ⟪R.vacuum, (ContinuousLinearMap.adjoint (R.rep a)) (R.rep a R.vacuum)⟫_ℝ *
      ⟪R.vacuum, (ContinuousLinearMap.adjoint (R.rep b)) (R.rep b R.vacuum)⟫_ℝ
  simp only [ContinuousLinearMap.adjoint_inner_right]
  have hcs := real_inner_mul_inner_self_le (R.rep a R.vacuum) (R.rep b R.vacuum)
  simpa [sq, real_inner_self_eq_norm_sq] using hcs

theorem limitState_one {C : CliffordTowerCompletion} (R : CliffordTowerGNSRepresentation C) :
    R.limitState 1 = 1 := by
  rw [limitState_apply, map_one, R.stateCLM_one]

theorem limitState_star_mul_self_nonneg {C : CliffordTowerCompletion}
    (R : CliffordTowerGNSRepresentation C) (x : Limit) :
    0 ≤ R.limitState (star x * x) := by
  rw [limitState_apply, map_mul, C.limitHom_star]
  exact R.stateCLM_star_mul_self_nonneg (C.limitHom x)

theorem limitState_stage_readout {C : CliffordTowerCompletion}
    (R : CliffordTowerGNSRepresentation C) (n : ℕ) (X : Stage n) :
    R.limitState (ofStage n X) = R.stateCLM (C.stageMap n X) := by
  rw [limitState_apply, C.limitHom_ofStage]

theorem limitState_stage_compat {C : CliffordTowerCompletion}
    (R : CliffordTowerGNSRepresentation C) (n : ℕ) (X : Stage n) :
    R.stateCLM (C.stageMap (n + 1) (stageBond n X)) = R.stateCLM (C.stageMap n X) := by
  rw [C.stage_compat]

end CliffordTowerGNSRepresentation

/-- Time-evolution, Tomita modular conjugation, and imaginary-time KMS shift data. -/
structure CliffordTowerModularKMSData (C : CliffordTowerCompletion)
    (R : CliffordTowerGNSRepresentation C) where
  σ : ℝ → (C.Carrier →L[ℝ] C.Carrier)
  σ_zero : ∀ a : C.Carrier, σ 0 a = a
  σ_add : ∀ (s t : ℝ) (a : C.Carrier), σ (s + t) a = σ s (σ t a)
  σ_one : ∀ t : ℝ, σ t 1 = 1
  σ_mul : ∀ (t : ℝ) (a b : C.Carrier), σ t (a * b) = σ t a * σ t b
  σ_star : ∀ (t : ℝ) (a : C.Carrier), σ t (star a) = star (σ t a)
  σ_state_invariant : ∀ (t : ℝ) (a : C.Carrier), R.stateCLM (σ t a) = R.stateCLM a
  J : R.Hilbert →L[ℝ] R.Hilbert
  J_sq : J.comp J = ContinuousLinearMap.id ℝ R.Hilbert
  J_symmetric : ∀ ξ η : R.Hilbert, ⟪J ξ, η⟫_ℝ = ⟪ξ, J η⟫_ℝ
  J_vacuum : J R.vacuum = R.vacuum
  J_commutant : ∀ a b : C.Carrier,
    (R.rep a).comp (J.comp ((R.rep b).comp J)) =
      (J.comp ((R.rep b).comp J)).comp (R.rep a)
  σ_imag : C.Carrier →ₐ[ℝ] C.Carrier
  kms_boundary : ∀ a b : C.Carrier, R.stateCLM (a * b) = R.stateCLM (b * σ_imag a)

namespace CliffordTowerModularKMSData

theorem J_isometry {C : CliffordTowerCompletion} {R : CliffordTowerGNSRepresentation C}
    (M : CliffordTowerModularKMSData C R) (ξ η : R.Hilbert) :
    ⟪M.J ξ, M.J η⟫_ℝ = ⟪ξ, η⟫_ℝ := by
  rw [M.J_symmetric]
  have hcomp : M.J (M.J η) = η := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : R.Hilbert →L[ℝ] R.Hilbert => f η) M.J_sq
  rw [hcomp]

theorem J_norm {C : CliffordTowerCompletion} {R : CliffordTowerGNSRepresentation C}
    (M : CliffordTowerModularKMSData C R) (ξ : R.Hilbert) :
    ‖M.J ξ‖ = ‖ξ‖ := by
  have hsq : ‖M.J ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact M.J_isometry ξ ξ
  nlinarith [norm_nonneg (M.J ξ), norm_nonneg ξ]

theorem σ_neg_comp {C : CliffordTowerCompletion} {R : CliffordTowerGNSRepresentation C}
    (M : CliffordTowerModularKMSData C R) (t : ℝ) :
    (M.σ (-t)).comp (M.σ t) = ContinuousLinearMap.id ℝ C.Carrier := by
  ext a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [← M.σ_add (-t) t a, neg_add_cancel, M.σ_zero]

theorem sigmaImag_state_invariant {C : CliffordTowerCompletion}
    {R : CliffordTowerGNSRepresentation C} (M : CliffordTowerModularKMSData C R)
    (a : C.Carrier) :
    R.stateCLM (M.σ_imag a) = R.stateCLM a := by
  have h := M.kms_boundary a 1
  simpa using h.symm

theorem centralizer_tracial {C : CliffordTowerCompletion}
    {R : CliffordTowerGNSRepresentation C} (M : CliffordTowerModularKMSData C R)
    {a : C.Carrier} (b : C.Carrier) (ha : M.σ_imag a = a) :
    R.stateCLM (a * b) = R.stateCLM (b * a) := by
  rw [M.kms_boundary a b, ha]

theorem kms_boundary_on_limit {C : CliffordTowerCompletion}
    {R : CliffordTowerGNSRepresentation C} (M : CliffordTowerModularKMSData C R)
    (x y : Limit) :
    R.limitState (x * y) = R.stateCLM (C.limitHom y * M.σ_imag (C.limitHom x)) := by
  rw [R.limitState_apply, map_mul, M.kms_boundary]

theorem modular_conjugation_vector_symmetry {C : CliffordTowerCompletion}
    {R : CliffordTowerGNSRepresentation C} (M : CliffordTowerModularKMSData C R)
    (a : C.Carrier) :
    ⟪R.vacuum, (M.J.comp ((R.rep a).comp M.J)) R.vacuum⟫_ℝ = R.stateCLM a := by
  simp only [ContinuousLinearMap.comp_apply, M.J_vacuum, R.stateCLM_apply]
  rw [← M.J_symmetric, M.J_vacuum]

end CliffordTowerModularKMSData

/-- Full inductive-limit KMS bridge system packaging completion, GNS representation, and modular data. -/
structure CliffordTowerKMSBridgeSystem where
  completion : CliffordTowerCompletion
  gns : CliffordTowerGNSRepresentation completion
  modular : CliffordTowerModularKMSData completion gns

namespace CliffordTowerKMSBridgeSystem

/-- Convenience projection for the limit state of a bridge system. -/
def limitState (Sys : CliffordTowerKMSBridgeSystem) : Limit →ₗ[ℝ] ℝ :=
  Sys.gns.limitState

/-- Convenience projection for the completion state of a bridge system. -/
def stateCLM (Sys : CliffordTowerKMSBridgeSystem) : Sys.completion.Carrier →L[ℝ] ℝ :=
  Sys.gns.stateCLM

end CliffordTowerKMSBridgeSystem

/-! ## 2. Constructive infinite-dimensional trace GNS witness -/

section TraceWitness

set_option synthInstance.maxHeartbeats 80000
set_option warn.classDefReducibility false

private theorem limit_smul_ofStage (r : ℝ) (n : ℕ) (A : Stage n) :
    r • ofStage n A = ofStage n (r • A) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  change realAlgebraMap r * ofStage n A = ofStage n (algebraMap ℝ (Stage n) r * A)
  rw [realAlgebraMap_stage n r, ← ofStage_mul]

private theorem limit_star_smul (r : ℝ) (x : Limit) : star (r • x) = r • star x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change star (r • ofStage n A) = r • star (ofStage n A)
      rw [limit_smul_ofStage, ← ofStage_star, ← ofStage_star, limit_smul_ofStage,
        star_smul, star_trivial]

private theorem normalizedTrace_one (n : ℕ) : normalizedTrace n 1 = 1 := by
  unfold normalizedTrace
  have htr : Matrix.trace (1 : Stage n) = (2 : ℝ) ^ n := by
    simp [Matrix.trace, TowerMatrix.idx_card_pow_two]
  rw [htr, div_self (pow_ne_zero n (by norm_num))]

private theorem normalizedTrace_star (n : ℕ) (A : Stage n) :
    normalizedTrace n (star A) = normalizedTrace n A := by
  unfold normalizedTrace
  have hstar : star A = Aᵀ := by
    ext i j
    simp [Matrix.star_apply]
  rw [hstar, Matrix.trace_transpose]

private theorem normalizedTrace_mul_comm (n : ℕ) (A B : Stage n) :
    normalizedTrace n (A * B) = normalizedTrace n (B * A) := by
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm]

private theorem normalizedTrace_star_mul_self_nonneg (n : ℕ) (A : Stage n) :
    0 ≤ normalizedTrace n (star A * A) := by
  unfold normalizedTrace
  refine div_nonneg ?_ (by positivity)
  have hdiag : Matrix.trace (star A * A) =
      ∑ i : TowerMatrix.Idx n, ∑ j : TowerMatrix.Idx n, (A j i) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, star_trivial, sq]
  rw [hdiag]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem normalizedTrace_star_mul_self_eq_zero_iff (n : ℕ) (A : Stage n) :
    normalizedTrace n (star A * A) = 0 ↔ A = 0 := by
  constructor
  · intro h
    unfold normalizedTrace at h
    have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have htr : Matrix.trace (star A * A) = 0 := (div_eq_zero_iff.mp h).resolve_right hpow
    have hdiag : Matrix.trace (star A * A) =
        ∑ i : TowerMatrix.Idx n, ∑ j : TowerMatrix.Idx n, (A j i) ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, star_trivial, sq]
    rw [hdiag] at htr
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _] at htr
    ext j i
    have hi := htr i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hi
    exact sq_eq_zero_iff.mp (hi j (Finset.mem_univ j))
  · intro h
    subst h
    simp [normalizedTrace]

private theorem normalizedTrace_bondMap (m n : ℕ) (h : m ≤ n) (A : Stage m) :
    normalizedTrace n (bondMap stageBond m n h A) = normalizedTrace m A := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht => normalizedTrace t (bondMap stageBond m t ht A) = normalizedTrace m A)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro t hmt ih
    rw [bondMap_succ stageBond m t hmt, RingHom.comp_apply]
    change normalizedTrace (t + 1) (matStageEmbed t (bondMap stageBond m t hmt A)) =
      normalizedTrace m A
    rw [normalizedTrace_matStageEmbed, ih]

/-- Normalized tracial linear functional on `Cl11TensorTowerLimit.Limit`. -/
def limitTrace : Limit →ₗ[ℝ] ℝ where
  toFun := DirectLimit.lift (fun m n h => bondMap stageBond m n h)
    (fun n => normalizedTrace n)
    (fun m n h A => (normalizedTrace_bondMap m n h A).symm)
  map_add' x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [DirectLimit.add_def, DirectLimit.lift_def, DirectLimit.lift_def, DirectLimit.lift_def]
        simp [normalizedTrace, Matrix.trace_add, add_div]
  map_smul' r x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change DirectLimit.lift _ _ _ (r • ofStage n A) =
          r * DirectLimit.lift _ _ _ (ofStage n A)
        rw [limit_smul_ofStage]
        change normalizedTrace n (r • A) = r * normalizedTrace n A
        simp [normalizedTrace, Matrix.trace_smul, mul_div_assoc]

@[simp]
theorem limitTrace_ofStage (n : ℕ) (A : Stage n) :
    limitTrace (ofStage n A) = normalizedTrace n A :=
  rfl

theorem limitTrace_one : limitTrace 1 = 1 := by
  rw [← ofStage_one 0, limitTrace_ofStage, normalizedTrace_one]

theorem limitTrace_star (x : Limit) : limitTrace (star x) = limitTrace x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change limitTrace (ofStage n (star A)) = limitTrace (ofStage n A)
      rw [limitTrace_ofStage, limitTrace_ofStage, normalizedTrace_star]

theorem limitTrace_mul_comm (x y : Limit) : limitTrace (x * y) = limitTrace (y * x) := by
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change limitTrace (ofStage n (A * B)) = limitTrace (ofStage n (B * A))
      rw [limitTrace_ofStage, limitTrace_ofStage, normalizedTrace_mul_comm]

theorem limitTrace_star_mul_self_nonneg (x : Limit) : 0 ≤ limitTrace (star x * x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change 0 ≤ limitTrace (star (ofStage n A) * ofStage n A)
      rw [← ofStage_star, ← ofStage_mul, limitTrace_ofStage]
      exact normalizedTrace_star_mul_self_nonneg n A

theorem limitTrace_star_mul_self_eq_zero_iff (x : Limit) :
    limitTrace (star x * x) = 0 ↔ x = 0 := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change limitTrace (star (ofStage n A) * ofStage n A) = 0 ↔ ofStage n A = 0
      rw [← ofStage_star, ← ofStage_mul, limitTrace_ofStage,
        normalizedTrace_star_mul_self_eq_zero_iff,
        ← directLimitOf_eq_zero_iff_of_injective stageBond matStageEmbed_injective]
      rfl

/-- Pre-Hilbert wrapper around `Cl11TensorTowerLimit.Limit` for GNS completion. -/
structure TracePreHilbert where
  val : Limit

instance : Inhabited TracePreHilbert := ⟨⟨0⟩⟩
instance : Zero TracePreHilbert := ⟨⟨0⟩⟩
instance : Add TracePreHilbert := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Neg TracePreHilbert := ⟨fun x => ⟨-x.val⟩⟩
instance : SMul ℝ TracePreHilbert := ⟨fun r x => ⟨r • x.val⟩⟩

@[ext]
theorem TracePreHilbert.ext {x y : TracePreHilbert} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp at h; subst h; rfl

instance : AddCommGroup TracePreHilbert where
  add_assoc a b c := by ext; exact add_assoc _ _ _
  zero_add a := by ext; exact zero_add _
  add_zero a := by ext; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext; exact neg_add_cancel _
  add_comm a b := by ext; exact add_comm _ _

instance : Module ℝ TracePreHilbert where
  one_smul a := by ext; exact one_smul _ _
  mul_smul r s a := by ext; exact mul_smul _ _ _
  smul_zero r := by ext; exact smul_zero _
  smul_add r a b := by ext; exact smul_add _ _ _
  add_smul r s a := by ext; exact add_smul _ _ _
  zero_smul a := by ext; exact zero_smul _ _

noncomputable instance tracePreHilbertCore : InnerProductSpace.Core ℝ TracePreHilbert where
  inner x y := limitTrace (star x.val * y.val)
  conj_inner_symm x y := by
    change limitTrace (star y.val * x.val) = limitTrace (star x.val * y.val)
    rw [← limitTrace_star (star y.val * x.val), star_mul, star_star]
  re_inner_nonneg x := by
    simpa using limitTrace_star_mul_self_nonneg x.val
  add_left x y z := by
    change limitTrace (star (x.val + y.val) * z.val) =
      limitTrace (star x.val * z.val) + limitTrace (star y.val * z.val)
    rw [star_add, add_mul, map_add]
  smul_left x y r := by
    change limitTrace (star (r • x.val) * y.val) = r * limitTrace (star x.val * y.val)
    rw [limit_star_smul, smul_mul_assoc, map_smul, smul_eq_mul]
  definite x hx := by
    ext
    exact (limitTrace_star_mul_self_eq_zero_iff x.val).mp hx

noncomputable instance tracePreHilbertNormedAddCommGroup : NormedAddCommGroup TracePreHilbert :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance tracePreHilbertInnerProductSpace : InnerProductSpace ℝ TracePreHilbert :=
  InnerProductSpace.ofCore tracePreHilbertCore.toCore

@[simp]
private theorem tracePreHilbert_inner_eq (x y : TracePreHilbert) :
    ⟪x, y⟫_ℝ = limitTrace (star x.val * y.val) :=
  rfl

/-- Concrete infinite-dimensional GNS Hilbert space completing `Cl11TensorTowerLimit.Limit`. -/
abbrev TraceGNS : Type := UniformSpace.Completion TracePreHilbert

private noncomputable instance traceGNS_normedAddCommGroup : NormedAddCommGroup TraceGNS :=
  UniformSpace.Completion.instNormedAddCommGroup TracePreHilbert

private noncomputable instance traceGNS_innerProductSpace : InnerProductSpace ℝ TraceGNS :=
  UniformSpace.Completion.innerProductSpace

private noncomputable instance traceGNS_completeSpace : CompleteSpace TraceGNS :=
  UniformSpace.Completion.completeSpace TracePreHilbert

private noncomputable instance traceOp_normedRing : NormedRing (TraceGNS →L[ℝ] TraceGNS) :=
  ContinuousLinearMap.toNormedRing

private noncomputable instance traceOp_isTopologicalRing :
    IsTopologicalRing (TraceGNS →L[ℝ] TraceGNS) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

private noncomputable instance traceOp_continuousStar :
    ContinuousStar (TraceGNS →L[ℝ] TraceGNS) :=
  NormedStarGroup.to_continuousStar

private def IsDiagUnitLe (t : ℕ) (M : Stage t) : Prop :=
  (∀ i j : TowerMatrix.Idx t, i ≠ j → M i j = 0) ∧
    (∀ i : TowerMatrix.Idx t, 0 ≤ M i i ∧ M i i ≤ 1)

private theorem isDiagUnitLe_single (n : ℕ) (q : TowerMatrix.Idx n) :
    IsDiagUnitLe n (Matrix.single q q (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [Matrix.single_apply]
    split_ifs with h
    · exact absurd (h.1.symm.trans h.2) hij
    · rfl
  · intro i
    rw [Matrix.single_apply]
    split_ifs <;> norm_num

private theorem isDiagUnitLe_stageBond (t : ℕ) {M : Stage t} (hM : IsDiagUnitLe t M) :
    IsDiagUnitLe (t + 1) (stageBond t M) := by
  refine ⟨?_, ?_⟩
  · intro ⟨i1, i2⟩ ⟨j1, j2⟩ hij
    change (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) (i1, i2) (j1, j2) = 0
    rw [Matrix.kroneckerMap_apply]
    by_cases h1 : i1 = j1
    · have h2 : i2 ≠ j2 := fun h2' => hij (Prod.ext h1 h2')
      simp [Matrix.one_apply_ne h2]
    · simp [hM.1 i1 j1 h1]
  · intro ⟨i1, i2⟩
    change 0 ≤ (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) (i1, i2) (i1, i2) ∧
      (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) (i1, i2) (i1, i2) ≤ 1
    simpa [Matrix.kroneckerMap_apply] using hM.2 i1

private theorem isDiagUnitLe_bondMap (m n : ℕ) (h : m ≤ n) {M : Stage m}
    (hM : IsDiagUnitLe m M) :
    IsDiagUnitLe n (bondMap stageBond m n h M) := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht => IsDiagUnitLe t (bondMap stageBond m t ht M))
    ?base ?succ n h
  · simpa [bondMap_refl] using hM
  · intro t hmt ih
    rw [bondMap_succ stageBond m t hmt, RingHom.comp_apply]
    exact isDiagUnitLe_stageBond t ih

private theorem normalizedTrace_mul_diagUnitLe (k : ℕ) (X M : Stage k)
    (hM : IsDiagUnitLe k M) :
    normalizedTrace k (star X * M * X) ≤ normalizedTrace k (star X * X) := by
  unfold normalizedTrace
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hcyc : Matrix.trace (star X * M * X) = Matrix.trace ((X * star X) * M) := by
    rw [Matrix.trace_mul_comm (star X * M) X, Matrix.mul_assoc]
  have hsym : Matrix.trace (X * star X) = Matrix.trace (star X * X) :=
    Matrix.trace_mul_comm X (star X)
  rw [hcyc, ← hsym]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Matrix.mul_apply]
  have hsingle : (∑ j : TowerMatrix.Idx k, (X * star X) i j * M j i) =
      (X * star X) i i * M i i := by
    refine Finset.sum_eq_single i ?_ (by simp)
    intro j _ hji
    rw [hM.1 j i hji, mul_zero]
  rw [hsingle]
  have hdiag_nn : 0 ≤ (X * star X) i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    simp [Matrix.star_apply, mul_self_nonneg]
  exact mul_le_of_le_one_right hdiag_nn (hM.2 i).2

private theorem single_star_mul_single (n : ℕ) (p q : TowerMatrix.Idx n) :
    star (Matrix.single p q (1 : ℝ)) * Matrix.single p q (1 : ℝ) =
      Matrix.single q q (1 : ℝ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hsingle : (∑ k : TowerMatrix.Idx n,
      (star (Matrix.single p q (1 : ℝ))) i k * (Matrix.single p q (1 : ℝ)) k j) =
      (star (Matrix.single p q (1 : ℝ))) i p * (Matrix.single p q (1 : ℝ)) p j := by
    refine Finset.sum_eq_single p ?_ (by simp)
    intro k _ hkp
    have hzero : Matrix.single p q (1 : ℝ) k j = 0 := by
      rw [Matrix.single_apply]
      split_ifs with h
      · exact absurd h.1.symm hkp
      · rfl
    rw [hzero, mul_zero]
  rw [hsingle, Matrix.star_apply]
  simp only [Matrix.single_apply, star_trivial]
  by_cases hiq : q = i <;> by_cases hjq : q = j <;> simp [hiq, hjq]

private theorem norm_stageSingle_mul_le (n : ℕ) (p q : TowerMatrix.Idx n) (x : TracePreHilbert) :
    ‖(⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)‖ ≤ ‖x‖ := by
  have hsq : ‖(⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)‖ ^ 2 ≤
      ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [tracePreHilbert_inner_eq, tracePreHilbert_inner_eq]
    rcases x with ⟨xv⟩
    change limitTrace (star (ofStage n (Matrix.single p q 1) * xv) *
        (ofStage n (Matrix.single p q 1) * xv)) ≤
      limitTrace (star xv * xv)
    induction xv using DirectLimit.induction with
    | _ m B =>
        let k := max n m
        have hnk : n ≤ k := le_max_left n m
        have hmk : m ≤ k := le_max_right n m
        let D : Stage k := bondMap stageBond n k hnk (Matrix.single p q (1 : ℝ))
        let X : Stage k := bondMap stageBond m k hmk B
        have hE : ofStage n (Matrix.single p q (1 : ℝ)) = ofStage k D := by
          exact (directLimitOf_bondMap stageBond n k hnk (Matrix.single p q (1 : ℝ))).symm
        have hX : (⟦⟨m, B⟩⟧ : Limit) = ofStage k X := by
          exact (directLimitOf_bondMap stageBond m k hmk B).symm
        rw [hE, hX, ← ofStage_mul, ← ofStage_star, ← ofStage_mul, ← ofStage_star,
          ← ofStage_mul, limitTrace_ofStage, limitTrace_ofStage]
        have hassoc : star (D * X) * (D * X) = star X * (star D * D) * X := by
          rw [star_mul]
          noncomm_ring
        rw [hassoc]
        have hDstarD : star D * D = bondMap stageBond n k hnk (Matrix.single q q (1 : ℝ)) := by
          dsimp [D]
          rw [← bondMap_star n k hnk (Matrix.single p q (1 : ℝ)), ← map_mul,
            single_star_mul_single]
        rw [hDstarD]
        exact normalizedTrace_mul_diagUnitLe k X _
          (isDiagUnitLe_bondMap n k hnk (isDiagUnitLe_single n q))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg x)).mp hsq

private theorem stage_eq_sum_single (n : ℕ) (A : Stage n) :
    A = ∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n,
      A p q • Matrix.single p q (1 : ℝ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hqj
      have hs : Matrix.single i q (1 : ℝ) i j = 0 := by
        rw [Matrix.single_apply]
        split_ifs with h
        · exact absurd h.2 hqj
        · rfl
      rw [hs, mul_zero]
    · simp
  · intro p _ hpi
    refine Finset.sum_eq_zero fun q _ => ?_
    have hs : Matrix.single p q (1 : ℝ) i j = 0 := by
      rw [Matrix.single_apply]
      split_ifs with h
      · exact absurd h.1 hpi
      · rfl
    rw [hs, mul_zero]
  · simp

private def stageLeftMulLinear (n : ℕ) (A : Stage n) :
    TracePreHilbert →ₗ[ℝ] TracePreHilbert where
  toFun x := ⟨ofStage n A * x.val⟩
  map_add' x y := by
    ext
    change ofStage n A * (x.val + y.val) = ofStage n A * x.val + ofStage n A * y.val
    rw [mul_add]
  map_smul' r x := by
    ext
    change ofStage n A * (r • x.val) = r • (ofStage n A * x.val)
    rw [mul_smul_comm]

private theorem tracePreHilbert_sum_val {ι : Type*} (s : Finset ι) (f : ι → TracePreHilbert) :
    (∑ p ∈ s, f p).val = ∑ p ∈ s, (f p).val := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact congrArg (fun z => (f a).val + z) ih

private theorem stageLeftMulLinear_bound (n : ℕ) (A : Stage n) (x : TracePreHilbert) :
    ‖stageLeftMulLinear n A x‖ ≤
      (∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n, |A p q|) * ‖x‖ := by
  have hsum : stageLeftMulLinear n A x =
      ∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n,
        A p q • (⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert) := by
    ext
    change ofStage n A * x.val =
      (∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n,
        A p q • (⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)).val
    rw [tracePreHilbert_sum_val]
    conv_rhs =>
      arg 2; ext p
      rw [tracePreHilbert_sum_val]
    conv_lhs => rw [stage_eq_sum_single n A]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsmul : ofStage n (A p q • Matrix.single p q (1 : ℝ)) =
        A p q • ofStage n (Matrix.single p q (1 : ℝ)) := by
      rw [Algebra.smul_def, Algebra.smul_def, ofStage_mul]
      change ofStage n (algebraMap ℝ (Stage n) (A p q)) * ofStage n (Matrix.single p q 1) =
        realAlgebraMap (A p q) * ofStage n (Matrix.single p q 1)
      rw [realAlgebraMap_stage n (A p q)]
    rw [hsmul, smul_mul_assoc]
    rfl
  rw [hsum]
  calc
    ‖∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n,
        A p q • (⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)‖
      ≤ ∑ p : TowerMatrix.Idx n, ‖∑ q : TowerMatrix.Idx n,
          A p q • (⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n,
          ‖A p q • (⟨ofStage n (Matrix.single p q (1 : ℝ)) * x.val⟩ : TracePreHilbert)‖ :=
        Finset.sum_le_sum fun p _ => norm_sum_le _ _
    _ ≤ ∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n, |A p q| * ‖x‖ := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_stageSingle_mul_le n p q x) (abs_nonneg _)
    _ = (∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n, |A p q|) * ‖x‖ := by
        simp only [← Finset.sum_mul]

private def stageLeftMulPre (n : ℕ) (A : Stage n) : TracePreHilbert →L[ℝ] TracePreHilbert :=
  (stageLeftMulLinear n A).mkContinuous
    (∑ p : TowerMatrix.Idx n, ∑ q : TowerMatrix.Idx n, |A p q|)
    (stageLeftMulLinear_bound n A)

@[simp]
private theorem stageLeftMulPre_apply (n : ℕ) (A : Stage n) (x : TracePreHilbert) :
    stageLeftMulPre n A x = ⟨ofStage n A * x.val⟩ :=
  rfl

private def stageLeftMulCLM (n : ℕ) (A : Stage n) : TraceGNS →L[ℝ] TraceGNS :=
  (stageLeftMulPre n A).completion

private theorem traceGNS_eq_of_coe_eq {T₁ T₂ : TraceGNS →L[ℝ] TraceGNS}
    (h : ∀ x : TracePreHilbert, T₁ (x : TraceGNS) = T₂ (x : TraceGNS)) :
    T₁ = T₂ := by
  ext ξ
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq T₁.continuous T₂.continuous
  | ih x => exact h x

private def stageLeftMulRingHom (n : ℕ) : Stage n →+* (TraceGNS →L[ℝ] TraceGNS) where
  toFun := stageLeftMulCLM n
  map_one' := by
    apply traceGNS_eq_of_coe_eq
    intro x
    dsimp [stageLeftMulCLM]
    rw [ContinuousLinearMap.completion_apply_coe]
    simp [stageLeftMulPre_apply]
  map_mul' A B := by
    apply traceGNS_eq_of_coe_eq
    intro x
    dsimp [stageLeftMulCLM]
    change (stageLeftMulPre n (A * B)).completion (x : TraceGNS) =
      (stageLeftMulPre n A).completion ((stageLeftMulPre n B).completion (x : TraceGNS))
    simp only [ContinuousLinearMap.completion_apply_coe, stageLeftMulPre_apply, ofStage_mul,
      mul_assoc]
  map_zero' := by
    apply traceGNS_eq_of_coe_eq
    intro x
    dsimp [stageLeftMulCLM]
    rw [ContinuousLinearMap.completion_apply_coe, stageLeftMulPre_apply, ofStage_zero, zero_mul]
    change ((⟨0⟩ : TracePreHilbert) : TraceGNS) = 0
    rfl
  map_add' A B := by
    apply traceGNS_eq_of_coe_eq
    intro x
    dsimp [stageLeftMulCLM]
    change (stageLeftMulPre n (A + B)).completion (x : TraceGNS) =
      (stageLeftMulPre n A).completion (x : TraceGNS) +
        (stageLeftMulPre n B).completion (x : TraceGNS)
    simp only [ContinuousLinearMap.completion_apply_coe]
    rw [← UniformSpace.Completion.coe_add]
    congr 1
    ext
    change ofStage n (A + B) * x.val = ofStage n A * x.val + ofStage n B * x.val
    rw [ofStage_add, add_mul]

private theorem stageLeftMul_compat : CompatibleCone stageBond stageLeftMulRingHom := by
  intro n A
  apply traceGNS_eq_of_coe_eq
  intro x
  dsimp [stageLeftMulRingHom, stageLeftMulCLM]
  simp only [ContinuousLinearMap.completion_apply_coe]
  congr 1
  ext
  change ofStage (n + 1) (stageEmbed n A) * x.val = ofStage n A * x.val
  rw [ofStage_apply_bond]

private theorem stageLeftMul_star (n : ℕ) (A : Stage n) :
    stageLeftMulRingHom n (star A) =
      ContinuousLinearMap.adjoint (stageLeftMulRingHom n A) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_left]
  induction ξ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (Continuous.inner ((stageLeftMulRingHom n (star A)).continuous) continuous_const)
        (Continuous.inner continuous_id continuous_const)
  | ih x =>
      induction η using UniformSpace.Completion.induction_on with
      | hp =>
          exact isClosed_eq
            (Continuous.inner continuous_const continuous_id)
            (Continuous.inner continuous_const (stageLeftMulRingHom n A).continuous)
      | ih y =>
          dsimp [stageLeftMulRingHom, stageLeftMulCLM]
          simp only [ContinuousLinearMap.completion_apply_coe,
            UniformSpace.Completion.inner_coe, stageLeftMulPre_apply, tracePreHilbert_inner_eq,
            ofStage_star, star_mul, star_star, mul_assoc]

private theorem stageLeftMul_algebraMap (n : ℕ) (r : ℝ) :
    stageLeftMulRingHom n (algebraMap ℝ (Stage n) r) =
      algebraMap ℝ (TraceGNS →L[ℝ] TraceGNS) r := by
  apply traceGNS_eq_of_coe_eq
  intro x
  dsimp [stageLeftMulRingHom, stageLeftMulCLM]
  rw [ContinuousLinearMap.completion_apply_coe]
  change ((stageLeftMulPre n (algebraMap ℝ (Stage n) r)) x : TraceGNS) = r • (x : TraceGNS)
  rw [← UniformSpace.Completion.coe_smul]
  congr 1
  ext
  change ofStage n (algebraMap ℝ (Stage n) r) * x.val = r • x.val
  rw [← realAlgebraMap_stage n r]
  exact (Algebra.smul_def r x.val).symm

private def traceLimitRingHom : Limit →+* (TraceGNS →L[ℝ] TraceGNS) :=
  directLimitLift stageBond stageLeftMulRingHom stageLeftMul_compat

@[simp]
private theorem traceLimitRingHom_ofStage (n : ℕ) (A : Stage n) :
    traceLimitRingHom (ofStage n A) = stageLeftMulRingHom n A :=
  directLimitLift_of stageBond stageLeftMulRingHom stageLeftMul_compat n A

/-- `⋆`-algebra representation of `Cl11TensorTowerLimit.Limit` on the trace GNS Hilbert space. -/
def traceLimitStarAlgHom : Limit →⋆ₐ[ℝ] (TraceGNS →L[ℝ] TraceGNS) where
  __ := traceLimitRingHom
  map_star' x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change traceLimitRingHom (ofStage n (star A)) = star (traceLimitRingHom (ofStage n A))
        rw [traceLimitRingHom_ofStage, traceLimitRingHom_ofStage, stageLeftMul_star]
        rfl
  commutes' r := by
    change traceLimitRingHom (realAlgebraMap r) = algebraMap ℝ (TraceGNS →L[ℝ] TraceGNS) r
    rw [realAlgebraMap_stage 0 r, traceLimitRingHom_ofStage, stageLeftMul_algebraMap]

@[simp]
private theorem traceLimitStarAlgHom_ofStage (n : ℕ) (A : Stage n) :
    traceLimitStarAlgHom (ofStage n A) = stageLeftMulRingHom n A :=
  traceLimitRingHom_ofStage n A

/-- Normed `⋆`-subalgebra closure of `Limit` inside `B(TraceGNS)`. -/
abbrev TraceCarrier : Type :=
  (traceLimitStarAlgHom.range.topologicalClosure : StarSubalgebra ℝ (TraceGNS →L[ℝ] TraceGNS))

instance : NormedRing TraceCarrier :=
  SubringClass.toNormedRing _

instance : ContinuousStar TraceCarrier :=
  ⟨continuous_induced_rng.mpr (continuous_star.comp continuous_subtype_val)⟩

private def traceStageMap (n : ℕ) : Stage n →+* TraceCarrier where
  toFun A := ⟨stageLeftMulRingHom n A,
    StarSubalgebra.le_topologicalClosure _ ⟨ofStage n A, traceLimitStarAlgHom_ofStage n A⟩⟩
  map_one' := by
    ext1
    exact (stageLeftMulRingHom n).map_one
  map_mul' A B := by
    ext1
    exact (stageLeftMulRingHom n).map_mul A B
  map_zero' := by
    ext1
    exact (stageLeftMulRingHom n).map_zero
  map_add' A B := by
    ext1
    exact (stageLeftMulRingHom n).map_add A B

/-- Constructive infinite-dimensional completion model for `CliffordTowerCompletion`. -/
abbrev traceCompletionModel : CliffordTowerCompletion where
  Carrier := TraceCarrier
  normedRing := inferInstance
  starRing := inferInstance
  normedAlgebra := inferInstance
  completeSpace := inferInstance
  continuousStar := inferInstance
  stageMap := traceStageMap
  stage_compat n X := by
    ext1
    exact stageLeftMul_compat n X
  stage_star n X := by
    ext1
    exact stageLeftMul_star n X
  stage_algebraMap n r := by
    ext1
    change stageLeftMulRingHom n (algebraMap ℝ (Stage n) r) =
      algebraMap ℝ (TraceGNS →L[ℝ] TraceGNS) r
    exact stageLeftMul_algebraMap n r

private def traceVacuum : TraceGNS := ((⟨1⟩ : TracePreHilbert) : TraceGNS)

private theorem traceVacuum_norm : ‖traceVacuum‖ = 1 := by
  dsimp [traceVacuum]
  rw [UniformSpace.Completion.norm_coe]
  have hsq : ‖(⟨1⟩ : TracePreHilbert)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, tracePreHilbert_inner_eq]
    simpa using limitTrace_one
  nlinarith [norm_nonneg (⟨1⟩ : TracePreHilbert)]

private def traceRepHom : TraceCarrier →+* (TraceGNS →L[ℝ] TraceGNS) :=
  traceLimitStarAlgHom.range.topologicalClosure.subtype.toRingHom

/-- Constructive infinite-dimensional GNS representation model for `traceCompletionModel`. -/
abbrev traceGNSModel : CliffordTowerGNSRepresentation traceCompletionModel where
  Hilbert := TraceGNS
  normedGroup := traceGNS_normedAddCommGroup
  innerProduct := traceGNS_innerProductSpace
  completeHilbert := traceGNS_completeSpace
  rep := traceRepHom
  rep_continuous := continuous_subtype_val
  rep_star _ := rfl
  rep_smul _ _ := rfl
  vacuum := traceVacuum
  vacuum_norm := traceVacuum_norm

private def traceStarPreLinear : TracePreHilbert →ₗ[ℝ] TracePreHilbert where
  toFun x := ⟨star x.val⟩
  map_add' x y := by ext; exact star_add x.val y.val
  map_smul' r x := by ext; exact limit_star_smul r x.val

private theorem traceStarPreLinear_norm (x : TracePreHilbert) :
    ‖traceStarPreLinear x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  have hsq : ‖traceStarPreLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      tracePreHilbert_inner_eq, tracePreHilbert_inner_eq]
    change limitTrace (star (star x.val) * star x.val) = limitTrace (star x.val * x.val)
    rw [star_star, limitTrace_mul_comm]
  nlinarith [norm_nonneg (traceStarPreLinear x), norm_nonneg x]

private def traceStarPreCLM : TracePreHilbert →L[ℝ] TracePreHilbert :=
  traceStarPreLinear.mkContinuous 1 traceStarPreLinear_norm

private def traceModularJ : TraceGNS →L[ℝ] TraceGNS :=
  traceStarPreCLM.completion

private theorem traceModularJ_sq :
    traceModularJ.comp traceModularJ = ContinuousLinearMap.id ℝ TraceGNS := by
  apply traceGNS_eq_of_coe_eq
  intro x
  change traceModularJ (traceModularJ (x : TraceGNS)) = (x : TraceGNS)
  dsimp [traceModularJ]
  simp only [ContinuousLinearMap.completion_apply_coe]
  congr 1
  ext
  exact star_star x.val

private theorem traceModularJ_symmetric (ξ η : TraceGNS) :
    ⟪traceModularJ ξ, η⟫_ℝ = ⟪ξ, traceModularJ η⟫_ℝ := by
  induction ξ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (Continuous.inner traceModularJ.continuous continuous_const)
        (Continuous.inner continuous_id continuous_const)
  | ih x =>
      induction η using UniformSpace.Completion.induction_on with
      | hp =>
          exact isClosed_eq
            (Continuous.inner continuous_const continuous_id)
            (Continuous.inner continuous_const traceModularJ.continuous)
      | ih y =>
          dsimp [traceModularJ]
          simp only [ContinuousLinearMap.completion_apply_coe,
            UniformSpace.Completion.inner_coe]
          change limitTrace (star (star x.val) * y.val) =
            limitTrace (star x.val * star y.val)
          rw [star_star, ← star_mul, limitTrace_star, limitTrace_mul_comm]

private theorem traceModularJ_vacuum : traceModularJ traceVacuum = traceVacuum := by
  dsimp [traceModularJ, traceVacuum]
  rw [ContinuousLinearMap.completion_apply_coe]
  congr 1
  ext
  exact star_one Limit

private theorem traceModularJ_conj_limit (y : Limit) (z : TracePreHilbert) :
    traceModularJ ((traceLimitStarAlgHom y) (traceModularJ (z : TraceGNS))) =
      ((⟨z.val * star y⟩ : TracePreHilbert) : TraceGNS) := by
  dsimp [traceModularJ]
  rw [ContinuousLinearMap.completion_apply_coe]
  induction y using DirectLimit.induction with
  | _ n A =>
      change traceStarPreCLM.completion
          ((traceLimitStarAlgHom (ofStage n A)) ((traceStarPreCLM z : TracePreHilbert) : TraceGNS)) =
        ((⟨z.val * star (ofStage n A)⟩ : TracePreHilbert) : TraceGNS)
      rw [traceLimitStarAlgHom_ofStage]
      dsimp [stageLeftMulRingHom, stageLeftMulCLM]
      rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
      congr 1
      ext
      change star (ofStage n A * star z.val) = z.val * star (ofStage n A)
      rw [star_mul, star_star]

private theorem traceModularJ_commutant (a b : TraceCarrier) :
    (traceRepHom a).comp (traceModularJ.comp ((traceRepHom b).comp traceModularJ)) =
      (traceModularJ.comp ((traceRepHom b).comp traceModularJ)).comp (traceRepHom a) := by
  have h_range : ∀ x y : Limit,
      (traceLimitStarAlgHom x).comp
          (traceModularJ.comp ((traceLimitStarAlgHom y).comp traceModularJ)) =
        (traceModularJ.comp ((traceLimitStarAlgHom y).comp traceModularJ)).comp
          (traceLimitStarAlgHom x) := by
    intro x y
    apply traceGNS_eq_of_coe_eq
    intro z
    change (traceLimitStarAlgHom x)
        (traceModularJ ((traceLimitStarAlgHom y) (traceModularJ (z : TraceGNS)))) =
      traceModularJ ((traceLimitStarAlgHom y) (traceModularJ ((traceLimitStarAlgHom x) (z : TraceGNS))))
    rw [traceModularJ_conj_limit y z]
    induction x using DirectLimit.induction with
    | _ n A =>
        change (traceLimitStarAlgHom (ofStage n A))
            ((⟨z.val * star y⟩ : TracePreHilbert) : TraceGNS) =
          traceModularJ ((traceLimitStarAlgHom y)
            (traceModularJ ((traceLimitStarAlgHom (ofStage n A)) (z : TraceGNS))))
        rw [traceLimitStarAlgHom_ofStage]
        dsimp [stageLeftMulRingHom, stageLeftMulCLM]
        rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
          stageLeftMulPre_apply, stageLeftMulPre_apply,
          traceModularJ_conj_limit y ⟨ofStage n A * z.val⟩]
        congr 1
        ext
        exact (mul_assoc (ofStage n A) z.val (star y)).symm
  have h_left_closure : ∀ (a' : TraceCarrier) (y : Limit),
      (traceRepHom a').comp
          (traceModularJ.comp ((traceLimitStarAlgHom y).comp traceModularJ)) =
        (traceModularJ.comp ((traceLimitStarAlgHom y).comp traceModularJ)).comp
          (traceRepHom a') := by
    intro a' y
    let Yconj : TraceGNS →L[ℝ] TraceGNS :=
      traceModularJ.comp ((traceLimitStarAlgHom y).comp traceModularJ)
    let S : Set (TraceGNS →L[ℝ] TraceGNS) :=
      {T | T * Yconj = Yconj * T}
    have hclosed : IsClosed S :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hsub : (traceLimitStarAlgHom.range : Set (TraceGNS →L[ℝ] TraceGNS)) ⊆ S := by
      rintro _ ⟨x, rfl⟩
      exact h_range x y
    exact closure_minimal hsub hclosed a'.2
  let Rset : Set (TraceGNS →L[ℝ] TraceGNS) :=
    {T | (traceRepHom a) * (traceModularJ * T * traceModularJ) =
      (traceModularJ * T * traceModularJ) * (traceRepHom a)}
  have hclosedR : IsClosed Rset := by
    have hconj : Continuous (fun T : TraceGNS →L[ℝ] TraceGNS =>
        traceModularJ * T * traceModularJ) :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine isClosed_eq (continuous_const.mul hconj) (hconj.mul continuous_const)
  have hsubR : (traceLimitStarAlgHom.range : Set (TraceGNS →L[ℝ] TraceGNS)) ⊆ Rset := by
    rintro _ ⟨y, rfl⟩
    exact h_left_closure a y
  exact closure_minimal hsubR hclosedR b.2

private theorem traceCarrier_state_tracial (a b : TraceCarrier) :
    ⟪traceVacuum, (traceRepHom (a * b)) traceVacuum⟫_ℝ =
      ⟪traceVacuum, (traceRepHom (b * a)) traceVacuum⟫_ℝ := by
  have h_range : ∀ x y : Limit,
      ⟪traceVacuum, (traceLimitStarAlgHom x * traceLimitStarAlgHom y) traceVacuum⟫_ℝ =
        ⟪traceVacuum, (traceLimitStarAlgHom y * traceLimitStarAlgHom x) traceVacuum⟫_ℝ := by
    intro x y
    rw [← map_mul, ← map_mul]
    have hact : ∀ w : Limit, traceLimitStarAlgHom w traceVacuum =
        ((⟨w⟩ : TracePreHilbert) : TraceGNS) := by
      intro w
      induction w using DirectLimit.induction with
      | _ n A =>
          change (traceLimitStarAlgHom (ofStage n A)) traceVacuum =
            ((⟨ofStage n A⟩ : TracePreHilbert) : TraceGNS)
          rw [traceLimitStarAlgHom_ofStage]
          dsimp [stageLeftMulRingHom, stageLeftMulCLM, traceVacuum]
          rw [ContinuousLinearMap.completion_apply_coe]
          congr 1
          ext
          exact mul_one (ofStage n A)
    rw [hact (x * y), hact (y * x)]
    dsimp [traceVacuum]
    rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
      tracePreHilbert_inner_eq, tracePreHilbert_inner_eq, star_one, one_mul, one_mul,
      limitTrace_mul_comm]
  have h_left_closure : ∀ (a' : TraceCarrier) (y : Limit),
      ⟪traceVacuum, (traceRepHom a' * traceLimitStarAlgHom y) traceVacuum⟫_ℝ =
        ⟪traceVacuum, (traceLimitStarAlgHom y * traceRepHom a') traceVacuum⟫_ℝ := by
    intro a' y
    let Yop : TraceGNS →L[ℝ] TraceGNS := traceLimitStarAlgHom y
    let S : Set (TraceGNS →L[ℝ] TraceGNS) :=
      {T | ⟪traceVacuum, (T * Yop) traceVacuum⟫_ℝ =
        ⟪traceVacuum, (Yop * T) traceVacuum⟫_ℝ}
    have hclosed : IsClosed S := by
      refine isClosed_eq ?_ ?_
      · exact Continuous.inner continuous_const
          (((ContinuousLinearMap.apply ℝ TraceGNS traceVacuum).continuous).comp
            (continuous_id.mul continuous_const))
      · exact Continuous.inner continuous_const
          (((ContinuousLinearMap.apply ℝ TraceGNS traceVacuum).continuous).comp
            (continuous_const.mul continuous_id))
    have hsub : (traceLimitStarAlgHom.range : Set (TraceGNS →L[ℝ] TraceGNS)) ⊆ S := by
      rintro _ ⟨x, rfl⟩
      exact h_range x y
    exact closure_minimal hsub hclosed a'.2
  let Rset : Set (TraceGNS →L[ℝ] TraceGNS) :=
    {T | ⟪traceVacuum, (traceRepHom a * T) traceVacuum⟫_ℝ =
      ⟪traceVacuum, (T * traceRepHom a) traceVacuum⟫_ℝ}
  have hclosedR : IsClosed Rset := by
    refine isClosed_eq ?_ ?_
    · exact Continuous.inner continuous_const
        (((ContinuousLinearMap.apply ℝ TraceGNS traceVacuum).continuous).comp
          (continuous_const.mul continuous_id))
    · exact Continuous.inner continuous_const
        (((ContinuousLinearMap.apply ℝ TraceGNS traceVacuum).continuous).comp
          (continuous_id.mul continuous_const))
  have hsubR : (traceLimitStarAlgHom.range : Set (TraceGNS →L[ℝ] TraceGNS)) ⊆ Rset := by
    rintro _ ⟨y, rfl⟩
    exact h_left_closure a y
  exact closure_minimal hsubR hclosedR b.2

/-- Constructive infinite-dimensional tracial modular KMS data on `traceGNSModel`. -/
def traceModularKMSModel :
    CliffordTowerModularKMSData traceCompletionModel traceGNSModel where
  σ := fun _ => ContinuousLinearMap.id ℝ TraceCarrier
  σ_zero _ := rfl
  σ_add _ _ _ := rfl
  σ_one _ := rfl
  σ_mul _ _ _ := rfl
  σ_star _ _ := rfl
  σ_state_invariant _ _ := rfl
  J := traceModularJ
  J_sq := traceModularJ_sq
  J_symmetric := traceModularJ_symmetric
  J_vacuum := traceModularJ_vacuum
  J_commutant := traceModularJ_commutant
  σ_imag := AlgHom.id ℝ TraceCarrier
  kms_boundary a b := traceCarrier_state_tracial a b

/-- Constructive 0-binder inhabitant of `CliffordTowerKMSBridgeSystem` via `traceKMSBridgeModel`. -/
def traceKMSBridgeModel : CliffordTowerKMSBridgeSystem where
  completion := traceCompletionModel
  gns := traceGNSModel
  modular := traceModularKMSModel

end TraceWitness

/-! ## 3. Conditional Bost--Connes KMS bridge & R5 separation theorems -/

/-- Under KMS boundary conditions and generator scaling `σ_imag(S_n) = n^{-β} S_n`,
diagonal projections evaluate to `n^{-β}`. -/
theorem kms_diagonal_projection_weight
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ}
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (n : ℕ+) :
    Sys.stateCLM (S C n * star (S C n)) = (n : ℝ) ^ (-β) := by
  change Sys.gns.stateCLM (S C n * star (S C n)) = (n : ℝ) ^ (-β)
  rw [Sys.modular.kms_boundary (S C n) (star (S C n)), h_scale n, mul_smul_comm, map_smul,
    S_isometry C n, Sys.gns.stateCLM_one, smul_eq_mul, mul_one]

/-- Under KMS boundary conditions, `0 < β`, and opposite imaginary-time scaling on `S_n` and
`S_n^*`, off-diagonal projection matrix elements `S_n S_m^*` (`n ≠ m`) vanish. -/
theorem kms_off_diagonal_projection_zero
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 0 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (h_scale_star : ∀ n : ℕ+, Sys.modular.σ_imag (star (S C n)) = ((n : ℝ) ^ β) • star (S C n))
    {n m : ℕ+} (hnm : n ≠ m) :
    Sys.stateCLM (S C n * star (S C m)) = 0 := by
  change Sys.gns.stateCLM (S C n * star (S C m)) = 0
  have hinv := Sys.modular.sigmaImag_state_invariant (S C n * star (S C m))
  rw [map_mul, h_scale n, h_scale_star m, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_smul, smul_eq_mul] at hinv
  have hratio_ne : (n : ℝ) ^ (-β) * (m : ℝ) ^ β ≠ 1 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
    have hpow : (n : ℝ) ^ (-β) * (m : ℝ) ^ β = ((m : ℝ) / (n : ℝ)) ^ β := by
      rw [Real.rpow_neg hn_pos.le, Real.div_rpow hm_pos.le hn_pos.le, inv_mul_eq_div]
    rw [hpow]
    have hmn_ne : (m : ℝ) ≠ (n : ℝ) := by
      intro heq
      apply hnm
      exact PNat.coe_injective (by exact_mod_cast heq.symm)
    rcases lt_or_gt_of_ne hmn_ne with hlt | hgt
    · have hdiv_lt : (m : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr hlt
      have hdiv_pos : 0 < (m : ℝ) / (n : ℝ) := div_pos hm_pos hn_pos
      exact ne_of_lt (Real.rpow_lt_one hdiv_pos.le hdiv_lt hβ)
    · have hdiv_gt : 1 < (m : ℝ) / (n : ℝ) := (one_lt_div hn_pos).mpr hgt
      exact ne_of_gt (Real.one_lt_rpow hdiv_gt hβ)
  have hsub : ((n : ℝ) ^ (-β) * (m : ℝ) ^ β - 1) * Sys.gns.stateCLM (S C n * star (S C m)) = 0 := by
    linarith
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hratio_ne)

/-- Constructs a normalized `BostConnesKMS.KMSProjectionState C` from a KMS bridge system
carrying a `1 < β` Bost--Connes Cuntz representation. -/
def bostConnesKMSProjectionState
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (h_scale_star : ∀ n : ℕ+, Sys.modular.σ_imag (star (S C n)) = ((n : ℝ) ^ β) • star (S C n)) :
    KMSProjectionState C where
  β := β
  ζβ := bostConnesPartition β
  φ := ((bostConnesPartition β)⁻¹ • Sys.stateCLM).toLinearMap.toAddMonoidHom
  eval_projection n m := by
    change (bostConnesPartition β)⁻¹ * Sys.stateCLM (S C n * star (S C m)) =
      kmsProjectionReadout β (bostConnesPartition β) n m
    by_cases hnm : n = m
    · subst hnm
      rw [kms_diagonal_projection_weight Sys C h_scale n, kmsProjectionReadout_self, div_eq_inv_mul]
    · rw [kms_off_diagonal_projection_zero Sys C (lt_trans zero_lt_one hβ) h_scale h_scale_star hnm,
        mul_zero, kmsProjectionReadout_ne hnm]

/-- Conditional Bost--Connes colimit KMS partition bridge theorem: derives zeta normalization,
Boltzmann projection weights, total mass `1`, positivity, and limit-stage compatibility. -/
theorem bostConnes_colimit_kms_partition_bridge
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n)
    (h_scale_star : ∀ n : ℕ+, Sys.modular.σ_imag (star (S C n)) = ((n : ℝ) ^ β) • star (S C n)) :
    let Φ := bostConnesKMSProjectionState Sys C hβ h_scale h_scale_star
    Φ.ζβ = (riemannZeta (β : ℂ)).re ∧
      (∀ n : ℕ+, Φ.φ (S C n * star (S C n)) = normalizedBostConnesWeight β n) ∧
      (∑' n : ℕ+, Φ.φ (S C n * star (S C n))) = 1 ∧
      (∀ n : ℕ+, 0 < Φ.φ (S C n * star (S C n))) ∧
      (∀ a : Sys.completion.Carrier, 0 ≤ Φ.φ (star a * a)) ∧
      (∀ (n : ℕ) (X : Stage n),
        Sys.limitState (ofStage (n + 1) (stageBond n X)) = Sys.limitState (ofStage n X)) := by
  dsimp only
  let Φ := bostConnesKMSProjectionState Sys C hβ h_scale h_scale_star
  refine ⟨bostConnesPartition_eq_riemannZeta_re β hβ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [Φ.kms_evaluation_on_diagonal_projection n]
    rfl
  · have hfn : (fun n : ℕ+ => Φ.φ (S C n * star (S C n))) = normalizedBostConnesWeight β := by
      ext n
      rw [Φ.kms_evaluation_on_diagonal_projection n]
      rfl
    rw [hfn]
    exact tsum_normalizedBostConnesWeight β hβ
  · intro n
    rw [Φ.kms_evaluation_on_diagonal_projection n]
    exact normalizedBostConnesWeight_pos β hβ n
  · intro a
    change 0 ≤ (bostConnesPartition β)⁻¹ * Sys.gns.stateCLM (star a * a)
    exact mul_nonneg (inv_nonneg.mpr (bostConnesPartition_pos β hβ).le)
      (Sys.gns.stateCLM_star_mul_self_nonneg a)
  · intro n X
    rw [CliffordTowerKMSBridgeSystem.limitState,
      Sys.gns.limitState_stage_readout (n + 1) (stageBond n X),
      Sys.gns.limitState_stage_readout n X,
      Sys.gns.limitState_stage_compat n X]

/-- R5 separation (matrix base): Witt creation and annihilation do not commute. -/
theorem witt_base_noncommutative :
    wittCreationBase * wittAnnihilationBase ≠ wittAnnihilationBase * wittCreationBase := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [wittCreationBase, wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Explicit `Matrix (Fin 2) (Fin 2) ℝ` non-commutativity witness via Witt base matrices. -/
theorem witt_base_matrix_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨wittCreationBase, wittAnnihilationBase, witt_base_noncommutative⟩

/-- R5 separation (algebraic colimit): `Cl11TensorTowerLimit.Limit` is noncommutative. -/
theorem limit_noncommutative : ∃ x y : Limit, x * y ≠ y * x := by
  let x1 : Stage 1 := (1 : Stage 0) ⊗ₖ wittCreationBase
  let y1 : Stage 1 := (1 : Stage 0) ⊗ₖ wittAnnihilationBase
  refine ⟨ofStage 1 x1, ofStage 1 y1, ?_⟩
  intro h
  rw [← ofStage_mul, ← ofStage_mul] at h
  have hstage : x1 * y1 = y1 * x1 :=
    directLimitOf_injective stageBond matStageEmbed_injective 1 h
  have h00 := congrArg (fun M : Stage 1 => M ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)))
    hstage
  have hL : (x1 * y1) ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = 1 := by
    have hmul : x1 * y1 = ((1 : Stage 0) * 1) ⊗ₖ (wittCreationBase * wittAnnihilationBase) :=
      (Matrix.mul_kronecker_mul (1 : Stage 0) 1 wittCreationBase wittAnnihilationBase).symm
    change (x1 * y1) ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = 1
    rw [hmul, Matrix.one_mul]
    simp [Matrix.kroneckerMap_apply, wittCreationBase, wittAnnihilationBase]
  have hR : (y1 * x1) ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = 0 := by
    have hmul : y1 * x1 = ((1 : Stage 0) * 1) ⊗ₖ (wittAnnihilationBase * wittCreationBase) :=
      (Matrix.mul_kronecker_mul (1 : Stage 0) 1 wittAnnihilationBase wittCreationBase).symm
    change (y1 * x1) ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = 0
    rw [hmul, Matrix.one_mul]
    simp [Matrix.kroneckerMap_apply, wittCreationBase, wittAnnihilationBase]
  linarith

/-- R5 separation (tracial vs. `β > 1` KMS): any Bost--Connes KMS shift at `1 < β`
must have `σ_imag ≠ AlgHom.id`, separating it from the tracial witness `traceKMSBridgeModel`. -/
theorem bostConnes_kms_requires_nontrivial_modular_shift
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ n : ℕ+, Sys.modular.σ_imag (S C n) = ((n : ℝ) ^ (-β)) • S C n) :
    Sys.modular.σ_imag ≠ AlgHom.id ℝ Sys.completion.Carrier := by
  intro hid
  let two : ℕ+ := ⟨2, by norm_num⟩
  have hdiag := kms_diagonal_projection_weight Sys C h_scale two
  have htracial : Sys.stateCLM (S C two * star (S C two)) = 1 := by
    change Sys.gns.stateCLM (S C two * star (S C two)) = 1
    rw [Sys.modular.kms_boundary (S C two) (star (S C two)), hid]
    change Sys.gns.stateCLM (star (S C two) * S C two) = 1
    rw [S_isometry C two, Sys.gns.stateCLM_one]
  have heq : ((two : ℝ) ^ (-β)) = 1 := hdiag.symm.trans htracial
  have h2_gt : (1 : ℝ) < (two : ℝ) := by norm_num [two]
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ
  have hpow_lt : (two : ℝ) ^ (-β) < 1 := by
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow h2_gt hβ_pos
  linarith

/-- Exact backward-compatible Bost--Connes colimit KMS package. -/
theorem colimit_kms_state_exists {β : ℝ} (hβ : 1 < β) :
    1 < β ∧
      bostConnesPartition β = (riemannZeta (β : ℂ)).re ∧
      (∑' n : ℕ+, normalizedBostConnesWeight β n) = 1 ∧
      ∀ n : ℕ+, 0 < normalizedBostConnesWeight β n := by
  exact ⟨hβ, bostConnesPartition_eq_riemannZeta_re β hβ,
    tsum_normalizedBostConnesWeight β hβ,
    fun n => normalizedBostConnesWeight_pos β hβ n⟩

end InfoGeometry.Canonical.BostConnesColimitKMSBridge
