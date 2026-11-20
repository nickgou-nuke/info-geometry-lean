/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularOperators
import InfoGeometry.Lie.SplitOctonionScalarPotentialObstruction
import InfoGeometry.Thermo.ProjectedGramDissipation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# Actual split-octonion associators as projected Gram channels

The canonical Zorn coordinate equivalence is composed with native product,
function-space, and `WithLp` equivalences to obtain an eight-dimensional real
Euclidean space. This chooses the positive sum-of-coordinate-squares metric;
it does not turn the indefinite split norm into a Hilbert norm.

The linear defect `R_b ∘ R_a - R_(a*b)` uses the existing right multiplication
operators. Its value on `v` is exactly `(v*a)*b - v*(a*b)`, in that order.
Finite dimensionality makes its transported endomorphism continuous.

An arbitrary finite family of these actual associators instantiates the
existing projected Gram construction. Its quadratic form, kernel, and strict
production criterion are expressed below in the original Zorn products. The
same specialization constructs the existing metriplectic flow with nonnegative
mobility and explicit reversible hypotheses. No basis independence, operator
rank, nonzero lower bound, or trajectory theorem is asserted.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Lie.SplitOctonionAssociatorDissipation

open scoped BigOperators
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionScalarPotentialObstruction
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Thermo.ProjectedGramDissipation

local notation "CZ" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "E" => EuclideanSpace ℝ (Fin 2 ⊕ (Fin 3 ⊕ Fin 3))

/-- Positive Euclidean coordinates, assembled entirely from existing equivalences. -/
def coordinateEquiv : CZ ≃ₗ[ℝ] E :=
  (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv (R := ℝ)).trans
    ((LinearEquiv.prodAssoc ℝ ℝ ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ))).symm.trans
      (((LinearEquiv.finTwoArrow ℝ ℝ).symm.prodCongr
        (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) ℝ ℝ).symm).trans
        ((LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 3 ⊕ Fin 3) ℝ ℝ).symm.trans
          (WithLp.linearEquiv 2 ℝ ((Fin 2 ⊕ (Fin 3 ⊕ Fin 3)) → ℝ)).symm)))

@[simp] theorem coordinateEquiv_a (X : CZ) : coordinateEquiv X (Sum.inl 0) = X.a := rfl

@[simp] theorem coordinateEquiv_b (X : CZ) : coordinateEquiv X (Sum.inl 1) = X.b := rfl

@[simp] theorem coordinateEquiv_x (X : CZ) (i : Fin 3) :
    coordinateEquiv X (Sum.inr (Sum.inl i)) = X.x i := rfl

@[simp] theorem coordinateEquiv_y (X : CZ) (i : Fin 3) :
    coordinateEquiv X (Sum.inr (Sum.inr i)) = X.y i := rfl

/-- The selected positive metric is the unweighted sum of all eight coordinate squares. -/
theorem coordinateEquiv_norm_sq (X : CZ) :
    ‖coordinateEquiv X‖ ^ 2 =
      X.a ^ 2 + X.b ^ 2 + (∑ i : Fin 3, X.x i ^ 2) + ∑ i : Fin 3, X.y i ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, Fin.sum_univ_two,
    coordinateEquiv_a, coordinateEquiv_b, coordinateEquiv_x, coordinateEquiv_y]
  ring

theorem euclidean_finrank : Module.finrank ℝ E = 8 := by simp

/-- The first-variable associator is the ordered defect of existing right actions. -/
def associatorLinear (a b : CZ) : Module.End ℝ CZ :=
  (rightMultiplication b).comp (rightMultiplication a) - rightMultiplication (a * b)

@[simp] theorem associatorLinear_apply (a b v : CZ) :
    associatorLinear a b v = (v * a) * b - v * (a * b) := rfl

/-- Transport the actual associator and use native finite-dimensional continuity. -/
def associatorOperator (a b : CZ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (coordinateEquiv.toLinearMap.comp
      ((associatorLinear a b).comp coordinateEquiv.symm.toLinearMap))

@[simp] theorem associatorOperator_apply (a b : CZ) (x : E) :
    associatorOperator a b x = coordinateEquiv
      ((coordinateEquiv.symm x * a) * b - coordinateEquiv.symm x * (a * b)) := by
  simp [associatorOperator, associatorLinear_apply]

@[simp] theorem associatorOperator_apply_coordinate (a b v : CZ) :
    associatorOperator a b (coordinateEquiv v) =
      coordinateEquiv ((v * a) * b - v * (a * b)) := by
  simp only [associatorOperator_apply, LinearEquiv.symm_apply_apply]

/-- All three arguments in the existing associative core give a zero channel. -/
theorem associatorOperator_eq_zero_of_mem_core (v a b : CZ)
    (hv : v ∈ coreSubmodule) (ha : a ∈ coreSubmodule) (hb : b ∈ coreSubmodule) :
    associatorOperator a b (coordinateEquiv v) = 0 := by
  have h := InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc v a b hv ha hb
  change (v * a) * b = v * (a * b) at h
  rw [associatorOperator_apply_coordinate, h, sub_self, map_zero]

/-- An actual channel remains nonzero on a vector in that core when an argument leaves it. -/
theorem associatorOperator_core_ambient_ne_zero :
    associatorOperator kUnit (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3))
      (coordinateEquiv lUnit) ≠ 0 := by
  intro h
  apply core_ambient_associator_ne_zero
  apply coordinateEquiv.injective
  simpa only [associatorOperator_apply_coordinate, map_zero] using h

variable {ι : Type*} [Fintype ι]

/-- Specialize the native projected Gram operator to a finite family of actual associators. -/
def associatorGram (a b : ι → CZ) (h : CZ) : E →L[ℝ] E :=
  projectedGram (fun i => associatorOperator (a i) (b i)) (coordinateEquiv h)

/-- Exact production in the chosen positive metric, after the actual energy projection. -/
theorem associatorGram_quadratic (a b : ι → CZ) (h v : CZ) :
    let w := coordinateEquiv.symm
      ((ℝ ∙ coordinateEquiv h)ᗮ.starProjection (coordinateEquiv v))
    inner ℝ (coordinateEquiv v) (associatorGram a b h (coordinateEquiv v)) =
      ∑ i, ‖coordinateEquiv ((w * a i) * b i - w * (a i * b i))‖ ^ 2 := by
  dsimp only
  simpa only [associatorGram, associatorOperator_apply] using
    projectedGram_quadratic (fun i => associatorOperator (a i) (b i))
      (coordinateEquiv h) (coordinateEquiv v)

/-- The kernel is exactly the simultaneous vanishing of the projected Zorn associators. -/
theorem associatorGram_apply_eq_zero_iff (a b : ι → CZ) (h v : CZ) :
    let w := coordinateEquiv.symm
      ((ℝ ∙ coordinateEquiv h)ᗮ.starProjection (coordinateEquiv v))
    associatorGram a b h (coordinateEquiv v) = 0 ↔
      ∀ i, (w * a i) * b i - w * (a i * b i) = 0 := by
  dsimp only
  rw [associatorGram, projectedGram_apply_eq_zero_iff]
  constructor
  · intro hz i
    apply coordinateEquiv.injective
    simpa only [associatorOperator_apply, map_zero] using hz i
  · intro hz i
    rw [associatorOperator_apply, hz i, map_zero]

/-- Strict production requires a nonzero channel after projection, not merely an ambient witness. -/
theorem associatorGram_quadratic_pos_iff (a b : ι → CZ) (h v : CZ) :
    let w := coordinateEquiv.symm
      ((ℝ ∙ coordinateEquiv h)ᗮ.starProjection (coordinateEquiv v))
    0 < inner ℝ (coordinateEquiv v) (associatorGram a b h (coordinateEquiv v)) ↔
      ∃ i, (w * a i) * b i - w * (a i * b i) ≠ 0 := by
  dsimp only
  rw [associatorGram, projectedGram_quadratic_pos_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro hz
    apply hi
    rw [associatorOperator_apply, hz, map_zero]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro hz
    apply hi
    apply coordinateEquiv.injective
    simpa only [associatorOperator_apply, map_zero] using hz

/-- The existing flow structure with the actual associator family and nonnegative mobility. -/
def associatorFlow (a b : ι → CZ) (h s : CZ) (J : E →L[ℝ] E)
    (γ : ℝ) (hγ : 0 ≤ γ) : InfoGeometry.SuperMetriplectic.MetriplecticFlow E :=
  projectedGramFlow (fun i => associatorOperator (a i) (b i))
    (coordinateEquiv h) (coordinateEquiv s) J γ hγ

theorem associatorFlow_energy_rate (a b : ι → CZ) (h s : CZ) (J : E →L[ℝ] E)
    (hJ : J.adjoint = -J) (γ : ℝ) (hγ : 0 ≤ γ) :
    inner ℝ (coordinateEquiv h) (associatorFlow a b h s J γ hγ).totalFlow = 0 :=
  projectedGramFlow_energy_rate (fun i => associatorOperator (a i) (b i))
    (coordinateEquiv h) (coordinateEquiv s) J hJ γ hγ

/-- The entropy rate is a nonnegative-mobility sum of actual squared associators. -/
theorem associatorFlow_entropy_rate (a b : ι → CZ) (h s : CZ) (J : E →L[ℝ] E)
    (hJ : J.adjoint = -J) (hJs : J (coordinateEquiv s) = 0) (γ : ℝ) (hγ : 0 ≤ γ) :
    let w := coordinateEquiv.symm
      ((ℝ ∙ coordinateEquiv h)ᗮ.starProjection (coordinateEquiv s))
    inner ℝ (coordinateEquiv s) (associatorFlow a b h s J γ hγ).totalFlow =
      γ * ∑ i, ‖coordinateEquiv ((w * a i) * b i - w * (a i * b i))‖ ^ 2 := by
  dsimp only
  simpa only [associatorFlow, associatorOperator_apply] using
    projectedGramFlow_entropy_rate (fun i => associatorOperator (a i) (b i))
      (coordinateEquiv h) (coordinateEquiv s) J hJ hJs γ hγ

end InfoGeometry.Lie.SplitOctonionAssociatorDissipation
