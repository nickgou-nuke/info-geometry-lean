/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Thermo.OnsagerOperatorClosure

/-!
# Souriau Coadjoint Orbits and Thermodynamic State Covariance

This module formalizes:
1. **Thermodynamic State Space as Lie Algebra**:
   The temperature state space $\beta \in \mathfrak{g}$ and its dual momentum observable $M \in \mathfrak{g}^*$.
2. **Coadjoint Action & Orbit Invariance**:
   The coadjoint generator $\operatorname{ad}^*_X M(Y) = -M([X, Y])$.
3. **The Kirillov-Kostant-Souriau (KKS) Symplectic Structure**:
   $\omega_{\text{KKS}}(X, Y) = M([X, Y]) = -\operatorname{ad}^*_X M(Y)$.
4. **Souriau-Koszul Fisher Metric & Covariance**:
   The symmetric positive semidefinite Hessian covariance metric $g(X, Y)$.
5. **The Coadjoint Quantum Geometric Tensor**:
   $\mathcal{Q}(X, Y) = g(X, Y) - i \cdot \frac{1}{2} \omega_{\text{KKS}}(X, Y)$ unifying thermodynamic dissipation
   with Hamiltonian symplectic rotation on the coadjoint orbit.

All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauCoadjointOrbitBridge

open SouriauKKS

section CommRingGeneral

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The coadjoint action of the Lie algebra L on its dual space Module.Dual R L. -/
def coadjointAction (X : L) (μ : Module.Dual R L) : Module.Dual R L where
  toFun := fun Y => -μ ⁅X, Y⁆
  map_add' := by
    intro Y₁ Y₂
    rw [lie_add, μ.map_add, neg_add]
  map_smul' := by
    intro c Y
    rw [lie_smul, μ.map_smul, smul_neg, RingHom.id_apply]

@[simp]
theorem coadjointAction_apply (X : L) (μ : Module.Dual R L) (Y : L) :
    coadjointAction X μ Y = -μ ⁅X, Y⁆ := rfl

/-- 
  THEOREM 1: The KKS Form as Coadjoint Contraction.
  The Kirillov-Kostant-Souriau 2-form evaluated on generators X, Y
  is identically the negative evaluation of the coadjoint action:
    ω_KKS(μ)(X, Y) = -⟨ad*_X μ, Y⟩
-/
theorem kksForm_eq_neg_coadjointAction (μ : Module.Dual R L) (X Y : L) :
    kksForm μ X Y = -coadjointAction X μ Y := by
  dsimp [kksForm, coadjointAction]
  rw [neg_neg]

/-- 
  THEOREM 2: Coadjoint Orbit Invariance of the KKS Symplectic 2-Form.
  The cyclic Jacobi identity of the Lie algebra translates to the closure
  dω_KKS = 0 of the symplectic form along the coadjoint orbit.
-/
theorem kks_coadjoint_jacobi_closure (μ : Module.Dual R L) (X Y Z : L) :
    kksForm μ X ⁅Y, Z⁆ + kksForm μ Y ⁅Z, X⁆ + kksForm μ Z ⁅X, Y⁆ = 0 :=
  kksForm_jacobi μ X Y Z

end CommRingGeneral

section RealSouriauThermodynamics

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- 
  The Complex Quantum Geometric Tensor on the Souriau Coadjoint Orbit:
  𝒬(X, Y) = g(X, Y) - i · (1/2) ω_KKS(X, Y)
-/
def souriauQGT
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L) (X Y : L) : ℂ :=
  ⟨fisherMetric X Y, -(1 / 2 : ℝ) * kksForm meanMomentum X Y⟩

/-- 
  THEOREM 3: Decomposition of the Souriau QGT into Metric and Symplectic Components.
-/
theorem souriauQGT_re_im
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L) (X Y : L) :
    (souriauQGT fisherMetric meanMomentum X Y).re = fisherMetric X Y ∧
    (souriauQGT fisherMetric meanMomentum X Y).im =
      -(1 / 2 : ℝ) * kksForm meanMomentum X Y :=
  ⟨rfl, rfl⟩

/-- 
  THEOREM 4: Norm-Squared Decomposition of the Souriau QGT.
  |𝒬(X, Y)|² = g(X, Y)² + (1/4) ω_KKS(X, Y)²
-/
theorem souriauQGT_normSq
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L) (X Y : L) :
    Complex.normSq (souriauQGT fisherMetric meanMomentum X Y) =
      (fisherMetric X Y) ^ 2 +
        (1 / 4 : ℝ) * (kksForm meanMomentum X Y) ^ 2 := by
  dsimp [souriauQGT, Complex.normSq]
  ring

/-- The algebraic KKS form at a momentum functional, as a real bilinear form on
the Lie algebra. -/
def souriauKKSBilinForm (meanMomentum : Module.Dual ℝ L) :
    LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (kksForm meanMomentum)
    (fun X Y Z => kksForm_add_left meanMomentum X Y Z)
    (fun r X Y => kksForm_smul_left meanMomentum r X Y)
    (fun X Y Z => kksForm_add_right meanMomentum X Y Z)
    (fun r X Y => kksForm_smul_right meanMomentum r X Y)

/-- Pair the Souriau Fisher response with the coadjoint KKS response as one
real Onsager--Casimir system. The dissipative channel is symmetric and
nonnegative; the orbit channel is skew by the Lie bracket antisymmetry. -/
def souriauOnsagerSystem
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L)
    (metric_symm : ∀ X Y, fisherMetric X Y = fisherMetric Y X)
    (metric_nonneg : ∀ X, 0 ≤ fisherMetric X X) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem L where
  dissipative := fisherMetric
  reversible := souriauKKSBilinForm meanMomentum
  dissipative_symm := metric_symm
  reversible_skew := by
    intro X Y
    exact kksForm_skew meanMomentum X Y
  dissipative_nonneg := metric_nonneg

/-- The quadratic entropy production of the combined Souriau system is
exactly the Fisher variance; the KKS response contributes zero on the
diagonal. -/
theorem souriauOnsagerSystem_entropy_production
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L)
    (metric_symm : ∀ X Y, fisherMetric X Y = fisherMetric Y X)
    (metric_nonneg : ∀ X, 0 ≤ fisherMetric X X) (X : L) :
    (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator X X =
        fisherMetric X X ∧
      0 ≤ (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator X X := by
  constructor
  · exact (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).entropy_production_eq X
  · exact (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).entropy_production_nonneg X

/-- The symmetric and skew parts of the total response recover respectively
the Souriau Fisher form and the KKS orbit form. -/
theorem souriauOnsagerSystem_reciprocity
    (fisherMetric : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (meanMomentum : Module.Dual ℝ L)
    (metric_symm : ∀ X Y, fisherMetric X Y = fisherMetric Y X)
    (metric_nonneg : ∀ X, 0 ≤ fisherMetric X X) (X Y : L) :
    (1 / 2 : ℝ) *
        ((souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator X Y +
          (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator Y X) =
        fisherMetric X Y ∧
      (1 / 2 : ℝ) *
        ((souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator X Y -
          (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator Y X) =
        kksForm meanMomentum X Y := by
  constructor
  · exact (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator_symm_part X Y
  · calc
      (1 / 2 : ℝ) *
          ((souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator X Y -
            (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator Y X) =
          (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).reversible X Y :=
        (souriauOnsagerSystem fisherMetric meanMomentum metric_symm metric_nonneg).totalGenerator_skew_part X Y
      _ = kksForm meanMomentum X Y := rfl

end RealSouriauThermodynamics

end InfoGeometry.Canonical.SouriauCoadjointOrbitBridge

end
