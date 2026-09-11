import InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Routing.FiniteMatrixMixture

/-! A finite convex mixture of the existing `GL32` conjugation actions.

This owner proves only preservation of the identity.  It does not claim that
the mixture is itself an algebra automorphism, nor that it permutes a gamma
frame.
-/

namespace InfoGeometry.Routing.Cl55SoftConjugation

open InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.Routing.FiniteMatrixMixture

abbrev Mat32 := InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge.Mat32
abbrev GL32 := InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge.GL32

def softConjugation {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G) (T : Mat32) : Mat32 :=
  ∑ g, (w.value g) • conjugate (action.U g) T

theorem softConjugation_one {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G) :
    softConjugation action w 1 = 1 := by
  rw [softConjugation]
  simp only [conjugate_one]
  rw [← Finset.sum_smul, w.sum_one, one_smul]

theorem softConjugation_delta {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (action : IntegratedCl55ActionDatum G) (g₀ : G) :
    softConjugation action (deltaWeights g₀) = conjugate (action.U g₀) := by
  funext T
  simp [softConjugation, deltaWeights]

theorem softConjugation_add {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G)
    (S T : Mat32) :
    softConjugation action w (S + T) =
      softConjugation action w S + softConjugation action w T := by
  rw [softConjugation]
  simp_rw [conjugate_add]
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  rfl

theorem softConjugation_zero {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G) :
    softConjugation action w 0 = 0 := by
  simp [softConjugation, conjugate]

theorem softConjugation_smul {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G)
    (c : ℝ) (T : Mat32) :
    softConjugation action w (c • T) =
      c • softConjugation action w T := by
  rw [softConjugation]
  simp_rw [conjugate_smul]
  simp only [smul_smul]
  change (∑ g, (w.value g * c) • conjugate (action.U g) T) =
    c • (∑ g, w.value g • conjugate (action.U g) T)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  simpa [mul_comm] using
    (smul_smul c (w.value g) (conjugate (action.U g) T)).symm

def softConjugationLinearMap {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G) :
    Mat32 →ₗ[ℝ] Mat32 where
  toFun := softConjugation action w
  map_add' S T := softConjugation_add action w S T
  map_smul' c T := softConjugation_smul action w c T

@[simp] theorem softConjugationLinearMap_apply {G : Type*} [Fintype G] [Group G]
    (action : IntegratedCl55ActionDatum G) (w : Weights G) (T : Mat32) :
    softConjugationLinearMap action w T = softConjugation action w T :=
  rfl

end InfoGeometry.Routing.Cl55SoftConjugation
