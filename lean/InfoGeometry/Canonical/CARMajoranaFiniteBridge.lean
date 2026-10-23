/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaMatrices
import InfoGeometry.Canonical.MajoranaPfaffian4
import InfoGeometry.Canonical.MajoranaPfaffianKernelCriterion

/-!
# Explicit CAR, finite chain, and Pfaffian kernel bridge

The same complex matrix carrier supports the CAR family, the native chain sum,
and its quadratic commutator action. The real skew coefficient matrix uses
K[1,2] = 2*t and the proved four-index Pfaffian square law. These are conserved
operators in the Majorana span, not state-space kernel vectors or a phase claim.
-/
namespace InfoGeometry.Canonical.CARMajoranaFiniteBridge
open scoped BigOperators
open MajoranaCoefficientAction MajoranaPfaffianKernelCriterion
open KitaevChainMajoranaZeroModes MajoranaPfaffian4 ProjectivePfaffianDeterminantCounts
noncomputable section

/-- Instantiate the existing Pfaffian carrier from the proved matching law. -/
def matchingKernel (a b c d e f : ℝ) : PfaffianKernel (Fin 4) where
  omega := skewMatrix4 a b c d e f
  skew := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M j i)
      (skewMatrix4_transpose a b c d e f)
    simpa using h
  pfaffian := pfaffian4 a b c d e f
  pf_sq_eq_det := by
    simpa only [pow_two] using skewMatrix4_pfaffian_sq_eq_det a b c d e f

/-- No assumed Majorana family or square-law witness remains in this instance. -/
theorem fourMode_pfaffian_iff_conserved_field (a b c d e f : ℝ) :
    pfaffian4 a b c d e f = 0 ↔ ∃ v : Fin 4 → ℝ,
      Fintype.linearCombination ℝ twoSiteMajorana v ≠ 0 ∧
      quadraticElement twoSiteMajorana (skewMatrix4 a b c d e f) * Fintype.linearCombination ℝ twoSiteMajorana v -
        Fintype.linearCombination ℝ twoSiteMajorana v * quadraticElement twoSiteMajorana (skewMatrix4 a b c d e f) = 0 :=
  pfaffian_zero_iff_conserved_majorana twoSiteMajorana_car (matchingKernel a b c d e f)

/-- The open sweet-spot matrix couples only the middle Majorana pair. -/
def sweetSpotKernel (t : ℝ) : PfaffianKernel (Fin 4) :=
  matchingKernel 0 0 0 (2 * t) 0 0

theorem sweetSpot_endpoint_kernel (t : ℝ) :
    (sweetSpotKernel t).omega.mulVec (Pi.single (0 : Fin 4) 1) = 0 ∧
    (sweetSpotKernel t).omega.mulVec (Pi.single (3 : Fin 4) 1) = 0 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [sweetSpotKernel, matchingKernel, skewMatrix4,
      Matrix.mulVec, dotProduct, Pi.single_apply]

theorem sweetSpot_pfaffian_zero (t : ℝ) : (sweetSpotKernel t).pfaffian = 0 := by
  simp [sweetSpotKernel, matchingKernel, pfaffian4]

/-- Two-site skew generator, with no additional imaginary factor. -/
def twoSiteGenerator (t : ℝ) : ChainOp :=
  t • (twoSiteMajorana 1 * twoSiteMajorana 2)

/-- Identify the concrete generator with the existing native chain sum
on precisely the same matrix carrier. -/
theorem twoSiteGenerator_eq_chain (t : ℝ) :
    twoSiteGenerator t =
      kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana := by
  simp [twoSiteGenerator, kitaevSweetSpotHamiltonian]

/-- Exact coefficient/operator normalization. -/
theorem sweetSpot_quadratic_eq_chain (t : ℝ) :
    quadraticElement twoSiteMajorana (sweetSpotKernel t).omega = twoSiteGenerator t := by
  have hanti : twoSiteMajorana 2 * twoSiteMajorana 1 =
      -(twoSiteMajorana 1 * twoSiteMajorana 2) := by
    have h := twoSiteMajorana_car (2 : Fin 4) (1 : Fin 4)
    simp only [Fin.isValue, show (2 : Fin 4) ≠ 1 by decide, ite_false] at h
    exact eq_neg_of_add_eq_zero_left h
  simp [quadraticElement, sweetSpotKernel, matchingKernel, skewMatrix4,
    Fin.sum_univ_succ, twoSiteGenerator, hanti]
  module

/-- The native chain commutator kernel is the sweet-spot coefficient kernel. -/
theorem sweetSpot_chain_commutator_eq_zero_iff (t : ℝ) (v : Fin 4 → ℝ) :
    let H := kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana
    H * Fintype.linearCombination ℝ twoSiteMajorana v -
      Fintype.linearCombination ℝ twoSiteMajorana v * H = 0 ↔
      (sweetSpotKernel t).omega.mulVec v = 0 := by
  dsimp only
  rw [← twoSiteGenerator_eq_chain, ← sweetSpot_quadratic_eq_chain]
  exact quadraticElement_commutator_eq_zero_iff twoSiteMajorana_car
    (sweetSpotKernel t).omega (sweetSpotKernel t).skew v

/-- Pfaffian criterion for that same native chain, not a state-space kernel. -/
theorem sweetSpot_pfaffian_iff_conserved_chain (t : ℝ) :
    (sweetSpotKernel t).pfaffian = 0 ↔ ∃ v : Fin 4 → ℝ,
      Fintype.linearCombination ℝ twoSiteMajorana v ≠ 0 ∧
      kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana *
          Fintype.linearCombination ℝ twoSiteMajorana v -
        Fintype.linearCombination ℝ twoSiteMajorana v *
          kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana = 0 := by
  simpa only [sweetSpot_quadratic_eq_chain, twoSiteGenerator_eq_chain] using
    pfaffian_zero_iff_conserved_majorana twoSiteMajorana_car (sweetSpotKernel t)

/-- Actual nonzero endpoint operators and the same chain's Pfaffian. -/
theorem car_to_chain_to_pfaffian (t : ℝ) :
    let H := kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana
    twoSiteMajorana 0 ≠ 0 ∧ twoSiteMajorana 3 ≠ 0 ∧
    H * twoSiteMajorana 0 - twoSiteMajorana 0 * H = 0 ∧
    H * twoSiteMajorana 3 - twoSiteMajorana 3 * H = 0 ∧
    (sweetSpotKernel t).pfaffian = 0 := by
  dsimp only
  obtain ⟨h0, h3⟩ := sweetSpot_endpoint_kernel t
  have c0 := (quadraticElement_commutator_eq_zero_iff twoSiteMajorana_car
    (sweetSpotKernel t).omega (sweetSpotKernel t).skew (Pi.single 0 1)).mpr h0
  have c3 := (quadraticElement_commutator_eq_zero_iff twoSiteMajorana_car
    (sweetSpotKernel t).omega (sweetSpotKernel t).skew (Pi.single 3 1)).mpr h3
  simp only [Fintype.linearCombination_apply_single, one_smul, sweetSpot_quadratic_eq_chain, twoSiteGenerator_eq_chain] at c0 c3
  exact ⟨twoSiteMajorana_ne_zero 0, twoSiteMajorana_ne_zero 3,
    c0, c3, sweetSpot_pfaffian_zero t⟩

end
end InfoGeometry.Canonical.CARMajoranaFiniteBridge
