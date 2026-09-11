import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic
import InfoGeometry.Canonical.CyclotomicProjectorReadout
import InfoGeometry.Canonical.DiscretePowerGradeReadout
import InfoGeometry.Canonical.GradedMellinReadout
import InfoGeometry.Canonical.HypercomplexOneParameterFlows
import InfoGeometry.Canonical.KANFlowCompatibility

/-!
# Matrix Stage Trifactor Compatibility & Forwarding Bridge

This module acts as the canonical forwarding and compatibility bridge between the
stage-based matrix constructions and the four modular readout owners:

1. `CyclotomicProjectorReadout` — Fourier spectral decomposition and eigenprojectors.
2. `DiscretePowerGradeReadout` — Discrete power monoid homomorphisms $k \mapsto X^k$.
3. `GradedMellinReadout` — Graded submodule algebra decompositions $A = \bigoplus A_g$.
4. `HypercomplexOneParameterFlows` — 1-parameter group flows in $A^\times$ ($R_J, B_H, U_N$).
5. `KANFlowCompatibility` — Composite Iwasawa dynamical flow factorization in $\text{GL}_2(\mathbb{C})$.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixStageTrifactorReadouts

open Matrix
open scoped ComplexConjugate
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic
open InfoGeometry.Canonical.CyclotomicProjector
open InfoGeometry.Canonical.DiscretePowerGradeReadout
open InfoGeometry.Canonical.GradedMellinReadout
open InfoGeometry.Canonical.HypercomplexOneParameterFlows
open InfoGeometry.Canonical.KANFlowCompatibility

/-! ## 1. Forwarding Structures for Stage-Based Computations -/

/-- Structural interface for the Fourier cyclotomic projector readout of an operator $X \in A$. -/
structure FourierCyclotomicReadout2 {A : Type*} [Ring A] (X : A) where
  projPlus : A
  projMinus : A
  partition_unity : projPlus + projMinus = 1
  projPlus_sq : projPlus * projPlus = projPlus
  projMinus_sq : projMinus * projMinus = projMinus
  ortho_plus_minus : projPlus * projMinus = 0
  ortho_minus_plus : projMinus * projPlus = 0
  synthesis : projPlus - projMinus = X

/-- Structural interface for the Mellin discrete moment / grading power readout. -/
structure MellinGradeReadout2 {A : Type*} [Ring A] (X : A) where
  gradePower : ℕ → A
  grade_zero : gradePower 0 = 1
  grade_succ : ∀ k, gradePower (k + 1) = X * gradePower k
  grade_periodic2 : ∀ k, gradePower (k + 2) = gradePower k

/-- Structural interface for the Laplace continuous 1-parameter dynamical flow readout. -/
structure LaplaceFlowReadout {A : Type*} [Ring A] where
  flow : ℝ → A
  flow_zero : flow 0 = 1
  flow_add : ∀ s t : ℝ, flow (s + t) = flow s * flow t

/-! ## 2. Compatibility Instances -/

/-- Fourier cyclotomic readout instance for an involution $H^2 = 1$. -/
def hyperbolicFourierReadout (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    FourierCyclotomicReadout2 H where
  projPlus := projPlus2 H
  projMinus := projMinus2 H
  partition_unity := projPlus2_add_projMinus2 H
  projPlus_sq := projPlus2_sq H hH
  projMinus_sq := projMinus2_sq H hH
  ortho_plus_minus := projPlus2_mul_projMinus2 H hH
  ortho_minus_plus := projMinus2_mul_projPlus2 H hH
  synthesis := spectral_reconstruction_order2 H

/-- Mellin moment power readout instance for an involution $H^2 = 1$. -/
def hyperbolicMellinReadout (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    MellinGradeReadout2 H where
  gradePower k := if k % 2 = 0 then 1 else H
  grade_zero := by simp
  grade_succ k := by
    by_cases h : k % 2 = 0
    · have hk1 : (k + 1) % 2 = 1 := by omega
      have hk1_ne : (k + 1) % 2 ≠ 0 := by omega
      simp [h, hk1_ne]
    · have hk : k % 2 = 1 := by omega
      have hk1 : (k + 1) % 2 = 0 := by omega
      simp [h, hk1, hH]
  grade_periodic2 k := by
    have hmod : (k + 2) % 2 = k % 2 := by omega
    by_cases h : k % 2 = 0
    · have h2 : (k + 2) % 2 = 0 := by omega
      simp [h, h2]
    · have h2 : (k + 2) % 2 ≠ 0 := by omega
      simp [h]

/-- 🏆 THEOREM: The Hyperbolic Boost Laplace Flow $\Phi_H(t)$ delegated to `HypercomplexOneParameterFlows`. -/
def hyperbolicLaplaceFlow (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    LaplaceFlowReadout (A := Matrix (Fin 2) (Fin 2) ℂ) where
  flow t := (hyperbolicUnit H hH t : Matrix (Fin 2) (Fin 2) ℂ)
  flow_zero := by
    have hA : hyperbolicUnit H hH 0 = 1 := by apply Units.ext; simp [hyperbolicUnit, hyperbolicMat]
    rw [hA]
    rfl
  flow_add s t := by
    have hmul := (hyperbolicFlow_of_sq_eq_one H hH).flowHom.map_mul
      (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)
    exact congrArg Units.val hmul

/-- 🏆 THEOREM: The Elliptic Rotation Laplace Flow $\Phi_J(t)$ delegated to `HypercomplexOneParameterFlows`. -/
def ellipticLaplaceFlow (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) :
    LaplaceFlowReadout (A := Matrix (Fin 2) (Fin 2) ℂ) where
  flow t := (ellipticUnit J hJ t : Matrix (Fin 2) (Fin 2) ℂ)
  flow_zero := by
    have hK : ellipticUnit J hJ 0 = 1 := by apply Units.ext; simp [ellipticUnit, ellipticMat]
    rw [hK]
    rfl
  flow_add s t := by
    have hmul := (ellipticFlow_of_sq_eq_neg_one J hJ).flowHom.map_mul
      (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)
    exact congrArg Units.val hmul

/-- 🏆 THEOREM: The Parabolic Shear Laplace Flow $\Phi_N(t)$ delegated to `HypercomplexOneParameterFlows`. -/
def parabolicLaplaceFlow (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) :
    LaplaceFlowReadout (A := Matrix (Fin 2) (Fin 2) ℂ) where
  flow t := (parabolicUnit N hN t : Matrix (Fin 2) (Fin 2) ℂ)
  flow_zero := by
    have hN' : parabolicUnit N hN 0 = 1 := by apply Units.ext; simp [parabolicUnit, parabolicMat]
    rw [hN']
    rfl
  flow_add s t := by
    have hmul := (parabolicFlow_of_sq_eq_zero N hN).flowHom.map_mul
      (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)
    exact congrArg Units.val hmul

/-! ## 3. Trifactor KAN Dynamical Synthesis -/

/-- 🏆 THEOREM: The composite KAN dynamical flow factored as $\Phi_K(t) \cdot \Phi_A(t) \cdot \Phi_N(t)$. -/
def trifactorKANFlow
    (J H N : Matrix (Fin 2) (Fin 2) ℂ)
    (hJ : J * J = -1) (hH : H * H = 1) (hN : N * N = 0) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  kanCompositeFlow J H N hJ hH hN t t t

/-- At $t = 0$, the composite KAN flow is the identity matrix. -/
@[simp]
theorem trifactorKANFlow_zero
    (J H N : Matrix (Fin 2) (Fin 2) ℂ)
    (hJ : J * J = -1) (hH : H * H = 1) (hN : N * N = 0) :
    trifactorKANFlow J H N hJ hH hN 0 = 1 := by
  dsimp [trifactorKANFlow]
  exact kanCompositeFlow_zero J H N hJ hH hN

end InfoGeometry.Canonical.MatrixStageTrifactorReadouts
