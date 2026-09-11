import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularSurprisalHestenesIntertwiner

/-!
# Finite Dirichlet Shift Operator Hestenes Bridge

This file transports the real shift operator algebra into the Hestenes flow 
via the intertwiner $J$. 

By leveraging the real-linearity of $J$, we can transport finite linear 
combinations of log-shifts (and specifically Dirichlet sums involving 
arithmetic coefficients like $\mathbf{1}, \mu, L, \Lambda$) into the 
Hestenes realization without invoking complex analytical functional calculus.
-/

namespace InfoGeometry.Canonical.FiniteDirichletShiftOperatorHestenesBridge

open InfoGeometry.Canonical.ModularSurprisalHestenesIntertwiner

variable {A M : Type*} 
  [AddCommGroup A] [Module ℝ A] 
  [AddCommGroup M] [Module ℝ M] 

/-- A simplified shift operator structure for the real algebra. -/
structure RealShiftDatum (A : Type*) [AddCommGroup A] [Module ℝ A] where
  T : ℝ → (A →ₗ[ℝ] A)

/-- Hestenes flow structure on M. -/
structure RealHestenesFlowDatum (M : Type*) [AddCommGroup M] [Module ℝ M] where
  realFlow : ℝ → (M →ₗ[ℝ] M)

/-- The intertwiner datum for real shifts. -/
structure RealIntertwinerDatum (A M : Type*) [AddCommGroup A] [Module ℝ A] [AddCommGroup M] [Module ℝ M] 
    (D_A : RealShiftDatum A) (D_M : RealHestenesFlowDatum M) where
  J : A →ₗ[ℝ] M
  flow_intertwining : ∀ u : ℝ, J ∘ₗ (D_A.T u) = (D_M.realFlow u) ∘ₗ J

variable {D_A : RealShiftDatum A} {D_M : RealHestenesFlowDatum M} 
  (W : RealIntertwinerDatum A M D_A D_M)

/-- Generic finite real shift-sum transport (Pointwise). -/
theorem finiteShiftSum_hestenes_intertwining {ι : Type*} (s : Finset ι) 
    (a : ι → ℝ) (u : ι → ℝ) (f : A) :
    W.J (∑ i ∈ s, a i • D_A.T (u i) f) = ∑ i ∈ s, a i • D_M.realFlow (u i) (W.J f) := by
  -- J is R-linear, so it distributes over finite sums and scalar multiplication
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smul]
  have h_intertwine : W.J (D_A.T (u i) f) = D_M.realFlow (u i) (W.J f) := by
    have h := LinearMap.ext_iff.mp (W.flow_intertwining (u i)) f
    exact h
  rw [h_intertwine]

noncomputable section

/-- Generic finite real shift-sum transport (Operator Equality). -/
theorem finiteShiftOperatorSum_intertwining {ι : Type*} (s : Finset ι) 
    (a : ι → ℝ) (u : ι → ℝ) :
    W.J ∘ₗ (∑ i ∈ s, a i • D_A.T (u i)) = (∑ i ∈ s, a i • D_M.realFlow (u i)) ∘ₗ W.J := by
  ext f
  dsimp
  rw [LinearMap.sum_apply]
  -- Evaluate LHS
  have h_lhs : W.J (∑ i ∈ s, (a i • D_A.T (u i)) f) = ∑ i ∈ s, a i • W.J (D_A.T (u i) f) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact LinearMap.map_smul W.J _ _
  -- Using pointwise
  have h_pt := finiteShiftSum_hestenes_intertwining W s a u f
  -- Adjusting to match types for rewriting
  have h_lhs_rewrite : (∑ i ∈ s, (a i • D_A.T (u i)) f) = ∑ i ∈ s, a i • D_A.T (u i) f := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have h_rhs_rewrite : (∑ i ∈ s, (a i • D_M.realFlow (u i))) (W.J f) = ∑ i ∈ s, a i • D_M.realFlow (u i) (W.J f) := by
    exact LinearMap.sum_apply _ _ _
  rw [h_lhs_rewrite]
  rw [h_pt]
  exact h_rhs_rewrite.symm

/-- Real finite Dirichlet shift operator on A. -/
def realFiniteDirichletShiftOperator (D_A : RealShiftDatum A) (s : Finset ℕ) (a : ℕ → ℝ) : A →ₗ[ℝ] A :=
  ∑ n ∈ s, a n • D_A.T (Real.log n)

/-- Hestenes finite Dirichlet operator on M. -/
def hestenesFiniteDirichletOperator (D_M : RealHestenesFlowDatum M) (s : Finset ℕ) (a : ℕ → ℝ) : M →ₗ[ℝ] M :=
  ∑ n ∈ s, a n • D_M.realFlow (Real.log n)

/-- CAPSTONE 1: Finite Dirichlet transport (Operator level). -/
theorem finiteDirichlet_hestenes_intertwining (s : Finset ℕ) (a : ℕ → ℝ) :
    W.J ∘ₗ realFiniteDirichletShiftOperator D_A s a = hestenesFiniteDirichletOperator D_M s a ∘ₗ W.J := by
  unfold realFiniteDirichletShiftOperator hestenesFiniteDirichletOperator
  exact finiteShiftOperatorSum_intertwining W s a (fun n => Real.log n)

/-- Finite Dirichlet transport (Pointwise level). -/
theorem finiteDirichlet_hestenes_intertwining_apply (s : Finset ℕ) (a : ℕ → ℝ) (f : A) :
    W.J (realFiniteDirichletShiftOperator D_A s a f) = hestenesFiniteDirichletOperator D_M s a (W.J f) := by
  have h := finiteDirichlet_hestenes_intertwining W s a
  exact LinearMap.ext_iff.mp h f

end

end InfoGeometry.Canonical.FiniteDirichletShiftOperatorHestenesBridge
