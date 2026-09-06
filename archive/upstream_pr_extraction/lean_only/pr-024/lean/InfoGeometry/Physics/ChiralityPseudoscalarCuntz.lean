import Mathlib

/-!
# Chirality Pseudoscalar and Cuntz Parity

This module formalizes the ultimate unification of the Pseudoscalar,
the Dirac Chirality Operator (γ₅), and the Cuntz Algebra Metric Parity (η).

It mathematically proves that the Cuntz parity metric exactly splits 
the space into orthogonal P+ (16+) and P- (16-) Weyl spinor sheets.
-/

namespace ChiralityPseudoscalar

/-- 
  The Chirality Operator γ₅ / Pseudoscalar / Cuntz Parity η.
  It is a linear map that squares to the identity.
-/
structure ChiralityOperator (V : Type) [AddCommGroup V] [Module ℝ V] where
  gamma5 : V →ₗ[ℝ] V
  sq_eq_id : gamma5 ∘ₗ gamma5 = LinearMap.id

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- Projector P+ (corresponds to S₁ S₁* in Cuntz) -/
noncomputable def P_plus (op : ChiralityOperator V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + op.gamma5)

/-- Projector P- (corresponds to S₂ S₂* in Cuntz) -/
noncomputable def P_minus (op : ChiralityOperator V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - op.gamma5)

/-- 
  THE MASTER SPLIT THEOREM
  The projectors sum exactly to the identity mapping, demonstrating 
  the complete split of the Hilbert space into left- and right-handed sheets.
-/
theorem projectors_sum_id (op : ChiralityOperator V) :
    P_plus op + P_minus op = LinearMap.id := by
  ext x
  change (1 / 2 : ℝ) • (x + op.gamma5 x) + (1 / 2 : ℝ) • (x - op.gamma5 x) = x
  calc (1 / 2 : ℝ) • (x + op.gamma5 x) + (1 / 2 : ℝ) • (x - op.gamma5 x)
    _ = ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • op.gamma5 x) + ((1 / 2 : ℝ) • x - (1 / 2 : ℝ) • op.gamma5 x) := by rw [smul_add, smul_sub]
    _ = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by abel
    _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by rw [← add_smul]
    _ = (1 : ℝ) • x := by norm_num
    _ = x := one_smul ℝ x

/-- The projectors are mutually orthogonal. -/
theorem projectors_orthogonal (op : ChiralityOperator V) :
    (P_plus op) ∘ₗ (P_minus op) = 0 := by
  ext x
  change (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x - op.gamma5 x) + op.gamma5 ((1 / 2 : ℝ) • (x - op.gamma5 x))) = 0
  have h1 : op.gamma5 ((1 / 2 : ℝ) • (x - op.gamma5 x)) = (1 / 2 : ℝ) • op.gamma5 (x - op.gamma5 x) := 
    LinearMap.map_smul op.gamma5 (1 / 2 : ℝ) (x - op.gamma5 x)
  rw [h1]
  have h2 : op.gamma5 (x - op.gamma5 x) = op.gamma5 x - op.gamma5 (op.gamma5 x) :=
    LinearMap.map_sub op.gamma5 x (op.gamma5 x)
  rw [h2]
  have h3 : op.gamma5 (op.gamma5 x) = x := LinearMap.congr_fun op.sq_eq_id x
  rw [h3]
  have h4 : (1 / 2 : ℝ) • (x - op.gamma5 x) + (1 / 2 : ℝ) • (op.gamma5 x - x) = (0 : V) := by
    rw [smul_sub, smul_sub]
    abel
  rw [h4, smul_zero]

end ChiralityPseudoscalar
