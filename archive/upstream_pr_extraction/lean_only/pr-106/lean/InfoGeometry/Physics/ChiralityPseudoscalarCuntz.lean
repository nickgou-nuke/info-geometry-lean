import Mathlib.Tactic

/-!
# Involutive chirality-operator projectors

This module proves elementary projector identities for a supplied real-linear
involution `gamma5`.  It does not construct Cuntz parity, Dirac chirality,
Weyl spinor sheets, or a physical unification theorem.
-/

namespace ChiralityPseudoscalar

/-- 
  The Chirality Operator γ₅ / Pseudoscalar / Cuntz Parity η.
  It is a linear map that squares to the identity.
-/
abbrev ChiralityOperator (V : Type) [AddCommGroup V] [Module ℝ V] :=
  {gamma5 : V →ₗ[ℝ] V // gamma5 ∘ₗ gamma5 = LinearMap.id}

abbrev ChiralityOperator.gamma5 {V : Type} [AddCommGroup V] [Module ℝ V]
    (op : ChiralityOperator V) : V →ₗ[ℝ] V := op.1

abbrev ChiralityOperator.sq_eq_id {V : Type} [AddCommGroup V] [Module ℝ V]
    (op : ChiralityOperator V) : op.gamma5 ∘ₗ op.gamma5 = LinearMap.id := op.2

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The `+` projector associated to a supplied involution. -/
noncomputable def P_plus (op : ChiralityOperator V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + op.gamma5)

/-- The `-` projector associated to a supplied involution. -/
noncomputable def P_minus (op : ChiralityOperator V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - op.gamma5)

/-- 
  The two projectors sum to the identity map.
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
