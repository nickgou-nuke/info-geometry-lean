import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Basic

/-!
# Concrete one-dimensional GNS representation as complex bounded operators

This file is the Lean translation target for the first executable GNS/CBO
corollary layer suggested by the AFP entries
`Gelfand_Naimark_Segal` and `Complex_Bounded_Operators`.

It proves the GNS theorem chain in the base C*-algebra `ℂ`:

* state `ω z = z`;
* involution `star`;
* cyclic vector `Ω = 1`;
* representation `π z` is the bounded operator `x ↦ z * x`.

The bounded-operator carrier is the existing CBO adapter
`ComplexBoundedOperators.Basic.CBO = ContinuousLinearMap` over `ℂ`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSConcrete

open scoped InnerProductSpace

abbrev GNSHilbert := ℂ
abbrev GNSOp := Basic.CBO GNSHilbert GNSHilbert

/-- The vector state from the GNS construction, specialized to `ℂ`. -/
def omega (z : ℂ) : ℂ := z

/-- The C*-involution on the algebra `ℂ`. -/
def involution (z : ℂ) : ℂ := star z

/-- The cyclic vector. -/
def Omega : GNSHilbert := 1

/-- The concrete bounded-operator representation: scalar multiplication by `z`. -/
def pi (z : ℂ) : GNSOp := z • Basic.id GNSHilbert

/-- The concrete operator `π z` acts by multiplication by `z`. -/
lemma pi_apply (z x : ℂ) :
    pi z x = z * x := by
  simp [pi, Basic.id]

/-- The cyclic vector coefficient recovers the state: `⟨Ω, π(u)Ω⟩ = ω(u)`. -/
lemma gns_vector_state_recovers_state (u : ℂ) :
    inner ℂ Omega (pi u Omega) = omega u := by
  simp [Omega, omega, pi_apply]

/-- Every vector in the one-dimensional Hilbert space is generated from the
cyclic vector by some algebra element. -/
lemma gns_cyclic_property (x : GNSHilbert) :
    ∃ u : ℂ, pi u Omega = x := by
  refine ⟨x, ?_⟩
  simp [Omega, pi_apply]

/-- The concrete cyclic orbit is the whole Hilbert space. -/
lemma gns_cyclic_set_eq_univ :
    {x : GNSHilbert | ∃ u : ℂ, pi u Omega = x} = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact gns_cyclic_property x

/-- `π` preserves addition. -/
lemma gns_rep_add (a b : ℂ) :
    pi (a + b) = pi a + pi b := by
  apply ContinuousLinearMap.ext
  intro x
  simp [pi_apply]
  ring

/-- `π` preserves multiplication as operator composition. -/
lemma gns_rep_mult (a b : ℂ) :
    pi (a * b) = Basic.comp (pi a) (pi b) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [pi_apply, Basic.comp_apply]
  ring

/-- `π` preserves complex scalar multiplication. -/
lemma gns_rep_scale (c a : ℂ) :
    pi (c • a) = c • pi a := by
  apply ContinuousLinearMap.ext
  intro x
  simp [pi_apply]
  ring

/-- `π(1)` is the identity bounded operator. -/
lemma gns_rep_one :
    pi 1 = Basic.id GNSHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  simp [pi_apply, Basic.id]

/-- The product matrix coefficient is the state of the product. -/
lemma gns_product_state_as_cyclic_matrix_coefficient (a b : ℂ) :
    inner ℂ Omega (pi (a * b) Omega) = omega (a * b) := by
  exact gns_vector_state_recovers_state (a * b)

/-- Squares in the algebra map to operator squares. -/
lemma gns_square_is_operator_square (a : ℂ) :
    pi (a * a) = Basic.comp (pi a) (pi a) := by
  exact gns_rep_mult a a

/-- Positive algebraic squares map to composed concrete operators. -/
lemma gns_positive_square_is_operator_square (a : ℂ) :
    pi (involution a * a) = Basic.comp (pi (involution a)) (pi a) := by
  exact gns_rep_mult (involution a) a

/-- The adjoint of multiplication by `a` is multiplication by `star a`. -/
lemma adjoint_pi_eq_smul_id (a : ℂ) :
    ContinuousLinearMap.adjoint (pi a) = star a • Basic.id GNSHilbert := by
  rw [pi]
  rw [map_smulₛₗ]
  simp [Basic.id]

/-- Pointwise form of the adjoint of multiplication by `a`. -/
lemma adjoint_pi_apply (a x : ℂ) :
    (ContinuousLinearMap.adjoint (pi a)) x = star a * x := by
  rw [adjoint_pi_eq_smul_id]
  simp [Basic.id]

/-- The concrete representation intertwines involution and Hilbert adjoint. -/
lemma gns_rep_involution (a : ℂ) :
    pi (involution a) = ContinuousLinearMap.adjoint (pi a) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [adjoint_pi_apply]
  simp [pi_apply, involution]

/-- A self-adjoint scalar is sent to a self-adjoint bounded operator. -/
lemma gns_self_adjoint_element_gives_self_adjoint_operator
    (a : ℂ) (ha : involution a = a) :
    ContinuousLinearMap.adjoint (pi a) = pi a := by
  rw [← gns_rep_involution]
  rw [ha]

/-- Positive algebraic squares map to `π(a)† ∘ π(a)`. -/
lemma gns_positive_square_is_adjoint_comp (a : ℂ) :
    pi (involution a * a) =
      Basic.comp (ContinuousLinearMap.adjoint (pi a)) (pi a) := by
  rw [← gns_rep_involution]
  exact gns_positive_square_is_operator_square a

/-- The cyclic coefficient of a positive algebraic square recovers its state value. -/
lemma gns_state_on_positive_square_as_cyclic_coefficient (a : ℂ) :
    inner ℂ Omega (pi (involution a * a) Omega) = omega (involution a * a) := by
  exact gns_vector_state_recovers_state (involution a * a)

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSConcrete
