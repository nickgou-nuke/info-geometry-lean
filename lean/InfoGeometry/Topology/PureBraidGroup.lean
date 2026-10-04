import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group

/-!
# Consequences of the three-strand pure-braid cyclic relation

This file records group-theoretic consequences of the cyclic relations on
three elements. It does not construct a presentation of the pure braid group
or assert that arbitrary triples in a group are pure braid generators.
-/

namespace ArtinPureBraid

variable {G : Type*} [Group G]

/-- Conjugation by a product, simplified using the group axioms. -/
theorem conj_by_mul_self (Y Z : G) :
    (Y * Z)⁻¹ * Y * (Y * Z) = Z⁻¹ * Y * Z := by
  group

/-- If `a` and `b` commute, then `b` commutes with `a⁻¹`. -/
lemma comm_inv_of_comm {a b : G} (h : a * b = b * a) :
    b * a⁻¹ = a⁻¹ * b := by
  calc
    b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
    _ = a⁻¹ * (b * a) * a⁻¹ := by rw [h]
    _ = a⁻¹ * b := by group

/-- Conjugations by commuting elements commute as automorphisms. -/
lemma conjugate_conjugate_of_comm (a b x : G) (h : a * b = b * a) :
    a⁻¹ * (b⁻¹ * x * b) * a = b⁻¹ * (a⁻¹ * x * a) * b := by
  have hinv : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
    simpa only [mul_inv_rev] using congrArg (fun q : G => q⁻¹) h.symm
  calc
    a⁻¹ * (b⁻¹ * x * b) * a = (a⁻¹ * b⁻¹) * x * (b * a) := by group
    _ = (b⁻¹ * a⁻¹) * x * (a * b) := by rw [hinv, h.symm]
    _ = b⁻¹ * (a⁻¹ * x * a) * b := by group

variable (X Y Z : G)

/-- The third cyclic equality follows from the first two. -/
theorem cyclic_three
    (h₁ : X * Y * Z = Y * Z * X)
    (h₂ : Y * Z * X = Z * X * Y) :
    Z * X * Y = X * Y * Z := by
  calc
    Z * X * Y = Y * Z * X := h₂.symm
    _ = X * Y * Z := h₁.symm

/-- In the cyclic triple, `X` commutes with `Y * Z`. -/
theorem comm_X_YZ
    (h₁ : X * Y * Z = Y * Z * X) :
    X * (Y * Z) = (Y * Z) * X := by
  simpa [mul_assoc] using h₁

/-- In the cyclic triple, `Y` commutes with `Z * X`. -/
theorem comm_Y_ZX
    (h₂ : Y * Z * X = Z * X * Y) :
    Y * (Z * X) = (Z * X) * Y := by
  simpa [mul_assoc] using h₂

/-- In the cyclic triple, `Z` commutes with `X * Y`. -/
theorem comm_Z_XY
    (h₁ : X * Y * Z = Y * Z * X)
    (h₂ : Y * Z * X = Z * X * Y) :
    Z * (X * Y) = (X * Y) * Z := by
  simpa [mul_assoc] using cyclic_three X Y Z h₁ h₂

/-- The common cyclic product `X * Y * Z` commutes with each of its three
factors. Thus the cyclic identities make it central in the subgroup generated
by `X`, `Y`, and `Z`. -/
theorem cyclic_product_centralizes
    (h₁ : X * Y * Z = Y * Z * X)
    (h₂ : Y * Z * X = Z * X * Y) :
    (X * Y * Z) * X = X * (X * Y * Z) ∧
    (X * Y * Z) * Y = Y * (X * Y * Z) ∧
    (X * Y * Z) * Z = Z * (X * Y * Z) := by
  have hX := comm_X_YZ X Y Z h₁
  have hY := comm_Y_ZX X Y Z h₂
  have hZ := comm_Z_XY X Y Z h₁ h₂
  constructor
  · calc
      (X * Y * Z) * X = X * ((Y * Z) * X) := by group
      _ = X * (X * (Y * Z)) := by rw [← hX]
      _ = X * (X * Y * Z) := by group
  constructor
  · calc
      (X * Y * Z) * Y = (Y * Z * X) * Y := by rw [h₁]
      _ = Y * ((Z * X) * Y) := by group
      _ = Y * (Y * (Z * X)) := by rw [← hY]
      _ = Y * (X * Y * Z) := by rw [h₁]; group
  · calc
      (X * Y * Z) * Z = (Z * X * Y) * Z := by rw [h₁, h₂]
      _ = Z * ((X * Y) * Z) := by group
      _ = Z * (Z * (X * Y)) := by rw [← hZ]
      _ = Z * (X * Y * Z) := by rw [h₁, h₂]; group

/-- The cyclic equalities are equivalent to the three product-commutation
identities. -/
theorem cyclic_iff_product_commutation :
    (X * Y * Z = Y * Z * X ∧ Y * Z * X = Z * X * Y) ↔
      (X * (Y * Z) = (Y * Z) * X ∧
       Y * (Z * X) = (Z * X) * Y ∧
       Z * (X * Y) = (X * Y) * Z) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨comm_X_YZ X Y Z h₁, comm_Y_ZX X Y Z h₂,
      comm_Z_XY X Y Z h₁ h₂⟩
  · rintro ⟨h₁, h₂, _h₃⟩
    exact ⟨by simpa [mul_assoc] using h₁,
      by simpa [mul_assoc] using h₂⟩

/-- Reduced nonlinear crossing relation for the middle generator. -/
theorem crossing_Y
    (h₂ : Y * Z * X = Z * X * Y) :
    X * Y * X⁻¹ = Z⁻¹ * Y * Z := by
  have hcomm := comm_Y_ZX X Y Z h₂
  calc
    X * Y * X⁻¹ = Z⁻¹ * ((Z * X) * Y) * X⁻¹ := by group
    _ = Z⁻¹ * (Y * (Z * X)) * X⁻¹ := by rw [← hcomm]
    _ = Z⁻¹ * Y * Z := by group

/-- Product-conjugation form of `crossing_Y`. -/
theorem crossing_Y_factored
    (h₂ : Y * Z * X = Z * X * Y) :
    X * Y * X⁻¹ = (Y * Z)⁻¹ * Y * (Y * Z) := by
  rw [conj_by_mul_self]
  exact crossing_Y X Y Z h₂

/-- Inverse-conjugation form of the middle crossing relation. -/
theorem crossing_Y_inv
    (h₁ : X * Y * Z = Y * Z * X)
    (h₂ : Y * Z * X = Z * X * Y) :
    X⁻¹ * Y * X = (Y * Z) * Y * (Y * Z)⁻¹ := by
  have hcomm : X * (Y * Z) = (Y * Z) * X := comm_X_YZ X Y Z h₁
  have hcross : X * Y * X⁻¹ = (Y * Z)⁻¹ * Y * (Y * Z) :=
    crossing_Y_factored X Y Z h₂
  have hconj := conjugate_conjugate_of_comm X (Y * Z) Y hcomm
  calc
    X⁻¹ * Y * X = (Y * Z) * ((Y * Z)⁻¹ * (X⁻¹ * Y * X) * (Y * Z)) * (Y * Z)⁻¹ := by group
    _ = (Y * Z) * (X⁻¹ * ((Y * Z)⁻¹ * Y * (Y * Z)) * X) * (Y * Z)⁻¹ := by rw [← hconj]
    _ = (Y * Z) * (X⁻¹ * (X * Y * X⁻¹) * X) * (Y * Z)⁻¹ := by rw [hcross]
    _ = (Y * Z) * Y * (Y * Z)⁻¹ := by group

/-- The crossing relation for `Z`, derived from its commutation with `X * Y`. -/
theorem crossing_Z
    (h₁ : X * Y * Z = Y * Z * X)
    (h₂ : Y * Z * X = Z * X * Y) :
    X⁻¹ * Z * X = Y * Z * Y⁻¹ := by
  have hcomm := comm_Z_XY X Y Z h₁ h₂
  calc
    X⁻¹ * Z * X = X⁻¹ * (Z * (X * Y)) * Y⁻¹ := by group
    _ = X⁻¹ * ((X * Y) * Z) * Y⁻¹ := by rw [hcomm]
    _ = Y * Z * Y⁻¹ := by group

/-- The crossing relation for `X`, derived from its commutation with `Y * Z`. -/
theorem crossing_X
    (h₁ : X * Y * Z = Y * Z * X) :
    Y⁻¹ * X * Y = Z * X * Z⁻¹ := by
  have hcomm := comm_X_YZ X Y Z h₁
  calc
    Y⁻¹ * X * Y = Y⁻¹ * (X * (Y * Z)) * Z⁻¹ := by group
    _ = Y⁻¹ * ((Y * Z) * X) * Z⁻¹ := by rw [hcomm]
    _ = Z * X * Z⁻¹ := by group

end ArtinPureBraid
