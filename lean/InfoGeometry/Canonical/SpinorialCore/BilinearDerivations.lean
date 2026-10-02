import Mathlib

/-!
# Derivations of an arbitrary bilinear product

No associativity is assumed for the product. The derivations form a native
Lie subalgebra of the associative endomorphism algebra. This does not identify
that Lie algebra with a particular real form or choose a particle multiplet.
-/

namespace InfoGeometry.Canonical.SpinorialCore.DerivationAction

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Leibniz operators for a bilinear, possibly nonassociative product. -/
def IsDerivation (μ : V →ₗ[R] V →ₗ[R] V) (D : Module.End R V) : Prop :=
  ∀ x y, D (μ x y) = μ (D x) y + μ x (D y)

theorem commutator_leibniz (μ : V →ₗ[R] V →ₗ[R] V)
    (D E : Module.End R V) (hD : IsDerivation μ D) (hE : IsDerivation μ E) :
    IsDerivation μ ⁅D, E⁆ := by
  intro x y
  change D (E (μ x y)) - E (D (μ x y)) =
    μ (D (E x) - E (D x)) y + μ x (D (E y) - E (D y))
  rw [hE x y, hD x y, map_add, map_add,
    hD (E x) y, hD x (E y), hE (D x) y, hE x (D y)]
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- Native Lie carrier; the bracket is the endomorphism commutator. -/
def derivations (μ : V →ₗ[R] V →ₗ[R] V) : LieSubalgebra R (Module.End R V) where
  carrier := {D | IsDerivation μ D}
  zero_mem' := by
    intro x y
    simp
  add_mem' := by
    intro D E hD hE x y
    change D (μ x y) + E (μ x y) = μ (D x + E x) y + μ x (D y + E y)
    rw [hD x y, hE x y]
    simp only [map_add, LinearMap.add_apply]
    abel
  smul_mem' := by
    intro a D hD x y
    change a • D (μ x y) = μ (a • D x) y + μ x (a • D y)
    rw [hD x y]
    simp [smul_add]
  lie_mem' := fun {D E} hD hE => commutator_leibniz μ D E hD hE

/-- The canonical representation on the original module. -/
def representation (μ : V →ₗ[R] V →ₗ[R] V) :
    derivations μ →ₗ⁅R⁆ Module.End R V :=
  (derivations μ).incl

theorem representation_faithful (μ : V →ₗ[R] V →ₗ[R] V) :
    Function.Injective (representation μ) := by
  intro D E h
  exact Subtype.ext h

/-- A cut stabilizer is again a Lie algebra, without a guessed classification. -/
def cutStabilizer (μ : V →ₗ[R] V →ₗ[R] V) (p : V) :
    LieSubalgebra R (Module.End R V) where
  carrier := {D | D ∈ derivations μ ∧ D p = 0}
  zero_mem' := ⟨(derivations μ).zero_mem, rfl⟩
  add_mem' := by
    intro D E hD hE
    exact ⟨(derivations μ).add_mem hD.1 hE.1,
      by change D p + E p = 0; rw [hD.2, hE.2, add_zero]⟩
  smul_mem' := by
    intro a D hD
    exact ⟨(derivations μ).smul_mem a hD.1,
      by change a • D p = 0; rw [hD.2, smul_zero]⟩
  lie_mem' := by
    intro D E hD hE
    refine ⟨(derivations μ).lie_mem hD.1 hE.1, ?_⟩
    change D (E p) - E (D p) = 0
    simp [hD.2, hE.2]

/-- Differentiating an actual idempotent gives its linearized cut equation. -/
theorem linearized_idempotent (μ : V →ₗ[R] V →ₗ[R] V)
    (p : V) (hp : μ p p = p) (D : derivations μ) :
    D.val p = μ (D.val p) p + μ p (D.val p) := by
  simpa only [hp] using D.property p p

end InfoGeometry.Canonical.SpinorialCore.DerivationAction
