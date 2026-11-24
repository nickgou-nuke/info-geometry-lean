/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.CompatibleEndomorphisms
import InfoGeometry.Arithmetic.FiniteEulerLogDerivative

/-!
# Compatible derivations on an algebraic direct limit

A family of native derivations which intertwines the algebra transition maps
induces a native derivation on Mathlib's root `DirectLimit`. Its underlying
linear map is the compatible endomorphism lift; the Leibniz rule is proved
after moving two elements to one finite stage.

`InfoGeometry.Modular.ModularColimitDerivation` separately treats possibly
noncommutative rings through a supplied cocone with exact representability and
eventual-equality hypotheses. Here the carrier and its quotient are the native
direct limit itself, and the stage operators are Mathlib `Derivation`s on
commutative algebras. We therefore reuse the native lift without importing that
owner's cocone structures or finite-spin dependency. The uniqueness theorem
identifies any native derivation with the same representative values.

Unit logarithmic expressions are natural under an intertwining algebra map.
Consequently each finite Euler-product identity, with its exact remainder,
holds after applying a canonical direct-limit map. No topology, infinite
Euler product, or vanishing of the remainder is asserted.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace InfoGeometry.Categorical.CompatibleDerivations

section Naturality

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

/-- An algebra map intertwining two derivations preserves the logarithmic
expression on units. No logarithm or inverse of a nonunit is used. -/
theorem map_units_logDeriv (φ : A →ₐ[k] B)
    (DA : Derivation k A A) (DB : Derivation k B B)
    (hD : ∀ x, DB (φ x) = φ (DA x)) (u : Aˣ) :
    φ ((u⁻¹).val * DA u.val) =
      ((Units.map φ.toMonoidHom u)⁻¹).val *
        DB (Units.map φ.toMonoidHom u).val := by
  change φ ((u⁻¹).val * DA u.val) = φ (u⁻¹).val * DB (φ u.val)
  rw [map_mul, hD]

end Naturality

section DirectLimit

variable {k I : Type*} [CommRing k] [Preorder I] [Nonempty I]
variable [IsDirectedOrder I]
variable {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
variable (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
variable [DirectedSystem A (f · · ·)]
variable (D : ∀ i, Derivation k (A i) (A i))
variable (hD : ∀ i j hij x, D j (f i j hij x) = f i j hij (D i x))

/-- The compatible stage derivations induce a native derivation on the
algebraic direct limit. The Leibniz law follows at a common representative. -/
def colimitDerivation :
    Derivation k (_root_.DirectLimit A f) (_root_.DirectLimit A f) := by
  let d := CompatibleEndomorphisms.liftEnd f (fun i => (D i).toLinearMap) hD
  refine Derivation.mk' d ?_
  intro x y
  simp only [smul_eq_mul]
  refine DirectLimit.induction₂ f (fun i a b => ?_) x y
  change d (DirectLimit.Algebra.of A f i a * DirectLimit.Algebra.of A f i b) =
    DirectLimit.Algebra.of A f i a * d (DirectLimit.Algebra.of A f i b) +
      DirectLimit.Algebra.of A f i b * d (DirectLimit.Algebra.of A f i a)
  have hd (z : A i) :
      d (DirectLimit.Algebra.of A f i z) = DirectLimit.Algebra.of A f i (D i z) :=
    rfl
  rw [← map_mul (DirectLimit.Algebra.of A f i) a b, hd, (D i).leibniz]
  simp only [smul_eq_mul, map_add, map_mul, hd]

/-- The descended derivation has exactly the prescribed value at each stage. -/
@[simp]
theorem colimitDerivation_of (i : I) (x : A i) :
    colimitDerivation f D hD (DirectLimit.Algebra.of A f i x) =
      DirectLimit.Algebra.of A f i (D i x) :=
  rfl

/-- Stage values determine the native direct-limit derivation uniquely. -/
theorem colimitDerivation_unique
    (Δ : Derivation k (_root_.DirectLimit A f) (_root_.DirectLimit A f))
    (hΔ : ∀ i x, Δ (DirectLimit.Algebra.of A f i x) =
      DirectLimit.Algebra.of A f i (D i x)) :
    Δ = colimitDerivation f D hD := by
  apply Derivation.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
      change Δ (DirectLimit.Algebra.of A f i x) =
        colimitDerivation f D hD (DirectLimit.Algebra.of A f i x)
      rw [hΔ, colimitDerivation_of]

/-- The logarithmic expression of an image unit is the image of its finite
stage logarithmic expression. Injectivity of the transition maps is unnecessary. -/
theorem units_logDeriv_of (i : I) (u : (A i)ˣ) :
    ((Units.map (DirectLimit.Algebra.of A f i).toMonoidHom u)⁻¹).val *
        colimitDerivation f D hD
          (Units.map (DirectLimit.Algebra.of A f i).toMonoidHom u).val =
      DirectLimit.Algebra.of A f i ((u⁻¹).val * D i u.val) := by
  exact (map_units_logDeriv (DirectLimit.Algebra.of A f i) (D i)
    (colimitDerivation f D hD) (colimitDerivation_of f D hD i) u).symm

/-- Every finite Euler product retains its exact finite prime-power remainder
in the algebraic direct limit. The product and truncation order remain finite. -/
theorem negative_units_logDeriv_eulerProduct_of_eq_sum_add_remainder
    {P : Type*} (i : I) (S : Finset P) (E : P → (A i)ˣ) (a ell : P → A i)
    (hEuler : ∀ p ∈ S, ((E p)⁻¹).val = 1 - a p)
    (hScale : ∀ p ∈ S, D i (a p) = -ell p * a p) (M : ℕ) :
    let φ := DirectLimit.Algebra.of A f i;
    let U := Units.map φ.toMonoidHom (∏ p ∈ S, E p);
    -((U⁻¹).val * colimitDerivation f D hD U.val) =
      φ (∑ p ∈ S, ((∑ j ∈ Finset.range M, ell p * a p ^ (j + 1)) +
        ell p * ((E p).val * a p ^ (M + 1)))) := by
  dsimp only
  rw [units_logDeriv_of, ← map_neg]
  exact congrArg (DirectLimit.Algebra.of A f i)
    (InfoGeometry.Arithmetic.FiniteEulerLogDerivative.negative_units_logDeriv_eulerProduct_eq_sum_add_remainder
      (D i) S E a ell hEuler hScale M)

end DirectLimit

end InfoGeometry.Categorical.CompatibleDerivations
