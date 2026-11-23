/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceBoundaryComplex
import InfoGeometry.Algebra.GradedNullconeAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Curved `ℤ/2`-graded differential algebras and their three curvature regimes

This module formalizes the bundled curved `ℤ/2`-graded differential algebra
`(A, α, ∂_F, h)` over a commutative ring `R`, where:

* `parity` (`α : A ≃ₐ[R] A`) is an involutive `R`-algebra parity automorphism (`α² = id`);
* `oddGen` (`F : A`) is an odd degree-1 generator (`α(F) = -F`);
* `diff` (`∂_F : Module.End R A`) is the graded inner differential
  `∂_F(x) = F * x - α(x) * F`;
* `curvature` (`h : A`) is `F * F`.

We prove the graded Leibniz rule, `∂_F² = [h, ·]`, Bianchi's identity `∂_F(h) = 0`,
and the exact centrality characterization `∂_F² = 0 ↔ h ∈ Subalgebra.center R A`.
We construct bridges from `GradedNullconeAlgebra.parityConj` (`ofParityConj`), from
`PeirceBoundaryComplex.differential` (`ofPeirce`), and from flat curved DGAs to
`CochainComplex (ModuleCat R) ℕ` (`toCochainComplex`).

We classify and witness all three curvature regimes (`CurvatureRegime`):
1. `flat` (`h = 0`), via directed Peirce corners (`ofPeirce10`, `ofPeirce01`) and
   `flatMat2DGA` on `M₂(ℝ)`.
2. `centralNonzero` (`h ≠ 0 ∧ IsCentral h`), via `centralMat2DGA` on `M₂(ℝ)` and
   `centralDoubledDGA` on `RealDoubledChiralKrein.EndH₂` (with `F = etaChiral`, `h = 1`).
3. `nonCentral` (`¬ IsCentral h`, equivalently `∂_F² ≠ 0`), via `nonCentralBlockDGA`
   on `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ` and transported `nonCentralMat4DGA`
   on `Matrix (Fin 4) (Fin 4) ℝ`.

Finally, we separate `∂_F` from the ordinary ungraded inner commutator derivation
`commutatorDeriv G x = G * x - x * G` (`commutatorDeriv_vs_curvedDiff`) and give the
concrete R5 witness `nilpotent_commutatorDeriv_sq_ne_zero` (`G² = 0 ∧ D_G² ≠ 0` while
`∂_G² = 0`). In particular, `ConnesSpectral.SpectralTriple.commutator` in
`InfoGeometry.Canonical.ConnesSpectralTripleBridge` (`PR #426`, untouched and not
imported here) is an ungraded commutator derivation `ST.dirac * f - f * ST.dirac`
with normed-algebra Lipschitz seminorm bounds, and is strictly distinct from the
`α`-twisted curved differential `∂_F`.
-/

universe uR uA

namespace InfoGeometry.Canonical.CurvedZ2GradedDGA

set_option linter.dupNamespace false

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Canonical.PeirceBoundaryComplex
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

section Core

/-- A curved `ℤ/2`-graded differential algebra `(A, α, F)` over a commutative ring `R`,
carrying only the foundational parity involution and odd generator; the differential
`diff`, curvature `curvature`, graded Leibniz rule, `diff ^ 2 = ad curvature`, and
Bianchi identity `diff curvature = 0` are derived rather than assumed. -/
structure CurvedZ2GradedDGA (R : Type uR) (A : Type uA)
    [CommRing R] [Ring A] [Algebra R A] where
  /-- Involutive `R`-algebra parity automorphism `α : A ≃ₐ[R] A`. -/
  parity : A ≃ₐ[R] A
  /-- Involution law `α(α(x)) = x`. -/
  parity_involutive : ∀ x : A, parity (parity x) = x
  /-- Odd degree-1 generator `F : A`. -/
  oddGen : A
  /-- Oddness condition `α(F) = -F`. -/
  oddGen_parity : parity oddGen = -oddGen

namespace CurvedZ2GradedDGA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

/-- Curvature element `h = F²`. -/
def curvature (D : CurvedZ2GradedDGA R A) : A :=
  D.oddGen * D.oddGen

/-- Graded inner differential `∂_F(x) = F * x - α(x) * F`. -/
def diff (D : CurvedZ2GradedDGA R A) : Module.End R A :=
  LinearMap.mulLeft R D.oddGen -
    (LinearMap.mulRight R D.oddGen).comp D.parity.toLinearEquiv.toLinearMap

@[simp] theorem diff_apply (D : CurvedZ2GradedDGA R A) (x : A) :
    D.diff x = D.oddGen * x - D.parity x * D.oddGen := rfl

/-- Even subspace predicate `α(x) = x`. -/
def IsEven (D : CurvedZ2GradedDGA R A) (x : A) : Prop :=
  D.parity x = x

/-- Odd subspace predicate `α(x) = -x`. -/
def IsOdd (D : CurvedZ2GradedDGA R A) (x : A) : Prop :=
  D.parity x = -x

/-- Centrality predicate in `A`. -/
def IsCentral (_D : CurvedZ2GradedDGA R A) (z : A) : Prop :=
  ∀ x : A, z * x = x * z

theorem isCentral_iff_mem_center (D : CurvedZ2GradedDGA R A) (z : A) :
    D.IsCentral z ↔ z ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

theorem isCentral_iff_commutes (D : CurvedZ2GradedDGA R A) (z : A) :
    D.IsCentral z ↔ ∀ x : A, z * x = x * z :=
  Iff.rfl

/-- The multiplicative identity is annihilated by `∂_F`. -/
theorem diff_one (D : CurvedZ2GradedDGA R A) : D.diff 1 = 0 := by
  simp only [diff_apply, map_one, mul_one, one_mul, sub_self]

/-- On `α`-even elements, `∂_F` reduces to the commutator `[F, x]`. -/
theorem diff_of_even (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsEven x) :
    D.diff x = D.oddGen * x - x * D.oddGen := by
  rw [diff_apply, hx]

theorem diff_of_even_eq_ad (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsEven x) :
    D.diff x = LieAlgebra.ad R A D.oddGen x := by
  rw [diff_of_even D hx]
  rfl

/-- On `α`-odd elements, `∂_F` reduces to the anticommutator `{F, x}`. -/
theorem diff_of_odd (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsOdd x) :
    D.diff x = D.oddGen * x + x * D.oddGen := by
  rw [diff_apply, hx, neg_mul, sub_neg_eq_add]

theorem diff_of_odd_eq_jordanLeft (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsOdd x) :
    D.diff x = jordanLeft (R := R) D.oddGen x := by
  rw [diff_of_odd D hx]
  rfl

/-- Graded Leibniz rule `∂_F(x * y) = ∂_F(x) * y + α(x) * ∂_F(y)`. -/
theorem diff_mul (D : CurvedZ2GradedDGA R A) (x y : A) :
    D.diff (x * y) = D.diff x * y + D.parity x * D.diff y := by
  simp only [diff_apply, map_mul]
  noncomm_ring

/-- `∂_F` anti-commutes with the parity automorphism `α`. -/
theorem parity_diff (D : CurvedZ2GradedDGA R A) (x : A) :
    D.parity (D.diff x) = -D.diff (D.parity x) := by
  simp only [diff_apply, map_sub, map_mul, D.oddGen_parity, D.parity_involutive]
  noncomm_ring

/-- `∂_F` maps even elements to odd elements. -/
theorem diff_isOdd_of_isEven (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsEven x) :
    D.IsOdd (D.diff x) := by
  unfold IsOdd
  rw [D.parity_diff x, hx]

/-- `∂_F` maps odd elements to even elements. -/
theorem diff_isEven_of_isOdd (D : CurvedZ2GradedDGA R A) {x : A} (hx : D.IsOdd x) :
    D.IsEven (D.diff x) := by
  unfold IsEven
  rw [D.parity_diff x, hx, map_neg, neg_neg]

/-- The curvature `h = F²` is always even. -/
theorem curvature_isEven (D : CurvedZ2GradedDGA R A) :
    D.IsEven D.curvature := by
  unfold IsEven curvature
  rw [map_mul, D.oddGen_parity, neg_mul, mul_neg, neg_neg]

/-- Core curved differential identity: `∂_F² = [h, ·]`. -/
theorem diff_sq (D : CurvedZ2GradedDGA R A) :
    D.diff ^ 2 = LieAlgebra.ad R A D.curvature := by
  rw [pow_two]
  apply LinearMap.ext
  intro x
  change D.diff (D.diff x) = D.curvature * x - x * D.curvature
  simp only [diff_apply, curvature, map_sub, map_mul, D.oddGen_parity, D.parity_involutive]
  noncomm_ring

theorem diff_sq_apply (D : CurvedZ2GradedDGA R A) (x : A) :
    (D.diff ^ 2) x = D.curvature * x - x * D.curvature := by
  rw [diff_sq]
  rfl

theorem diff_comp_diff_apply (D : CurvedZ2GradedDGA R A) (x : A) :
    D.diff (D.diff x) = D.curvature * x - x * D.curvature := by
  rw [← D.diff_sq_apply x, pow_two]
  rfl

/-- Bianchi identity `∂_F(h) = 0`. -/
theorem bianchi (D : CurvedZ2GradedDGA R A) :
    D.diff D.curvature = 0 := by
  rw [D.diff_of_even D.curvature_isEven, curvature]
  noncomm_ring

/-- `∂_F² = 0` holds if and only if the curvature belongs to `Subalgebra.center R A`. -/
theorem diff_sq_eq_zero_iff_mem_center (D : CurvedZ2GradedDGA R A) :
    D.diff ^ 2 = 0 ↔ D.curvature ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h x
    have hx := congrArg (fun f : Module.End R A => f x) h
    rw [D.diff_sq_apply x, LinearMap.zero_apply] at hx
    exact (sub_eq_zero.mp hx).symm
  · intro h
    ext x
    rw [D.diff_sq_apply x, LinearMap.zero_apply, sub_eq_zero]
    exact (h x).symm

/-- `∂_F² = 0` holds if and only if `h` commutes with every element of `A`. -/
theorem diff_sq_eq_zero_iff_commutes (D : CurvedZ2GradedDGA R A) :
    D.diff ^ 2 = 0 ↔ ∀ x : A, D.curvature * x = x * D.curvature := by
  rw [D.diff_sq_eq_zero_iff_mem_center, Subalgebra.mem_center_iff]
  exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

theorem diff_sq_eq_zero_of_curvature_eq_zero (D : CurvedZ2GradedDGA R A)
    (h : D.curvature = 0) : D.diff ^ 2 = 0 := by
  rw [D.diff_sq_eq_zero_iff_commutes, h]
  intro x
  rw [zero_mul, mul_zero]

/-- Two odd generators sharing the same parity automorphism satisfy the mixed
anticommutator identity `∂_{F₁} ∂_{F₂} + ∂_{F₂} ∂_{F₁} = [F₁ F₂ + F₂ F₁, ·]`. -/
theorem diff_anticommutator (D₁ D₂ : CurvedZ2GradedDGA R A)
    (hα : D₁.parity = D₂.parity) :
    D₁.diff * D₂.diff + D₂.diff * D₁.diff =
      LieAlgebra.ad R A (D₁.oddGen * D₂.oddGen + D₂.oddGen * D₁.oddGen) := by
  apply LinearMap.ext
  intro x
  change D₁.diff (D₂.diff x) + D₂.diff (D₁.diff x) =
    (D₁.oddGen * D₂.oddGen + D₂.oddGen * D₁.oddGen) * x -
      x * (D₁.oddGen * D₂.oddGen + D₂.oddGen * D₁.oddGen)
  have h12 : ∀ y : A, D₁.parity (D₂.parity y) = y := by
    intro y
    rw [← hα]
    exact D₁.parity_involutive y
  have h21 : ∀ y : A, D₂.parity (D₁.parity y) = y := by
    intro y
    rw [hα]
    exact D₂.parity_involutive y
  have h1F2 : D₁.parity D₂.oddGen = -D₂.oddGen := by
    rw [hα]
    exact D₂.oddGen_parity
  have h2F1 : D₂.parity D₁.oddGen = -D₁.oddGen := by
    rw [← hα]
    exact D₁.oddGen_parity
  simp only [diff_apply, map_sub, map_mul, h12, h21, h1F2, h2F1]
  noncomm_ring

/-! ### Constructors and bridges to `GradedNullconeAlgebra` and `PeirceBoundaryComplex` -/

/-- Lift `GradedNullconeAlgebra.parityConj Γ` to an `R`-algebra equivalence when `Γ² = 1`. -/
def parityConjAlgEquiv {Γ : A} (hΓ : Γ * Γ = 1) : A ≃ₐ[R] A where
  toFun := parityConj Γ
  invFun := parityConj Γ
  left_inv := parityConj_involutive hΓ
  right_inv := parityConj_involutive hΓ
  map_mul' := parityConj_mul hΓ
  map_add' := parityConj_add Γ
  commutes' := fun r => by
    rw [parityConj_apply, (Algebra.commutes r Γ).symm, mul_assoc, hΓ, mul_one]

@[simp] theorem parityConjAlgEquiv_apply {Γ : A} (hΓ : Γ * Γ = 1) (x : A) :
    parityConjAlgEquiv (R := R) hΓ x = parityConj Γ x := rfl

/-- Construct a `CurvedZ2GradedDGA` from an involutive parity operator `Γ` (`Γ² = 1`)
and an `α`-odd generator `F` (`Γ F Γ = -F`). -/
def ofParityConj {Γ F : A} (hΓ : Γ * Γ = 1) (hF : parityConj Γ F = -F) :
    CurvedZ2GradedDGA R A where
  parity := parityConjAlgEquiv (R := R) hΓ
  parity_involutive := parityConj_involutive hΓ
  oddGen := F
  oddGen_parity := hF

@[simp] theorem ofParityConj_parity {Γ F : A} (hΓ : Γ * Γ = 1)
    (hF : parityConj Γ F = -F) (x : A) :
    (ofParityConj (R := R) hΓ hF).parity x = parityConj Γ x := rfl

@[simp] theorem ofParityConj_oddGen {Γ F : A} (hΓ : Γ * Γ = 1)
    (hF : parityConj Γ F = -F) :
    (ofParityConj (R := R) hΓ hF).oddGen = F := rfl

@[simp] theorem ofParityConj_curvature {Γ F : A} (hΓ : Γ * Γ = 1)
    (hF : parityConj Γ F = -F) :
    (ofParityConj (R := R) hΓ hF).curvature = F * F := rfl

@[simp] theorem ofParityConj_diff_apply {Γ F : A} (hΓ : Γ * Γ = 1)
    (hF : parityConj Γ F = -F) (x : A) :
    (ofParityConj (R := R) hΓ hF).diff x = gradedInnerDiff Γ F x := rfl

/-- Construct a `CurvedZ2GradedDGA` from an idempotent `p` and a Peirce-odd generator `u`. -/
def ofPeirce {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) : CurvedZ2GradedDGA R A where
  parity := parityAlgEquiv (R := R) hp
  parity_involutive := parityAlgEquiv_involutive (R := R) hp
  oddGen := u
  oddGen_parity := by
    rw [parityAlgEquiv_apply, conjugation_apply,
      eq_neg_of_add_eq_zero_left (odd_anticommutes_reflection hp hu),
      neg_mul, mul_assoc, reflection_sq hp, mul_one]

@[simp] theorem ofPeirce_parity {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    (ofPeirce (R := R) hp hu).parity = parityAlgEquiv (R := R) hp := rfl

@[simp] theorem ofPeirce_oddGen {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    (ofPeirce (R := R) hp hu).oddGen = u := rfl

@[simp] theorem ofPeirce_curvature {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    (ofPeirce (R := R) hp hu).curvature = u * u := rfl

@[simp] theorem ofPeirce_diff_eq {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    (ofPeirce (R := R) hp hu).diff = PeirceBoundaryComplex.differential (R := R) p u := by
  ext x
  rw [diff_apply, ofPeirce_oddGen, ofPeirce_parity, parityAlgEquiv_apply,
    PeirceBoundaryComplex.differential_apply]

theorem ofPeirce_eq_ofParityConj_reflection {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    let hΓ : reflection p * reflection p = 1 := reflection_sq hp
    let hF : parityConj (reflection p) u = -u := by
      rw [parityConj_apply, eq_neg_of_add_eq_zero_left (odd_anticommutes_reflection hp hu),
        neg_mul, mul_assoc, reflection_sq hp, mul_one]
    (ofPeirce (R := R) hp hu).diff = (ofParityConj (R := R) hΓ hF).diff ∧
      (∀ x : A, (ofPeirce (R := R) hp hu).parity x =
        (ofParityConj (R := R) hΓ hF).parity x) ∧
      (ofPeirce (R := R) hp hu).curvature = (ofParityConj (R := R) hΓ hF).curvature := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [diff_apply, ofPeirce_oddGen, ofPeirce_parity, parityAlgEquiv_apply,
      conjugation_apply, ofParityConj_oddGen, ofParityConj_parity, parityConj_apply]
  · intro x
    simp only [ofPeirce_parity, parityAlgEquiv_apply, conjugation_apply,
      ofParityConj_parity, parityConj_apply]
  · rfl

/-- Native cochain complex on `A` induced by any flat (`curvature = 0`) curved DGA. -/
noncomputable def toCochainComplex (D : CurvedZ2GradedDGA R A) (hflat : D.curvature = 0) :
    CochainComplex (ModuleCat.{uA} R) ℕ :=
  CochainComplex.of (fun _ : ℕ => ModuleCat.of R A)
    (fun _ => ModuleCat.ofHom D.diff)
    (fun _ => by
      apply ModuleCat.hom_ext
      change D.diff * D.diff = 0
      simpa only [pow_two] using D.diff_sq_eq_zero_of_curvature_eq_zero hflat)

@[simp] theorem toCochainComplex_X (D : CurvedZ2GradedDGA R A) (hflat : D.curvature = 0)
    (i : ℕ) : (D.toCochainComplex hflat).X i = ModuleCat.of R A := rfl

@[simp] theorem toCochainComplex_d (D : CurvedZ2GradedDGA R A) (hflat : D.curvature = 0)
    (i : ℕ) : (D.toCochainComplex hflat).d i (i + 1) = ModuleCat.ofHom D.diff := by
  exact CochainComplex.of_d (fun _ : ℕ => ModuleCat.of R A)
    (fun _ => ModuleCat.ofHom D.diff) i

theorem ofPeirce_toCochainComplex_d_eq_cornerComplex_d {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (huodd : u ∈ LinearMap.range (odd p))
    (hflat : (ofPeirce (R := R) hp huodd).curvature = 0) (i : ℕ) :
    ((ofPeirce (R := R) hp huodd).toCochainComplex hflat).d i (i + 1) =
      (PeirceBoundaryComplex.cornerComplex (R := R) hp hu).d i (i + 1) := by
  rw [toCochainComplex_d, cornerComplex_d, ofPeirce_diff_eq]

end CurvedZ2GradedDGA

end Core

/-! ## F7: Three Curvature Regimes and Concrete Witnesses -/

section CurvatureRegimes

/-- The three exhaustive, mutually exclusive curvature regimes of a curved `ℤ/2`-graded DGA. -/
inductive CurvatureRegime
  | flat
  | centralNonzero
  | nonCentral
  deriving DecidableEq, Repr

/-- Ring-theoretic centrality predicate `∀ x, h * x = x * h`. -/
def IsCentral {A : Type*} [Ring A] (h : A) : Prop :=
  ∀ x : A, h * x = x * h

theorem isCentral_iff_mem_center {R : Type uR} {A : Type uA}
    [CommRing R] [Ring A] [Algebra R A] (h : A) :
    IsCentral h ↔ h ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  exact ⟨fun H x => (H x).symm, fun H x => (H x).symm⟩

/-- Regime (i): flat curvature (`h = 0`). -/
def IsFlatRegime {A : Type*} [Ring A] (h : A) : Prop :=
  h = 0

/-- Regime (ii): central nonzero curvature (`h ≠ 0` and `h` is central). -/
def IsCentralNonzeroRegime {A : Type*} [Ring A] (h : A) : Prop :=
  h ≠ 0 ∧ IsCentral h

/-- Regime (iii): non-central curvature (`¬ IsCentral h`). -/
def IsNonCentralRegime {A : Type*} [Ring A] (h : A) : Prop :=
  ¬ IsCentral h

theorem isCentral_zero {A : Type*} [Ring A] : IsCentral (0 : A) := by
  intro x
  rw [zero_mul, mul_zero]

theorem isCentral_one {A : Type*} [Ring A] : IsCentral (1 : A) := by
  intro x
  rw [one_mul, mul_one]

theorem isCentral_neg_one {A : Type*} [Ring A] : IsCentral (-1 : A) := by
  intro x
  rw [neg_mul, one_mul, mul_neg, mul_one]

/-- The three curvature regimes are exhaustive and pairwise mutually exclusive. -/
theorem curvatureRegime_trichotomy {A : Type*} [Ring A] (h : A) :
    (IsFlatRegime h ∨ IsCentralNonzeroRegime h ∨ IsNonCentralRegime h) ∧
      ¬ (IsFlatRegime h ∧ IsCentralNonzeroRegime h) ∧
      ¬ (IsFlatRegime h ∧ IsNonCentralRegime h) ∧
      ¬ (IsCentralNonzeroRegime h ∧ IsNonCentralRegime h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h0 : h = 0
    · exact Or.inl h0
    · by_cases hc : IsCentral h
      · exact Or.inr (Or.inl ⟨h0, hc⟩)
      · exact Or.inr (Or.inr hc)
  · rintro ⟨h0, hne, _⟩
    exact hne h0
  · rintro ⟨h0, hnc⟩
    rw [IsFlatRegime] at h0
    subst h0
    exact hnc isCentral_zero
  · rintro ⟨⟨_, hc⟩, hnc⟩
    exact hnc hc

/-- Classical classifier sending a curvature element `h` to its `CurvatureRegime`. -/
noncomputable def classifyRegime {A : Type*} [Ring A] (h : A) : CurvatureRegime := by
  classical
  exact if h = 0 then .flat else if IsCentral h then .centralNonzero else .nonCentral

theorem classifyRegime_eq_flat_iff {A : Type*} [Ring A] (h : A) :
    classifyRegime h = .flat ↔ IsFlatRegime h := by
  classical
  unfold classifyRegime IsFlatRegime
  split_ifs with h0 hc <;> simp [h0]

theorem classifyRegime_eq_centralNonzero_iff {A : Type*} [Ring A] (h : A) :
    classifyRegime h = .centralNonzero ↔ IsCentralNonzeroRegime h := by
  classical
  unfold classifyRegime IsCentralNonzeroRegime
  split_ifs with h0 hc
  · simp [h0]
  · simp [h0, hc]
  · simp [h0, hc]

theorem classifyRegime_eq_nonCentral_iff {A : Type*} [Ring A] (h : A) :
    classifyRegime h = .nonCentral ↔ IsNonCentralRegime h := by
  classical
  unfold classifyRegime IsNonCentralRegime
  split_ifs with h0 hc
  · subst h0
    simp [isCentral_zero]
  · simp [hc]
  · simp [hc]

theorem diff_sq_eq_zero_iff_isCentral {R : Type uR} {A : Type uA}
    [CommRing R] [Ring A] [Algebra R A] (D : CurvedZ2GradedDGA R A) :
    D.diff ^ 2 = 0 ↔ IsCentral D.curvature :=
  D.diff_sq_eq_zero_iff_commutes

theorem isNonCentralRegime_iff_diff_sq_ne_zero {R : Type uR} {A : Type uA}
    [CommRing R] [Ring A] [Algebra R A] (D : CurvedZ2GradedDGA R A) :
    IsNonCentralRegime D.curvature ↔ D.diff ^ 2 ≠ 0 := by
  rw [IsNonCentralRegime, ← diff_sq_eq_zero_iff_isCentral]

theorem isFlatRegime_implies_diff_sq_zero {R : Type uR} {A : Type uA}
    [CommRing R] [Ring A] [Algebra R A] (D : CurvedZ2GradedDGA R A)
    (h : IsFlatRegime D.curvature) : D.diff ^ 2 = 0 :=
  D.diff_sq_eq_zero_of_curvature_eq_zero h

theorem isCentralNonzeroRegime_implies_diff_sq_zero {R : Type uR} {A : Type uA}
    [CommRing R] [Ring A] [Algebra R A] (D : CurvedZ2GradedDGA R A)
    (h : IsCentralNonzeroRegime D.curvature) :
    D.diff ^ 2 = 0 ∧ D.curvature ≠ 0 :=
  ⟨(diff_sq_eq_zero_iff_isCentral D).mpr h.2, h.1⟩

end CurvatureRegimes

/-! ### Regime (i): Flat Witnesses (`F² = 0`) -/

section FlatWitnesses

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

private theorem peirce10_mem_odd {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) : u ∈ LinearMap.range (odd p) := by
  rw [mem_odd_iff hp, left_support10 hp hu, right_support10 hp hu, add_zero]

private theorem peirce01_mem_odd {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce01 p) : u ∈ LinearMap.range (odd p) := by
  rw [mem_odd_iff hp, left_support01 hp hu, right_support01 hp hu, zero_add]

/-- Curved DGA (flat regime) induced by a `peirce10` directed corner element. -/
def ofPeirce10 {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    CurvedZ2GradedDGA R A :=
  CurvedZ2GradedDGA.ofPeirce (R := R) hp (peirce10_mem_odd hp hu)

/-- Curved DGA (flat regime) induced by a `peirce01` directed corner element. -/
def ofPeirce01 {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce01 p) :
    CurvedZ2GradedDGA R A :=
  CurvedZ2GradedDGA.ofPeirce (R := R) hp (peirce01_mem_odd hp hu)

theorem ofPeirce10_isFlat {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    IsFlatRegime (ofPeirce10 (R := R) hp hu).curvature := by
  change u * u = 0
  exact peirce10_mul_peirce10_eq_zero p hp.eq hu hu

theorem ofPeirce01_isFlat {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce01 p) :
    IsFlatRegime (ofPeirce01 (R := R) hp hu).curvature := by
  change u * u = 0
  exact peirce01_mul_peirce01_eq_zero p hp.eq hu hu

theorem ofPeirce10_diff_sq {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    (ofPeirce10 (R := R) hp hu).diff ^ 2 = 0 :=
  isFlatRegime_implies_diff_sq_zero _ (ofPeirce10_isFlat hp hu)

theorem ofPeirce01_diff_sq {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce01 p) :
    (ofPeirce01 (R := R) hp hu).diff ^ 2 = 0 :=
  isFlatRegime_implies_diff_sq_zero _ (ofPeirce01_isFlat hp hu)

theorem ofPeirce10_diff_ne_zero {p u : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hu0 : u ≠ 0) :
    (ofPeirce10 (R := R) hp hu).diff ≠ 0 := by
  simpa only [ofPeirce10, CurvedZ2GradedDGA.ofPeirce_diff_eq] using
    PeirceBoundaryComplex.differential_ne_zero (R := R) hp hu hu0

theorem ofPeirce10_toCochainComplex_d_eq_cornerComplex_d {p u : A}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (i : ℕ) :
    ((ofPeirce10 (R := R) hp hu).toCochainComplex (ofPeirce10_isFlat hp hu)).d i (i + 1) =
      (PeirceBoundaryComplex.cornerComplex (R := R) hp hu).d i (i + 1) := by
  rw [CurvedZ2GradedDGA.toCochainComplex_d (D := ofPeirce10 (R := R) hp hu)
    (hflat := ofPeirce10_isFlat hp hu), PeirceBoundaryComplex.cornerComplex_d]
  simp only [ofPeirce10, CurvedZ2GradedDGA.ofPeirce_diff_eq]
  rfl

end FlatWitnesses

section ConcreteMat2Witnesses

/-- Closed Trap T16 noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2R_noncommutative_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  mat2R_mul_noncommutative

private theorem parityConj_gammaCut2_atomNeg2 :
    parityConj gammaCut2 atomNeg2 = -atomNeg2 := by
  have hAnti := atom_car_relations.2.2.2.2
  have hSq := cl11_atom_laws.1
  have h1 : atomNeg2 * gammaCut2 = -(gammaCut2 * atomNeg2) :=
    eq_neg_of_add_eq_zero_left hAnti
  rw [parityConj_apply, mul_assoc, h1, mul_neg, ← mul_assoc, hSq, one_mul]

/-- Concrete flat-regime witness on `M₂(ℝ)` with `Γ = gammaCut2` and `F = atomNeg2`. -/
def flatMat2DGA : CurvedZ2GradedDGA ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) cl11_atom_laws.1 parityConj_gammaCut2_atomNeg2

theorem flatMat2DGA_curvature_eq_zero : flatMat2DGA.curvature = 0 :=
  atom_car_relations.2.1

theorem flatMat2DGA_isFlat : IsFlatRegime flatMat2DGA.curvature :=
  flatMat2DGA_curvature_eq_zero

theorem flatMat2DGA_classifyRegime : classifyRegime flatMat2DGA.curvature = .flat :=
  (classifyRegime_eq_flat_iff _).mpr flatMat2DGA_isFlat

theorem flatMat2DGA_oddGen_ne_zero : flatMat2DGA.oddGen ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [flatMat2DGA, atomNeg2] at h01

theorem flatMat2DGA_diff_sq : flatMat2DGA.diff ^ 2 = 0 :=
  isFlatRegime_implies_diff_sq_zero _ flatMat2DGA_isFlat

theorem flatMat2DGA_diff_atomPos2 : flatMat2DGA.diff atomPos2 = 1 := by
  have hOdd : parityConj gammaCut2 atomPos2 = -atomPos2 := by
    have hAnti := atom_car_relations.2.2.2.1
    have hSq := cl11_atom_laws.1
    have h1 : atomPos2 * gammaCut2 = -(gammaCut2 * atomPos2) :=
      eq_neg_of_add_eq_zero_left hAnti
    rw [parityConj_apply, mul_assoc, h1, mul_neg, ← mul_assoc, hSq, one_mul]
  change gradedInnerDiff gammaCut2 atomNeg2 atomPos2 = 1
  rw [gradedInnerDiff_of_odd hOdd]
  have hCAR := atom_car_relations.2.2.1
  rw [add_comm] at hCAR
  exact hCAR

theorem flatMat2DGA_diff_ne_zero : flatMat2DGA.diff ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : Module.End ℝ (Matrix (Fin 2) (Fin 2) ℝ) => f atomPos2) h
  rw [flatMat2DGA_diff_atomPos2, LinearMap.zero_apply] at h1
  have h00 := congrFun (congrFun h1 0) 0
  simp at h00

/-! ### Regime (ii): Central Nonzero Witnesses (`F²` central, `F² ≠ 0`) -/

private theorem parityConj_gammaCut2_gammaMir2 :
    parityConj gammaCut2 gammaMir2 = -gammaMir2 := by
  have hAnti := cl11_atom_laws.2.2.1
  have hSq := cl11_atom_laws.1
  have h1 : gammaMir2 * gammaCut2 = -(gammaCut2 * gammaMir2) :=
    eq_neg_of_add_eq_zero_right hAnti
  rw [parityConj_apply, mul_assoc, h1, mul_neg, ← mul_assoc, hSq, one_mul]

/-- Concrete central-nonzero witness on `M₂(ℝ)` with `Γ = gammaCut2` and `F = gammaMir2`. -/
def centralMat2DGA : CurvedZ2GradedDGA ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) cl11_atom_laws.1 parityConj_gammaCut2_gammaMir2

theorem centralMat2DGA_curvature_eq_one : centralMat2DGA.curvature = 1 :=
  cl11_atom_laws.2.1

theorem centralMat2DGA_isCentralNonzero : IsCentralNonzeroRegime centralMat2DGA.curvature := by
  rw [centralMat2DGA_curvature_eq_one]
  refine ⟨?_, isCentral_one⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00

theorem centralMat2DGA_classifyRegime :
    classifyRegime centralMat2DGA.curvature = .centralNonzero :=
  (classifyRegime_eq_centralNonzero_iff _).mpr centralMat2DGA_isCentralNonzero

theorem centralMat2DGA_diff_sq : centralMat2DGA.diff ^ 2 = 0 :=
  (isCentralNonzeroRegime_implies_diff_sq_zero _ centralMat2DGA_isCentralNonzero).1

theorem centralMat2DGA_diff_gammaCut2 :
    centralMat2DGA.diff gammaCut2 = (-2 : ℝ) • gammaSkew2 := by
  have hEven : parityConj gammaCut2 gammaCut2 = gammaCut2 := by
    rw [parityConj_apply, cl11_atom_laws.1, one_mul]
  change gradedInnerDiff gammaCut2 gammaMir2 gammaCut2 = (-2 : ℝ) • gammaSkew2
  rw [gradedInnerDiff_of_even hEven]
  have hMirCut : gammaMir2 * gammaCut2 = -gammaSkew2 := by
    have h1 : gammaMir2 * gammaCut2 = -(gammaCut2 * gammaMir2) :=
      eq_neg_of_add_eq_zero_right cl11_atom_laws.2.2.1
    rw [h1, cl11_atom_laws.2.2.2.1]
  rw [hMirCut, cl11_atom_laws.2.2.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaSkew2] <;> norm_num

theorem centralMat2DGA_diff_ne_zero : centralMat2DGA.diff ≠ 0 := by
  intro h
  have hval := congrArg (fun f : Module.End ℝ (Matrix (Fin 2) (Fin 2) ℝ) => f gammaCut2) h
  rw [centralMat2DGA_diff_gammaCut2, LinearMap.zero_apply] at hval
  have h01 := congrFun (congrFun hval 0) 1
  simp [gammaSkew2] at h01

private theorem parityConj_gammaCut2_gammaSkew2 :
    parityConj gammaCut2 gammaSkew2 = -gammaSkew2 := by
  have hAnti : gammaCut2 * gammaSkew2 + gammaSkew2 * gammaCut2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gammaCut2, gammaSkew2]
  have h1 : gammaSkew2 * gammaCut2 = -(gammaCut2 * gammaSkew2) :=
    eq_neg_of_add_eq_zero_right hAnti
  rw [parityConj_apply, mul_assoc, h1, mul_neg, ← mul_assoc, cl11_atom_laws.1, one_mul]

/-- Companion central-nonzero witness on `M₂(ℝ)` with `F = gammaSkew2` and `h = -1`. -/
def centralSkewMat2DGA : CurvedZ2GradedDGA ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) cl11_atom_laws.1 parityConj_gammaCut2_gammaSkew2

theorem centralSkewMat2DGA_curvature_eq_neg_one : centralSkewMat2DGA.curvature = -1 :=
  cl11_atom_laws.2.2.2.2.1

theorem centralSkewMat2DGA_isCentralNonzero :
    IsCentralNonzeroRegime centralSkewMat2DGA.curvature := by
  rw [centralSkewMat2DGA_curvature_eq_neg_one]
  refine ⟨?_, isCentral_neg_one⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00

theorem centralSkewMat2DGA_diff_sq : centralSkewMat2DGA.diff ^ 2 = 0 :=
  (isCentralNonzeroRegime_implies_diff_sq_zero _ centralSkewMat2DGA_isCentralNonzero).1

end ConcreteMat2Witnesses

section DoubledSpaceWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedAlgebra ℝ (EndH₂ (E := E)) := inferInstance

private theorem gamma5_mul_self :
    gamma5 (E := E) * gamma5 (E := E) = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, gamma5_involution]

private theorem parityConj_gamma5_etaChiral :
    parityConj (gamma5 (E := E)) (etaChiral (E := E)) = -(etaChiral (E := E)) := by
  rw [parityConj_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  have hAnti : (gamma5 (E := E)).comp (etaChiral (E := E)) =
      -((etaChiral (E := E)).comp (gamma5 (E := E))) := by
    rw [etaChiral_gamma5_anticommute, neg_neg]
  change ((gamma5 (E := E)).comp (etaChiral (E := E))).comp (gamma5 (E := E)) =
    -(etaChiral (E := E))
  rw [hAnti, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc,
    gamma5_involution, ContinuousLinearMap.comp_id]

/-- Central-nonzero witness on the doubled real Krein endomorphism algebra `EndH₂`
with `Γ = gamma5` and `F = etaChiral` (`h = F² = 1`). -/
noncomputable def centralDoubledDGA (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CurvedZ2GradedDGA ℝ (EndH₂ (E := E)) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) (gamma5_mul_self (E := E))
    (parityConj_gamma5_etaChiral (E := E))

theorem centralDoubledDGA_curvature_eq_one :
    (centralDoubledDGA E).curvature = 1 := by
  change etaChiral (E := E) * etaChiral (E := E) = 1
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, etaChiral_involution]

omit [CompleteSpace E] in
theorem endH2_one_ne_zero [Nontrivial E] : (1 : EndH₂ (E := E)) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hv := congrArg (fun f : EndH₂ (E := E) => f (to_doubled x 0 : H₂ (E := E))) h
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, zero_apply] at hv
  have hfst := congrArg WithLp.fst hv
  simp only [WithLp.zero_fst] at hfst
  exact hx hfst

theorem centralDoubledDGA_isCentralNonzero [Nontrivial E] :
    IsCentralNonzeroRegime (centralDoubledDGA E).curvature := by
  rw [centralDoubledDGA_curvature_eq_one]
  exact ⟨endH2_one_ne_zero, isCentral_one⟩

theorem centralDoubledDGA_classifyRegime [Nontrivial E] :
    classifyRegime (centralDoubledDGA E).curvature = .centralNonzero :=
  (classifyRegime_eq_centralNonzero_iff _).mpr (centralDoubledDGA_isCentralNonzero)

theorem centralDoubledDGA_diff_sq :
    (centralDoubledDGA E).diff ^ 2 = 0 := by
  rw [diff_sq_eq_zero_iff_isCentral, centralDoubledDGA_curvature_eq_one]
  exact isCentral_one

theorem centralDoubledDGA_diff_gamma5 :
    (centralDoubledDGA E).diff (gamma5 (E := E)) =
      (2 : ℝ) • chiralComplexStructure (E := E) := by
  have hEven : parityConj (gamma5 (E := E)) (gamma5 (E := E)) = gamma5 (E := E) := by
    rw [parityConj_apply, gamma5_mul_self, one_mul]
  change gradedInnerDiff (gamma5 (E := E)) (etaChiral (E := E)) (gamma5 (E := E)) =
    (2 : ℝ) • chiralComplexStructure (E := E)
  rw [gradedInnerDiff_of_even hEven]
  change (etaChiral (E := E)).comp (gamma5 (E := E)) -
      (gamma5 (E := E)).comp (etaChiral (E := E)) =
    (2 : ℝ) • chiralComplexStructure (E := E)
  have hAnti : (gamma5 (E := E)).comp (etaChiral (E := E)) =
      -((etaChiral (E := E)).comp (gamma5 (E := E))) := by
    rw [etaChiral_gamma5_anticommute, neg_neg]
  rw [hAnti, sub_neg_eq_add, ← two_smul ℝ]
  rfl

theorem centralDoubledDGA_diff_gamma5_isUnit :
    IsUnit ((centralDoubledDGA E).diff (gamma5 (E := E))) := by
  rw [centralDoubledDGA_diff_gamma5]
  refine ⟨⟨(2 : ℝ) • chiralComplexStructure (E := E),
      (-(1 / 2 : ℝ)) • chiralComplexStructure (E := E), ?_, ?_⟩, rfl⟩
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply, map_smul]
    have hsq : chiralComplexStructure (E := E) (chiralComplexStructure (E := E) u) = -u := by
      have := congrArg (fun f : EndH₂ (E := E) => f u) (chiralComplexStructure_sq (E := E))
      simpa using this
    rw [hsq]
    simp only [smul_neg, smul_smul]
    norm_num
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply, map_smul]
    have hsq : chiralComplexStructure (E := E) (chiralComplexStructure (E := E) u) = -u := by
      have := congrArg (fun f : EndH₂ (E := E) => f u) (chiralComplexStructure_sq (E := E))
      simpa using this
    rw [hsq]
    simp only [smul_neg, neg_smul, smul_smul]
    norm_num

theorem centralDoubledDGA_diff_ne_zero [Nontrivial E] :
    (centralDoubledDGA E).diff ≠ 0 := by
  intro h
  have hv := congrArg (fun f : Module.End ℝ (EndH₂ (E := E)) => f (gamma5 (E := E))) h
  rw [LinearMap.zero_apply] at hv
  obtain ⟨u, hu⟩ := centralDoubledDGA_diff_gamma5_isUnit (E := E)
  rw [hv] at hu
  have h10 : (1 : EndH₂ (E := E)) = 0 := by
    have hmul := congrArg (fun x : EndH₂ (E := E) => x * (u.inv : EndH₂ (E := E))) hu
    simpa [zero_mul] using hmul.symm
  exact endH2_one_ne_zero h10

end DoubledSpaceWitness

/-! ### Regime (iii): Non-Central Witness (`¬ IsCentral (F²)`, `∂_F² ≠ 0`) -/

section NonCentralWitnesses

/-- Grading operator `diag(I₂, -I₂)` on `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ`. -/
def nonCentralGammaBlock : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 (-1)

/-- Corner idempotent `[[1, 0], [0, 0]]` in `M₂(ℝ)`. -/
def nonCentralCorner2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- Odd generator on `Fin 2 ⊕ Fin 2` whose square `diag(e₁₁, e₁₁)` is non-central. -/
def nonCentralFBlock : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 0 nonCentralCorner2 nonCentralCorner2 0

/-- Test matrix on `Fin 2 ⊕ Fin 2` detecting non-centrality of `F²`. -/
def nonCentralTestBlock : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks atomNeg2 0 0 0

private theorem nonCentralCorner2_sq :
    nonCentralCorner2 * nonCentralCorner2 = nonCentralCorner2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonCentralCorner2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem nonCentralCorner2_mul_atomNeg2 :
    nonCentralCorner2 * atomNeg2 = atomNeg2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonCentralCorner2, atomNeg2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem atomNeg2_mul_nonCentralCorner2 :
    atomNeg2 * nonCentralCorner2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonCentralCorner2, atomNeg2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem nonCentralGammaBlock_sq :
    nonCentralGammaBlock * nonCentralGammaBlock = 1 := by
  rw [nonCentralGammaBlock, Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one]

private theorem nonCentralFBlock_odd :
    parityConj nonCentralGammaBlock nonCentralFBlock = -nonCentralFBlock := by
  rw [parityConj_apply, nonCentralGammaBlock, nonCentralFBlock,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg]

/-- Closed Trap T16 noncommutativity witness for `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ`. -/
theorem mat2Sum2R_mul_noncommutative :
    ∃ A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨nonCentralFBlock, nonCentralTestBlock, ?_⟩
  intro h
  have h01 := congrFun (congrFun h (Sum.inr 0)) (Sum.inl 1)
  simp [nonCentralFBlock, nonCentralTestBlock, nonCentralCorner2, atomNeg2,
    Matrix.fromBlocks_multiply] at h01

/-- Concrete non-central-regime witness on `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ`. -/
def nonCentralBlockDGA :
    CurvedZ2GradedDGA ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) nonCentralGammaBlock_sq nonCentralFBlock_odd

theorem nonCentralBlockDGA_curvature :
    nonCentralBlockDGA.curvature =
      Matrix.fromBlocks nonCentralCorner2 0 0 nonCentralCorner2 := by
  change nonCentralFBlock * nonCentralFBlock =
    Matrix.fromBlocks nonCentralCorner2 0 0 nonCentralCorner2
  rw [nonCentralFBlock, Matrix.fromBlocks_multiply]
  simp [nonCentralCorner2_sq]

theorem nonCentralBlockDGA_diff_sq_test :
    (nonCentralBlockDGA.diff ^ 2) nonCentralTestBlock = nonCentralTestBlock := by
  rw [nonCentralBlockDGA.diff_sq_apply, nonCentralBlockDGA_curvature, nonCentralTestBlock,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [nonCentralCorner2_mul_atomNeg2, atomNeg2_mul_nonCentralCorner2]

theorem nonCentralBlockDGA_test_ne_zero : nonCentralTestBlock ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
  simp [nonCentralTestBlock, atomNeg2] at h01

theorem nonCentralBlockDGA_diff_sq_ne_zero : nonCentralBlockDGA.diff ^ 2 ≠ 0 := by
  intro h
  have hv := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) =>
      f nonCentralTestBlock) h
  rw [nonCentralBlockDGA_diff_sq_test, LinearMap.zero_apply] at hv
  exact nonCentralBlockDGA_test_ne_zero hv

theorem nonCentralBlockDGA_isNonCentral :
    IsNonCentralRegime nonCentralBlockDGA.curvature :=
  (isNonCentralRegime_iff_diff_sq_ne_zero nonCentralBlockDGA).mpr
    nonCentralBlockDGA_diff_sq_ne_zero

theorem nonCentralBlockDGA_classifyRegime :
    classifyRegime nonCentralBlockDGA.curvature = .nonCentral :=
  (classifyRegime_eq_nonCentral_iff _).mpr nonCentralBlockDGA_isNonCentral

theorem nonCentralBlockDGA_bianchi :
    nonCentralBlockDGA.diff nonCentralBlockDGA.curvature = 0 :=
  nonCentralBlockDGA.bianchi

theorem nonCentralBlockDGA_leibniz
    (x y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) :
    nonCentralBlockDGA.diff (x * y) =
      nonCentralBlockDGA.diff x * y +
        nonCentralBlockDGA.parity x * nonCentralBlockDGA.diff y :=
  nonCentralBlockDGA.diff_mul x y

/-- Explicit `4 × 4` grading matrix `diag(1, 1, -1, -1)`. -/
def nonCentralGamma4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Explicit `4 × 4` odd generator `F` with non-central square `diag(1, 0, 1, 0)`. -/
def nonCentralF4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0]

/-- Explicit `4 × 4` test matrix detecting `∂_F² ≠ 0`. -/
def nonCentralTest4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

private noncomputable abbrev blockToMat4Equiv :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv

private theorem finSum2_symm_0 :
    (finSumFinEquiv (m := 2) (n := 2)).symm 0 = Sum.inl 0 := by decide
private theorem finSum2_symm_1 :
    (finSumFinEquiv (m := 2) (n := 2)).symm 1 = Sum.inl 1 := by decide
private theorem finSum2_symm_2 :
    (finSumFinEquiv (m := 2) (n := 2)).symm 2 = Sum.inr 0 := by decide
private theorem finSum2_symm_3 :
    (finSumFinEquiv (m := 2) (n := 2)).symm 3 = Sum.inr 1 := by decide

private theorem blockToMat4_nonCentralGammaBlock :
    blockToMat4Equiv nonCentralGammaBlock = nonCentralGamma4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockToMat4Equiv, nonCentralGammaBlock, nonCentralGamma4,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSum2_symm_0, finSum2_symm_1, finSum2_symm_2, finSum2_symm_3]

private theorem blockToMat4_nonCentralFBlock :
    blockToMat4Equiv nonCentralFBlock = nonCentralF4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockToMat4Equiv, nonCentralFBlock, nonCentralCorner2, nonCentralF4,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSum2_symm_0, finSum2_symm_1, finSum2_symm_2, finSum2_symm_3]

private theorem blockToMat4_nonCentralTestBlock :
    blockToMat4Equiv nonCentralTestBlock = nonCentralTest4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockToMat4Equiv, nonCentralTestBlock, atomNeg2, nonCentralTest4,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSum2_symm_0, finSum2_symm_1, finSum2_symm_2, finSum2_symm_3]

private theorem nonCentralGamma4_sq :
    nonCentralGamma4 * nonCentralGamma4 = 1 := by
  rw [← blockToMat4_nonCentralGammaBlock, ← map_mul, nonCentralGammaBlock_sq, map_one]

private theorem nonCentralF4_odd :
    parityConj nonCentralGamma4 nonCentralF4 = -nonCentralF4 := by
  rw [parityConj_apply, ← blockToMat4_nonCentralGammaBlock, ← blockToMat4_nonCentralFBlock,
    ← map_mul, ← map_mul]
  have h := congrArg blockToMat4Equiv nonCentralFBlock_odd
  simpa only [parityConj_apply, map_neg] using h

/-- Closed Trap T16 noncommutativity witness for `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem mat4R_mul_noncommutative :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨nonCentralF4, nonCentralTest4, ?_⟩
  intro h
  have h21 := congrFun (congrFun h 2) 1
  simp [nonCentralF4, nonCentralTest4, Matrix.mul_apply, Fin.sum_univ_four] at h21

/-- Concrete non-central-regime witness on `Matrix (Fin 4) (Fin 4) ℝ` with `∂_F² ≠ 0`. -/
def nonCentralMat4DGA : CurvedZ2GradedDGA ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  CurvedZ2GradedDGA.ofParityConj (R := ℝ) nonCentralGamma4_sq nonCentralF4_odd

theorem nonCentralMat4DGA_curvature :
    nonCentralMat4DGA.curvature =
      !![1, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
  change nonCentralF4 * nonCentralF4 = _
  rw [← blockToMat4_nonCentralFBlock, ← map_mul]
  change blockToMat4Equiv nonCentralBlockDGA.curvature = _
  rw [nonCentralBlockDGA_curvature]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockToMat4Equiv, nonCentralCorner2, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSum2_symm_0, finSum2_symm_1, finSum2_symm_2, finSum2_symm_3]

theorem nonCentralMat4DGA_diff_sq_test :
    nonCentralMat4DGA.diff (nonCentralMat4DGA.diff nonCentralTest4) = nonCentralTest4 := by
  change (nonCentralMat4DGA.diff ^ 2) nonCentralTest4 = nonCentralTest4
  rw [nonCentralMat4DGA.diff_sq_apply]
  change nonCentralF4 * nonCentralF4 * nonCentralTest4 -
    nonCentralTest4 * (nonCentralF4 * nonCentralF4) = nonCentralTest4
  rw [← blockToMat4_nonCentralFBlock, ← blockToMat4_nonCentralTestBlock,
    ← map_mul, ← map_mul, ← map_mul, ← map_sub]
  have hblock :
      nonCentralBlockDGA.curvature * nonCentralTestBlock -
        nonCentralTestBlock * nonCentralBlockDGA.curvature = nonCentralTestBlock := by
    rw [← nonCentralBlockDGA.diff_sq_apply, nonCentralBlockDGA_diff_sq_test]
  change blockToMat4Equiv
    (nonCentralBlockDGA.curvature * nonCentralTestBlock -
      nonCentralTestBlock * nonCentralBlockDGA.curvature) =
    blockToMat4Equiv nonCentralTestBlock
  rw [hblock]

theorem nonCentralMat4DGA_test4_ne_zero : nonCentralTest4 ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [nonCentralTest4] at h01

theorem nonCentralMat4DGA_diff_sq_ne_zero : nonCentralMat4DGA.diff ^ 2 ≠ 0 := by
  intro h
  have hv := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f nonCentralTest4) h
  change nonCentralMat4DGA.diff (nonCentralMat4DGA.diff nonCentralTest4) = 0 at hv
  rw [nonCentralMat4DGA_diff_sq_test] at hv
  exact nonCentralMat4DGA_test4_ne_zero hv

theorem nonCentralMat4DGA_isNonCentral :
    IsNonCentralRegime nonCentralMat4DGA.curvature :=
  (isNonCentralRegime_iff_diff_sq_ne_zero nonCentralMat4DGA).mpr
    nonCentralMat4DGA_diff_sq_ne_zero

theorem nonCentralMat4DGA_classifyRegime :
    classifyRegime nonCentralMat4DGA.curvature = .nonCentral :=
  (classifyRegime_eq_nonCentral_iff _).mpr nonCentralMat4DGA_isNonCentral

theorem nonCentralMat4DGA_bianchi :
    nonCentralMat4DGA.diff nonCentralMat4DGA.curvature = 0 :=
  nonCentralMat4DGA.bianchi

theorem nonCentralMat4DGA_leibniz (x y : Matrix (Fin 4) (Fin 4) ℝ) :
    nonCentralMat4DGA.diff (x * y) =
      nonCentralMat4DGA.diff x * y + nonCentralMat4DGA.parity x * nonCentralMat4DGA.diff y :=
  nonCentralMat4DGA.diff_mul x y

end NonCentralWitnesses

/-! ## F8: Separation from Ordinary Commutator Derivations `D_G` and `PR #426`

Note on `PR #426` (`InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean`):
`ConnesSpectral.SpectralTriple.commutator f = ST.dirac * f - f * ST.dirac` is strictly an
ungraded inner commutator derivation (`commutatorDeriv (ST.dirac)`), satisfying the
ungraded Leibniz rule `commutator_mul`. By `curvedDiff_ne_commutatorDeriv_of_unit` and
`nilpotent_commutatorDeriv_sq_ne_zero` below, `∂_F` and `D_G` are algebraically distinct
(twisted vs untwisted Leibniz, and `G² = 0 ⇒ ∂_G² = 0` vs `G² = 0 ∧ D_G² ≠ 0`).
`ConnesSpectralTripleBridge.lean` is neither imported nor modified here. -/

section CommutatorSeparation

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

/-- Ordinary ungraded inner commutator derivation `D_G(x) = [G, x] = G * x - x * G`. -/
def commutatorDeriv (G : A) : Module.End R A where
  toFun x := G * x - x * G
  map_add' x y := by noncomm_ring
  map_smul' r x := by
    simp only [RingHom.id_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

@[simp] theorem commutatorDeriv_apply (G x : A) :
    commutatorDeriv (R := R) G x = G * x - x * G := rfl

theorem commutatorDeriv_eq_ad (G : A) :
    commutatorDeriv (R := R) G = LieAlgebra.ad R A G := rfl

theorem commutatorDeriv_eq_innerRingDeriv (G x : A) :
    commutatorDeriv (R := R) G x =
      InfoGeometry.Algebra.GradedNullconeAlgebra.innerRingDeriv G x := rfl

/-- Ungraded Leibniz rule for `commutatorDeriv`. -/
theorem commutatorDeriv_mul (G x y : A) :
    commutatorDeriv (R := R) G (x * y) =
      commutatorDeriv (R := R) G x * y + x * commutatorDeriv (R := R) G y := by
  simp only [commutatorDeriv_apply]
  noncomm_ring

theorem commutatorDeriv_sq (G x : A) :
    commutatorDeriv (R := R) G (commutatorDeriv (R := R) G x) =
      (G * G) * x - (G * x * G + G * x * G) + x * (G * G) := by
  simp only [commutatorDeriv_apply]
  noncomm_ring

theorem commutatorDeriv_sq_of_sq_zero {G : A} (hG : G * G = 0) (x : A) :
    commutatorDeriv (R := R) G (commutatorDeriv (R := R) G x) =
      -(G * x * G + G * x * G) := by
  rw [commutatorDeriv_sq, hG, zero_mul, mul_zero, zero_sub, add_zero]

/-- Pointwise discrepancy between `∂_F` and `D_F = [F, ·]`. -/
theorem curvedDiff_sub_commutatorDeriv (D : CurvedZ2GradedDGA R A) (x : A) :
    D.diff x - commutatorDeriv (R := R) D.oddGen x = (x - D.parity x) * D.oddGen := by
  simp only [CurvedZ2GradedDGA.diff_apply, commutatorDeriv_apply]
  noncomm_ring

theorem curvedDiff_eq_commutatorDeriv_of_even (D : CurvedZ2GradedDGA R A)
    {x : A} (hx : D.IsEven x) :
    D.diff x = commutatorDeriv (R := R) D.oddGen x := by
  rw [D.diff_of_even hx, commutatorDeriv_apply]

theorem curvedDiff_sub_commutatorDeriv_of_odd (D : CurvedZ2GradedDGA R A)
    {x : A} (hx : D.IsOdd x) :
    D.diff x - commutatorDeriv (R := R) D.oddGen x = (2 : R) • (x * D.oddGen) := by
  rw [curvedDiff_sub_commutatorDeriv, hx, sub_neg_eq_add, add_mul, ← two_smul R]

/-- Universal obstruction: if `∂_F = D_G` for ANY `G`, then `(x - α(x)) * ∂_F(y) = 0`
for all `x, y : A`. -/
theorem curvedDiff_eq_commutatorDeriv_obstruction (D : CurvedZ2GradedDGA R A)
    {G : A} (h : D.diff = commutatorDeriv (R := R) G) (x y : A) :
    (x - D.parity x) * D.diff y = 0 := by
  have hmul := congrArg (fun f : Module.End R A => f (x * y)) h
  rw [D.diff_mul x y, commutatorDeriv_mul] at hmul
  have hx := congrArg (fun f : Module.End R A => f x) h
  have hy := congrArg (fun f : Module.End R A => f y) h
  rw [← hx, ← hy] at hmul
  have hsub : D.diff x * y + x * D.diff y - (D.diff x * y + D.parity x * D.diff y) = 0 :=
    sub_eq_zero.mpr hmul.symm
  calc
    (x - D.parity x) * D.diff y =
        D.diff x * y + x * D.diff y - (D.diff x * y + D.parity x * D.diff y) := by
      noncomm_ring
    _ = 0 := hsub

/-- Any `CurvedZ2GradedDGA` admitting a non-even element and a unit-differential element
cannot equal `commutatorDeriv G` for ANY `G : A`. -/
theorem curvedDiff_ne_commutatorDeriv_of_unit (D : CurvedZ2GradedDGA R A)
    (hx : ∃ x : A, D.parity x ≠ x) (hy : ∃ y : A, IsUnit (D.diff y)) (G : A) :
    D.diff ≠ commutatorDeriv (R := R) G := by
  intro h
  rcases hx with ⟨x, hxne⟩
  rcases hy with ⟨y, u, hu⟩
  have hobs := curvedDiff_eq_commutatorDeriv_obstruction D h x y
  rw [← hu] at hobs
  have hmul := congrArg (fun z : A => z * (u.inv : A)) hobs
  simp only [mul_assoc, Units.val_inv, mul_one, zero_mul] at hmul
  exact hxne (sub_eq_zero.mp hmul).symm

/-- Combined separation theorem contrasting `commutatorDeriv` (ungraded Leibniz) with
`CurvedZ2GradedDGA.diff` (`α`-twisted Leibniz), including the universal obstruction and
unit-based non-equality criterion. -/
theorem commutatorDeriv_vs_curvedDiff (D : CurvedZ2GradedDGA R A) :
    (∀ x y : A, commutatorDeriv (R := R) D.oddGen (x * y) =
      commutatorDeriv (R := R) D.oddGen x * y + x * commutatorDeriv (R := R) D.oddGen y) ∧
    (∀ x y : A, D.diff (x * y) = D.diff x * y + D.parity x * D.diff y) ∧
    (∀ G : A, D.diff = commutatorDeriv (R := R) G →
      ∀ x y : A, (x - D.parity x) * D.diff y = 0) ∧
    ((∃ x : A, D.parity x ≠ x) → (∃ y : A, IsUnit (D.diff y)) →
      ∀ G : A, D.diff ≠ commutatorDeriv (R := R) G) :=
  ⟨commutatorDeriv_mul D.oddGen, D.diff_mul,
    fun _ h => curvedDiff_eq_commutatorDeriv_obstruction D h,
    curvedDiff_ne_commutatorDeriv_of_unit D⟩

end CommutatorSeparation

section ConcreteSeparations

/-- `flatMat2DGA.diff` differs from `commutatorDeriv H` for every `H : M₂(ℝ)`. -/
theorem flatMat2DGA_diff_ne_commutatorDeriv (H : Matrix (Fin 2) (Fin 2) ℝ) :
    flatMat2DGA.diff ≠ commutatorDeriv (R := ℝ) H := by
  refine curvedDiff_ne_commutatorDeriv_of_unit flatMat2DGA ?_ ?_ H
  · refine ⟨atomNeg2, ?_⟩
    intro h
    change parityConj gammaCut2 atomNeg2 = atomNeg2 at h
    rw [parityConj_gammaCut2_atomNeg2] at h
    have h01 := congrFun (congrFun h 0) 1
    simp [atomNeg2] at h01
    norm_num at h01
  · refine ⟨atomPos2, ?_⟩
    rw [flatMat2DGA_diff_atomPos2]
    exact isUnit_one

/-- `centralMat2DGA.diff` differs from `commutatorDeriv H` for every `H : M₂(ℝ)`. -/
theorem centralMat2DGA_diff_ne_commutatorDeriv (H : Matrix (Fin 2) (Fin 2) ℝ) :
    centralMat2DGA.diff ≠ commutatorDeriv (R := ℝ) H := by
  refine curvedDiff_ne_commutatorDeriv_of_unit centralMat2DGA ?_ ?_ H
  · refine ⟨gammaMir2, ?_⟩
    intro h
    change parityConj gammaCut2 gammaMir2 = gammaMir2 at h
    rw [parityConj_gammaCut2_gammaMir2] at h
    have h01 := congrFun (congrFun h 0) 1
    simp [gammaMir2] at h01
    norm_num at h01
  · refine ⟨gammaCut2, ?_⟩
    rw [centralMat2DGA_diff_gammaCut2]
    refine ⟨⟨(-2 : ℝ) • gammaSkew2, (1 / 2 : ℝ) • gammaSkew2, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, cl11_atom_laws.2.2.2.2.1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · rw [smul_mul_smul_comm, cl11_atom_laws.2.2.2.2.1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end ConcreteSeparations

section DoubledSpaceSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedAlgebra ℝ (EndH₂ (E := E)) := inferInstance

/-- `(centralDoubledDGA E).diff` differs from `commutatorDeriv H` for every `H : EndH₂`. -/
theorem centralDoubledDGA_diff_ne_commutatorDeriv [Nontrivial E]
    (H : EndH₂ (E := E)) :
    (centralDoubledDGA E).diff ≠ commutatorDeriv (R := ℝ) H := by
  refine curvedDiff_ne_commutatorDeriv_of_unit (centralDoubledDGA E) ?_ ?_ H
  · refine ⟨etaChiral (E := E), ?_⟩
    intro h
    have hOdd : (centralDoubledDGA E).parity (etaChiral (E := E)) = -(etaChiral (E := E)) :=
      (centralDoubledDGA E).oddGen_parity
    rw [hOdd] at h
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hv := congrArg (fun f : EndH₂ (E := E) => f (to_doubled x 0 : H₂ (E := E))) h
    have hsnd := congrArg WithLp.snd hv
    simp only [neg_apply, etaChiral_to_doubled, WithLp.neg_snd, snd_to_doubled] at hsnd
    have hxx : x + x = 0 := by
      calc
        x + x = x + (-x) := by nth_rw 2 [← hsnd]
        _ = 0 := add_neg_cancel x
    have hx2 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      exact hxx
    exact hx (smul_eq_zero.mp hx2 |>.resolve_left (by norm_num))
  · exact ⟨gamma5 (E := E), centralDoubledDGA_diff_gamma5_isUnit⟩

end DoubledSpaceSeparation

section R5Witness

/-- Concrete R5 witness: for `G = atomNeg2`, we have `G * G = 0` and yet
`D_G²(atomPos2) ≠ 0` (so `D_G ^ 2 ≠ 0`), in stark contrast to `∂_G² = 0` (`flatMat2DGA`),
together with explicit product separation on `atomPos2 * !![1, 0; 0, 0]`. -/
theorem nilpotent_commutatorDeriv_sq_ne_zero :
    atomNeg2 * atomNeg2 = 0 ∧
      commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) =
        !![0, -2; 0, 0] ∧
      commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) ≠ 0 ∧
      (commutatorDeriv (R := ℝ) atomNeg2) ^ 2 ≠ 0 ∧
      flatMat2DGA.diff ^ 2 = 0 ∧
      flatMat2DGA.diff (atomPos2 * !![1, 0; 0, 0]) ≠
        commutatorDeriv (R := ℝ) atomNeg2 (atomPos2 * !![1, 0; 0, 0]) := by
  have hsq : atomNeg2 * atomNeg2 = 0 := atom_car_relations.2.1
  have hD1 : commutatorDeriv (R := ℝ) atomNeg2 atomPos2 = gammaCut2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [commutatorDeriv_apply, atomNeg2, atomPos2, gammaCut2]
  have hD2 : commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) =
      !![0, -2; 0, 0] := by
    rw [hD1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [commutatorDeriv_apply, atomNeg2, gammaCut2]; try norm_num)
  have hD2_ne : commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) ≠ 0 := by
    rw [hD2]
    intro h
    have h01 := congrFun (congrFun h 0) 1
    simp at h01
  have hDsq_ne : (commutatorDeriv (R := ℝ) atomNeg2) ^ 2 ≠ 0 := by
    intro h
    have hv := congrArg
      (fun f : Module.End ℝ (Matrix (Fin 2) (Fin 2) ℝ) => f atomPos2) h
    change commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) = 0 at hv
    exact hD2_ne hv
  have hprod : atomPos2 * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = atomPos2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomPos2, Matrix.mul_apply, Fin.sum_univ_two]
  have hsep : flatMat2DGA.diff (atomPos2 * !![1, 0; 0, 0]) ≠
      commutatorDeriv (R := ℝ) atomNeg2 (atomPos2 * !![1, 0; 0, 0]) := by
    rw [hprod, flatMat2DGA_diff_atomPos2, hD1]
    intro h
    have h11 := congrFun (congrFun h 1) 1
    simp [gammaCut2] at h11
    norm_num at h11
  exact ⟨hsq, hD2, hD2_ne, hDsq_ne, flatMat2DGA_diff_sq, hsep⟩

end R5Witness

end InfoGeometry.Canonical.CurvedZ2GradedDGA
