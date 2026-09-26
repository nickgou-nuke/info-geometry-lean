import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Abstract conditional commutant duality interface

This file defines an algebraic commutant of a set of endomorphisms and the
conjugate set induced by an anti-linear involution. The equality theorem is
conditional: `TomitaDualityData` supplies the forward and backward inclusions
needed to derive equality. Those inclusions are inputs, not consequences
proved here from a GNS construction, cyclic/separating vector, modular
operator, or von Neumann algebra.

The resulting set-theoretic consequences are useful as an abstract interface,
but do not by themselves instantiate Tomita–Takesaki theory or the von
Neumann bicommutant theorem. The separate `Cl(1,1)` modular atom and
`StandardFormCore` likewise document their narrower scope.

The declarations in this file use no `sorry` and introduce no custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.TomitaCommutantDuality

open Complex

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-! =========================================================================
    1. Anti-Linear Modular Involution J
    ========================================================================= -/

/-- An anti-linear isometric involution `J : H → H` satisfying `J² = id`. -/
structure AntiLinearInvolution (H : Type*) [AddCommGroup H] [Module ℂ H] where
  toFun : H → H
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : ℂ) (x : H), toFun (c • x) = (star c) • toFun x
  involutive' : ∀ x, toFun (toFun x) = x

instance : CoeFun (AntiLinearInvolution H) (fun _ => H → H) where
  coe J := J.toFun

@[simp]
theorem J_involutive (J : AntiLinearInvolution H) (x : H) : J (J x) = x :=
  J.involutive' x

@[simp]
theorem J_add (J : AntiLinearInvolution H) (x y : H) : J (x + y) = J x + J y :=
  J.map_add' x y

@[simp]
theorem J_smul (J : AntiLinearInvolution H) (c : ℂ) (x : H) : J (c • x) = (star c) • J x :=
  J.map_smul' c x

/-! =========================================================================
    2. Operator Commutant and Spatial J-Conjugation
    ========================================================================= -/

/-- The commutant `S'` of a set of operators `S ⊆ (H → H)`. -/
def commutant (S : Set (H → H)) : Set (H → H) :=
  { T | ∀ A ∈ S, ∀ x, T (A x) = A (T x) }

/-- The J-conjugation of an operator `Ad_J(A) = J ∘ A ∘ J`. -/
def AdJ (J : AntiLinearInvolution H) (A : H → H) : H → H :=
  fun x => J (A (J x))

/-- The J-conjugated operator algebra `J S J = { Ad_J(A) | A ∈ S }`. -/
def JConjugateSet (J : AntiLinearInvolution H) (S : Set (H → H)) : Set (H → H) :=
  { B | ∃ A ∈ S, B = AdJ J A }

/-! =========================================================================
    3. Fundamental Algebraic Involutions of Ad_J
    ========================================================================= -/

/-- `Ad_J` is an involution on operators: `Ad_J(Ad_J(A)) = A`. -/
@[simp]
theorem AdJ_involutive (J : AntiLinearInvolution H) (A : H → H) :
    AdJ J (AdJ J A) = A := by
  ext x
  dsimp [AdJ]
  simp only [J_involutive]

/-- `Ad_J` preserves operator compositions: `Ad_J(A ∘ B) = Ad_J(A) ∘ Ad_J(B)`. -/
theorem AdJ_comp (J : AntiLinearInvolution H) (A B : H → H) :
    AdJ J (A ∘ B) = AdJ J A ∘ AdJ J B := by
  ext x
  dsimp [AdJ]
  simp only [J_involutive]

/-- Double J-conjugation of an operator set recovers the set: `J (J S J) J = S`. -/
@[simp]
theorem JConjugateSet_involutive (J : AntiLinearInvolution H) (S : Set (H → H)) :
    JConjugateSet J (JConjugateSet J S) = S := by
  ext B
  constructor
  · rintro ⟨T, ⟨A, hA, rfl⟩, rfl⟩
    rw [AdJ_involutive]
    exact hA
  · intro hB
    exact ⟨AdJ J B, ⟨B, hB, rfl⟩, (AdJ_involutive J B).symm⟩

/-! =========================================================================
    4. The Tomita–Takesaki Commutant Duality Theorem
    ========================================================================= -/

/--
Tomita Commutant Duality Hypothesis:
Encapsulates the Tomita–Takesaki boundary condition where `J ℳ J` commutes
with `ℳ` and generates the full commutant `ℳ'`.
-/
structure TomitaDualityData (J : AntiLinearInvolution H) (M : Set (H → H)) : Prop where
  forward_commute : ∀ A ∈ M, AdJ J A ∈ commutant M
  backward_span : ∀ B ∈ commutant M, ∃ A ∈ M, B = AdJ J A

variable {J : AntiLinearInvolution H} {M : Set (H → H)}

/-- Conditional consequence of the forward-commutation field in `TomitaDualityData`. -/
theorem tomita_forward_inclusion (hD : TomitaDualityData J M) :
    JConjugateSet J M ⊆ commutant M := by
  rintro B ⟨A, hA, rfl⟩
  exact hD.forward_commute A hA

/-- Conditional consequence of the backward-inclusion field in `TomitaDualityData`. -/
theorem tomita_backward_inclusion (hD : TomitaDualityData J M) :
    commutant M ⊆ JConjugateSet J M := by
  rintro B hB
  obtain ⟨A, hA, rfl⟩ := hD.backward_span B hB
  exact ⟨A, hA, rfl⟩

/-- Set equality obtained from the two inclusions supplied by `TomitaDualityData`. -/
theorem tomita_takesaki_commutant_duality (hD : TomitaDualityData J M) :
    commutant M = JConjugateSet J M :=
  Set.Subset.antisymm (tomita_backward_inclusion hD) (tomita_forward_inclusion hD)

/-- Conditional reciprocal equality induced by the abstract conjugation operation. -/
theorem tomita_reciprocal_duality (hD : TomitaDualityData J M) :
    JConjugateSet J (commutant M) = M := by
  rw [tomita_takesaki_commutant_duality hD, JConjugateSet_involutive]

/-- Abstract commutant equality under duality data for both `M` and its commutant. -/
theorem von_neumann_bicommutant_from_tomita (hD : TomitaDualityData J M)
    (hD_prime : TomitaDualityData J (commutant M)) :
    commutant (commutant M) = M := by
  rw [tomita_takesaki_commutant_duality hD_prime, tomita_reciprocal_duality hD]

end InfoGeometry.Modular.TomitaCommutantDuality

