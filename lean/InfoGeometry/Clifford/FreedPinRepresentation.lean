/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NormalizedVectorPin
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Represented Pin suspensions, grading, and linear operator intertwiners

The ordered algebra maps of `FreedCliffordSuspension` now act on arbitrary
represented modules. The normalized Pin action is a homomorphism into actual
units and, for bounded representations, continuous linear equivalences.

A source vector maps to a product of two target vectors. Thus a linear map
which anticommutes with the target vector actions intertwines the suspended
action. This applies to grading operators and to a linear unbounded operator
on an invariant submodule domain. Ambient evenness is not identified with the
source Clifford grading: the source odd generator has an ambient even image.
-/

noncomputable section

namespace InfoGeometry.Clifford.FreedPinRepresentation

open CliffordAlgebra
open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.Clifford.NormalizedVectorPin

variable {R M A : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Ring A] [Algebra R A]

/-- The represented positive suspension retains the ordered product `v * e`. -/
def positiveRepresentation (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] A) : CliffordAlgebra Q →ₐ[R] A :=
  ρ.comp (positiveMap Q)

/-- The represented negative suspension has source quadratic form `-Q`. -/
def negativeRepresentation (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] A) : CliffordAlgebra (-Q) →ₐ[R] A :=
  ρ.comp (negativeMap Q)

@[simp] theorem positiveRepresentation_ι (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] A) (v : M) :
    positiveRepresentation Q ρ (ι Q v) =
      ρ (ι (positiveForm Q) (v, 0)) * ρ (ι (positiveForm Q) (0, 1)) := by
  simp only [positiveRepresentation, AlgHom.comp_apply, positiveMap_ι, map_mul]

@[simp] theorem negativeRepresentation_ι (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] A) (v : M) :
    negativeRepresentation Q ρ (ι (-Q) v) =
      ρ (ι (negativeForm Q) (v, 0)) * ρ (ι (negativeForm Q) (0, 1)) := by
  simp only [negativeRepresentation, AlgHom.comp_apply, negativeMap_ι, map_mul]

theorem positiveRepresentation_pair (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] A) (v w : M) :
    positiveRepresentation Q ρ (ι Q v * ι Q w) =
      ρ (ι (positiveForm Q) (v, 0)) * ρ (ι (positiveForm Q) (w, 0)) := by
  change ρ (positiveMap Q (ι Q v * ι Q w)) = _
  rw [positiveMap_ι_mul_ι, map_mul]

theorem negativeRepresentation_pair (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] A) (v w : M) :
    negativeRepresentation Q ρ (ι (-Q) v * ι (-Q) w) =
      -(ρ (ι (negativeForm Q) (v, 0)) * ρ (ι (negativeForm Q) (w, 0))) := by
  change ρ (negativeMap Q (ι (-Q) v * ι (-Q) w)) = _
  rw [negativeMap_ι_mul_ι, map_neg, map_mul]

/-- A Clifford representation induces an action of the actual normalized Pin group. -/
def pinRepresentation (Q : QuadraticForm R M) (ρ : CliffordAlgebra Q →ₐ[R] A) :
    pin Q →* Aˣ :=
  (Units.map ρ.toMonoidHom).comp (pin Q).subtype

@[simp] theorem pinRepresentation_coe (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] A) (g : pin Q) :
    (pinRepresentation Q ρ g : A) = ρ ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  rfl

@[simp] theorem pinRepresentation_vector (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] A) (v : M) (hv : Q v = 1 ∨ Q v = -1) :
    (pinRepresentation Q ρ (pinVector Q v hv) : A) = ρ (ι Q v) := by
  rw [pinRepresentation_coe, pinVector_coe]

/-- Representing after the positive group embedding agrees with representing
the pullback Clifford algebra action. -/
theorem positivePinRepresentation_comp (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] A) :
    pinRepresentation Q (positiveRepresentation Q ρ) =
      (Units.map ρ.toMonoidHom).comp
        ((evenPinToUnits (positiveForm Q)).comp (positivePinHom Q)) := by
  ext g
  rfl

theorem negativePinRepresentation_comp (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] A) :
    pinRepresentation (-Q) (negativeRepresentation Q ρ) =
      (Units.map ρ.toMonoidHom).comp
        ((evenPinToUnits (negativeForm Q)).comp (negativePinHom Q)) := by
  ext g
  rfl

section Intertwiners

variable {V W : Type*} [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Intertwining the generating vectors suffices for the universal Clifford
action, with no finite-dimensional assumption on either module. -/
theorem intertwines_of_vectors (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R V)
    (σ : CliffordAlgebra Q →ₐ[R] Module.End R W) (T : V →ₗ[R] W)
    (h : ∀ v x, T (ρ (ι Q v) x) = σ (ι Q v) (T x))
    (a : CliffordAlgebra Q) (x : V) : T (ρ a x) = σ a (T x) := by
  induction a using CliffordAlgebra.induction generalizing x with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι v => exact h v x
  | mul a b ha hb =>
      simp only [map_mul, Module.End.mul_apply]
      rw [ha, hb]
  | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      rw [ha, hb]

/-- Two target odd actions become an intertwining ordered source action. -/
theorem positive_intertwines_of_odd_vectors (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R V)
    (σ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R W) (T : V →ₗ[R] W)
    (h : ∀ v x, T (ρ (ι (positiveForm Q) v) x) =
      -(σ (ι (positiveForm Q) v) (T x)))
    (a : CliffordAlgebra Q) (x : V) :
    T (positiveRepresentation Q ρ a x) = positiveRepresentation Q σ a (T x) := by
  apply intertwines_of_vectors Q (positiveRepresentation Q ρ)
    (positiveRepresentation Q σ) T _ a x
  intro v y
  simp only [positiveRepresentation_ι, Module.End.mul_apply]
  rw [h, h, map_neg, neg_neg]

theorem negative_intertwines_of_odd_vectors (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] Module.End R V)
    (σ : CliffordAlgebra (negativeForm Q) →ₐ[R] Module.End R W) (T : V →ₗ[R] W)
    (h : ∀ v x, T (ρ (ι (negativeForm Q) v) x) =
      -(σ (ι (negativeForm Q) v) (T x)))
    (a : CliffordAlgebra (-Q)) (x : V) :
    T (negativeRepresentation Q ρ a x) = negativeRepresentation Q σ a (T x) := by
  apply intertwines_of_vectors (-Q) (negativeRepresentation Q ρ)
    (negativeRepresentation Q σ) T _ a x
  intro v y
  simp only [negativeRepresentation_ι, Module.End.mul_apply]
  rw [h, h, map_neg, neg_neg]

/-- In particular, a target grading commutes with every represented suspended
Pin element; the source Clifford grading is not identified with this grading. -/
theorem positivePin_preserves_grading (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R V) (Γ : Module.End R V)
    (h : ∀ v x, Γ (ρ (ι (positiveForm Q) v) x) =
      -(ρ (ι (positiveForm Q) v) (Γ x))) (g : pin Q) (x : V) :
    Γ ((pinRepresentation Q (positiveRepresentation Q ρ) g : Module.End R V) x) =
      (pinRepresentation Q (positiveRepresentation Q ρ) g : Module.End R V) (Γ x) :=
  positive_intertwines_of_odd_vectors Q ρ ρ Γ h _ x

theorem negativePin_preserves_grading (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] Module.End R V) (Γ : Module.End R V)
    (h : ∀ v x, Γ (ρ (ι (negativeForm Q) v) x) =
      -(ρ (ι (negativeForm Q) v) (Γ x))) (g : pin (-Q)) (x : V) :
    Γ ((pinRepresentation (-Q) (negativeRepresentation Q ρ) g : Module.End R V) x) =
      (pinRepresentation (-Q) (negativeRepresentation Q ρ) g : Module.End R V) (Γ x) :=
  negative_intertwines_of_odd_vectors Q ρ ρ Γ h _ x

/-- Invariance of a submodule under target vectors extends to the whole
Clifford algebra by its universal generation. -/
theorem preserves_domain_of_vectors (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R V) (S : Submodule R V)
    (h : ∀ v x, x ∈ S → ρ (ι Q v) x ∈ S)
    (a : CliffordAlgebra Q) (x : V) (hx : x ∈ S) : ρ a x ∈ S := by
  induction a using CliffordAlgebra.induction generalizing x with
  | algebraMap r => simpa [Algebra.algebraMap_eq_smul_one] using S.smul_mem r hx
  | ι v => exact h v x hx
  | mul a b ha hb =>
      simp only [map_mul, Module.End.mul_apply]
      exact ha _ (hb x hx)
  | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      exact S.add_mem (ha x hx) (hb x hx)

/-- The target action restricted to its invariant linear domain. -/
def domainRepresentation (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R V) (S : Submodule R V)
    (h : ∀ v x, x ∈ S → ρ (ι Q v) x ∈ S) :
    CliffordAlgebra Q →ₐ[R] Module.End R S where
  toFun a := (ρ a).restrict (preserves_domain_of_vectors Q ρ S h a)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' r := by ext x; simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem domainRepresentation_apply (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R V) (S : Submodule R V)
    (h : ∀ v x, x ∈ S → ρ (ι Q v) x ∈ S) (a : CliffordAlgebra Q) (x : S) :
    (domainRepresentation Q ρ S h a x : V) = ρ a x := rfl

/-- An odd domain operator becomes equivariant for the represented suspended
Pin action. The domain action is constructed from vector invariance. -/
theorem positivePin_domain_operator (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R V) (S : Submodule R V)
    (hS : ∀ v x, x ∈ S → ρ (ι (positiveForm Q) v) x ∈ S) (D : S →ₗ[R] V)
    (hD : ∀ v x, D (domainRepresentation (positiveForm Q) ρ S hS
      (ι (positiveForm Q) v) x) = -(ρ (ι (positiveForm Q) v) (D x)))
    (g : pin Q) (x : S) :
    D ((pinRepresentation Q (positiveRepresentation Q
      (domainRepresentation (positiveForm Q) ρ S hS)) g : Module.End R S) x) =
      (pinRepresentation Q (positiveRepresentation Q ρ) g : Module.End R V) (D x) :=
  positive_intertwines_of_odd_vectors Q
    (domainRepresentation (positiveForm Q) ρ S hS) ρ D hD _ x

/-- The negative suspension has the same domain-equivariance mechanism,
with its declared source form `-Q`. -/
theorem negativePin_domain_operator (Q : QuadraticForm R M)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[R] Module.End R V) (S : Submodule R V)
    (hS : ∀ v x, x ∈ S → ρ (ι (negativeForm Q) v) x ∈ S) (D : S →ₗ[R] V)
    (hD : ∀ v x, D (domainRepresentation (negativeForm Q) ρ S hS
      (ι (negativeForm Q) v) x) = -(ρ (ι (negativeForm Q) v) (D x)))
    (g : pin (-Q)) (x : S) :
    D ((pinRepresentation (-Q) (negativeRepresentation Q
      (domainRepresentation (negativeForm Q) ρ S hS)) g : Module.End R S) x) =
      (pinRepresentation (-Q) (negativeRepresentation Q ρ) g : Module.End R V) (D x) :=
  negative_intertwines_of_odd_vectors Q
    (domainRepresentation (negativeForm Q) ρ S hS) ρ D hD _ x

end Intertwiners

section ContinuousAction

variable {N H : Type*} [AddCommGroup N] [Module ℝ N]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bounded Clifford representations give genuine continuous linear Pin actions. -/
def continuousPinAction (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H)) : pin Q →* (H ≃L[ℝ] H) :=
  (ContinuousLinearEquiv.unitsEquiv ℝ H).toMonoidHom.comp (pinRepresentation Q ρ)

@[simp] theorem continuousPinAction_apply (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H)) (g : pin Q) (x : H) :
    continuousPinAction Q ρ g x =
      ρ ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) x := rfl

theorem positiveContinuousPinAction_vector (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra (positiveForm Q) →ₐ[ℝ] (H →L[ℝ] H))
    (v : N) (hv : Q v = 1 ∨ Q v = -1) (x : H) :
    continuousPinAction Q (positiveRepresentation Q ρ) (pinVector Q v hv) x =
      ρ (ι (positiveForm Q) (v, 0)) (ρ (ι (positiveForm Q) (0, 1)) x) := by
  rw [continuousPinAction_apply, pinVector_coe, positiveRepresentation_ι]
  rfl

theorem negativeContinuousPinAction_vector (Q : QuadraticForm ℝ N)
    (ρ : CliffordAlgebra (negativeForm Q) →ₐ[ℝ] (H →L[ℝ] H))
    (v : N) (hv : (-Q) v = 1 ∨ (-Q) v = -1) (x : H) :
    continuousPinAction (-Q) (negativeRepresentation Q ρ) (pinVector (-Q) v hv) x =
      ρ (ι (negativeForm Q) (v, 0)) (ρ (ι (negativeForm Q) (0, 1)) x) := by
  rw [continuousPinAction_apply, pinVector_coe, negativeRepresentation_ι]
  rfl

end ContinuousAction

end InfoGeometry.Clifford.FreedPinRepresentation

end
