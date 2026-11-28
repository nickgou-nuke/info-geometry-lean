/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit
import InfoGeometry.Erlangen.FlowSymmetryClosure
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Smooth change of coordinates for vector fields and flow generators

The existing smooth diffeomorphism group acts on actual vector fields `E → E`
by Fréchet pushforward. The chain rule proves the action law, with no
commutativity assumption on diffeomorphisms. Linearity in the field supplies
the native action on submodules as well.

Differentiating the conjugated time maps at zero gives the pushed-forward
generator. Thus symmetry of the complete flow implies symmetry of its
generator. The converse would require an ODE uniqueness argument and is not
part of this construction. A homomorphism alone supplies no time regularity.

Pointwise fixing of a field family implies setwise preservation of its real
linear span. This span consists of global fields with constant coefficients;
it is not identified here with a smooth distribution or a PDE symmetry group.
The actions on fields and submodules are scoped to avoid changing unrelated
pointwise function actions.

Outside this namespace, open the
`InfoGeometry.Canonical.SmoothVectorFieldPushforward` scope for fields and
the additional `Pointwise` scope for submodules.
-/

noncomputable section

namespace InfoGeometry.Canonical.SmoothVectorFieldPushforward

open InfoGeometry.Erlangen.FlowSymmetryClosure
open scoped ContDiff Pointwise InfoGeometry.Erlangen.FlowSymmetryClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness of the acting homeomorphism supplies its actual derivative. -/
theorem differentiable (g : smoothDiffeomorphismSubgroup E) :
    Differentiable ℝ (g.val : E → E) :=
  g.property.1.differentiable (by simp)

/-- Push a field forward by a smooth change of coordinates. -/
def pushforward (g : smoothDiffeomorphismSubgroup E) (X : E → E) : E → E :=
  fun y => fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y))

/-- Smooth fields remain smooth under the derivative pushforward. -/
theorem contDiff_pushforward (g : smoothDiffeomorphismSubgroup E) (X : E → E)
    (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (pushforward g X) := by
  exact ((g.property.1.fderiv_right (m := ∞) (by simp)).comp g.property.2).clm_apply
    (hX.comp g.property.2)

@[simp] theorem pushforward_one (X : E → E) : pushforward 1 X = X := by
  funext y
  change fderiv ℝ id y (X y) = X y
  simp

/-- The Fréchet chain rule gives composition in the correct noncommutative order. -/
theorem pushforward_mul (g h : smoothDiffeomorphismSubgroup E) (X : E → E) :
    pushforward (g * h) X = pushforward g (pushforward h X) := by
  funext y
  change fderiv ℝ ((g.val : E → E) ∘ (h.val : E → E))
      (h.val.symm (g.val.symm y)) (X (h.val.symm (g.val.symm y))) =
    fderiv ℝ (g.val : E → E) (g.val.symm y)
      (fderiv ℝ (h.val : E → E) (h.val.symm (g.val.symm y))
        (X (h.val.symm (g.val.symm y))))
  rw [fderiv_comp _ (differentiable g _) (differentiable h _)]
  simp

@[simp] theorem pushforward_zero (g : smoothDiffeomorphismSubgroup E) :
    pushforward g (0 : E → E) = 0 := by
  funext y
  exact map_zero _

theorem pushforward_add (g : smoothDiffeomorphismSubgroup E) (X Y : E → E) :
    pushforward g (X + Y) = pushforward g X + pushforward g Y := by
  funext y
  exact map_add _ _ _

theorem pushforward_smul (g : smoothDiffeomorphismSubgroup E) (r : ℝ) (X : E → E) :
    pushforward g (r • X) = r • pushforward g X := by
  funext y
  exact map_smul _ _ _

/-- Select derivative pushforward in preference to generic function actions. -/
scoped instance (priority := 2000) vectorFieldPushforwardSMul :
    SMul (smoothDiffeomorphismSubgroup E) (E → E) where
  smul := pushforward

/-- The native group action on fields, defined by the actual Fréchet derivative. -/
scoped instance (priority := 2000) vectorFieldPushforwardAction :
    MulAction (smoothDiffeomorphismSubgroup E) (E → E) where
  toSMul := vectorFieldPushforwardSMul
  one_smul := pushforward_one
  mul_smul := pushforward_mul

/-- The pushforward action is additive in the field. -/
scoped instance (priority := 2000) vectorFieldPushforwardDistribMulAction :
    DistribMulAction (smoothDiffeomorphismSubgroup E) (E → E) where
  toMulAction := vectorFieldPushforwardAction
  smul_zero := pushforward_zero
  smul_add := pushforward_add

/-- Pushforward commutes with constant real scalar multiplication of fields. -/
scoped instance vectorFieldPushforwardSMulCommClass :
    SMulCommClass (smoothDiffeomorphismSubgroup E) ℝ (E → E) where
  smul_comm := pushforward_smul

@[simp] theorem smul_field_apply (g : smoothDiffeomorphismSubgroup E)
    (X : E → E) (y : E) :
    (g • X) y = fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y)) := rfl

/-- The same coordinate change conjugates the field's actual symmetry subgroup. -/
theorem vectorField_stabilizer_pushforward (g : smoothDiffeomorphismSubgroup E)
    (X : E → E) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (pushforward g X) =
      (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X).map
        (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g X

/-- The native orbit of a field is the coset space of its pointwise symmetry group. -/
def vectorFieldOrbitEquivQuotient (X : E → E) :
    MulAction.orbit (smoothDiffeomorphismSubgroup E) X ≃
      (smoothDiffeomorphismSubgroup E) ⧸
        MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X :=
  MulAction.orbitEquivQuotientStabilizer (smoothDiffeomorphismSubgroup E) X

/-- Pointwise field symmetries preserve the generated real linear span setwise.
The target uses Mathlib's native action on submodules. -/
theorem fixingSubgroup_le_span_stabilizer (S : Set (E → E)) :
    fixingSubgroup (smoothDiffeomorphismSubgroup E) S ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (Submodule.span ℝ S) := by
  intro g hg
  have h := (mem_fixingSubgroup_iff (smoothDiffeomorphismSubgroup E)).mp hg
  have himage : g • S = S := by
    ext X
    change (∃ Y ∈ S, g • Y = X) ↔ X ∈ S
    constructor
    · rintro ⟨Y, hY, hYX⟩
      rw [h Y hY] at hYX
      exact hYX ▸ hY
    · intro hX
      exact ⟨X, hX, h X hX⟩
  change g • Submodule.span ℝ S = Submodule.span ℝ S
  rw [Submodule.smul_span, himage]

@[simp] theorem conjugateFlow_apply_point (g : smoothDiffeomorphismSubgroup E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)
    (t : Multiplicative ℝ) (y : E) :
    (conjugateFlow g Φ t).val y = g.val ((Φ t).val (g.val.symm y)) := rfl

/-- At time zero, differentiation intertwines flow conjugation with Fréchet
pushforward. The time derivative is an explicit hypothesis at every basepoint. -/
theorem hasDerivAt_conjugateFlow (g : smoothDiffeomorphismSubgroup E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (y : E) :
    HasDerivAt (fun t : ℝ => (conjugateFlow g Φ (Multiplicative.ofAdd t)).val y)
      (pushforward g X y) 0 := by
  have h0 : g.val.symm y = (Φ (Multiplicative.ofAdd (0 : ℝ))).val (g.val.symm y) := by
    simp
  have h := (differentiable g (g.val.symm y)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hΦ (g.val.symm y)) h0
  simpa only [Function.comp_def, conjugateFlow_apply_point, pushforward] using h

/-- Every symmetry of the full flow fixes its time-zero generator.
This direction uses derivative uniqueness, not ODE uniqueness. -/
theorem flow_stabilizer_le_vectorField_stabilizer
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) Φ ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X := by
  intro g hg
  change conjugateFlow g Φ = Φ at hg
  change pushforward g X = X
  funext y
  have h := hasDerivAt_conjugateFlow g Φ X hΦ y
  rw [hg] at h
  exact h.unique (hΦ y)

/-- Time maps of a one-parameter group commute with the entire flow. -/
theorem timeMap_mem_flow_stabilizer
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (t : Multiplicative ℝ) :
    Φ t ∈ MulAction.stabilizer (smoothDiffeomorphismSubgroup E) Φ := by
  apply (mem_flow_stabilizer_iff (Φ t) Φ).mpr
  intro u
  change Φ t * Φ u = Φ u * Φ t
  rw [← map_mul, ← map_mul, mul_comm t u]

/-- A flow preserves its own generator under the actual derivative pushforward. -/
theorem timeMap_pushforward_generator
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (t : Multiplicative ℝ) : pushforward (Φ t) X = X :=
  flow_stabilizer_le_vectorField_stabilizer Φ X hΦ (timeMap_mem_flow_stabilizer Φ t)

end InfoGeometry.Canonical.SmoothVectorFieldPushforward
