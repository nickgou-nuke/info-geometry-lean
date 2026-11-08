/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

/-!
# Real dual twistor incidence and its two canonical forms

The carrier is `V × Module.Dual ℝ V`, with the actual algebraic dual, rather
than a second coordinate copy of `V`.  The symmetric evaluation form and the
alternating evaluation form are different native bilinear forms.  The
ambitwistor constraint is `φ v = 0`; its rank-one operator is square-zero
exactly on this constraint for nonzero primal and dual factors.

These are algebraic constructions.  No null-geodesic quotient, manifold,
complexification, or analytic quantization is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealDualTwistor

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A real twistor together with a genuine covector. -/
abbrev Carrier (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V × Module.Dual ℝ V

/-- The symmetric hyperbolic evaluation form, without a factor of `1/2`. -/
def neutralForm : LinearMap.BilinForm ℝ (Carrier V) :=
  LinearMap.mk₂ ℝ (fun p q => p.2 q.1 + q.2 p.1)
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, smul_eq_mul, mul_add])
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, smul_eq_mul, mul_add])

/-- The canonical alternating form on a vector space and its dual. -/
def symplecticForm : LinearMap.BilinForm ℝ (Carrier V) :=
  LinearMap.mk₂ ℝ (fun p q => q.2 p.1 - p.2 q.1)
    (by intros; simp [map_add, sub_add_sub_comm])
    (by intros; simp [map_smul, smul_eq_mul, mul_sub])
    (by intros; simp [map_add, sub_add_sub_comm])
    (by intros; simp [map_smul, smul_eq_mul, mul_sub])

@[simp] theorem neutralForm_apply (p q : Carrier V) :
    neutralForm p q = p.2 q.1 + q.2 p.1 := rfl

@[simp] theorem symplecticForm_apply (p q : Carrier V) :
    symplecticForm p q = q.2 p.1 - p.2 q.1 := rfl

theorem neutralForm_symm (p q : Carrier V) :
    neutralForm p q = neutralForm q p := by simp [add_comm]

theorem symplecticForm_skew (p q : Carrier V) :
    symplecticForm p q = -symplecticForm q p := by simp

@[simp] theorem symplecticForm_self (p : Carrier V) :
    symplecticForm p p = 0 := by simp

/-- Algebraic covectors separate points; no finite-dimensional assumption. -/
theorem eq_zero_of_dual_vanishes (v : V)
    (h : ∀ φ : Module.Dual ℝ V, φ v = 0) : v = 0 := by
  let b := Module.Basis.ofVectorSpace ℝ V
  apply b.repr.injective
  ext i
  simpa using h (b.coord i)

theorem neutralForm_left_radical (p : Carrier V)
    (h : ∀ q, neutralForm p q = 0) : p = 0 := by
  apply Prod.ext
  · apply eq_zero_of_dual_vanishes
    intro φ
    simpa using h (0, φ)
  · ext v
    simpa using h (v, 0)

theorem neutralForm_nondegenerate :
    (neutralForm (V := V)).Nondegenerate := by
  constructor
  · exact neutralForm_left_radical
  · intro p hp
    apply neutralForm_left_radical p
    intro q
    rw [neutralForm_symm]
    exact hp q

theorem symplecticForm_left_radical (p : Carrier V)
    (h : ∀ q, symplecticForm p q = 0) : p = 0 := by
  apply Prod.ext
  · apply eq_zero_of_dual_vanishes
    intro φ
    simpa using h (0, φ)
  · ext v
    simpa using h (v, 0)

theorem symplecticForm_nondegenerate :
    (symplecticForm (V := V)).Nondegenerate := by
  constructor
  · exact symplecticForm_left_radical
  · intro p hp
    apply symplecticForm_left_radical p
    intro q
    rw [symplecticForm_skew, hp q, neg_zero]

/-- The primal/covector grading, with square `+1`. -/
def para : Module.End ℝ (Carrier V) :=
  (LinearMap.id : Module.End ℝ V).prodMap
    (-LinearMap.id : Module.End ℝ (Module.Dual ℝ V))

@[simp] theorem para_apply (p : Carrier V) : para p = (p.1, -p.2) := rfl

@[simp] theorem para_sq : para (V := V) * para = 1 := by
  ext p <;> simp

theorem neutralForm_para_anti (p q : Carrier V) :
    neutralForm (para p) (para q) = -neutralForm p q := by simp; ring

theorem symplecticForm_eq_neutralForm_para (p q : Carrier V) :
    symplecticForm p q = neutralForm (para p) q := by simp; ring

/-- The contragredient lift of a real change of twistor frame. -/
def frameAction (e : V ≃ₗ[ℝ] W) : Carrier V ≃ₗ[ℝ] Carrier W where
  toFun p := (e p.1, p.2.comp e.symm.toLinearMap)
  invFun p := (e.symm p.1, p.2.comp e.toLinearMap)
  left_inv p := by
    apply Prod.ext
    · simp
    · ext x; simp
  right_inv p := by
    apply Prod.ext
    · simp
    · ext x; simp
  map_add' p q := by
    apply Prod.ext
    · simp
    · ext x; simp
  map_smul' c p := by
    apply Prod.ext
    · simp
    · ext x; simp

@[simp] theorem frameAction_fst (e : V ≃ₗ[ℝ] W) (p : Carrier V) :
    (frameAction e p).1 = e p.1 := rfl

@[simp] theorem frameAction_snd_apply (e : V ≃ₗ[ℝ] W)
    (p : Carrier V) (w : W) : (frameAction e p).2 w = p.2 (e.symm w) := rfl

@[simp] theorem neutralForm_frameAction (e : V ≃ₗ[ℝ] W) (p q : Carrier V) :
    neutralForm (frameAction e p) (frameAction e q) = neutralForm p q := by simp

@[simp] theorem symplecticForm_frameAction (e : V ≃ₗ[ℝ] W) (p q : Carrier V) :
    symplecticForm (frameAction e p) (frameAction e q) = symplecticForm p q := by simp

/-- Affine ambitwistor incidence; nonzero conditions are imposed separately. -/
def Incident (p : Carrier V) : Prop := p.2 p.1 = 0

@[simp] theorem incident_frameAction (e : V ≃ₗ[ℝ] W) (p : Carrier V) :
    Incident (frameAction e p) ↔ Incident p := by simp [Incident]

theorem incident_iff_neutral_self (p : Carrier V) :
    Incident p ↔ neutralForm p p = 0 := by
  simp only [Incident, neutralForm_apply]
  constructor <;> intro h <;> linarith

theorem incident_rescale (p : Carrier V) (a b : ℝ) (h : Incident p) :
    Incident (a • p.1, b • p.2) := by
  change p.2 p.1 = 0 at h
  simp [Incident, map_smul, h]

/-- The actual endomorphism `x ↦ φ(x) v`. -/
def dyad (p : Carrier V) : Module.End ℝ V := p.2.smulRight p.1

@[simp] theorem dyad_apply (p : Carrier V) (x : V) :
    dyad p x = p.2 x • p.1 := rfl

theorem dyad_mul (p q : Carrier V) :
    dyad p * dyad q = (p.2 q.1) • q.2.smulRight p.1 := by
  ext x
  simp only [Module.End.mul_apply, dyad_apply, map_smul,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]
  rw [mul_comm]

theorem dyad_sq (p : Carrier V) :
    dyad p * dyad p = (p.2 p.1) • dyad p := dyad_mul p p

theorem dyad_ne_zero (p : Carrier V) (hv : p.1 ≠ 0) (hφ : p.2 ≠ 0) :
    dyad p ≠ 0 := by
  intro h
  apply hφ
  ext x
  have hx : p.2 x • p.1 = 0 := by
    simpa only [dyad_apply, LinearMap.zero_apply] using
      congrArg (fun A : Module.End ℝ V => A x) h
  exact (smul_eq_zero.mp hx).resolve_right hv

/-- Incidence is exactly square-zero rank-one dynamics on nonzero factors. -/
theorem dyad_sq_zero_iff (p : Carrier V) (hv : p.1 ≠ 0) (hφ : p.2 ≠ 0) :
    dyad p * dyad p = 0 ↔ Incident p := by
  rw [dyad_sq, smul_eq_zero]
  exact or_iff_left (dyad_ne_zero p hv hφ)

/-- Rank-one operators transform by conjugation, using the same dual action. -/
theorem dyad_frameAction (e : V ≃ₗ[ℝ] W) (p : Carrier V) :
    dyad (frameAction e p) =
      e.toLinearMap.comp ((dyad p).comp e.symm.toLinearMap) := by
  ext x
  simp [dyad_apply]

/-- A nonzero real incidence pair: neither factor nor its dyad vanishes. -/
def examplePair : Carrier (ℝ × ℝ) := ((1, 0), LinearMap.snd ℝ ℝ ℝ)

theorem examplePair_incident : Incident examplePair := rfl

theorem examplePair_dyad_ne_zero : dyad examplePair ≠ 0 := by
  intro h
  have hx := congrArg (fun A : Module.End ℝ (ℝ × ℝ) => (A (0, 1)).1) h
  norm_num [dyad_apply, examplePair] at hx

end InfoGeometry.Twistor.RealDualTwistor
