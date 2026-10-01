import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Kähler--Atiyah Cartan-form realization on the exterior algebra

This module formalizes the algebraic core of the Kähler--Atiyah construction
directly on Mathlib's `ExteriorAlgebra`.

For a real module `V` equipped with a bilinear form `g`, a vector `v`
acts on `ExteriorAlgebra ℝ V` by

`c_g(v) = ε(v) + ι(g(v,-))`,

where `ε(v)` is left exterior multiplication and `ι(g(v,-))` is Mathlib's
left contraction operator.  The creation/annihilation CAR imply

`c_g(v)c_g(u) + c_g(u)c_g(v)
    = (g v u + g u v) • 1`.

For symmetric `g`, this is the Clifford relation

`{c_g(v), c_g(u)} = 2 g(v,u) • 1`.

The square law `c_g(v)^2 = g(v,v) • 1` then gives a canonical algebra
homomorphism from the Clifford algebra of the quadratic form
`v ↦ g(v,v)` into endomorphisms of the exterior algebra.

This is an algebraic theorem.  It does not assert a global spin structure,
identify all differential forms with irreducible spinors, or identify exterior
parity with Weyl chirality without further hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.KahlerAtiyahCartanForms

open ExteriorAlgebra
open InfoGeometry.Clifford.NeutralPhaseSpaceCore

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

abbrev Forms (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  ExteriorAlgebra ℝ V

abbrev FormEnd (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  Module.End ℝ (Forms V)

/-- Exterior creation by a Cartan one-form/vector generator. -/
def wedgeOperator (v : V) : FormEnd V :=
  Algebra.lmul ℝ (Forms V) (ExteriorAlgebra.ι ℝ v)

/-- Interior contraction by a covector. -/
def contractionOperator (φ : Module.Dual ℝ V) : FormEnd V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V)) φ

@[simp] theorem wedgeOperator_apply (v : V) (α : Forms V) :
    wedgeOperator v α = ExteriorAlgebra.ι ℝ v * α := rfl

@[simp] theorem wedgeOperator_sq_zero (v : V) :
    wedgeOperator v * wedgeOperator v = 0 := by
  apply LinearMap.ext
  intro α
  change ExteriorAlgebra.ι ℝ v *
      (ExteriorAlgebra.ι ℝ v * α) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem wedgeOperator_anticommutator_zero (v u : V) :
    wedgeOperator v * wedgeOperator u +
        wedgeOperator u * wedgeOperator v = 0 := by
  apply LinearMap.ext
  intro α
  change ExteriorAlgebra.ι ℝ v *
        (ExteriorAlgebra.ι ℝ u * α) +
      ExteriorAlgebra.ι ℝ u *
        (ExteriorAlgebra.ι ℝ v * α) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

@[simp] theorem contractionOperator_sq_zero
    (φ : Module.Dual ℝ V) :
    contractionOperator φ * contractionOperator φ = 0 := by
  apply LinearMap.ext
  intro α
  exact CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm ℝ V)) φ α

theorem contractionOperator_anticommutator_zero
    (φ ψ : Module.Dual ℝ V) :
    contractionOperator φ * contractionOperator ψ +
        contractionOperator ψ * contractionOperator φ = 0 := by
  apply LinearMap.ext
  intro α
  change CliffordAlgebra.contractLeft φ
      (CliffordAlgebra.contractLeft ψ α) +
      CliffordAlgebra.contractLeft ψ
        (CliffordAlgebra.contractLeft φ α) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  simp

/-- Creation/annihilation CAR:
`ι_φ ε_v + ε_v ι_φ = φ(v)`. -/
theorem contraction_wedge_CAR
    (φ : Module.Dual ℝ V) (v : V) :
    contractionOperator φ * wedgeOperator v +
        wedgeOperator v * contractionOperator φ =
      (φ v) • (1 : FormEnd V) := by
  apply LinearMap.ext
  intro α
  change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℝ V)) φ
      (ExteriorAlgebra.ι ℝ v * α) +
      ExteriorAlgebra.ι ℝ v *
        contractionOperator φ α =
      ((φ v) • (1 : FormEnd V)) α
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp only [contractionOperator]
  abel

/-- Metric musical map `v ↦ g(v,-)`. -/
def metricFlat
    (g : LinearMap.BilinForm ℝ V) :
    V →ₗ[ℝ] Module.Dual ℝ V :=
  g

/-- Graph embedding of the metric musical map into the canonical neutral
phase space `V ⊕ V*`. -/
def metricGraph
    (g : LinearMap.BilinForm ℝ V) :
    V →ₗ[ℝ] PhaseSpaceCarrier V where
  toFun v := (v, metricFlat g v)
  map_add' v u := by
    ext <;> simp [metricFlat]
  map_smul' c v := by
    ext <;> simp [metricFlat]

@[simp] theorem metricGraph_apply
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    metricGraph g v = (v, g v) := rfl

/-- The neutral quadratic form restricted to the metric graph is exactly
the metric quadratic value `g(v,v)`. -/
theorem neutralQuadratic_on_metricGraph
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    canonicalNeutralFormUnscaled (metricGraph g v) = g v v := by
  simp [metricGraph, metricFlat]

/-- Kähler--Atiyah/Cartan Clifford action:
`c_g(v) = ε(v) + ι(g(v,-))`. -/
def cartanCliffordAction
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    FormEnd V :=
  wedgeOperator v + contractionOperator (metricFlat g v)

@[simp] theorem cartanCliffordAction_apply
    (g : LinearMap.BilinForm ℝ V)
    (v : V) (α : Forms V) :
    cartanCliffordAction g v α =
      wedgeOperator v α +
        contractionOperator (g v) α := rfl

/-- The Cartan Clifford action is linear in its one-form/vector generator. -/
def cartanCliffordActionMap
    (g : LinearMap.BilinForm ℝ V) :
    V →ₗ[ℝ] FormEnd V where
  toFun := cartanCliffordAction g
  map_add' v u := by
    apply LinearMap.ext
    intro α
    change
      ExteriorAlgebra.ι ℝ (v + u) * α +
          CliffordAlgebra.contractLeft (g (v + u)) α =
        (ExteriorAlgebra.ι ℝ v * α +
          CliffordAlgebra.contractLeft (g v) α) +
        (ExteriorAlgebra.ι ℝ u * α +
          CliffordAlgebra.contractLeft (g u) α)
    rw [map_add, add_mul, map_add]
    simp only [LinearMap.add_apply]
    abel
  map_smul' c v := by
    apply LinearMap.ext
    intro α
    change
      ExteriorAlgebra.ι ℝ (c • v) * α +
          CliffordAlgebra.contractLeft (g (c • v)) α =
        c • (ExteriorAlgebra.ι ℝ v * α +
          CliffordAlgebra.contractLeft (g v) α)
    rw [map_smul, smul_mul_assoc, map_smul]
    simp only [LinearMap.smul_apply, smul_add]

@[simp] theorem cartanCliffordActionMap_apply
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    cartanCliffordActionMap g v = cartanCliffordAction g v := rfl

/-- General anticommutator: the symmetric part of `g` is the Clifford metric. -/
theorem cartanCliffordAction_anticommutator
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    cartanCliffordAction g v * cartanCliffordAction g u +
        cartanCliffordAction g u * cartanCliffordAction g v =
      (g v u + g u v) • (1 : FormEnd V) := by
  calc
    cartanCliffordAction g v * cartanCliffordAction g u +
          cartanCliffordAction g u * cartanCliffordAction g v =
        (wedgeOperator v * wedgeOperator u +
          wedgeOperator u * wedgeOperator v) +
        (contractionOperator (g v) * wedgeOperator u +
          wedgeOperator u * contractionOperator (g v)) +
        (contractionOperator (g u) * wedgeOperator v +
          wedgeOperator v * contractionOperator (g u)) +
        (contractionOperator (g v) * contractionOperator (g u) +
          contractionOperator (g u) * contractionOperator (g v)) := by
            simp only [cartanCliffordAction, add_mul, mul_add]
            abel
    _ = (g v u + g u v) • (1 : FormEnd V) := by
      rw [wedgeOperator_anticommutator_zero]
      rw [contractionOperator_anticommutator_zero]
      rw [contraction_wedge_CAR (g v) u]
      rw [contraction_wedge_CAR (g u) v]
      simp only [zero_add, add_zero]
      rw [← add_smul]

/-- For a symmetric metric, the Cartan one-forms satisfy the Clifford relation
`{c(v),c(u)} = 2 g(v,u)`. -/
theorem cartanCliffordAction_anticommutator_of_symmetric
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ v u, g v u = g u v)
    (v u : V) :
    cartanCliffordAction g v * cartanCliffordAction g u +
        cartanCliffordAction g u * cartanCliffordAction g v =
      (2 * g v u) • (1 : FormEnd V) := by
  rw [cartanCliffordAction_anticommutator]
  rw [← hg v u]
  congr 1
  ring

/-- The square of a Cartan Clifford generator is the metric scalar. -/
theorem cartanCliffordAction_sq
    (g : LinearMap.BilinForm ℝ V)
    (v : V) :
    cartanCliffordAction g v * cartanCliffordAction g v =
      (g v v) • (1 : FormEnd V) := by
  calc
    cartanCliffordAction g v * cartanCliffordAction g v =
        wedgeOperator v * contractionOperator (g v) +
          contractionOperator (g v) * wedgeOperator v := by
      simp only [cartanCliffordAction, add_mul, mul_add,
        wedgeOperator_sq_zero, contractionOperator_sq_zero,
        zero_add, add_zero]
    _ = (g v v) • (1 : FormEnd V) := by
      rw [add_comm, contraction_wedge_CAR]

/-- The metric quadratic form underlying the Kähler--Atiyah Clifford algebra. -/
def metricQuadraticForm
    (g : LinearMap.BilinForm ℝ V) :
    QuadraticForm ℝ V :=
  g.toQuadraticMap

@[simp] theorem metricQuadraticForm_apply
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    metricQuadraticForm g v = g v v := by
  simp [metricQuadraticForm]

/-- Canonical Clifford-algebra representation on the same exterior carrier.

The universal property is discharged by `cartanCliffordAction_sq`; no
matrix gamma representation is introduced. -/
def kahlerAtiyahRepresentation
    (g : LinearMap.BilinForm ℝ V) :
    CliffordAlgebra (metricQuadraticForm g) →ₐ[ℝ] FormEnd V :=
  CliffordAlgebra.lift (metricQuadraticForm g)
    ⟨cartanCliffordActionMap g, by
      intro v
      simpa [metricQuadraticForm] using
        cartanCliffordAction_sq g v⟩

@[simp] theorem kahlerAtiyahRepresentation_ι
    (g : LinearMap.BilinForm ℝ V) (v : V) :
    kahlerAtiyahRepresentation g
        (CliffordAlgebra.ι (metricQuadraticForm g) v) =
      cartanCliffordAction g v := by
  exact CliffordAlgebra.lift_ι_apply _ _ v

/-- Coframe form of the Clifford relation.  Any family `θ` whose metric
matrix is `η` acts by the corresponding Clifford generators. -/
theorem cartanCoframe_clifford_relation
    {ι : Type*}
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ v u, g v u = g u v)
    (θ : ι → V)
    (η : ι → ι → ℝ)
    (hθ : ∀ a b, g (θ a) (θ b) = η a b)
    (a b : ι) :
    cartanCliffordAction g (θ a) *
          cartanCliffordAction g (θ b) +
        cartanCliffordAction g (θ b) *
          cartanCliffordAction g (θ a) =
      (2 * η a b) • (1 : FormEnd V) := by
  rw [cartanCliffordAction_anticommutator_of_symmetric g hg]
  rw [hθ]

end InfoGeometry.Canonical.KahlerAtiyahCartanForms
