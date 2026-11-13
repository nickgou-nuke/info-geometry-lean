/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Connections, curvature, and cyclic actions on an associative algebra

The base differential operators are native linear endomorphisms with an
explicit associative Leibniz law. Mathlib's Derivation has a commutative domain;
it would be the wrong carrier for this noncommutative coefficient algebra.

Commuting base derivatives give the curvature formula. Gauge transport and
invariance of a finite cyclic curvature action are derived. The action is a
finite algebraic functional, not a spacetime integral or a Chern--Simons action.
-/

noncomputable section

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A : Type*} [Ring R] [Ring A] [Module R A] [SMulCommClass R A A]

def IsLeibniz (D : Module.End R A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

/-- A concrete source of associative derivations over any ring `[Ring R]`. -/
def innerDerivative [IsScalarTower R A A] (a : A) : Module.End R A :=
  LinearMap.mulLeft R a - LinearMap.mulRight R a

theorem innerDerivative_isLeibniz [IsScalarTower R A A] (a : A) :
    IsLeibniz (innerDerivative (R := R) a) := by
  intro x y
  change a * (x * y) - (x * y) * a =
    (a * x - x * a) * y + x * (a * y - y * a)
  noncomm_ring

def covariantDerivative (D : Module.End R A) (a : A) : Module.End R A :=
  D + LinearMap.mulLeft R a

@[simp] theorem covariantDerivative_apply (D : Module.End R A) (a x : A) :
    covariantDerivative D a x = D x + a * x := rfl

theorem connection_leibniz (D : Module.End R A) (hD : IsLeibniz D) (a x y : A) :
    covariantDerivative D a (x * y) =
      covariantDerivative D a x * y + x * D y := by
  simp only [covariantDerivative_apply, hD x y]
  noncomm_ring

def curvature (D E : Module.End R A) (a b : A) : A :=
  D b - E a + a * b - b * a

omit [SMulCommClass R A A] in
theorem curvature_antisymm (D E : Module.End R A) (a b : A) :
    curvature D E a b = -curvature E D b a := by
  simp only [curvature]
  noncomm_ring

/-- Curvature is derived from the commutator of the two connections. -/
theorem curvature_action (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b x : A) :
    covariantDerivative D a (covariantDerivative E b x) -
      covariantDerivative E b (covariantDerivative D a x) =
        curvature D E a b * x := by
  simp only [covariantDerivative_apply, map_add, hD b x, hE a x, curvature, hcomm]
  noncomm_ring

def conjugate {A : Type*} [Ring A] (g : Aˣ) (x : A) : A := (g : A) * x * (↑g⁻¹ : A)

theorem conjugate_mul {A : Type*} [Ring A] (g : Aˣ) (x y : A) :
    conjugate g x * conjugate g y = conjugate g (x * y) := by
  simp only [conjugate]
  calc
    _ = (g : A) * x * ((↑g⁻¹ : A) * (g : A)) * y * (↑g⁻¹ : A) := by
      noncomm_ring
    _ = _ := by simp [mul_assoc]

def gaugePotential (D : Module.End R A) (a : A) (g : Aˣ) : A :=
  conjugate g a - D (g : A) * (↑g⁻¹ : A)

/-- Gauge covariance of the connection, including the inhomogeneous derivative term. -/
theorem gauge_intertwine (D : Module.End R A) (hD : IsLeibniz D)
    (a : A) (g : Aˣ) (x : A) :
    covariantDerivative D (gaugePotential D a g) ((g : A) * x) =
      (g : A) * covariantDerivative D a x := by
  have hcancel (b : A) :
      (b * (↑g⁻¹ : A)) * ((g : A) * x) = b * x := by
    calc
      _ = b * ((↑g⁻¹ : A) * (g : A)) * x := by noncomm_ring
      _ = b * x := by simp
  simp only [covariantDerivative_apply, gaugePotential, conjugate]
  rw [hD, sub_mul, hcancel, hcancel]
  noncomm_ring

/-- The curvature transformation follows from connection covariance. -/
theorem curvature_gauge_covariant (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b : A) (g : Aˣ) :
    curvature D E (gaugePotential D a g) (gaugePotential E b g) =
      conjugate g (curvature D E a b) := by
  have haction (x : A) :
      curvature D E (gaugePotential D a g) (gaugePotential E b g) * ((g : A) * x) =
        (g : A) * (curvature D E a b * x) := by
    calc
      _ = covariantDerivative D (gaugePotential D a g)
              (covariantDerivative E (gaugePotential E b g) ((g : A) * x)) -
            covariantDerivative E (gaugePotential E b g)
              (covariantDerivative D (gaugePotential D a g) ((g : A) * x)) :=
        (curvature_action D E hD hE hcomm _ _ _).symm
      _ = (g : A) *
            (covariantDerivative D a (covariantDerivative E b x) -
              covariantDerivative E b (covariantDerivative D a x)) := by
        simp only [gauge_intertwine D hD, gauge_intertwine E hE, mul_sub]
      _ = _ := by rw [curvature_action D E hD hE hcomm]
  simpa [conjugate, mul_assoc] using haction (↑g⁻¹ : A)

omit [SMulCommClass R A A] in
theorem cyclic_conjugate (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y, τ (x * y) = τ (y * x)) (g : Aˣ) (x : A) :
    τ (conjugate g x) = τ x := by
  dsimp [conjugate]
  rw [hcyclic, ← mul_assoc, Units.inv_mul, one_mul]

/-- A finite curvature-square functional for a separately supplied cyclic trace. -/
def cyclicAction {ι : Type*} [Fintype ι] (τ : A →ₗ[R] R) (F : ι → ι → A) : R :=
  ∑ i, ∑ j, τ (F i j * F i j)

omit [SMulCommClass R A A] in
theorem cyclicAction_conjugate {ι : Type*} [Fintype ι] (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y, τ (x * y) = τ (y * x)) (g : Aˣ) (F : ι → ι → A) :
    cyclicAction τ (fun i j => conjugate g (F i j)) = cyclicAction τ F := by
  simp only [cyclicAction, conjugate_mul, cyclic_conjugate τ hcyclic]

theorem connectionAction_gauge_invariant {ι : Type*} [Fintype ι]
    (τ : A →ₗ[R] R) (hcyclic : ∀ x y, τ (x * y) = τ (y * x))
    (D : ι → Module.End R A) (hD : ∀ i, IsLeibniz (D i))
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (a : ι → A) (g : Aˣ) :
    cyclicAction τ (fun i j =>
      curvature (D i) (D j) (gaugePotential (D i) (a i) g) (gaugePotential (D j) (a j) g)) =
        cyclicAction τ (fun i j => curvature (D i) (D j) (a i) (a j)) := by
  simp_rw [curvature_gauge_covariant _ _ (hD _) (hD _) (hcomm _ _)]
  exact cyclicAction_conjugate τ hcyclic g _

/-! ## Adjoint connection and the differential Bianchi identity -/

section Adjoint

variable [IsScalarTower R A A]

/-- The connection induced on the algebra of endomorphisms of the regular
right module. Unlike the fundamental connection, this obeys Leibniz. -/
def adjointCovariantDerivative (D : Module.End R A) (a : A) : Module.End R A :=
  D + innerDerivative a

@[simp] theorem adjointCovariantDerivative_apply (D : Module.End R A) (a x : A) :
    adjointCovariantDerivative D a x = D x + (a * x - x * a) := rfl

theorem adjointCovariantDerivative_isLeibniz
    (D : Module.End R A) (hD : IsLeibniz D) (a : A) :
    IsLeibniz (adjointCovariantDerivative D a) := by
  intro x y
  simp only [adjointCovariantDerivative_apply, hD x y]
  noncomm_ring

/-- The commutator of adjoint connections acts by the commutator with curvature.
It does not determine central curvature, which the fundamental action detects. -/
theorem adjoint_curvature_action (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b x : A) :
    adjointCovariantDerivative D a (adjointCovariantDerivative E b x) -
      adjointCovariantDerivative E b (adjointCovariantDerivative D a x) =
        curvature D E a b * x - x * curvature D E a b := by
  simp only [adjointCovariantDerivative_apply, map_add, map_sub,
    hD b x, hD x b, hE a x, hE x a, curvature, hcomm]
  noncomm_ring

/-- The exact second Bianchi identity in three commuting differential directions.
No constancy or commutativity of the connection coefficients is assumed. -/
theorem curvature_bianchi (D E G : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E) (hG : IsLeibniz G)
    (hDE : ∀ x, D (E x) = E (D x))
    (hEG : ∀ x, E (G x) = G (E x))
    (hGD : ∀ x, G (D x) = D (G x)) (a b c : A) :
    adjointCovariantDerivative D a (curvature E G b c) +
      adjointCovariantDerivative E b (curvature G D c a) +
      adjointCovariantDerivative G c (curvature D E a b) = 0 := by
  simp only [adjointCovariantDerivative_apply, curvature, map_sub, map_add,
    hD b c, hD c b, hE c a, hE a c, hG a b, hG b a, hDE, hEG, hGD]
  noncomm_ring

end Adjoint

omit [SMulCommClass R A A] in
/-- The derivative, mixed cubic, and quartic terms retain their order.
The two mixed products cannot in general be replaced by twice one of them. -/
theorem curvature_square_split (D E : Module.End R A) (a b : A) :
    curvature D E a b ^ 2 =
      (D b - E a) ^ 2 +
      (D b - E a) * (a * b - b * a) +
      (a * b - b * a) * (D b - E a) +
      (a * b - b * a) ^ 2 := by
  unfold curvature
  noncomm_ring

/-- The square transforms by the same conjugation, before taking any trace. -/
theorem curvature_square_gauge_covariant (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b : A) (g : Aˣ) :
    curvature D E (gaugePotential D a g) (gaugePotential E b g) ^ 2 =
      conjugate g (curvature D E a b ^ 2) := by
  rw [curvature_gauge_covariant D E hD hE hcomm]
  simpa only [pow_two] using conjugate_mul g (curvature D E a b) (curvature D E a b)

end InfoGeometry.Geometry.AssociativeGaugeConnection
