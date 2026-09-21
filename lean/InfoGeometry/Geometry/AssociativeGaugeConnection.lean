import Mathlib.Tactic
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

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def IsLeibniz (D : Module.End R A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

/-- A concrete source of associative derivations. -/
def innerDerivative (a : A) : Module.End R A :=
  LinearMap.mulLeft R a - LinearMap.mulRight R a

theorem innerDerivative_isLeibniz (a : A) : IsLeibniz (innerDerivative (R := R) a) := by
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
  simp only [covariantDerivative_apply, hD]
  noncomm_ring

def curvature (D E : Module.End R A) (a b : A) : A :=
  D b - E a + a * b - b * a

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
  simp only [covariantDerivative_apply, map_add, hD, hE, curvature, hcomm]
  noncomm_ring

def conjugate (g : Aˣ) (x : A) : A := (g : A) * x * (↑g⁻¹ : A)

theorem conjugate_mul (g : Aˣ) (x y : A) :
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

theorem cyclic_conjugate (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y, τ (x * y) = τ (y * x)) (g : Aˣ) (x : A) :
    τ (conjugate g x) = τ x := by
  dsimp [conjugate]
  rw [hcyclic, ← mul_assoc, Units.inv_mul, one_mul]

/-- A finite curvature-square functional for a separately supplied cyclic trace. -/
def cyclicAction {ι : Type*} [Fintype ι] (τ : A →ₗ[R] R) (F : ι → ι → A) : R :=
  ∑ i, ∑ j, τ (F i j * F i j)

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

end InfoGeometry.Geometry.AssociativeGaugeConnection
