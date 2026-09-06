import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Projective.Quadrics.Polarization

Generic algebraic polarization lemmas for quadrics induced by symmetric
bilinear pairings, plus the Poincaré-pairing readout from a symmetric
trilinear invariant.

This file is finite algebra only:

* no Schubert-calculus claim;
* no Klein-quadric Grassmannian theorem;
* no Gromov--Witten/Chow-ring identification;
* no axiom.

The existing projective-null and Zorn/split-octonion polar-incidence lanes remain
the concrete projective-quadric owners.
-/

namespace InfoGeometry.Projective.Quadrics.Polarization

/--
Poincaré pairing extracted from a trilinear invariant by inserting a chosen
class in the third slot.

The trilinear invariant is represented by an iterated `LinearMap`, so additivity
and homogeneity are inherited from Mathlib rather than restated as proof fields.
-/
def poincareMetric
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I₃ : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (unitClass : V) (x y : V) : ℝ :=
  I₃ x y unitClass

namespace PoincareMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (I₃ : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (unitClass : V)

/-- The Poincaré pairing is additive in the first slot. -/
theorem add_left (x₁ x₂ y : V) :
    poincareMetric I₃ unitClass (x₁ + x₂) y =
      poincareMetric I₃ unitClass x₁ y + poincareMetric I₃ unitClass x₂ y := by
  simp [poincareMetric]

/-- The Poincaré pairing is additive in the second slot. -/
theorem add_right (x y₁ y₂ : V) :
    poincareMetric I₃ unitClass x (y₁ + y₂) =
      poincareMetric I₃ unitClass x y₁ + poincareMetric I₃ unitClass x y₂ := by
  simp [poincareMetric]

/-- The Poincaré pairing is homogeneous in the first slot. -/
theorem smul_left (c : ℝ) (x y : V) :
    poincareMetric I₃ unitClass (c • x) y = c * poincareMetric I₃ unitClass x y := by
  simp [poincareMetric]

/-- The Poincaré pairing is homogeneous in the second slot. -/
theorem smul_right (c : ℝ) (x y : V) :
    poincareMetric I₃ unitClass x (c • y) = c * poincareMetric I₃ unitClass x y := by
  simp [poincareMetric]

/-- Symmetry of the extracted Poincaré pairing from symmetry of the first two slots. -/
theorem symm
    (hsymm12 : ∀ x y z : V, I₃ x y z = I₃ y x z)
    (x y : V) :
    poincareMetric I₃ unitClass x y = poincareMetric I₃ unitClass y x := by
  exact hsymm12 x y unitClass

end PoincareMetric

/-- Quadratic readout associated to a bilinear pairing. -/
def quadricReadout
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x : V) : ℝ :=
  g x x

/--
Algebraic polarization identity for a symmetric bilinear pairing.

This is the finite algebraic core of the Cayley--Klein-style quadric readout:

`Q(x + y) - Q(x) - Q(y) = 2 g(x,y)`.
-/
theorem polarization_identity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y : V, g x y = g y x)
    (x y : V) :
    quadricReadout g (x + y) - quadricReadout g x - quadricReadout g y =
      2 * g x y := by
  unfold quadricReadout
  simp [map_add, hsymm y x]
  ring

/-- Linear-map form of the Poincaré pairing. -/
def poincareMetricLinear
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I₃ : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (unitClass : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => I₃ x y unitClass
      map_add' := by intro y₁ y₂; simp
      map_smul' := by intro c y; simp }
  map_add' := by
    intro x₁ x₂
    ext y
    simp
  map_smul' := by
    intro c x
    ext y
    simp

@[simp]
theorem poincareMetricLinear_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I₃ : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (unitClass x y : V) :
    poincareMetricLinear I₃ unitClass x y = poincareMetric I₃ unitClass x y :=
  rfl

/--
Poincaré--Cayley--Klein polarization theorem.

A symmetric trilinear invariant induces a Poincaré pairing, and the associated
quadric satisfies the polarization identity.
-/
theorem poincare_polarization
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I₃ : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm12 : ∀ x y z : V, I₃ x y z = I₃ y x z)
    (unitClass : V) (x y : V) :
    quadricReadout (poincareMetricLinear I₃ unitClass) (x + y)
        - quadricReadout (poincareMetricLinear I₃ unitClass) x
        - quadricReadout (poincareMetricLinear I₃ unitClass) y =
      2 * poincareMetric I₃ unitClass x y := by
  simpa using
    polarization_identity (poincareMetricLinear I₃ unitClass)
      (by intro x y; exact PoincareMetric.symm I₃ unitClass hsymm12 x y) x y

/-!
#### Closed finite theorems

* `PoincareMetric.add_left`
* `PoincareMetric.add_right`
* `PoincareMetric.smul_left`
* `PoincareMetric.smul_right`
* `PoincareMetric.symm`
* `polarization_identity`
* `poincare_polarization`

#### Conditional surface

`poincare_polarization` is conditional on a concrete trilinear linear map, a
symmetry hypothesis for the first two slots, and a chosen `unitClass : V`.

#### Open closure debt

Klein quadric line embedding, Plücker relations, `Gr(2,4)` Schubert calculus,
and Gromov--Witten/Chow-ring identification are not proved here.
-/

end InfoGeometry.Projective.Quadrics.Polarization
