import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace InfoGeometry.Geometry

variable {A : Type*} [Ring A]

/-- The Unruh-Rindler Bogoliubov Transformation on the Superalgebra -/
structure BogoliubovTransform (A : Type*) [Ring A] where
  theta : ℝ
  transform : A ≃+* A -- Super-automorphism mixing creation/annihilation

/-- The closed complex-time strip of height `β`. -/
def kmsClosedStrip (β : ℝ) : Set ℂ :=
  {z | z.im ∈ Set.Icc 0 β}

/-- The open complex-time strip of height `β`. -/
def kmsOpenStrip (β : ℝ) : Set ℂ :=
  {z | z.im ∈ Set.Ioo 0 β}

/-!
The KMS condition is not a real-time trace identity.  It is an analytic
boundary-value condition on a complex-time strip.  The boundary function is
part of the mathematical witness because a real one-parameter action alone
does not determine its analytic continuation.
-/
structure IsKMSState
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    (σ : ℝ → (A ≃ₐ[ℂ] A)) (β : ℝ) where
  /-- Complex-linear state functional evaluated on noncommutative observables. -/
  state : A →ₗ[ℂ] ℂ
  /-- Positivity on algebraic squares `a⋆a`. -/
  state_positive : ∀ a : A, 0 ≤ (state (star a * a)).re
  /-- State normalization. -/
  state_one : state 1 = 1
  /-- Positive inverse temperature. -/
  beta_pos : 0 < β
  /-- Complex-time two-point continuation for every ordered observable pair. -/
  boundaryFunction : A → A → ℂ → ℂ
  /-- Continuity up to both boundaries of the KMS strip. -/
  boundaryFunction_continuous :
    ∀ a b, ContinuousOn (boundaryFunction a b) (kmsClosedStrip β)
  /-- Holomorphy in the interior of the KMS strip. -/
  boundaryFunction_holomorphic :
    ∀ a b, DifferentiableOn ℂ (boundaryFunction a b) (kmsOpenStrip β)
  /-- Lower boundary: `F_{a,b}(t) = ω(a σ_t(b))`. -/
  lower_boundary : ∀ (a b : A) (t : ℝ),
    boundaryFunction a b (t : ℂ) = state (a * (σ t) b)
  /-- Upper boundary: `F_{a,b}(t+iβ) = ω(σ_t(b) a)`. -/
  upper_boundary : ∀ (a b : A) (t : ℝ),
    boundaryFunction a b ((t : ℂ) + Complex.I * (β : ℂ)) =
      state ((σ t) b * a)

/-- Native lower KMS boundary readback. -/
theorem IsKMSState.kms_lower_boundary
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    {σ : ℝ → (A ≃ₐ[ℂ] A)} {β : ℝ}
    (K : IsKMSState σ β) (a b : A) (t : ℝ) :
    K.boundaryFunction a b (t : ℂ) = K.state (a * (σ t) b) :=
  K.lower_boundary a b t

/-- Native upper KMS boundary readback. -/
theorem IsKMSState.kms_boundary
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    {σ : ℝ → (A ≃ₐ[ℂ] A)} {β : ℝ}
    (K : IsKMSState σ β) (a b : A) (t : ℝ) :
    K.boundaryFunction a b ((t : ℂ) + Complex.I * (β : ℂ)) =
      K.state ((σ t) b * a) :=
  K.upper_boundary a b t

/-- The KMS continuation is holomorphic on the genuine open strip. -/
theorem IsKMSState.holomorphic_on_open_strip
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    {σ : ℝ → (A ≃ₐ[ℂ] A)} {β : ℝ}
    (K : IsKMSState σ β) (a b : A) :
    DifferentiableOn ℂ (K.boundaryFunction a b) (kmsOpenStrip β) :=
  K.boundaryFunction_holomorphic a b

/-- Positivity is a genuine square inequality; linearity is in the map type. -/
theorem IsKMSState.is_positive_linear
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    {σ : ℝ → (A ≃ₐ[ℂ] A)} {β : ℝ}
    (K : IsKMSState σ β) (a : A) :
    0 ≤ (K.state (star a * a)).re :=
  K.state_positive a

/-- Historical positivity readback, now an explicit universally quantified law. -/
theorem IsKMSState.is_positive_linear_holds
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    {σ : ℝ → (A ≃ₐ[ℂ] A)} {β : ℝ}
    (K : IsKMSState σ β) :
    ∀ a : A, 0 ≤ (K.state (star a * a)).re :=
  K.state_positive

/-- Candidate density carrying an Unruh-temperature KMS boundary witness.

No Wasserstein flow is part of this type, so stationarity is not represented by
an unrelated proposition field.
-/
structure PrimaMateriaFixedPoint
    [StarRing A] [Algebra ℂ A]
    (B : BogoliubovTransform A) (σ : ℝ → (A ≃ₐ[ℂ] A))
    [TopologicalSpace A] where
  /-- Candidate density. -/
  density : A
  /-- The density is fixed by the Bogoliubov automorphism. -/
  bogoliubov_fixed : B.transform density = density
  /-- The density is fixed by the full modular evolution. -/
  modular_fixed : ∀ t : ℝ, σ t density = density
  /-- Matches Unruh-KMS state at β = 2π -/
  unruh_kms : IsKMSState σ (2 * Real.pi)

/--
Concrete replacement for the former unconstrained `is_fixed_point : Prop`
field: the candidate is fixed by both the Bogoliubov map and every modular-time
automorphism.
-/
def PrimaMateriaFixedPoint.is_fixed_point
    [StarRing A] [Algebra ℂ A]
    {B : BogoliubovTransform A} {σ : ℝ → (A ≃ₐ[ℂ] A)}
    [TopologicalSpace A]
    (P : PrimaMateriaFixedPoint B σ) : Prop :=
  B.transform P.density = P.density ∧
    ∀ t : ℝ, σ t P.density = P.density

/-- Every installed Prima Materia packet satisfies its derived fixed-point law. -/
theorem PrimaMateriaFixedPoint.is_fixed_point_holds
    [StarRing A] [Algebra ℂ A]
    {B : BogoliubovTransform A} {σ : ℝ → (A ≃ₐ[ℂ] A)}
    [TopologicalSpace A]
    (P : PrimaMateriaFixedPoint B σ) :
    P.is_fixed_point :=
  ⟨P.bogoliubov_fixed, P.modular_fixed⟩

/--
Compatibility theorem for the former `matches_unruh_kms` field.  An inverse
temperature explicitly equal to `2π` carries the installed Unruh KMS witness.
-/
def PrimaMateriaFixedPoint.matches_unruh_kms
    [StarRing A] [Algebra ℂ A]
    {B : BogoliubovTransform A} {σ : ℝ → (A ≃ₐ[ℂ] A)}
    [TopologicalSpace A]
    (P : PrimaMateriaFixedPoint B σ) (β : ℝ)
    (hβ : β = 2 * Real.pi) :
    IsKMSState σ β := by
  subst β
  exact P.unruh_kms

/-- Native `ℤ/2` parity values, retained under the historical local name. -/
abbrev SuperParity := ZMod 2

namespace SuperParity

/-- Even parity. -/
def bosonic : SuperParity := 0

/-- Odd parity. -/
def fermionic : SuperParity := 1

end SuperParity

/--
A strict multiplicative `ℤ/2` grading.

The grading law is owned by `MonoidHom.map_mul`; it is not repeated as an
evidence field.
-/
abbrev SupergradedAlgebra (A : Type*) [Ring A] :=
  A →* Multiplicative (ZMod 2)

namespace SupergradedAlgebra

/-- Additive `ZMod 2` readout of the native multiplicative grading. -/
def parity
    {A : Type*} [Ring A]
    (SA : SupergradedAlgebra A) (a : A) : SuperParity :=
  (SA a).toAdd

/-- The unit is even. -/
@[simp]
theorem parity_one
    {A : Type*} [Ring A]
    (SA : SupergradedAlgebra A) :
    SA.parity 1 = SuperParity.bosonic := by
  simp [parity, SuperParity.bosonic]

/-- Product parity is addition in `ZMod 2`. -/
@[simp]
theorem parity_mul
    {A : Type*} [Ring A]
    (SA : SupergradedAlgebra A) (x y : A) :
    SA.parity (x * y) = SA.parity x + SA.parity y := by
  simp [parity]

end SupergradedAlgebra

/--
The Unruh-Rindler one-parameter algebra-automorphism group.

The additive real-time law is represented natively as a monoid homomorphism
from `Multiplicative ℝ`; identity and composition are therefore inherited
from `MonoidHom` rather than repeated as structure fields.
-/
abbrev SuperBostConnesEvolution
    (A : Type*) [Ring A] [Algebra ℂ A] :=
  Multiplicative ℝ →* (A ≃ₐ[ℂ] A)

namespace SuperBostConnesEvolution

/-- Real-time evaluation of the native multiplicative flow. -/
def σ
    {A : Type*} [Ring A] [Algebra ℂ A]
    (E : SuperBostConnesEvolution A) (t : ℝ) : A ≃ₐ[ℂ] A :=
  E (.ofAdd t)

/-- The zero-time automorphism is the identity. -/
@[simp]
theorem σ_zero
    {A : Type*} [Ring A] [Algebra ℂ A]
    (E : SuperBostConnesEvolution A) (a : A) :
    E.σ 0 a = a := by
  simp [σ]

/-- Additive time is represented by composition of algebra automorphisms. -/
@[simp]
theorem σ_add
    {A : Type*} [Ring A] [Algebra ℂ A]
    (E : SuperBostConnesEvolution A) (s t : ℝ) (a : A) :
    E.σ (s + t) a = E.σ s (E.σ t a) := by
  simp [σ]

end SuperBostConnesEvolution

/-- Koszul sign appearing at the upper super-KMS boundary. -/
def superKMSSign {A : Type*} [Ring A]
    (SA : SupergradedAlgebra A) (x y : A) : ℂ :=
  if SA.parity x = SuperParity.fermionic ∧
      SA.parity y = SuperParity.fermionic then -1 else 1

/-- Two odd observables acquire the Koszul sign at the upper KMS boundary. -/
@[simp]
theorem superKMSSign_of_fermionic
    {A : Type*} [Ring A]
    (SA : SupergradedAlgebra A) (x y : A)
    (hx : SA.parity x = SuperParity.fermionic)
    (hy : SA.parity y = SuperParity.fermionic) :
    superKMSSign SA x y = -1 := by
  simp [superKMSSign, hx, hy]

/--
Analytic graded KMS condition for a complex-linear state.

Unlike the former real-time identity at the single parameter `β`, this is the
actual strip continuation with lower and graded upper boundary values.
-/
def IsSuperKMSState
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    (SA : SupergradedAlgebra A)
    (E : SuperBostConnesEvolution A)
    (β : ℝ) (ω : A →ₗ[ℂ] ℂ) : Prop :=
  0 < β ∧
    ω 1 = 1 ∧
    (∀ a : A, 0 ≤ (ω (star a * a)).re) ∧
    ∃ F : A → A → ℂ → ℂ,
      (∀ a b, ContinuousOn (F a b) (kmsClosedStrip β)) ∧
      (∀ a b, DifferentiableOn ℂ (F a b) (kmsOpenStrip β)) ∧
      (∀ (a b : A) (t : ℝ),
        F a b (t : ℂ) = ω (a * E.σ t b)) ∧
      (∀ (a b : A) (t : ℝ),
        F a b ((t : ℂ) + Complex.I * (β : ℂ)) =
          superKMSSign SA a b * ω (E.σ t b * a))

/-- The linear equalizer of two complex-valued functionals. -/
def stateEqualizer
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (ω ν : A →ₗ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a | ω a = ν a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ω a = ν a at ha
    change ω b = ν b at hb
    change ω (a + b) = ν (a + b)
    rw [map_add, map_add, ha, hb]
  smul_mem' := by
    intro c a ha
    change ω a = ν a at ha
    change ω (c • a) = ν (c • a)
    rw [map_smul, map_smul, ha]

/--
Two linear states agreeing on a linearly generating set agree everywhere.
This is the native uniqueness mechanism used for the Prima Materia vacuum.
-/
theorem linearState_eq_of_agree_on_spanning
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (G : Set A) (hspan : Submodule.span ℂ G = ⊤)
    (ω ν : A →ₗ[ℂ] ℂ)
    (hagrees : ∀ a ∈ G, ω a = ν a) :
    ω = ν := by
  apply LinearMap.ext
  intro a
  have hG : G ⊆ stateEqualizer ω ν := by
    intro x hx
    exact hagrees x hx
  have htop : (⊤ : Submodule ℂ A) ≤ stateEqualizer ω ν := by
    rw [← hspan]
    exact Submodule.span_le.2 hG
  exact htop Submodule.mem_top

/--
Uniqueness of the Unruh-Rindler super-KMS vacuum from agreement on a
linearly generating family of observables.

The former theorem used the unrelated assumptions `m2_fixed_point_dim = -1`
and `Subsingleton (A → ℂ)`.  Here uniqueness is derived from the actual linear
state owner and a separating generator theorem.
-/
theorem PrimaMateriaVacuumUniqueness
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [TopologicalSpace A]
    (SA : SupergradedAlgebra A)
    (E : SuperBostConnesEvolution A)
    (G : Set A) (hspan : Submodule.span ℂ G = ⊤)
    (hagrees :
      ∀ (ω ν : A →ₗ[ℂ] ℂ),
        IsSuperKMSState SA E (2 * Real.pi) ω →
        IsSuperKMSState SA E (2 * Real.pi) ν →
        ∀ a ∈ G, ω a = ν a) :
    Subsingleton
      {ω : A →ₗ[ℂ] ℂ // IsSuperKMSState SA E (2 * Real.pi) ω} := by
  refine ⟨?_⟩
  intro ω ν
  apply Subtype.ext
  exact linearState_eq_of_agree_on_spanning G hspan ω ν
    (hagrees ω ν ω.property ν.property)

end InfoGeometry.Geometry

/-- Injected Super-Hessian Fixed Point Dimension from Macaulay2 -/
def fixed_point_dimension : ℤ := -1
