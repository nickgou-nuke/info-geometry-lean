import InfoGeometry.Canonical.WeylGaugeField

namespace InfoGeometry.Canonical

/-!
# Weyl Transport

Trajectory-level coupling layer for local Weyl gauge transport.

This file keeps the base `GeneratedFlow` abstraction clean while adding:

- trajectory pullback of Weyl connection and curvature,
- covariant section transport along trajectories,
- bundled scale-equivariant flow objects,
- abstract line integration and holonomy interfaces.
-/

/-- Index-parameterized trajectory in the Weyl base space. -/
structure WeylTrajectory (I X : Type*) where
  point : I → X

/-- Abstract line-integration operator over trajectory-indexed fields. -/
structure WeylLineIntegrator (I A S : Type*) where
  integrate : (I → A) → S

/-- Abstract holonomy/readout map from integrated scale data. -/
structure WeylHolonomyMap (S P : Type*) where
  toHolonomy : S → P

/-- Bundled generated-flow transport with attached Weyl scale track. -/
structure ScaleEquivariantFlow (I F A : Type*) where
  flowOf : I → F
  scaleOf : I → A

attribute [spine_object] WeylTrajectory WeylLineIntegrator WeylHolonomyMap ScaleEquivariantFlow

namespace WeylTrajectory

variable {I X : Type*}

/-- View a trajectory as its underlying point map. -/
def along (γ : WeylTrajectory I X) : I → X :=
  γ.point


end WeylTrajectory

namespace WeylGaugeField

variable {I X A K W F R : Type*}

/-- Pull the Weyl connection field back along a trajectory. -/
def connectionAlong (B : WeylGaugeField X A) (γ : WeylTrajectory I X) : I → A :=
  fun i => B.gaugeOf (γ.point i)

/-- Pointwise expansion of `connectionAlong`. -/
@[simp] theorem connectionAlong_apply
    (B : WeylGaugeField X A) (γ : WeylTrajectory I X) (i : I) :
    B.connectionAlong γ i = B.gaugeOf (γ.point i) := by
  rfl

/-- Pull a generated flow back along a trajectory in the generator space. -/
def generatedAlong (Φ : GeneratedFlow X F) (γ : WeylTrajectory I X) : I → F :=
  fun i => Φ.flowOf (γ.point i)

/-- Pointwise expansion of `generatedAlong`. -/
@[simp] theorem generatedAlong_apply
    (Φ : GeneratedFlow X F) (γ : WeylTrajectory I X) (i : I) :
    generatedAlong Φ γ i = Φ.flowOf (γ.point i) := by
  rfl

/-- Response pulled back along a trajectory through a generated flow. -/
def responseAlong
    (resp : GeometricResponse F R)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X) : I → R :=
  fun i => resp.responseOf (Φ.flowOf (γ.point i))

/-- Pointwise expansion of `responseAlong`. -/
@[simp] theorem responseAlong_apply
    (resp : GeometricResponse F R)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X)
    (i : I) :
    responseAlong resp Φ γ i = resp.responseOf (Φ.flowOf (γ.point i)) := by
  rfl

/-- `responseAlong` factors through `GeometricResponse.along` and trajectory pullback. -/
@[simp] theorem responseAlong_eq_along_comp
    (resp : GeometricResponse F R)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X) :
    responseAlong resp Φ γ = resp.along Φ ∘ γ.point := by
  funext i
  rfl

section Curvature

variable [Ring K] [AddCommGroup A] [Module K A]

/-- Pull Weyl field strength back along a trajectory. -/
def curvatureAlong
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X) : I → A :=
  fun i => (B.fieldStrength Δ).strengthOf (γ.point i)

/-- Pointwise expansion of `curvatureAlong`. -/
@[simp] theorem curvatureAlong_apply
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X)
    (i : I) :
    B.curvatureAlong Δ γ i = (B.fieldStrength Δ).strengthOf (γ.point i) := by
  rfl

/-- Pull covariant derivative of a section back along a trajectory. -/
def covariantSectionAlong
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (γ : WeylTrajectory I X) : I → A :=
  fun i => B.covariantDerivative Δ q ψ (γ.point i)

/-- Pointwise expansion of `covariantSectionAlong`. -/
@[simp] theorem covariantSectionAlong_apply
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (γ : WeylTrajectory I X)
    (i : I) :
    B.covariantSectionAlong Δ q ψ γ i = B.covariantDerivative Δ q ψ (γ.point i) := by
  rfl

/-- Curvature pullback is invariant under local potential gauge transforms. -/
theorem curvatureAlong_transformByPotential_eq
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A)
    (γ : WeylTrajectory I X) :
    (B.transformByPotential Δ α).curvatureAlong Δ γ = B.curvatureAlong Δ γ := by
  funext i
  simpa [curvatureAlong] using
    congrArg (fun FS => FS.strengthOf (γ.point i))
      (B.fieldStrength_transformByPotential_eq (Δ := Δ) (α := α))

/-- Covariant section pullback obeys the same local Weyl compensation law. -/
theorem covariantSectionAlong_transform_eq
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (α : WeylGaugeParameter X A)
    (γ : WeylTrajectory I X) :
    (B.transformByPotential Δ α).covariantSectionAlong Δ q (transformSection q ψ α) γ =
      B.covariantSectionAlong Δ q ψ γ := by
  funext i
  simpa [covariantSectionAlong] using
    congrArg (fun f => f (γ.point i))
      (B.covariantDerivative_transformSection_eq (Δ := Δ) (q := q) (ψ := ψ) (α := α))

/--
Canonical constructor: generated flow plus Weyl-covariant section transport along
one trajectory yields a scale-equivariant flow package.
-/
def covariantGeneratedFlow
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X) : ScaleEquivariantFlow I F A where
  flowOf := generatedAlong Φ γ
  scaleOf := B.covariantSectionAlong Δ q ψ γ

/-- Pointwise expansion of the flow component of `covariantGeneratedFlow`. -/
@[simp] theorem covariantGeneratedFlow_flowOf_apply
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X)
    (i : I) :
    (B.covariantGeneratedFlow Δ q ψ Φ γ).flowOf i = Φ.flowOf (γ.point i) := by
  rfl

/-- Pointwise expansion of the scale component of `covariantGeneratedFlow`. -/
@[simp] theorem covariantGeneratedFlow_scaleOf_apply
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X)
    (i : I) :
    (B.covariantGeneratedFlow Δ q ψ Φ γ).scaleOf i = B.covariantDerivative Δ q ψ (γ.point i) := by
  rfl

/-- Read response from the flow branch of a scale-equivariant flow package. -/
def respondCovariantFlow
    (resp : GeometricResponse F R)
    (Ξ : ScaleEquivariantFlow I F A) : I → R :=
  fun i => resp.responseOf (Ξ.flowOf i)

omit [AddCommGroup A] in
/-- Pointwise expansion of `respondCovariantFlow`. -/
@[simp] theorem respondCovariantFlow_apply
    (resp : GeometricResponse F R)
    (Ξ : ScaleEquivariantFlow I F A)
    (i : I) :
    respondCovariantFlow resp Ξ i = resp.responseOf (Ξ.flowOf i) := by
  rfl

/-- The flow-response branch is gauge-covariant under compensated section transform. -/
theorem respondCovariantFlow_transform_eq
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (α : WeylGaugeParameter X A)
    (Φ : GeneratedFlow X F)
    (γ : WeylTrajectory I X)
    (resp : GeometricResponse F R) :
    respondCovariantFlow resp
        ((B.transformByPotential Δ α).covariantGeneratedFlow Δ q (transformSection q ψ α) Φ γ)
      =
    respondCovariantFlow resp (B.covariantGeneratedFlow Δ q ψ Φ γ) := by
  funext i
  simp [respondCovariantFlow]

end Curvature

attribute [spine_morphism, spine_functor, spine_functor_lift] WeylGaugeField.connectionAlong
attribute [spine_morphism, spine_functor, spine_functor_lift] WeylGaugeField.generatedAlong
attribute [spine_functor, spine_functor_responder] WeylGaugeField.responseAlong
attribute [spine_functor, spine_functor_responder] WeylGaugeField.curvatureAlong
attribute [spine_functor, spine_functor_lift] WeylGaugeField.covariantSectionAlong
attribute [spine_morphism, spine_functor, spine_functor_constructor] WeylGaugeField.covariantGeneratedFlow
attribute [spine_functor, spine_functor_responder] WeylGaugeField.respondCovariantFlow

end WeylGaugeField

namespace ScaleEquivariantFlow

variable {I F A P : Type*}

/-- Two-point multiplicative transport observable extracted from the scale track. -/
def transportObservable [Group P] (Ξ : ScaleEquivariantFlow I F A) (phaseOf : A → P) :
    I → I → P :=
  fun i j => (phaseOf (Ξ.scaleOf i))⁻¹ * phaseOf (Ξ.scaleOf j)


/-- Abstract cocycle law for a two-point transport observable. -/
def IsCocycle [Monoid P] (T : I → I → P) : Prop :=
  ∀ i j k : I, T i k = T i j * T j k

/-- The scale-track transport observable satisfies the multiplicative cocycle law. -/
theorem transportObservable_isCocycle [Group P]
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P) :
    IsCocycle (transportObservable Ξ phaseOf) := by
  intro i j k
  simp [transportObservable, mul_assoc]

attribute [spine_functor, spine_functor_responder] ScaleEquivariantFlow.transportObservable

end ScaleEquivariantFlow

namespace WeylLineIntegrator

variable {I X A S P K : Type*}

section Finite

variable [Fintype I]
variable [AddCommMonoid A]

/--
Concrete discrete Weyl line integrator for finite trajectories.

It computes line integration by summing the trajectory-indexed field over all
indices.
-/
def finiteSumIntegrator : WeylLineIntegrator I A A where
  integrate f := ∑ i : I, f i


end Finite

/-- Integrate the connection pullback along a trajectory. -/
def integrateConnection
    (Λ : WeylLineIntegrator I A S)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X) : S :=
  Λ.integrate (B.connectionAlong γ)


section FiniteConnection

variable [Fintype I]
variable [AddCommMonoid A]


end FiniteConnection

section Curvature

variable [Ring K] [AddCommGroup A] [Module K A]

/-- Integrate trajectory pullback of Weyl curvature. -/
def integrateCurvature
    (Λ : WeylLineIntegrator I A S)
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X) : S :=
  Λ.integrate (B.curvatureAlong Δ γ)

/-- Curvature integration is invariant under local potential gauge transforms. -/
theorem integrateCurvature_transformByPotential_eq
    (Λ : WeylLineIntegrator I A S)
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A)
    (γ : WeylTrajectory I X) :
    Λ.integrateCurvature Δ (B.transformByPotential Δ α) γ =
      Λ.integrateCurvature Δ B γ := by
  simp [integrateCurvature, B.curvatureAlong_transformByPotential_eq (Δ := Δ) (α := α) (γ := γ)]

section FiniteCurvature

variable [Fintype I]


/--
Flat local curvature collapses finite integrated curvature to zero.

This is the canonical finite-trajectory bridge from local flatness to a global
vanishing curvature integral.
-/
theorem finiteSumIntegrator_integrateCurvature_eq_zero_of_flat
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B γ = 0 := by
  change ∑ i : I, B.curvatureAlong Δ γ i = 0
  exact Finset.sum_eq_zero fun i _ => by
    change (B.fieldStrength Δ).strengthOf (γ.point i) = 0
    exact hFlat (γ.point i)

end FiniteCurvature

end Curvature

/-- Abstract Weyl holonomy from integrated connection data. -/
def holonomy
    (Λ : WeylLineIntegrator I A S)
    (H : WeylHolonomyMap S P)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X) : P :=
  H.toHolonomy (Λ.integrateConnection B γ)


section FiniteHolonomy

variable [Fintype I]
variable [AddCommMonoid A]


end FiniteHolonomy

section GaugeCovariantHolonomy

variable {K : Type*} [Ring K]
variable [AddCommGroup A] [Module K A]
variable [Group P]

/--
Endpoint-compensated holonomy observable between two trajectory indices.

This is the canonical boundary-scaled transport quantity used to encode local
Weyl covariance at the transport level.
-/
def gaugeCompensatedHolonomy
    (Λ : WeylLineIntegrator I A S)
    (H : WeylHolonomyMap S P)
    (endpointScale : X → P)
    (B : WeylGaugeField X A)
    (γ : WeylTrajectory I X)
    (iStart iEnd : I) : P :=
  (endpointScale (γ.point iStart))⁻¹ *
    Λ.holonomy H B γ *
    endpointScale (γ.point iEnd)


/--
Gauge-covariant transport theorem.

If transformed holonomy picks up exactly the expected endpoint Weyl factors,
then the boundary-compensated observable equals the original (untransformed)
transport.
-/
theorem gaugeCompensatedHolonomy_eq_base_of_boundary_law
    (Δ : WeylDifferentialOperator K X A)
    (Λ : WeylLineIntegrator I A S)
    (H : WeylHolonomyMap S P)
    (endpointScale : X → P)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A)
    (γ : WeylTrajectory I X)
    (iStart iEnd : I)
    (hBoundary :
      Λ.holonomy H (B.transformByPotential Δ α) γ =
        endpointScale (γ.point iStart) *
          Λ.holonomy H B γ *
          (endpointScale (γ.point iEnd))⁻¹) :
    Λ.gaugeCompensatedHolonomy H endpointScale (B.transformByPotential Δ α) γ iStart iEnd =
      Λ.holonomy H B γ := by
  unfold gaugeCompensatedHolonomy
  rw [hBoundary]
  simp [mul_assoc]

end GaugeCovariantHolonomy

attribute [spine_functor, spine_functor_responder] WeylLineIntegrator.integrateConnection
attribute [spine_functor, spine_functor_responder] WeylLineIntegrator.integrateCurvature
attribute [spine_functor, spine_functor_responder] WeylLineIntegrator.holonomy
attribute [spine_functor, spine_functor_responder] WeylLineIntegrator.gaugeCompensatedHolonomy

end WeylLineIntegrator

end InfoGeometry.Canonical
