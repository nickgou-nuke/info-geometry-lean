import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.SocketTarget

set_option linter.unusedSectionVars false

open scoped InnerProductSpace ENNReal

/-!
# InfoGeometry.Canonical.ModularCartanCantorSystem

Bounded real-doubled root lemmas for modular twin cylinders and projective
count potentials.

This file does not formalize full type-III Tomita--Takesaki standard form.
It records the theorem-safe part of the dictionary already supported by the
repo:

* a modular reflection is represented by an involutive bounded operator `J`;
* the doubled pair involution sends `(A, B)` to `(J B J, J A J)`;
* selfdual and anti-selfdual twin pairs are fixed/negated by this involution;
* dyadic cylinder splitting is preserved by modular reflection;
* count-cylinder logarithmic increments are projective: common positive
  rescaling of the weights does not change the increment.

The type-III words "volume", "determinant", and "barrier" are therefore routed
through projective count potentials and modular reflection data, not asserted
as canonical traces or determinants.
-/

namespace InfoGeometry.Canonical.ModularCartanCantorSystem

open InfoGeometry.Krein
open InfoGeometry.Canonical.RelativePotentialCountBridge

section DoubledOperatorReflection

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Modular twin of an operator under an involutive real doubled reflection. -/
@[rep_depth operator]
noncomputable def modularTwin (J A : EndH) : EndH :=
  J * A * J

/-- If `J² = 1`, modular twinning is involutive. -/
@[rep_depth operator]
theorem modularTwin_modularTwin_of_involutive
    {J A : EndH}
    (hJ : J * J = 1) :
    modularTwin (E := E) J (modularTwin (E := E) J A) = A := by
  unfold modularTwin
  calc
    J * (J * A * J) * J = (J * J) * A * (J * J) := by
      noncomm_ring
    _ = 1 * A * 1 := by
      rw [hJ]
    _ = A := by
      simp

/--
Cartan-style doubled involution on left/right operator pairs:
`Θ(A,B) = (J B J, J A J)`.
-/
@[rep_depth operator]
noncomputable def pairTheta (J : EndH) (X : EndH × EndH) : EndH × EndH :=
  (modularTwin (E := E) J X.2, modularTwin (E := E) J X.1)

/-- `Θ² = 1` when the reflecting operator has square `1`. -/
@[rep_depth operator]
theorem pairTheta_pairTheta_of_involutive
    {J : EndH}
    (hJ : J * J = 1)
    (X : EndH × EndH) :
    pairTheta (E := E) J (pairTheta (E := E) J X) = X := by
  cases X with
  | mk A B =>
      apply Prod.ext
      · exact modularTwin_modularTwin_of_involutive (E := E) hJ
      · exact modularTwin_modularTwin_of_involutive (E := E) hJ

/-- Selfdual diagonal twin pair `(A, JAJ)`. -/
@[rep_depth operator]
noncomputable def selfDualTwinPair (J A : EndH) : EndH × EndH :=
  (A, modularTwin (E := E) J A)

/-- Anti-selfdual normal twin pair `(A, -JAJ)`. -/
@[rep_depth operator]
noncomputable def antiSelfDualTwinPair (J A : EndH) : EndH × EndH :=
  (A, -modularTwin (E := E) J A)

/-- The selfdual twin pair is fixed by the Cartan pair involution. -/
@[rep_depth operator]
theorem pairTheta_selfDualTwinPair
    {J A : EndH}
    (hJ : J * J = 1) :
    pairTheta (E := E) J (selfDualTwinPair (E := E) J A)
      = selfDualTwinPair (E := E) J A := by
  apply Prod.ext
  · exact modularTwin_modularTwin_of_involutive (E := E) hJ
  · rfl

/-- The anti-selfdual twin pair is negated by the Cartan pair involution. -/
@[rep_depth operator]
theorem pairTheta_antiSelfDualTwinPair
    {J A : EndH}
    (hJ : J * J = 1) :
    pairTheta (E := E) J (antiSelfDualTwinPair (E := E) J A)
      = -antiSelfDualTwinPair (E := E) J A := by
  apply Prod.ext
  · calc
      modularTwin (E := E) J (-modularTwin (E := E) J A)
          = -modularTwin (E := E) J (modularTwin (E := E) J A) := by
            unfold modularTwin
            noncomm_ring
      _ = -A := by
            rw [modularTwin_modularTwin_of_involutive (E := E) hJ]
  · simp [pairTheta, antiSelfDualTwinPair]

/--
Modular twinning preserves a dyadic cylinder split.

This is the bounded-operator shadow of `p_w = p_{w0} + p_{w1}` being reflected
to the commutant/twin lane.
-/
@[rep_depth operator]
theorem modularTwin_preserves_cylinder_split
    {J p p0 p1 : EndH}
    (h : p = p0 + p1) :
    modularTwin (E := E) J p
      = modularTwin (E := E) J p0 + modularTwin (E := E) J p1 := by
  rw [h]
  unfold modularTwin
  noncomm_ring

/-- The selfdual twin cylinder also splits into selfdual twin children. -/
@[rep_depth operator]
theorem selfDualTwinPair_preserves_cylinder_split
    {J p p0 p1 : EndH}
    (h : p = p0 + p1) :
    selfDualTwinPair (E := E) J p
      = selfDualTwinPair (E := E) J p0 + selfDualTwinPair (E := E) J p1 := by
  apply Prod.ext
  · exact h
  · exact modularTwin_preserves_cylinder_split (E := E) (J := J) h

end DoubledOperatorReflection

section ProjectiveCountCylinders

variable {Word : Type*}

/-- Negative logarithmic cylinder potential from a positive weight profile. -/
@[rep_depth projective]
noncomputable def cylinderLogPotential (weight : Word → ℝ) (w : Word) : ℝ :=
  -Real.log (weight w)

/--
Negative logarithmic branch increment:
`-log(weight child / weight parent)`.
-/
@[rep_depth projective]
noncomputable def cylinderLogIncrement
    (weight : Word → ℝ)
    (parent child : Word) : ℝ :=
  -Real.log (weight child / weight parent)

/--
The cylinder logarithmic increment is projective: common positive rescaling of
the cylinder weights does not change it.
-/
@[rep_depth projective]
theorem cylinderLogIncrement_common_pos_smul
    (weight : Word → ℝ)
    (parent child : Word)
    {c : ℝ}
    (hc : 0 < c) :
    cylinderLogIncrement (fun w => c * weight w) parent child
      = cylinderLogIncrement weight parent child := by
  unfold cylinderLogIncrement
  have hratio :
      c * weight child / (c * weight parent) = weight child / weight parent := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_div_mul_left (weight child) (weight parent) hc.ne')
  rw [hratio]

/--
Existing count-side modular Hamiltonian profiles already have projective
invariance under common positive rescaling.
-/
@[rep_depth projective]
theorem relativeCountModularProfile_projective_rescale
    {n : Nat}
    (counts ref : RelativeCounts n)
    {c : ℝ}
    (hc : 0 < c) :
    relativeCountModularProfile n (c • counts) (c • ref)
      = relativeCountModularProfile n counts ref :=
  relativeCountModularProfile_common_pos_smul (n := n) c hc counts ref

end ProjectiveCountCylinders

section StandardFormNormalCone

variable {H Functional Projection : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Positive cone vectors orthogonal to `ξ`. This is the inward normal convention. -/
@[rep_depth operator]
def inwardConeOrthogonal (P : Set H) (ξ : H) : Set H :=
  {η | η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

/-- Negative cone vectors orthogonal to `ξ`. This is the outward normal convention. -/
@[rep_depth operator]
def outwardConeOrthogonal (P : Set H) (ξ : H) : Set H :=
  {η | -η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

/-- Convex-analytic outward normal cone to `P` at `ξ`. -/
@[rep_depth operator]
def convexOutwardNormalCone (P : Set H) (ξ : H) : Set H :=
  {η | ∀ ζ : H, ζ ∈ P → ⟪η, ζ - ξ⟫_ℝ ≤ 0}

/-- Convex-analytic inward normal cone to `P` at `ξ`. -/
@[rep_depth operator]
def convexInwardNormalCone (P : Set H) (ξ : H) : Set H :=
  {η | ∀ ζ : H, ζ ∈ P → 0 ≤ ⟪η, ζ - ξ⟫_ℝ}

/--
Standard-form realization of the normal positive cone.

`Functional` stands for normal positive functionals.  The bridge records the
standard-form square-root vector map and the natural cone carrier.  The cone
membership, modular reflection, and normal-cone formulas are theorem owners
below rather than proof fields.
-/
@[rep_depth operator]
structure StandardFormNormalCone where
  /-- Tomita modular conjugation / real reflection. -/
  J : EndH

  /-- Natural positive cone `P`. -/
  naturalCone : Set H

  /-- Standard-form cone vector representing a normal positive functional. -/
  coneVector : Functional → H

namespace StandardFormNormalCone

variable (S : StandardFormNormalCone (H := H) (Functional := Functional))

/-- Readback: normal positive functionals are represented by natural-cone vectors. -/
@[rep_depth operator]
theorem coneVector_mem_naturalCone (ω : Functional) :
    S.coneVector ω ∈ S.naturalCone := by
  sorry

/-- `J² = 1`. -/
@[rep_depth operator]
theorem J_involutive :
    S.J * S.J = (1 : EndH) := by
  sorry

/-- `J` fixes natural-cone vectors pointwise. -/
@[rep_depth operator]
theorem J_fixes_naturalCone
    {ξ : H} (hξ : ξ ∈ S.naturalCone) :
    S.J ξ = ξ := by
  sorry

/-- Readback: `J` fixes the cone vector of a normal positive functional. -/
@[rep_depth operator]
theorem J_fixes_coneVector (ω : Functional) :
    S.J (S.coneVector ω) = S.coneVector ω :=
  S.J_fixes_naturalCone (S.coneVector_mem_naturalCone ω)

/-- Outward normal cone formula `N_P(ξ) = -P ∩ ξᗮ`. -/
@[rep_depth operator]
theorem outward_normal_cone
    (ξ : H) (hξ : ξ ∈ S.naturalCone) :
    convexOutwardNormalCone S.naturalCone ξ = outwardConeOrthogonal S.naturalCone ξ := by
  sorry

/-- Inward normal cone formula `N_P^in(ξ) = P ∩ ξᗮ`. -/
@[rep_depth operator]
theorem inward_normal_cone
    (ξ : H) (hξ : ξ ∈ S.naturalCone) :
    convexInwardNormalCone S.naturalCone ξ = inwardConeOrthogonal S.naturalCone ξ := by
  sorry

/-- Outward normal cone at a cone vector is `-P ∩ ξᗮ`. -/
@[rep_depth operator]
theorem outwardNormalCone_coneVector (ω : Functional) :
    convexOutwardNormalCone S.naturalCone (S.coneVector ω) =
      outwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
  S.outward_normal_cone (S.coneVector ω) (S.coneVector_mem_naturalCone ω)

/-- Inward normal cone at a cone vector is `P ∩ ξᗮ`. -/
@[rep_depth operator]
theorem inwardNormalCone_coneVector (ω : Functional) :
    convexInwardNormalCone S.naturalCone (S.coneVector ω) =
      inwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
  S.inward_normal_cone (S.coneVector ω) (S.coneVector_mem_naturalCone ω)

end StandardFormNormalCone

/--
Supported face data for a standard-form natural cone.

This is the abstract form of `P_p = p J p J P`.  The actual projection algebra
and support order are supplied by the backend.
-/
@[rep_depth operator]
structure SupportedNaturalConeFaces where
  standardForm :
    StandardFormNormalCone (H := H) (Functional := Functional)

  /-- Support projection of a normal positive functional. -/
  supportProjection : Functional → Projection

  /-- Complementary projection, morally `1 - p`. -/
  complementProjection : Projection → Projection

  /-- Supported natural-cone face `P_p`. -/
  face : Projection → Set H

  /-- Face-localizing operator, morally `p J p J`. -/
  faceLocalizer : Projection → EndH

namespace SupportedNaturalConeFaces

variable (F : SupportedNaturalConeFaces (H := H) (Functional := Functional)
  (Projection := Projection))

/-- Readback of the supported-face localizer image law. -/
@[rep_depth operator]
theorem face_eq_localizer_image_readback (p : Projection) :
    F.face p =
      {ξ | ∃ η : H, η ∈ F.standardForm.naturalCone ∧ F.faceLocalizer p η = ξ} := by
  sorry

/-- The standard-form vector of a functional lies in its support face. -/
@[rep_depth operator]
theorem coneVector_mem_supportFace_readback (ω : Functional) :
    F.standardForm.coneVector ω ∈ F.face (F.supportProjection ω) := by
  sorry

/-- Outward normal cone at a supported vector is the negative complementary face. -/
@[rep_depth operator]
theorem outwardNormalCone_eq_negative_complementary_face (ω : Functional) :
    convexOutwardNormalCone F.standardForm.naturalCone (F.standardForm.coneVector ω) =
      {η | -η ∈ F.face (F.complementProjection (F.supportProjection ω))} := by
  sorry

end SupportedNaturalConeFaces

end StandardFormNormalCone

section RelativeEntropyBarrier

open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy

variable {A Modular Weight Deriv Score : Type*}
variable [Ring A] [Zero Modular] [Mul Modular] [One Deriv] [Mul Deriv]

/--
Type III-safe replacement for determinant barriers.

The barrier is a relative-entropy readout, and the logarithmic derivative is
represented by Connes cocycle/spatial-derivative data.  Finite determinant
  barriers can only enter through an explicit finite-split approximant theorem.
-/
@[socket_debt_tag, rep_depth operator]
structure RelativeEntropyBarrierSocket
    (A Modular Weight Deriv Score : Type*)
    [Ring A] [Zero Modular] [Mul Modular] [One Deriv] [Mul Deriv] [Zero Score] [Add Score] where
  /-- Araki/Connes relative entropy socket. -/
  relativeEntropy :
    UnnormalizedRelativeEntropyDatum A Modular

  /-- Connes cocycle derivative `[Dφ : Dψ]_t`. -/
  connesCocycle :
    ConnesCocycleDerivative A Weight

  /-- Connes spatial derivative / relative modular derivative. -/
  spatialDerivative :
    ConnesSpatialDerivative Weight Deriv

  /-- Modular logarithmic score, when a generator exists. -/
  modularScore :
    Weight → Weight → Score


namespace RelativeEntropyBarrierSocket

variable [Ring A] [Zero Modular] [Mul Modular] [One Deriv] [Mul Deriv] [Zero Score] [Add Score]
variable (B : RelativeEntropyBarrierSocket A Modular Weight Deriv Score)

/-- Relative entropy is the barrier readout; self-divergence vanishes. -/
@[rep_depth operator]
theorem entropy_self_eq_zero
    (φ : InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy.OperatorWeight A) :
    B.relativeEntropy.entropy φ φ = 0 :=
  B.relativeEntropy.self_eq_zero φ

/-- Relative entropy is nonnegative. -/
@[rep_depth operator]
theorem entropy_nonnegative
    (φ ψ : InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy.OperatorWeight A) :
    (0 : ℝ≥0∞) ≤ B.relativeEntropy.entropy φ ψ :=
  B.relativeEntropy.nonnegative φ ψ

/-- Same-weight Connes cocycle is trivial. -/
@[rep_depth operator]
theorem connesCocycle_same_weight
    (φ : Weight)
    (t : ℝ) :
    B.connesCocycle.cocycle φ φ t = 1 :=
  B.connesCocycle.same_weight φ t

/-- Same-weight spatial derivative is identity. -/
@[rep_depth operator]
theorem spatialDerivative_same_weight
    (φ : Weight) :
    B.spatialDerivative.spatialDerivative φ φ = 1 :=
  B.spatialDerivative.same_weight φ

/-- The modular score vanishes for identical weights. -/
@[rep_depth operator]
theorem modular_score_self (φ : Weight) :
    B.modularScore φ φ = 0 := by
  sorry

/-- The modular score satisfies the additive chain rule. -/
@[rep_depth operator]
theorem modular_score_chain (φ ψ η : Weight) :
    B.modularScore φ ψ + B.modularScore ψ η = B.modularScore φ η := by
  sorry

end RelativeEntropyBarrierSocket

end RelativeEntropyBarrier

section ModularMetricPullback

variable {Base State : Type*}
variable {Tangent : Base → Type*}
variable {StateTangent : State → Type*}
variable {MetricValue : Type*}

/--
Pullback of the modular information metric from state/weight space.

`metric` is a spacetime/parameter-space metric only because `stateMap` and
`stateDerivative` are supplied.  The backend decides whether `modularMetric` is
BKM/Araki Hessian, Bures/Hellinger, or another explicitly certified metric.
-/
@[rep_depth operator]
structure ModularInformationMetricPullback where
  /-- Map from base/scale/spacetime parameter into modular state data. -/
  stateMap : Base → State

  /-- Differential of the state map. -/
  stateDerivative : ∀ x : Base, Tangent x → StateTangent (stateMap x)

  /-- Metric on the modular state/weight side. -/
  modularMetric : ∀ ω : State, StateTangent ω → StateTangent ω → MetricValue

  /-- Pullback metric on the base side. -/
  metric : ∀ x : Base, Tangent x → Tangent x → MetricValue

namespace ModularInformationMetricPullback

variable (P : ModularInformationMetricPullback (Base := Base) (State := State)
  (Tangent := Tangent) (StateTangent := StateTangent) (MetricValue := MetricValue))

/-- Readback: base metric is a pullback from modular state/weight geometry. -/
@[rep_depth operator]
theorem metric_eq_pullback (x : Base) (u v : Tangent x) :
    P.metric x u v =
      P.modularMetric (P.stateMap x) (P.stateDerivative x u) (P.stateDerivative x v) := by
  sorry

end ModularInformationMetricPullback

end ModularMetricPullback

end InfoGeometry.Canonical.ModularCartanCantorSystem
