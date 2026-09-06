/-
InfoGeometry/Optics/OperatorialJonesCalculus.lean

Operatorial Jones calculus.

A smooth reflecting interface supplies a polarization operator

  R = r_s P_s + r_p P_p

where `P_s` and `P_p` are the Fresnel eigenprojectors.

Brewster reflection is a Drazin/rank-collapse boundary event.
Total internal reflection is a phase-retarder/unitary branch.
Rough reflection is modeled by channels, not a single Jones operator.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone
import InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge

noncomputable section

namespace InfoGeometry.Optics.OperatorialJonesCalculus

/-! ## 1. Polarization projectors -/

/--
A pair of complementary polarization projectors.

The intended model is the Fresnel `s/p` basis.
-/
structure PolarizationProjectorPair
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel `s`-sector projector. -/
  P_s : Op

  /-- Fresnel `p`-sector projector. -/
  P_p : Op

  /-- The `s` projector is idempotent. -/
  P_s_idem :
    P_s * P_s = P_s

  /-- The `p` projector is idempotent. -/
  P_p_idem :
    P_p * P_p = P_p

  /-- The sectors are disjoint in the `s`-then-`p` order. -/
  s_p_disjoint :
    P_s * P_p = 0

  /-- The sectors are disjoint in the `p`-then-`s` order. -/
  p_s_disjoint :
    P_p * P_s = 0

  /-- The two sectors decompose the identity. -/
  sum_eq_one :
    P_s + P_p = 1

namespace PolarizationProjectorPair

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (P : PolarizationProjectorPair Op)

/--
The Fresnel reflection operator:

`R = r_s P_s + r_p P_p`.
-/
def fresnelReflector
    (r_s r_p : ℂ) : Op :=
  r_s • P.P_s + r_p • P.P_p

/--
The Fresnel Cartan operator for the `s/p` basis.
-/
def spCartan : Op :=
  P.P_s - P.P_p

/--
Brewster reflector: the `p` channel is killed.
-/
def brewsterReflector
    (r_s : ℂ) : Op :=
  P.fresnelReflector r_s 0

/--
At Brewster angle, the reflector is a scalar multiple of the `s` projector.
-/
theorem brewsterReflector_eq
    (r_s : ℂ) :
    P.brewsterReflector r_s = r_s • P.P_s := by
  simp [brewsterReflector, fresnelReflector]

/--
Total-internal-reflection / retarder branch.

The amplitudes are unit-modulus phases; this records the operator, not the
analytic Fresnel formula for the phases.
-/
def phaseRetarder
    (phi_s phi_p : ℝ) : Op :=
  (Complex.exp (Complex.I * (phi_s : ℂ))) • P.P_s +
    (Complex.exp (Complex.I * (phi_p : ℂ))) • P.P_p

/--
A deterministic Jones action on an operator-valued state.

For a concrete star-algebra this is the abstract form of `R ρ R†`.
-/
def jonesAction
    (adj : Op → Op)
    (R rho : Op) : Op :=
  R * rho * adj R

end PolarizationProjectorPair

/-! ## 2. Deterministic and projective Jones layers -/

/--
A deterministic Jones datum.

This is the coherent single-operator layer.
-/
structure DeterministicJonesDatum
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Boundary/Jones operator. -/
  R : Op

  /-- Abstract adjoint backend. -/
  adj : Op → Op

  /-- Deterministic state action. -/
  action : Op → Op

  /-- The action is `rho ↦ R rho R†`. -/
  action_eq_jones :
    ∀ rho : Op,
      action rho =
        PolarizationProjectorPair.jonesAction adj R rho

/--
A projective Jones datum.

This represents ray-level action where global nonzero scalar factors are
discarded.  Brewster reflection becomes projector-like at this layer.
-/
structure ProjectiveJonesDatum
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Boundary operator. -/
  R : Op

  /-- Projective equivalence predicate. -/
  projectivelyEquivalent : Op → Op → Prop

  /-- The projective equivalence is reflexive. -/
  projective_refl :
    ∀ x : Op, projectivelyEquivalent x x

namespace ProjectiveJonesDatum

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (J : ProjectiveJonesDatum Op)

/-- Re-export reflexivity of projective equivalence. -/
theorem refl
    (x : Op) :
    J.projectivelyEquivalent x x :=
  J.projective_refl x

end ProjectiveJonesDatum

/-! ## 3. Optical branch sockets -/

/--
Brewster rank-collapse branch.

The raw Jones operator is a scalar multiple of the surviving `s` projector.
-/
structure BrewsterRankCollapse
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Surviving `s` coefficient. -/
  r_s : ℂ

  /-- Nonzero surviving channel. -/
  r_s_ne_zero :
    r_s ≠ 0

  /-- Brewster operator. -/
  R : Op

  /-- Rank-collapse law. -/
  R_eq :
    R = PolarizationProjectorPair.brewsterReflector projectors r_s

/--
Total-internal-reflection / phase-retarder branch.

There is no rank collapse; the geometric content is relative phase holonomy.
-/
structure PhaseRetarderBranch
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- `s` channel phase. -/
  phi_s : ℝ

  /-- `p` channel phase. -/
  phi_p : ℝ

  /-- Retarder operator. -/
  R : Op

  /-- Retarder law. -/
  R_eq :
    R = PolarizationProjectorPair.phaseRetarder projectors phi_s phi_p

namespace PhaseRetarderBranch

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]
variable (T : PhaseRetarderBranch Op)

/-- Relative phase controlling the projective Poincare-sphere action. -/
def relativePhase : ℝ :=
  T.phi_p - T.phi_s

end PhaseRetarderBranch

/--
Lossy metal mirror branch.

This records the complex retarder/diattenuator case without forcing unitarity.
-/
structure LossyMetalMirrorBranch
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Complex `s` coefficient. -/
  r_s : ℂ

  /-- Complex `p` coefficient. -/
  r_p : ℂ

  /-- Mirror operator. -/
  R : Op

  /-- Fresnel/Jones law. -/
  R_eq :
    R = PolarizationProjectorPair.fresnelReflector projectors r_s r_p

  /-- Certificate that this is the intended lossy metal/ellipsometric branch. -/
  lossy_metal_certificate : Prop

/-! ## 4. Statistical channel layer -/

/--
A statistical polarization channel.

This is the Jones-to-Mueller upgrade: one no longer has a single coherent
operator, but a family of scattering operators.
-/
structure PolarizationChannel
    (Op : Type*) [Ring Op] where
  /-- Index of scattering/Jones branches. -/
  Branch : Type*

  /-- Branch operator. -/
  branchOp : Branch → Op

  /-- Abstract adjoint. -/
  adj : Op → Op

  /-- Channel action. -/
  channel : Op → Op

  /-- Channel is represented as a branch sum, left abstract if infinite. -/
  channel_law : Prop

/--
Rough reflection belongs to the channel/Mueller layer, not the pure Jones
single-operator layer.
-/
structure RoughReflectionChannel
    (Op : Type*) [Ring Op]
    extends PolarizationChannel Op where
  /-- Certificate that roughness/depolarization invalidates a single global Jones operator. -/
  depolarizing_or_direction_mixing : Prop

/-! ## 5. Owner target -/

/--
Owner target for connecting Fresnel/Jones data to the bilingual operator
geometry.
-/
def OperatorialJonesOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] : Prop :=
  Nonempty (PolarizationProjectorPair Op)

end InfoGeometry.Optics.OperatorialJonesCalculus
