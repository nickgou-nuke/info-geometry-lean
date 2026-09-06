/-
InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean

Operatorial Jones calculus sockets.

Ordinary Jones transformations need not be J-unitary: lossless optical
elements are unitary up to phase, projective Jones maps act on rays, and
polarizers may be non-unitary.  The Krein/CPT branch is therefore recorded as
an optional calibration rather than a global requirement.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 1. Basic projective/operatorial predicates -/

/-- Algebraic projector. -/
def IsProjector
    {Op : Type*} [Mul Op]
    (P : Op) : Prop :=
  P * P = P

/--
A Jones transport acts projectively if it sends projectors/rays to
projectors/rays.
-/
def ActsProjectively
    {Op : Type*} [Mul Op]
    (T : Op → Op) : Prop :=
  ∀ P : Op, IsProjector P → IsProjector (T P)

/--
A transport preserves the chiral/polarization axis on the left.
-/
def PreservesChirality
    {Op : Type*} [Mul Op]
    (chi : Op)
    (T : Op → Op) : Prop :=
  ∀ x : Op, T (chi * x) = chi * T x

/--
A transport reverses the chiral/polarization axis on the left.
-/
def FlipsChirality
    {Op : Type*} [Mul Op] [Neg Op]
    (chi : Op)
    (T : Op → Op) : Prop :=
  ∀ x : Op, T (chi * x) = -(chi * T x)

/--
Optional classification of surface/operator type.
-/
inductive JonesSurfaceKind where
  | dielectricReflection
  | brewsterProjection
  | totalInternalReflection
  | metalMirror
  | chiralMedium
  | roughDepolarizingSurface
  | metasurface
  | abstractTransport
deriving DecidableEq, Repr

/-! ## 2. Base operatorial Jones datum -/

/--
An operatorial Jones datum.

This is the generic socket: it only requires projective action. More restrictive
branches, such as chirality-preserving or J-unitary Jones transports, are
separate structures.
-/
structure OperatorialJonesDatum
    (Op : Type*) [Mul Op] where
  /-- Chiral grading or polarization axis. -/
  chi : Op

  /-- Jones transport on the operator algebra. -/
  transform : Op → Op

  /-- Projective action proof. -/
  acts_projectively :
    ActsProjectively transform

  /-- Surface/transport classification. -/
  kind : JonesSurfaceKind

  /-- Coherence flag: if false in a concrete model, use Mueller/Stokes data. -/
  coherent : Prop

namespace OperatorialJonesDatum

variable {Op : Type*} [Mul Op]

/-- Apply the Jones transport to an operator. -/
def apply
    (J : OperatorialJonesDatum Op)
    (x : Op) : Op :=
  J.transform x

/-- Re-export projective action. -/
theorem maps_projectors
    (J : OperatorialJonesDatum Op)
    (P : Op)
    (hP : IsProjector P) :
    IsProjector (J.apply P) :=
  J.acts_projectively P hP

/--
Composition of two Jones transports with the same chiral axis.
-/
def compose
    (J₂ J₁ : OperatorialJonesDatum Op)
    (_hchi : J₂.chi = J₁.chi) :
    OperatorialJonesDatum Op where
  chi := J₁.chi
  transform := fun x => J₂.transform (J₁.transform x)
  acts_projectively := by
    intro P hP
    exact J₂.acts_projectively (J₁.transform P) (J₁.acts_projectively P hP)
  kind := JonesSurfaceKind.abstractTransport
  coherent := J₁.coherent ∧ J₂.coherent

end OperatorialJonesDatum

/-! ## 3. Branch datums -/

/--
Jones transport that preserves the chiral/polarization axis.

Examples include ordinary diagonal dielectric reflection away from
sector-mixing interfaces.
-/
structure ChiralityPreservingJonesDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  preserves_chirality :
    PreservesChirality base.chi base.transform

namespace ChiralityPreservingJonesDatum

variable {Op : Type*} [Mul Op]

/-- Re-export chirality preservation as a theorem-usable proof. -/
theorem preserves_apply
    (J : ChiralityPreservingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = J.base.chi * J.base.transform x :=
  J.preserves_chirality x

end ChiralityPreservingJonesDatum

/--
Jones transport that flips the chiral/polarization axis.

This is the socket for mirror/CPT-type or propagation-handedness flips.
-/
structure ChiralityFlippingJonesDatum
    (Op : Type*) [Mul Op] [Neg Op] where
  base : OperatorialJonesDatum Op
  flips_chirality :
    FlipsChirality base.chi base.transform

namespace ChiralityFlippingJonesDatum

variable {Op : Type*} [Mul Op] [Neg Op]

/-- Re-export chirality flipping as a theorem-usable proof. -/
theorem flips_apply
    (J : ChiralityFlippingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = -(J.base.chi * J.base.transform x) :=
  J.flips_chirality x

end ChiralityFlippingJonesDatum

/--
Jones transport with a Krein/J-unitary calibration.

This should be used only for the CPT/Krein branch. Ordinary polarizers and
lossy mirrors should not be forced into this structure.
-/
structure JUnitaryCalibratedJonesDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  junitary : Prop

namespace JUnitaryCalibratedJonesDatum

variable {Op : Type*} [Mul Op]

end JUnitaryCalibratedJonesDatum

/-! ## 4. Surface operators -/

/--
A Brewster surface is projective but non-unitary: it collapses to a sector.
-/
structure BrewsterSurfaceDatum
    (Op : Type*) [Mul Op] where
  base : ChiralityPreservingJonesDatum Op
  rank_collapse : Prop

namespace BrewsterSurfaceDatum

variable {Op : Type*} [Mul Op]

end BrewsterSurfaceDatum

/--
Total internal reflection is a lossless phase-retarder branch.
-/
structure TotalInternalReflectionDatum
    (Op : Type*) [Mul Op] where
  base : JUnitaryCalibratedJonesDatum Op
  phase_retarder : Prop

namespace TotalInternalReflectionDatum

variable {Op : Type*} [Mul Op]

end TotalInternalReflectionDatum

/--
Metal mirrors are generally lossy complex retarders: not automatically
J-unitary and not automatically chirality-preserving.
-/
structure MetalMirrorDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  lossy_retarder : Prop

namespace MetalMirrorDatum

variable {Op : Type*} [Mul Op]

end MetalMirrorDatum

/--
Chiral media are Cartan-diagonal in the circular basis, with possible
birefringence or dichroism.
-/
structure ChiralMediumDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  circular_cartan : Prop

namespace ChiralMediumDatum

variable {Op : Type*} [Mul Op]

end ChiralMediumDatum

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

-- [STITCHER: MISSING OVERLAP] --
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
The `s/p` Cartan operator is an involution.

This is the optical Cartan-axis fact: complementary Fresnel projectors define
the polarization grading `chi_sp = P_s - P_p`.
-/
theorem spCartan_sq :
    P.spCartan * P.spCartan = 1 := by
  dsimp [spCartan]
  calc
    (P.P_s - P.P_p) * (P.P_s - P.P_p)
        = P.P_s * P.P_s - P.P_s * P.P_p -
            P.P_p * P.P_s + P.P_p * P.P_p := by
            noncomm_ring
    _ = P.P_s - 0 - 0 + P.P_p := by
            rw [P.P_s_idem, P.P_p_idem, P.s_p_disjoint, P.p_s_disjoint]
    _ = P.P_s + P.P_p := by
            abel
    _ = 1 := P.sum_eq_one

/-- The complementary projector identity `1 - P_s = P_p`. -/
theorem one_sub_P_s_eq_P_p :
    (1 : Op) - P.P_s = P.P_p := by
  rw [← P.sum_eq_one]
  abel

/-- The complementary projector identity `1 - P_p = P_s`. -/
theorem one_sub_P_p_eq_P_s :
    (1 : Op) - P.P_p = P.P_s := by
  rw [← P.sum_eq_one]
  abel

/--
The Fresnel reflector acts on the `s` eigensector by the scalar `r_s`.
-/
theorem fresnelReflector_mul_P_s
    (r_s r_p : ℂ) :
    P.fresnelReflector r_s r_p * P.P_s = r_s • P.P_s := by
  dsimp [fresnelReflector]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, P.P_s_idem, P.p_s_disjoint,
    smul_zero, add_zero]

/--
The Fresnel reflector acts on the `p` eigensector by the scalar `r_p`.
-/
theorem fresnelReflector_mul_P_p
    (r_s r_p : ℂ) :
    P.fresnelReflector r_s r_p * P.P_p = r_p • P.P_p := by
  dsimp [fresnelReflector]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, P.s_p_disjoint, P.P_p_idem,
    smul_zero, zero_add]

/--
The `s` eigensector reads out the scalar `r_s` on the left as well.
-/
theorem P_s_mul_fresnelReflector
    (r_s r_p : ℂ) :
    P.P_s * P.fresnelReflector r_s r_p = r_s • P.P_s := by
  dsimp [fresnelReflector]
  rw [mul_add, mul_smul_comm, mul_smul_comm, P.P_s_idem, P.s_p_disjoint,
    smul_zero, add_zero]

/--
The `p` eigensector reads out the scalar `r_p` on the left as well.
-/
theorem P_p_mul_fresnelReflector
    (r_s r_p : ℂ) :
    P.P_p * P.fresnelReflector r_s r_p = r_p • P.P_p := by
  dsimp [fresnelReflector]
  rw [mul_add, mul_smul_comm, mul_smul_comm, P.p_s_disjoint, P.P_p_idem,
    smul_zero, zero_add]

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
Brewster reflection is projector-like up to its surviving scalar:

`R_B² = r_s R_B`.

It is literally idempotent only when the surviving amplitude is normalized to
`1`; projectively, the ray action is the same as `P_s` whenever `r_s ≠ 0`.
-/
theorem brewsterReflector_sq
    (r_s : ℂ) :
    P.brewsterReflector r_s * P.brewsterReflector r_s =
      r_s • P.brewsterReflector r_s := by
  rw [P.brewsterReflector_eq r_s]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, mul_assoc]

/--
Candidate Drazin inverse for Brewster reflection when `r_s ≠ 0`.

The stronger Drazin API bridge can import this formula and prove the full
Drazin laws against the repository's Drazin definitions.
-/
def brewsterDrazinInverseCandidate
    (r_s : ℂ) : Op :=
  r_s⁻¹ • P.P_s

/--
The Brewster reflector composed with its inverse candidate gives the surviving
core projector `P_s`.
-/
theorem brewster_core_projector_left
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    P.brewsterReflector r_s * P.brewsterDrazinInverseCandidate r_s = P.P_s := by
  rw [P.brewsterReflector_eq r_s]
  dsimp [brewsterDrazinInverseCandidate]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, hrs]

/--
The inverse candidate composed with the Brewster reflector gives the same
surviving core projector `P_s`.
-/
theorem brewster_core_projector_right
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    P.brewsterDrazinInverseCandidate r_s * P.brewsterReflector r_s = P.P_s := by
  rw [P.brewsterReflector_eq r_s]
  dsimp [brewsterDrazinInverseCandidate]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, P.P_s_idem, hrs, mul_comm]

/--
The complementary Brewster nil/generalized-zero projector is the killed
`p` sector.
-/
theorem brewster_nil_projector_eq_P_p
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    (1 : Op) -
        P.brewsterReflector r_s * P.brewsterDrazinInverseCandidate r_s =
      P.P_p := by
  rw [P.brewster_core_projector_left hrs]
  exact P.one_sub_P_s_eq_P_p

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
Diattenuator branch: the two Fresnel eigensectors have unequal amplitudes.
-/
structure DiattenuatorBranch
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Fresnel eigenprojectors. -/
  projectors : PolarizationProjectorPair Op

  /-- Complex `s` coefficient. -/
  r_s : ℂ

  /-- Complex `p` coefficient. -/
  r_p : ℂ

  /-- Boundary/Jones operator. -/
  R : Op

  /-- Fresnel/Jones law. -/
  R_eq :
    R = PolarizationProjectorPair.fresnelReflector projectors r_s r_p

  /-- Unequal amplitude response. -/
  amplitude_unequal :
    ‖r_s‖ ≠ ‖r_p‖

/--
Pure retarder branch: the two Fresnel amplitudes have unit magnitude.

The projective action is controlled by relative phase, not amplitude collapse.
-/
structure PureRetarderBranch
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- Phase-retarder data. -/
  phaseBranch : PhaseRetarderBranch Op

  /-- Unit magnitude of the `s` phase coefficient. -/
  s_unit_modulus :
    ‖Complex.exp (Complex.I * (phaseBranch.phi_s : ℂ))‖ = 1

  /-- Unit magnitude of the `p` phase coefficient. -/
  p_unit_modulus :
    ‖Complex.exp (Complex.I * (phaseBranch.phi_p : ℂ))‖ = 1

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


/--
Rough reflection belongs to the channel/Mueller layer, not the pure Jones
single-operator layer.
-/
structure RoughReflectionChannel
    (Op : Type*) [Ring Op]
    extends PolarizationChannel Op where

/-! ## 5. Owner target -/

/--
Owner target for connecting Fresnel/Jones data to the bilingual operator
geometry.
-/
structure OperatorialJonesOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- The Fresnel `s/p` projector pair owned by the Jones calculus layer. -/
  projectors : PolarizationProjectorPair Op

namespace OperatorialJonesOwnerTarget

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]

/-- Read back the concrete projector pair carried by the owner target. -/
def toProjectorPair
    (T : OperatorialJonesOwnerTarget Op) :
    PolarizationProjectorPair Op :=
  T.projectors

@[simp] theorem toProjectorPair_mk
    (P : PolarizationProjectorPair Op) :
    toProjectorPair (OperatorialJonesOwnerTarget.mk P) = P :=
  rfl

end OperatorialJonesOwnerTarget

end InfoGeometry.Optics.OperatorialJonesCalculus
