import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus.PolarizationProjectors

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

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

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
