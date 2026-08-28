import InfoGeometry.Projective.Conf3ConcreteDLog
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Dynamics.DuallyFlatOperatorFamily
import InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge

/-!
# `d log Q` as a generating-potential readout

This file connects the concrete coefficient `1 / Q(x_i-x_j)` to the two
existing finite thermodynamic interfaces.  The logarithm is kept complex and
branch-local; the dual-flat and metriplectic contracts remain independent
real-algebraic structures.  No global differential-form or physical
identification is asserted.
-/

namespace InfoGeometry.Projective.Conf3LogSouriauBridge

open InfoGeometry.Projective.TwistorConfigurationSpace
open InfoGeometry.Projective.Conf3ConcreteDLog
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Dynamics.DuallyFlat
open InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge

noncomputable section

/-- The logarithmic generating potential attached to an ordered edge. -/
def logGeneratingPotential (X : FQ3) (i j : Fin 3) : ℂ :=
  Complex.log (X.separation i j)

/- The logarithmic potential has the concrete `d log` coefficient as its
derivative on the chosen slit-plane branch. -/
theorem logGeneratingPotential_deriv
    (X : FQ3) (i j : Fin 3) (hbranch : X.separation i j ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => Complex.log z)
      (dlogCoefficient X i j) (X.separation i j) := by
  simpa [dlogCoefficient, grothendieckLog, grothendieck_dlog] using
    grothendieckLog_deriv_log (X.separation i j) hbranch

/-- A dual-flat family may use the real readout of the logarithmic potential as
its scalar generating potential.  The equality is an explicit compatibility
field rather than an identification imposed by the bridge. -/
structure LogGeneratingDualFamily
    {S M : Type*} [AddCommGroup S] [AddCommGroup M]
    [Module ℝ S] [Module ℝ M]
    (interaction : S →ₗ[ℝ] M →ₗ[ℝ] ℝ) where
  family : OperatorFamily interaction
  logReadout : S → ℝ
  potential_eq_logReadout : family.Psi = logReadout

theorem log_family_bregman_equilibrium
    {S M : Type*} [AddCommGroup S] [AddCommGroup M]
    [Module ℝ S] [Module ℝ M]
    (interaction : S →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    (F : LogGeneratingDualFamily interaction) (x : S) :
    OperatorFamily.bregmanDivergence interaction F.family x x = 0 :=
  OperatorFamily.bregmanDivergence_self interaction F.family x

/-- Souriau's reversible and dissipative channels can be attached to the same
log-generated family through the existing metriplectic contract. -/
structure LogSouriauMetriplecticPacket (V : Type*) [AddCommGroup V]
    [Module ℝ V] where
  generatingFamily : V → ℝ
  system : MetriplecticBracket V

theorem log_packet_energy_conserved
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : LogSouriauMetriplecticPacket V) :
    metriplecticFlow P.system P.system.dH = 0 :=
  first_law_energy_conservation P.system

theorem log_packet_entropy_nonneg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : LogSouriauMetriplecticPacket V) :
    0 ≤ metriplecticFlow P.system P.system.dS :=
  second_law_entropy_production P.system

end
end InfoGeometry.Projective.Conf3LogSouriauBridge
