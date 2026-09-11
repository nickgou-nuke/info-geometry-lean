import InfoGeometry.Projective.Conf3ConcreteDLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Dynamics.DuallyFlatOperatorFamily
import InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge
import InfoGeometry.Thermo.ProjectiveQuadraticPotential

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
open InfoGeometry.Thermo.ProjectiveQuadraticPotential

noncomputable section

/-- The logarithmic generating potential attached to an ordered edge. -/
def logGeneratingPotential (X : FQ3) (i j : Fin 3) : ℂ :=
  Complex.log (X.separation i j)

/- A real scalarization obtained by fixing an ordered projective edge. -/
def projectiveScalarParameter (i j : Fin 3) : FQ3 → ℝ :=
  fun X => logPotential X i j

theorem projectiveScalarParameter_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    projectiveScalarParameter i j (X.permute σ) =
      projectiveScalarParameter (σ i) (σ j) X := by
  exact logPotential_permute σ X i j

theorem projectiveScalarParameter_exponentialScaling
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    projectiveScalarParameter i j (exponentialScalingChart t) =
      2 * t + projectiveScalarParameter i j standardConfiguration := by
  exact exponentialScalingChart_logPotential t i j hij

theorem projectiveScalarParameter_exponentialScaling_deriv
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    deriv (fun s => projectiveScalarParameter i j (exponentialScalingChart s)) t = 2 := by
  simpa [projectiveScalarParameter] using
    deriv_exponentialScalingChart_chartLogPotential t i j hij

theorem projectiveScalarParameter_exponentialScaling_secondDeriv
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    deriv (fun s => deriv (fun r =>
      projectiveScalarParameter i j (exponentialScalingChart r)) s) t = 0 := by
  simpa [projectiveScalarParameter] using
    secondDeriv_exponentialScalingChart_chartLogPotential t i j hij

/- The nonlinear scalar model evaluated on the explicit projective scalarization. -/
def quadraticProjectivePotential (i j : Fin 3) (X : FQ3) : ℝ :=
  quadraticPotential (projectiveScalarParameter i j X)

theorem quadraticProjectivePotential_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    quadraticProjectivePotential i j (X.permute σ) =
      quadraticProjectivePotential (σ i) (σ j) X := by
  unfold quadraticProjectivePotential
  rw [projectiveScalarParameter_permute]

theorem quadraticProjectivePotential_exponentialScaling
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    quadraticProjectivePotential i j (exponentialScalingChart t) =
      (2 * t + projectiveScalarParameter i j standardConfiguration) ^ 2 := by
  unfold quadraticProjectivePotential
  rw [projectiveScalarParameter_exponentialScaling t i j hij]
  rfl

theorem hasDerivAt_quadraticProjectivePotential_exponentialScaling
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    HasDerivAt (fun s => quadraticProjectivePotential i j
      (exponentialScalingChart s))
      (4 * (2 * t + projectiveScalarParameter i j standardConfiguration)) t := by
  have hθ : HasDerivAt
      (fun s => projectiveScalarParameter i j (exponentialScalingChart s)) 2 t :=
    hasDerivAt_exponentialScalingChart_chartLogPotential t i j hij
  have hsq := hθ.pow 2
  rw [projectiveScalarParameter_exponentialScaling t i j hij] at hsq
  convert hsq using 1 <;> simp [quadraticProjectivePotential,
    projectiveScalarParameter, pow_two] <;> ring

theorem secondDeriv_quadraticProjectivePotential_exponentialScaling
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    deriv (fun s => deriv (fun r => quadraticProjectivePotential i j
      (exponentialScalingChart r)) s) t = 8 := by
  have hfirst : ∀ s : ℝ,
      deriv (fun r => quadraticProjectivePotential i j
        (exponentialScalingChart r)) s =
        4 * (2 * s + projectiveScalarParameter i j standardConfiguration) := by
    intro s
    exact (hasDerivAt_quadraticProjectivePotential_exponentialScaling
      s i j hij).deriv
  have hlin := (hasDerivAt_id t).const_mul 8 |>.add_const
    (4 * projectiveScalarParameter i j standardConfiguration)
  rw [show (fun s => deriv (fun r => quadraticProjectivePotential i j
      (exponentialScalingChart r)) s) =
      (fun s => 8 * s + 4 * projectiveScalarParameter i j
        standardConfiguration) by
    funext s
    rw [hfirst]
    ring]
  convert hlin.deriv using 1 <;> norm_num

theorem secondDeriv_quadraticProjectivePotential_exponentialScaling_pos
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    0 < deriv (fun s => deriv (fun r => quadraticProjectivePotential i j
      (exponentialScalingChart r)) s) t := by
  rw [secondDeriv_quadraticProjectivePotential_exponentialScaling t i j hij]
  norm_num

/- The induced quadratic potential has a concrete Bregman defect along the
   exponential scaling chart. -/
theorem quadraticProjectivePotential_exponentialScaling_bregman
    (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s =
      4 * (t - s) ^ 2 := by
  have hvalue (r : ℝ) :
      quadraticProjectivePotential i j (exponentialScalingChart r) =
        (2 * r + projectiveScalarParameter i j standardConfiguration) ^ 2 :=
    quadraticProjectivePotential_exponentialScaling r i j hij
  have hderiv :
      deriv (fun r => quadraticProjectivePotential i j
        (exponentialScalingChart r)) s =
        4 * (2 * s + projectiveScalarParameter i j standardConfiguration) :=
    (hasDerivAt_quadraticProjectivePotential_exponentialScaling s i j hij).deriv
  unfold InfoGeometry.bregmanDiv
  change quadraticProjectivePotential i j (exponentialScalingChart t) -
      quadraticProjectivePotential i j (exponentialScalingChart s) -
      deriv (fun r => quadraticProjectivePotential i j
        (exponentialScalingChart r)) s * (t - s) = 4 * (t - s) ^ 2
  rw [hvalue t, hvalue s, hderiv]
  ring

theorem quadraticProjectivePotential_exponentialScaling_bregman_nonneg
    (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    0 ≤ InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s := by
  rw [quadraticProjectivePotential_exponentialScaling_bregman t s i j hij]
  positivity

theorem quadraticProjectivePotential_exponentialScaling_bregman_eq_zero_iff
    (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s = 0 ↔
      t = s := by
  rw [quadraticProjectivePotential_exponentialScaling_bregman t s i j hij]
  constructor
  · intro h
    nlinarith [sq_nonneg (t - s)]
  · intro h
    simp [h]

theorem quadraticProjectivePotential_exponentialScaling_bregman_pos
  (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) (hneq : t ≠ s) :
    0 < InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s := by
  rw [quadraticProjectivePotential_exponentialScaling_bregman t s i j hij]
  have hsq : 0 < (t - s) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
  nlinarith

theorem quadraticProjectivePotential_exponentialScaling_bregman_eq_half_hessian
    (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s =
      (1 / 2 : ℝ) *
        deriv (fun r => deriv (fun q => quadraticProjectivePotential i j
          (exponentialScalingChart q)) r) s * (t - s) ^ 2 := by
  rw [quadraticProjectivePotential_exponentialScaling_bregman t s i j hij]
  rw [secondDeriv_quadraticProjectivePotential_exponentialScaling s i j hij]
  ring

theorem quadraticProjectivePotential_exponentialScaling_bregman_symm
    (t s : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) t s =
    InfoGeometry.bregmanDiv
      (fun r => quadraticProjectivePotential i j (exponentialScalingChart r)) s t := by
  rw [quadraticProjectivePotential_exponentialScaling_bregman t s i j hij,
    quadraticProjectivePotential_exponentialScaling_bregman s t i j hij]
  ring

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
