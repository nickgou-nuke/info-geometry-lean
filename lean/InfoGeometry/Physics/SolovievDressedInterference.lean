import InfoGeometry.Physics.SolovievCircularInterference
import InfoGeometry.Geometry.RelationalQuantumKinematics

namespace InfoGeometry.Physics.SolovievDressedInterference

open InfoGeometry.Canonical.Algebraic
open InfoGeometry.Geometry.CocyclicDressing
open InfoGeometry.Geometry.RelationalQuantumKinematics
open SolovievCircularInterference
open SolovievPhononCorrections
open NuclearQuasiparticleCAR NuclearQuasiparticleCAR.QuasiparticleCAR

variable {Gauge Configuration : Type*} [Group Gauge] [MulAction Gauge Configuration]

theorem phonon_commutator_unit_phases {Index Operator : Type*} [DecidableEq Index]
    [Ring Operator] [Algebra ℂ Operator] (car : QuasiparticleCAR Index Operator)
    (first second : Index) (distinct : first ≠ second)
    (forward backward : ℂ) (forwardPhase backwardPhase : Circle) :
    comm (phononAnnihilation car first second
        ((forwardPhase : ℂ) * forward) ((backwardPhase : ℂ) * backward))
      (phononCreation car first second
        ((forwardPhase : ℂ) * forward) ((backwardPhase : ℂ) * backward)) =
    comm (phononAnnihilation car first second forward backward)
      (phononCreation car first second forward backward) := by
  rw [phonon_commutator car first second distinct,
    phonon_commutator car first second distinct]
  simp [Complex.normSq_mul]

theorem isCocyclic_add (cocycle : MulActionCocycle Gauge Configuration Circle)
    (orbital spin : Configuration → ℂ)
    (orbital_covariant : IsCocyclic cocycle orbital)
    (spin_covariant : IsCocyclic cocycle spin) :
    IsCocyclic cocycle (fun configuration => orbital configuration + spin configuration) := by
  intro gauge configuration
  change orbital (gauge • configuration) + spin (gauge • configuration) =
    cocycle gauge configuration • (orbital configuration + spin configuration)
  rw [orbital_covariant, spin_covariant, smul_add]

theorem dressed_total_strength (cocycle : MulActionCocycle Gauge Configuration Circle)
    (first second : Configuration →[Gauge] Gauge) (orbital spin : Configuration → ℂ)
    (orbital_covariant : IsCocyclic cocycle orbital)
    (spin_covariant : IsCocyclic cocycle spin) (configuration : Configuration) :
    Complex.normSq (dressedField second orbital configuration + dressedField second spin configuration) =
      Complex.normSq (dressedField first orbital configuration + dressedField first spin configuration) := by
  simpa only [Complex.normSq_eq_norm_sq, dressedField, Function.comp_apply] using
    congrArg (fun norm : ℝ => norm ^ 2)
      (dressedWave_norm_change_frame cocycle first second _
        (isCocyclic_add cocycle orbital spin orbital_covariant spin_covariant) configuration)

theorem dressed_cancellation_iff (cocycle : MulActionCocycle Gauge Configuration Circle)
    (first second : Configuration →[Gauge] Gauge) (orbital spin : Configuration → ℂ)
    (orbital_covariant : IsCocyclic cocycle orbital)
    (spin_covariant : IsCocyclic cocycle spin) (configuration : Configuration) :
    dressedField second spin configuration = -dressedField second orbital configuration ↔
      dressedField first spin configuration = -dressedField first orbital configuration := by
  rw [← strength_zero_iff, ← strength_zero_iff,
    dressed_total_strength cocycle first second orbital spin
      orbital_covariant spin_covariant configuration]

theorem dressed_cross_term (cocycle : MulActionCocycle Gauge Configuration Circle)
    (first second : Configuration →[Gauge] Gauge) (orbital spin : Configuration → ℂ)
    (orbital_covariant : IsCocyclic cocycle orbital)
    (spin_covariant : IsCocyclic cocycle spin) (configuration : Configuration) :
    (dressedField second orbital configuration *
      starRingEnd ℂ (dressedField second spin configuration)).re =
    (dressedField first orbital configuration *
      starRingEnd ℂ (dressedField first spin configuration)).re := by
  have total := dressed_total_strength cocycle first second orbital spin
    orbital_covariant spin_covariant configuration
  have orbital_norm := congrArg (fun norm : ℝ => norm ^ 2)
    (dressedWave_norm_change_frame cocycle first second orbital orbital_covariant configuration)
  have spin_norm := congrArg (fun norm : ℝ => norm ^ 2)
    (dressedWave_norm_change_frame cocycle first second spin spin_covariant configuration)
  rw [Complex.normSq_add, Complex.normSq_add] at total
  simp only [Complex.normSq_eq_norm_sq] at total
  linarith

end InfoGeometry.Physics.SolovievDressedInterference
