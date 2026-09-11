import InfoGeometry.Twistor.Pin55PurePinorVacuum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace

/-!
# Pure pinor vacuum readout on the doubled real Krein carrier

The pure pinor and the doubled real Krein carrier are different objects.  This
file records only their common vacuum readout: the scalar vacuum is sent to
the first coordinate component of `DoubledSpace ℝ`.  The two Pin sign presentations are
retained as labels; no Pin⁻ action on the exterior spinor module is inferred.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55PurePinorDoubledKreinBridge

open InfoGeometry.Krein
open InfoGeometry.Twistor.Pin55PurePinorVacuum

abbrev VacuumCarrier := DoubledSpace ℝ

def purePinorVacuumReadout : VacuumCarrier :=
  to_doubled (1 : ℝ) 0

@[simp] theorem purePinorVacuumReadout_fst :
    WithLp.fst purePinorVacuumReadout = (1 : ℝ) := by
  rfl

@[simp] theorem purePinorVacuumReadout_snd :
    WithLp.snd purePinorVacuumReadout = (0 : ℝ) := by
  rfl

theorem purePinorVacuumReadout_krein_norm :
    KreinSpace.kreinInner purePinorVacuumReadout purePinorVacuumReadout = 1 := by
  rw [krein_inner_prod_l2]
  simp

theorem purePinorVacuumReadout_not_null :
    KreinSpace.kreinInner purePinorVacuumReadout purePinorVacuumReadout ≠ 0 := by
  rw [purePinorVacuumReadout_krein_norm]
  exact one_ne_zero

theorem purePinorVacuumReadout_spectral_fixed :
    spectral_epsilon purePinorVacuumReadout = purePinorVacuumReadout := by
  simp [purePinorVacuumReadout]

theorem purePinorVacuumReadout_modular_swap :
    modular_j purePinorVacuumReadout = to_doubled (0 : ℝ) 1 := by
  simp [purePinorVacuumReadout]

theorem purePinorVacuumReadout_modular_not_fixed :
    modular_j purePinorVacuumReadout ≠ purePinorVacuumReadout := by
  intro h
  have hfst := congrArg (fun u : VacuumCarrier => WithLp.fst u) h
  simp at hfst

end InfoGeometry.Twistor.Pin55PurePinorDoubledKreinBridge
