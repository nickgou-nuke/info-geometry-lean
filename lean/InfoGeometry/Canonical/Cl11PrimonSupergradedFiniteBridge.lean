import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

noncomputable section

namespace InfoGeometry.Canonical.Cl11PrimonSupergradedFiniteBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! The stage-one finite readout uses the existing algebra representation of
    the real matrix `Cl(1,1)` atom on the doubled Krein carrier. -/

noncomputable def stageOneReadout :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] Module.End ℝ (DoubledSpace E) :=
  ρclockAlg (E := E)

omit [CompleteSpace E] in
theorem stageOneReadout_creation_sq :
    stageOneReadout (E := E) wittCreationBase *
      stageOneReadout (E := E) wittCreationBase = 0 := by
  rw [← map_mul, wittCreationBase_sq, map_zero]

omit [CompleteSpace E] in
theorem stageOneReadout_annihilation_sq :
    stageOneReadout (E := E) wittAnnihilationBase *
      stageOneReadout (E := E) wittAnnihilationBase = 0 := by
  rw [← map_mul, ← realEncodedWittAnnihilationBase_eq,
    realEncodedWittAnnihilationBase_sq, map_zero]

omit [CompleteSpace E] in
theorem stageOneReadout_annihilation_creation_anticommutator :
    stageOneReadout (E := E) wittAnnihilationBase *
          stageOneReadout (E := E) wittCreationBase +
        stageOneReadout (E := E) wittCreationBase *
          stageOneReadout (E := E) wittAnnihilationBase =
      (1 : Module.End ℝ (DoubledSpace E)) := by
  rw [← map_mul, ← map_mul, ← map_add,
    ← realEncodedWittCreationBase_eq,
    ← realEncodedWittAnnihilationBase_eq,
    add_comm, realEncodedWitt_anticomm, map_one]

omit [CompleteSpace E] in
theorem stageOneReadout_CAR_profile :
    stageOneReadout (E := E) wittCreationBase *
          stageOneReadout (E := E) wittCreationBase = 0 ∧
      stageOneReadout (E := E) wittAnnihilationBase *
          stageOneReadout (E := E) wittAnnihilationBase = 0 ∧
      stageOneReadout (E := E) wittAnnihilationBase *
          stageOneReadout (E := E) wittCreationBase +
        stageOneReadout (E := E) wittCreationBase *
          stageOneReadout (E := E) wittAnnihilationBase =
        (1 : Module.End ℝ (DoubledSpace E)) := by
  exact ⟨stageOneReadout_creation_sq (E := E),
    stageOneReadout_annihilation_sq (E := E),
    stageOneReadout_annihilation_creation_anticommutator (E := E)⟩

theorem stageOneReadout_annihilation_eq_concreteCAR :
    stageOneReadout (E := E) wittAnnihilationBase =
      (cliffordConcreteAnnihilation (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro w
  have hw : InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w) = w := by
    apply DoubledSpace.ext <;>
      simp [InfoGeometry.Krein.to_doubled]
  rw [← hw]
  change stageOneReadout (E := E) wittAnnihilationBase
      (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w)) =
    cliffordConcreteAnnihilation (E := E)
      (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w))
  rw [cliffordConcreteAnnihilation_apply_to_doubled]
  apply DoubledSpace.ext <;>
    simp [stageOneReadout, ρclockAlg_apply, ρclock_apply, matrixAction,
      wittAnnihilationBase]

theorem stageOneReadout_creation_eq_concreteCAR :
    stageOneReadout (E := E) wittCreationBase =
      (cliffordConcreteCreation (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro w
  have hw : InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w) = w := by
    apply DoubledSpace.ext <;>
      simp [InfoGeometry.Krein.to_doubled]
  rw [← hw]
  change stageOneReadout (E := E) wittCreationBase
      (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w)) =
    cliffordConcreteCreation (E := E)
      (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w))
  rw [cliffordConcreteCreation_apply_to_doubled]
  apply DoubledSpace.ext <;>
    simp [stageOneReadout, ρclockAlg_apply, ρclock_apply, matrixAction,
      wittCreationBase]

end InfoGeometry.Canonical.Cl11PrimonSupergradedFiniteBridge
