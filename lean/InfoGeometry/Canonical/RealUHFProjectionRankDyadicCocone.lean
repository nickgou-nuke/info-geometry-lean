import InfoGeometry.Canonical.RealUHFProjectionRankSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DyadicDimensionGroupUniversalProperty
import InfoGeometry.Canonical.DyadicDimensionGroupTensorTower

namespace InfoGeometry.Canonical

/-!
# Dyadic cocone attached to a coherent real projection-rank system

This is the additive bridge from the finite real binary tower to the existing
dyadic direct-limit universal property.  It records only the rank readout;
it does not identify the result with `K₀`, `KO₀`, or a completed UHF algebra.
-/

namespace RealUHFProjectionRankSystem

/-! The canonical cocone for the bonding maps `z ↦ 2z`. -/
noncomputable def canonicalDyadicCocone : DyadicCocone DyadicRational where
  leg n := (dyadicStageLinearMap n).toAddMonoidHom
  compatible n z := by
    simpa [LinearMap.comp_apply, dyadicDouble, dyadicStageLinearMap] using
      dyadicStageMap_succ n z

theorem canonicalDyadicCocone_lift_stage (n : ℕ) (z : ℤ) :
    canonicalDyadicCocone.lift (dyadicStageMap n z) =
      dyadicStageMap n z := by
  rw [DyadicCocone.lift_stage]
  rfl

theorem canonicalDyadicCocone_liftToDirectLimit_stage
    (n : ℕ) (z : ℤ) :
    canonicalDyadicCocone.liftToDirectLimit
        (Quotient.mk _ ⟨z, n⟩) =
      dyadicStageMap n z := by
  rw [DyadicCocone.liftToDirectLimit_stage]
  rfl

theorem dimensionClass_readout_as_stage
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicDirectLimitEquiv (S.dimensionClass n) =
      dyadicStageMap n (projectionRank (S.projection n).map : ℤ) := by
  rw [S.dimensionClass_readout]
  apply Subtype.ext
  rfl

theorem dimensionClass_as_canonical_lift
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicDirectLimitEquiv (S.dimensionClass n) =
      canonicalDyadicCocone.liftToDirectLimit
        (Quotient.mk _
          ⟨(projectionRank (S.projection n).map : ℤ), n⟩) := by
  rw [dimensionClass_readout_as_stage]
  exact (canonicalDyadicCocone_liftToDirectLimit_stage n
    (projectionRank (S.projection n).map : ℤ)).symm

theorem dimensionClass_readout_stable
    (S : RealUHFProjectionRankSystem) (n k : ℕ) :
    dyadicDirectLimitEquiv (S.dimensionClass (n + k)) =
      dyadicStageMap n (projectionRank (S.projection n).map : ℤ) := by
  rw [S.dimensionClass_add n k]
  exact S.dimensionClass_readout_as_stage n

end RealUHFProjectionRankSystem

end InfoGeometry.Canonical
