/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentedKMS
import InfoGeometry.Canonical.FiniteMatrixGibbsParity
import InfoGeometry.Canonical.FilteredGNSBoundedGeneratorUnitaryFlow

/-!
# Real-time evolution of the actual finite-seed represented Gibbs state

The represented seed Hamiltonian generates the existing exponential unitary
flow. Its direct conjugation action uses the positive-time convention
`exp(i t H) A exp(-i t H)`. Gibbs invariance follows from the proved twisted
identity and commutation of the mapped density with this unitary. No flow or
invariance conclusion is supplied as an input. No analytic strip claim is made.
-/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.OperatorAlgebra

/-- A twisted readout is invariant under conjugation by a commuting unitary. -/
theorem twisted_readout_unitary_invariant {A : Type*} [Ring A] [StarRing A]
    (φ : A → ℂ) (δ : Aˣ)
    (htwist : ∀ x y, φ (x * y) = φ (y * ((δ : A) * x * (↑δ⁻¹ : A))))
    (U : unitary A) (hcomm : Commute (δ : A) (U : A)) (a : A) :
    φ ((U : A) * a * star (U : A)) = φ a := by
  have hfix : (δ : A) * (U : A) * (↑δ⁻¹ : A) = (U : A) := by
    rw [hcomm.eq, mul_assoc, Units.mul_inv, mul_one]
  calc
    φ ((U : A) * a * star (U : A)) = φ ((U : A) * (a * star (U : A))) := by
      rw [mul_assoc]
    _ = φ ((a * star (U : A)) * ((δ : A) * (U : A) * (↑δ⁻¹ : A))) :=
      htwist (U : A) (a * star (U : A))
    _ = φ a := by rw [hfix, mul_assoc, unitary.coe_star_mul_self, mul_one]

end InfoGeometry.OperatorAlgebra

namespace CStarStateColimit.Native.FilteredGNSRepresentedKMS

open FilteredStarAlgebraDirectLimit FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumReadback FilteredGNSVacuumState
universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
attribute [local instance] FilteredGNSVacuumState.representedSpectralOrder
  FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- Transparent invariance property of the actual constructed State. -/
def representedVacuumUnitaryInvariant (v : I)
    (U : unitary (representedCStarClosure Stage sys ω)) : Prop :=
  let ρ := representedVacuumState Stage sys ω v
  ∀ a : representedCStarClosure Stage sys ω,
    ρ.functional (Unitary.conjStarAlgAut (S := ℂ) U a) = ρ.functional a

/-- Apply the algebraic invariance argument abstractly, before specializing
large dependent represented-state types. -/
theorem representedVacuumUnitaryInvariant_of_twisted (v : I)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ)
    (htwist : representedVacuumTwistedCyclic Stage sys ω v δraw)
    (U : unitary (representedCStarClosure Stage sys ω))
    (hcomm : Commute
      ((Units.map (algebraicColimitToRepresentedClosure Stage sys ω).toMonoidHom δraw :
        (representedCStarClosure Stage sys ω)ˣ) : representedCStarClosure Stage sys ω)
      (U : representedCStarClosure Stage sys ω)) :
    representedVacuumUnitaryInvariant Stage sys ω v U := by
  intro a
  exact InfoGeometry.OperatorAlgebra.twisted_readout_unitary_invariant
    (representedVacuumState Stage sys ω v).functional
    (Units.map (algebraicColimitToRepresentedClosure Stage sys ω).toMonoidHom δraw)
    htwist U hcomm a

end CStarStateColimit.Native.FilteredGNSRepresentedKMS

namespace InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSRepresentedKMS
open CStarStateColimit.Native.FilteredGNSBoundedGeneratorUnitaryFlow
open CStarStateColimit.Native.FilteredGNSRepresentedCStarModularAutomorphism
open CuntzMatrixTowerInstantiation CantorBernoulliCStarMatrixTraceState
open FiniteMatrixGibbsFunctional AlgebraicKMSStateColimit FiniteSeedRepresentedKMS

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
local notation "ωseed" => finiteSeedCompatibleStageStates H hH β
local notation "C" => representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ωseed

/-- The native seed matrix mapped into the existing represented closure. -/
def seedStageHom : MatrixStage k →⋆ₐ[ℂ] C :=
  (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem ωseed).comp
    ((algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem k).comp
      CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom)

/-- Hermiticity is preserved by the actual stage star map. -/
theorem seedHamiltonian_selfAdjoint : IsSelfAdjoint (seedStageHom H hH β H) := by
  change star (seedStageHom H hH β H) = seedStageHom H hH β H
  rw [← map_star]
  exact congrArg (seedStageHom H hH β) hH

/-- The bounded self-adjoint generator is the image of H, not an extra input. -/
def seedGenerator : selfAdjoint C :=
  ⟨seedStageHom H hH β H, seedHamiltonian_selfAdjoint H hH β⟩

/-- Actual image of the native finite Gibbs unit. -/
def representedDensityUnit : Cˣ :=
  Units.map (algebraicColimitToRepresentedClosure CStarMatrixStage
    cstarMatrixInductiveSystem ωseed).toMonoidHom (seedDensityUnit H hH β)

theorem representedDensityUnit_coe :
    (representedDensityUnit H hH β : C) = seedStageHom H hH β (gibbsDensity H hH β) := rfl

/-- Density/generator commutation is derived from the native finite CFC theorem. -/
theorem representedDensity_commutes_generator :
    Commute (representedDensityUnit H hH β : C) (seedGenerator H hH β : C) := by
  change Commute (seedStageHom H hH β (gibbsDensity H hH β)) (seedStageHom H hH β H)
  exact (gibbsDensity_commutes_of_commute H H hH (Commute.refl H) β).map
    (seedStageHom H hH β)

/-- Existing exponential construction, specialized to the actual seed generator. -/
def seedUnitary (t : ℝ) : unitary C :=
  boundedGeneratorUnitary CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedGenerator H hH β) t

/-- Use the native standard-orientation flow with the proved generator. -/
def seedUnitaryFlow : ClosureUnitaryFlowStd CStarMatrixStage cstarMatrixInductiveSystem ωseed :=
  boundedGeneratorClosureUnitaryFlow CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedGenerator H hH β)

theorem seedUnitary_continuous : Continuous (seedUnitary H hH β) := by
  exact selfAdjoint.continuous_expUnitary.comp (continuous_id.smul continuous_const)

theorem representedDensity_commutes_unitary (t : ℝ) :
    Commute (representedDensityUnit H hH β : C) (seedUnitary H hH β t : C) := by
  change Commute (representedDensityUnit H hH β : C)
    (NormedSpace.exp (Complex.I • (t • (seedGenerator H hH β : C))))
  exact (((representedDensity_commutes_generator H hH β).smul_right t).smul_right
    Complex.I).exp_right

/-- Positive real-time conjugation on the existing closure. This does not use
 the time-reversing standard-flow-to-completion adapter. -/
def seedRealTimeAut (t : ℝ) : C ≃⋆ₐ[ℂ] C :=
  Unitary.conjStarAlgAut (S := ℂ) (seedUnitary H hH β t)

theorem seedRealTimeAut_zero (a : C) : seedRealTimeAut H hH β 0 a = a := by
  simp [seedRealTimeAut, seedUnitary, boundedGeneratorUnitary_zero]

theorem seedRealTimeAut_add (t s : ℝ) (a : C) :
    seedRealTimeAut H hH β (t + s) a =
      seedRealTimeAut H hH β t (seedRealTimeAut H hH β s a) := by
  change Unitary.conjStarAlgAut (S := ℂ)
    (boundedGeneratorUnitary CStarMatrixStage cstarMatrixInductiveSystem ωseed
      (seedGenerator H hH β) (t + s)) a = _
  rw [boundedGeneratorUnitary_add, Unitary.conjStarAlgAut_mul_apply]
  rfl

/-- Every observable has a norm-continuous real-time orbit. -/
theorem seedRealTimeAut_continuous (a : C) :
    Continuous (fun t : ℝ => seedRealTimeAut H hH β t a) := by
  have hu : Continuous (fun t : ℝ => (seedUnitary H hH β t : C)) :=
    continuous_subtype_val.comp (seedUnitary_continuous H hH β)
  exact (hu.mul continuous_const).mul hu.star

/-- Invariance of the actual finite-seed completed State, for every choice of
vacuum stage. Neither invariance nor traciality is assumed. -/
theorem finiteSeed_realTime_state_invariant (v : ℕ) (t : ℝ) :
    representedVacuumUnitaryInvariant CStarMatrixStage cstarMatrixInductiveSystem ωseed
      v (seedUnitary H hH β t) := by
  exact representedVacuumUnitaryInvariant_of_twisted CStarMatrixStage
    cstarMatrixInductiveSystem ωseed v (seedDensityUnit H hH β)
    (finiteSeed_representedVacuumTwistedCyclic H hH β v)
    (seedUnitary H hH β t) (representedDensity_commutes_unitary H hH β t)

end InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
