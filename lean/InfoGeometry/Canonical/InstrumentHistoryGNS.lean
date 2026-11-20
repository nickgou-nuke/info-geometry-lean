/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.InstrumentHistory
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import InfoGeometry.Canonical.FilteredGNSVacuumState

/-!
# A represented C⋆ state constructed from instrument histories

The ordinary-trace history functionals are transported to Mathlib's native
`CStarMatrix` type copies. Native `StarAlgEquiv.arrowCongr` transports the
existing concrete tower maps without importing an unrelated trace-state chain.
The functionals' positivity, normalization, and compatibility
are proved from the actual complete instruments, then supplied to the existing
filtered GNS construction. This gives a state on the norm closure of that
represented algebraic colimit and recovers every specified full-matrix stage
functional. Dense range gives uniqueness for this full family on this closure.

The pointer density is the selected dephased density from `InstrumentHistory`.
Agreement of diagonal outcome probabilities alone is not a uniqueness premise
here. No traciality, KMS condition, or von Neumann factor type is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.InstrumentHistoryGNS

open CStarStateColimit.Native
open CStarStateColimit.Native.ContinuousStarInductiveSystem
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumState
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Quantum.InstrumentHistory
open scoped ComplexOrder

variable {S κ : Type*} [Fintype S] [DecidableEq S] [Fintype κ] [DecidableEq κ]

local notation "HistoryCStarStage" =>
  (fun n : ℕ => CStarMatrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)

local instance historyStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (HistoryCStarStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance historyStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (HistoryCStarStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Expose the native instances at the dependent-family type used by filtered GNS. -/
private abbrev historyStageCStarFamily : ∀ n, CStarAlgebra (HistoryCStarStage n) :=
  fun n => (inferInstance : CStarAlgebra (HistoryCStarStage n))

private abbrev historyStageOrderFamily : ∀ n, PartialOrder (HistoryCStarStage n) :=
  fun n => (inferInstance : PartialOrder (HistoryCStarStage n))

private abbrev historyStageStarOrderFamily : ∀ n, StarOrderedRing (HistoryCStarStage n) :=
  fun n => (inferInstance : StarOrderedRing (HistoryCStarStage n))

attribute [local instance] historyStageCStarFamily historyStageOrderFamily
  historyStageStarOrderFamily

attribute [local instance]
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralOrder
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- The existing full matrix tower transported through Mathlib's native type-copy equivalences.
All raw embeddings and coherence laws remain those of `CuntzMatrixTraceTower`. -/
def historyMatrixSystem : ContinuousStarInductiveSystem HistoryCStarStage where
  map := fun {i j} hij =>
    StarAlgEquiv.arrowCongr
      (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] HistoryCStarStage i)
      (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage j ≃⋆ₐ[ℂ] HistoryCStarStage j)
      (concreteMap hij)
  map_id := by
    intro i
    apply StarAlgHom.ext
    intro A
    let e : MatrixStage i ≃⋆ₐ[ℂ] HistoryCStarStage i := CStarMatrix.ofMatrixStarAlgEquiv
    change e (concreteMap (le_refl i) (e.symm A)) = A
    rw [concreteMap_id]
    exact e.apply_symm_apply A
  map_comp := by
    intro i j k hij hjk
    simpa only [concreteMap_comp] using
      (StarAlgEquiv.arrowCongr_comp
        (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] HistoryCStarStage i)
        (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage j ≃⋆ₐ[ℂ] HistoryCStarStage j)
        (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] HistoryCStarStage k)
        (concreteMap hij) (concreteMap hjk)).symm

/-- Reading a transported transition in matrix coordinates recovers the existing concrete map. -/
theorem historyMatrixSystem_toMatrix {i j : ℕ} (hij : i ≤ j)
    (A : HistoryCStarStage i) :
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage j ≃⋆ₐ[ℂ] HistoryCStarStage j).symm
        (historyMatrixSystem.map hij A) =
      concreteMap hij
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] HistoryCStarStage i).symm A) := by
  let e : MatrixStage j ≃⋆ₐ[ℂ] HistoryCStarStage j := CStarMatrix.ofMatrixStarAlgEquiv
  change e.symm (e (concreteMap hij
    ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] HistoryCStarStage i).symm A))) = _
  exact e.symm_apply_apply _

/-- The ordinary-trace functional on the native C⋆ matrix type copy. -/
def cstarHistoryFunctional (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) : HistoryCStarStage n →ₗ[ℂ] ℂ :=
  (historyFunctional ρ K n).comp
    (CStarMatrix.ofMatrixStarAlgEquiv :
      MatrixStage n ≃⋆ₐ[ℂ] HistoryCStarStage n).symm.toAlgEquiv.toLinearMap

@[simp] theorem cstarHistoryFunctional_apply (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (A : HistoryCStarStage n) :
    cstarHistoryFunctional ρ K n A =
      historyFunctional ρ K n
        ((CStarMatrix.ofMatrixStarAlgEquiv :
          MatrixStage n ≃⋆ₐ[ℂ] HistoryCStarStage n).symm A) := rfl

/-- Native C⋆ positivity follows from square decomposition and full-matrix positivity. -/
theorem cstarHistoryFunctional_nonneg (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ)
    (A : HistoryCStarStage n) (hA : 0 ≤ A) :
    0 ≤ cstarHistoryFunctional ρ K n A := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  rw [cstarHistoryFunctional_apply, map_mul, map_star]
  exact historyFunctional_nonneg ρ hρ K n _
    (Matrix.posSemidef_conjTranspose_mul_self _)

/-- A positive map is constructed from the actual history functional. -/
def cstarHistoryPositiveFunctional (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) : HistoryCStarStage n →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (cstarHistoryFunctional ρ K n)
    (cstarHistoryFunctional_nonneg ρ hρ K n)

/-- Complete instruments and trace-one input construct a native state at every stage. -/
def cstarHistoryState (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) : State (HistoryCStarStage n) where
  functional := cstarHistoryPositiveFunctional ρ hρ K n
  normalized := by
    change historyFunctional ρ K n
      ((CStarMatrix.ofMatrixStarAlgEquiv :
        MatrixStage n ≃⋆ₐ[ℂ] HistoryCStarStage n).symm 1) = 1
    rw [map_one, historyFunctional_one ρ K hK, htrace]

/-- The exact full-matrix stage readout uses ordinary trace. -/
@[simp] theorem cstarHistoryState_apply (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) (A : HistoryCStarStage n) :
    (cstarHistoryState ρ hρ htrace K hK n).functional A =
      historyFunctional ρ K n
        ((CStarMatrix.ofMatrixStarAlgEquiv :
          MatrixStage n ≃⋆ₐ[ℂ] HistoryCStarStage n).symm A) := rfl

/-- The native states satisfy the existing tower's projective restriction law. -/
theorem cstarHistoryState_restrict (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    {i j : ℕ} (hij : i ≤ j) :
    (cstarHistoryState ρ hρ htrace K hK j).restrict (historyMatrixSystem.map hij) =
      cstarHistoryState ρ hρ htrace K hK i := by
  apply State.ext
  apply PositiveLinearMap.ext
  intro A
  change historyFunctional ρ K j
      ((CStarMatrix.ofMatrixStarAlgEquiv).symm (historyMatrixSystem.map hij A)) =
    historyFunctional ρ K i ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)
  rw [historyMatrixSystem_toMatrix]
  exact historyFunctional_transition ρ K hK hij _

/-- The compatible state family is constructed, rather than assumed as data. -/
def cstarHistoryStateFamily (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1) :
    CompatibleStateFamily HistoryCStarStage historyMatrixSystem where
  state := cstarHistoryState ρ hρ htrace K hK
  compatible := cstarHistoryState_restrict ρ hρ htrace K hK

section RepresentedState

set_option maxHeartbeats 1000000

variable (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
variable (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
variable (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)

/-- The actual instrument family instantiates the existing represented GNS state construction. -/
def representedHistoryState :=
  representedVacuumState HistoryCStarStage historyMatrixSystem
    (cstarHistoryStateFamily ρ hρ htrace K hK) 0

end RepresentedState

end InfoGeometry.Canonical.InstrumentHistoryGNS
