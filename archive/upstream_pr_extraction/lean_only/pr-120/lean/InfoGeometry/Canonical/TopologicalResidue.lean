import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TopologicalResidue

Topological-residue coherence surface over the current supercharge and
analytical-index owners.

This file keeps the zero-mode and memory vocabulary, and it proves the exact
coherence fact currently available on the canonical doubled-carrier lane:
the modular supercharge is an involution, so its zero-mode sector is trivial
and the induced analytical residue vanishes.
-/

namespace InfoGeometry.Canonical.TopologicalResidue

open InfoGeometry.Quantum
open InfoGeometry.Krein
open InfoGeometry.Canonical.AnalyticalIndex

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
Compatibility predicate for zero modes of the modular supercharge.
-/
@[rep_depth transport]
def InformationalZeroMode
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : SuperchargeMultiplet (E := E)) (ψ : DoubledSpace E) : Prop :=
  M.modular.Q ψ = 0

/--
Compatibility predicate for states fixed by both modular and parity supercharge.
-/
@[rep_depth transport]
def IsTopologicalMemory
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : SuperchargeMultiplet (E := E)) (ψ : DoubledSpace E) : Prop :=
  InformationalZeroMode M ψ ∧ M.parity.Q ψ = 0

/--
The modular supercharge is involutive on the doubled carrier.
-/
@[rep_depth transport]
theorem modular_sq_eq_id
    (M : SuperchargeMultiplet (E := E)) :
    M.modular.Q.comp M.modular.Q = ContinuousLinearMap.id ℝ H₂ := by
  rw [M.modular_eq_epsilon, spectral_epsilon_involution]

/--
Zero modes of the modular supercharge are trivial on the canonical doubled
carrier.
-/
@[rep_depth transport]
theorem informationalZeroMode_iff_eq_zero
    (M : SuperchargeMultiplet (E := E))
    (ψ : H₂) :
    InformationalZeroMode M ψ ↔ ψ = 0 := by
  constructor
  · intro hZero
    have hSq := congrArg (fun T : H₂ →L[ℝ] H₂ => T ψ) (modular_sq_eq_id (E := E) M)
    calc
      ψ = (ContinuousLinearMap.id ℝ H₂) ψ := by simp
      _ = (M.modular.Q.comp M.modular.Q) ψ := by
            simpa using hSq.symm
      _ = M.modular.Q (M.modular.Q ψ) := rfl
      _ = M.modular.Q 0 := by simpa [InformationalZeroMode] using congrArg M.modular.Q hZero
      _ = 0 := by simp
  · intro hψ
    simp [InformationalZeroMode, hψ]

/--
Topological memory collapses to the zero vector on the canonical doubled
carrier.
-/
@[rep_depth transport]
theorem isTopologicalMemory_iff_eq_zero
    (M : SuperchargeMultiplet (E := E))
    (ψ : H₂) :
    IsTopologicalMemory M ψ ↔ ψ = 0 := by
  constructor
  · intro hMem
    exact (informationalZeroMode_iff_eq_zero (E := E) M ψ).mp hMem.1
  · intro hψ
    constructor
    · exact (informationalZeroMode_iff_eq_zero (E := E) M ψ).mpr hψ
    · simp [hψ]

/--
Topological residue/Witten index induced by the modular supercharge on the
canonical doubled carrier.
-/
@[rep_depth transport]
noncomputable def wittenIndexResidue
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (M : SuperchargeMultiplet (E := E)) : ℤ :=
  analyticalIndex
    M.modular.Q.toLinearMap
    (modular_j (E := E)).toLinearMap

/--
Root analytical-index presentation of the topological residue on the doubled
carrier.
-/
@[rep_depth transport]
theorem wittenIndexResidue_eq_analyticalIndex_modular_j
    [FiniteDimensional ℝ E]
    (M : SuperchargeMultiplet (E := E)) :
    wittenIndexResidue (E := E) M
      =
    analyticalIndex
      M.modular.Q.toLinearMap
      (modular_j (E := E)).toLinearMap := by
  rfl

/--
The modular supercharge carries zero analytical residue because it is an
involution.
-/
@[rep_depth transport]
theorem wittenIndexResidue_eq_zero
    [FiniteDimensional ℝ E]
    (M : SuperchargeMultiplet (E := E)) :
    wittenIndexResidue (E := E) M = 0 := by
  have hKer :
      LinearMap.ker M.modular.Q.toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hSq : ∀ v : H₂, M.modular.Q (M.modular.Q v) = v := by
      intro v
      have hComp := congrArg (fun T : H₂ →L[ℝ] H₂ => T v) (modular_sq_eq_id (E := E) M)
      simpa [ContinuousLinearMap.comp_apply] using hComp
    have hQQ : M.modular.Q (M.modular.Q x) = M.modular.Q (M.modular.Q y) := by
      simpa using congrArg M.modular.Q hxy
    calc
      x = M.modular.Q (M.modular.Q x) := by symm; exact hSq x
      _ = M.modular.Q (M.modular.Q y) := hQQ
      _ = y := hSq y
  have hPlus :
      chiralKernelSlicePlus
          M.modular.Q.toLinearMap
          (modular_j (E := E)).toLinearMap
        = ⊥ := by
    unfold chiralKernelSlicePlus
    rw [hKer]
    simp
  have hMinus :
      chiralKernelSliceMinus
          M.modular.Q.toLinearMap
          (modular_j (E := E)).toLinearMap
        = ⊥ := by
    unfold chiralKernelSliceMinus
    rw [hKer]
    simp
  unfold wittenIndexResidue analyticalIndex
  rw [hPlus, hMinus]
  simp

/--
Canonical doubled-carrier specialization of the root residue vanishing law.
-/
@[rep_depth transport]
theorem canonicalSuperchargeMultiplet_wittenIndexResidue_eq_zero
    [FiniteDimensional ℝ E] :
    wittenIndexResidue (E := E) (canonicalSuperchargeMultiplet.inst (E := E)) = 0 := by
  simpa using
    (wittenIndexResidue_eq_zero (E := E) (canonicalSuperchargeMultiplet.inst (E := E)))

attribute [expository] InformationalZeroMode IsTopologicalMemory

end InfoGeometry.Canonical.TopologicalResidue
