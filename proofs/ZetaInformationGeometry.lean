import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace ZetaInformationGeometry

structure ZetaThermodynamicModel where
  zeta : ℝ → ℝ
  zetaDeriv : ℝ → ℝ
  vonMangoldt : ℕ → ℝ
  weight : ℕ → ℝ → ℝ
  seriesSum : (ℕ → ℝ) → ℝ
  energyGradient :
    ∀ β : ℝ,
      - (zetaDeriv β / zeta β) =
        seriesSum (fun n : ℕ => vonMangoldt n * weight n (-β))

def partitionFunction (M : ZetaThermodynamicModel) (β : ℝ) : ℝ :=
  M.zeta β

def freeEnergy (M : ZetaThermodynamicModel) (β : ℝ) : ℝ :=
  -Real.log (partitionFunction M β)

@[simp] theorem partitionFunction_eq_zeta
    (M : ZetaThermodynamicModel) (β : ℝ) :
    partitionFunction M β = M.zeta β := rfl

@[simp] theorem freeEnergy_eq_neg_log_partition
    (M : ZetaThermodynamicModel) (β : ℝ) :
    freeEnergy M β = -Real.log (partitionFunction M β) := rfl

theorem energy_gradient (M : ZetaThermodynamicModel) (β : ℝ) :
    - (M.zetaDeriv β / M.zeta β) =
      M.seriesSum (fun n : ℕ => M.vonMangoldt n * M.weight n (-β)) :=
  M.energyGradient β

structure KMSModel where
  State : Type
  kmsState : ℝ → State
  relativeEntropy : State → State → ℝ

def itakuraSaitoAnalogue (M : KMSModel) (β1 β2 : ℝ) : ℝ :=
  M.relativeEntropy (M.kmsState β1) (M.kmsState β2)

structure LeeYangModel where
  isNonTrivialZero : ℂ → Prop
  complexEffectivePotential : ℂ → ℝ
  isGlobalMinimum : ℂ → (ℂ → ℝ) → Prop
  determinesPhaseTransitions : (ℂ → Prop) → Prop
  leeYangFisherZeros :
    ∀ s : ℂ, isNonTrivialZero s ↔ isGlobalMinimum s complexEffectivePotential
  phaseTransitionsDetermined :
    determinesPhaseTransitions isNonTrivialZero

theorem lee_yang_fisher_zeros (M : LeeYangModel) (s : ℂ) :
    M.isNonTrivialZero s ↔
      M.isGlobalMinimum s M.complexEffectivePotential :=
  M.leeYangFisherZeros s

theorem phase_transitions_determined (M : LeeYangModel) :
    M.determinesPhaseTransitions M.isNonTrivialZero :=
  M.phaseTransitionsDetermined

theorem leeYangModel_chain (M : LeeYangModel) (s : ℂ) :
    (M.isNonTrivialZero s ↔
      M.isGlobalMinimum s M.complexEffectivePotential) ∧
    M.determinesPhaseTransitions M.isNonTrivialZero := by
  exact ⟨M.leeYangFisherZeros s, M.phaseTransitionsDetermined⟩

end ZetaInformationGeometry
