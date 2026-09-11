import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DyadicDimensionGroup
import InfoGeometry.Canonical.RealStageNormalizedProjectionRank

/-!
# Finite-stage dimension readouts for the real binary tower

The repository's finite stages are real matrix algebras and the bonding map is
`A ↦ A ⊗ I₂`.  This owner records the exact trace scaling and the normalized
readout invariance.  It does not identify these readouts with `K₀` or `KO₀`.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

structure RealUHFProjectionRankSystem where
  projection : ∀ n : ℕ,
    IdempotentProjection ℝ (RealStageVector n)
  coherent : ∀ n : ℕ,
    nextStageProjectionData (projection n) = projection (n + 1)

namespace RealUHFProjectionRankSystem

noncomputable def normalizedReadout
    (S : RealUHFProjectionRankSystem) (n : ℕ) : DyadicRational :=
  normalizedProjectionRankDyadic (S.projection n)

theorem normalizedReadout_succ
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    S.normalizedReadout (n + 1) = S.normalizedReadout n := by
  unfold normalizedReadout
  rw [← S.coherent n]
  apply Subtype.ext
  exact normalizedProjectionRank_nextStage (S.projection n)

theorem normalizedReadout_add
    (S : RealUHFProjectionRankSystem) (n k : ℕ) :
    S.normalizedReadout (n + k) = S.normalizedReadout n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        S.normalizedReadout (n + Nat.succ k) =
            S.normalizedReadout ((n + k) + 1) := by
              rw [Nat.add_succ]
        _ = S.normalizedReadout (n + k) := S.normalizedReadout_succ (n + k)
        _ = S.normalizedReadout n := ih

theorem normalizedReadout_mem_unitInterval
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    ((S.normalizedReadout n : DyadicRational) : ℚ) ∈ Set.Icc (0 : ℚ) 1 := by
  change normalizedProjectionRank (S.projection n) ∈ Set.Icc (0 : ℚ) 1
  exact ⟨normalizedProjectionRank_nonneg (S.projection n),
    normalizedProjectionRank_le_one (S.projection n)⟩

noncomputable def normalizedReadoutInterval
    (S : RealUHFProjectionRankSystem) (n : ℕ) : Set.Icc (0 : ℚ) 1 :=
  ⟨S.normalizedReadout n, S.normalizedReadout_mem_unitInterval n⟩

theorem normalizedReadoutInterval_succ
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    S.normalizedReadoutInterval (n + 1) =
      S.normalizedReadoutInterval n := by
  apply Subtype.ext
  exact congrArg (fun q : DyadicRational => (q : ℚ))
    (S.normalizedReadout_succ n)

noncomputable def dimensionClass
    (S : RealUHFProjectionRankSystem) (n : ℕ) : DyadicDirectLimit :=
  dyadicDirectLimitEquiv.symm (S.normalizedReadout n)

theorem dimensionClass_readout
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicDirectLimitEquiv (S.dimensionClass n) =
      S.normalizedReadout n := by
  exact dyadicDirectLimitEquiv.apply_symm_apply _

theorem dimensionClass_add
    (S : RealUHFProjectionRankSystem) (n k : ℕ) :
    S.dimensionClass (n + k) = S.dimensionClass n := by
  unfold dimensionClass
  rw [S.normalizedReadout_add]

theorem normalizedReadout_isDyadic
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    ((S.normalizedReadout n : DyadicRational) : ℚ) ∈ dyadicRational := by
  exact (S.normalizedReadout n).property

def finiteStageTrace (n : ℕ) : MatStage n → ℝ :=
  Matrix.trace

def finiteStageNormalizedTrace (n : ℕ) : MatStage n → ℝ :=
  normalizedTrace n

@[simp] theorem finiteStageTrace_apply (n : ℕ) (A : MatStage n) :
    finiteStageTrace n A = Matrix.trace A := rfl

@[simp] theorem finiteStageNormalizedTrace_apply (n : ℕ) (A : MatStage n) :
    finiteStageNormalizedTrace n A = normalizedTrace n A := rfl

theorem finiteStageTrace_stageEmbed (n : ℕ) (A : MatStage n) :
    finiteStageTrace (n + 1) (stageEmbed n A) =
      2 * finiteStageTrace n A := by
  simpa [finiteStageTrace] using matStageEmbed_trace n A

theorem finiteStageNormalizedTrace_stageEmbed (n : ℕ) (A : MatStage n) :
    finiteStageNormalizedTrace (n + 1) (stageEmbed n A) =
      finiteStageNormalizedTrace n A := by
  simpa [finiteStageNormalizedTrace] using
    normalizedTrace_matStageEmbed n A

theorem finiteStageNormalizedTrace_stageEmbed_apply (n : ℕ) (A : MatStage n) :
    normalizedTrace (n + 1) (stageEmbed n A) = normalizedTrace n A := by
  exact normalizedTrace_matStageEmbed n A

end RealUHFProjectionRankSystem
end
end InfoGeometry.Canonical
