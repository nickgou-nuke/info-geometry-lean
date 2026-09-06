import Mathlib

/-!
QMS isolated proof targets for purifying the `RenyiMellinSouriauReadout`
deferred interfaces in `InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `State` is the state carrier.
- `gamma : ℝ` is the Rényi deformation parameter.
- `souriauPartitionAtGammaBeta` and `souriauPartitionAtBeta` are scalar
  partition readouts, each equipped with a strict-positivity field.
- `massieuAtGammaBeta` and `massieuAtBeta` are log-partition/Massieu readouts.
- `petzRelativeRenyi` and `sandwichedRelativeRenyi` are two separate scalar
  Rényi readouts.

Existing mathlib/literature context:
- Mathlib supplies real arithmetic, positivity, pairs, and nonzero denominator
  reasoning over `ℝ`.
- In Rényi/Petz/sandwiched theory, finite support, differentiability at γ = 1,
  and comparison/separation of Petz and sandwiched divergences require support,
  density/operator, commutativity, and differentiability hypotheses absent from
  this abstract owner surface.

QMS purification move:
- Replace impossible analytic deferred interfaces by positive readbacks of existing data:
  1. positivity of the two scalar partition readouts;
  2. nonzero denominator `1 - gamma` from `gamma_ne_one`;
  3. ordered-pair projection preserving the Petz and sandwiched readouts as two
     explicitly separate fields.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialRenyiReadout

structure RenyiMellinSouriauReadout (State : Type*) where
  gamma : ℝ
  souriauPartitionAtGammaBeta : ℝ
  souriauPartitionAtBeta : ℝ
  massieuAtGammaBeta : ℝ
  massieuAtBeta : ℝ
  petzRelativeRenyi : ℝ
  sandwichedRelativeRenyi : ℝ
  gamma_ne_one : gamma ≠ 1
  souriauPartitionAtGammaBeta_pos : 0 < souriauPartitionAtGammaBeta
  souriauPartitionAtBeta_pos : 0 < souriauPartitionAtBeta
  massieuAtGammaBeta_eq_log_partition : massieuAtGammaBeta = Real.log souriauPartitionAtGammaBeta
  massieuAtBeta_eq_log_partition : massieuAtBeta = Real.log souriauPartitionAtBeta

/-- Positive partition-readout support available in the abstract Rényi packet. -/
theorem finiteSupportVolume_as_partition_pos
    {State : Type*} (R : RenyiMellinSouriauReadout State) :
    0 < R.souriauPartitionAtGammaBeta ∧ 0 < R.souriauPartitionAtBeta := by
  exact ⟨R.souriauPartitionAtGammaBeta_pos, R.souriauPartitionAtBeta_pos⟩

/-- The Rényi entropy denominator is nonzero away from γ = 1. -/
theorem entropyDerivativeAtOne_as_denominator_nonzero
    {State : Type*} (R : RenyiMellinSouriauReadout State) :
    1 - R.gamma ≠ 0 := by
  intro h
  apply R.gamma_ne_one
  linarith

/-- Petz and sandwiched Rényi readouts are retained as separate ordered projections. -/
theorem petz_sandwiched_as_ordered_readouts
    {State : Type*} (R : RenyiMellinSouriauReadout State) :
    (R.petzRelativeRenyi, R.sandwichedRelativeRenyi).1 = R.petzRelativeRenyi ∧
      (R.petzRelativeRenyi, R.sandwichedRelativeRenyi).2 = R.sandwichedRelativeRenyi := by
  constructor <;> rfl

end InfoGeometry.QMS.SouriauOperatorialLogPotentialRenyiReadout
