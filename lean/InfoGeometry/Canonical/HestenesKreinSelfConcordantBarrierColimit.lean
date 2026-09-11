import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-!
# Itakura--Saito barrier transport on the Hestenes--Krein colimit

This owner translates the finite real self-concordant barrier kernel into the
Hestenes--Krein colimit language.  The positive scalar readout and its
compatibility are explicit premises.  No infinite prime sum, zeta barrier,
or RH variational theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Krein

def stageBarrier
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  isBarrierKernel (readout n x)

def limitBarrier
    {C : HestenesKreinCone}
    (readout : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  isBarrierKernel (readout x)

theorem stageBarrier_eq_limitBarrier
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, readout n x = limitReadout (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageBarrier readout n x = limitBarrier limitReadout (C.ι n x) := by
  unfold stageBarrier limitBarrier
  rw [hreadout n x]

theorem stageBarrier_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      readout (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        readout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageBarrier readout (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stageBarrier readout n x := by
  unfold stageBarrier
  rw [hreadout n m x]

theorem stageBarrier_nonneg
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hpositive : ∀ n x, 0 < readout n x)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ stageBarrier readout n x := by
  exact isBarrierKernel_nonneg (readout n x) (hpositive n x)

theorem stageBarrier_pos_of_ne_one
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hpositive : ∀ n x, 0 < readout n x)
    (hne : ∀ n x, readout n x ≠ 1)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 < stageBarrier readout n x := by
  exact isBarrierKernel_pos (readout n x) (hpositive n x) (hne n x)

theorem limitBarrier_pos_of_stage_ne_one
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, readout n x = limitReadout (C.ι n x))
    (hpositive : ∀ n x, 0 < readout n x)
    (hne : ∀ n x, readout n x ≠ 1)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 < limitBarrier limitReadout (C.ι n x) := by
  rw [← stageBarrier_eq_limitBarrier readout limitReadout hreadout n x]
  exact stageBarrier_pos_of_ne_one readout hpositive hne n x

end InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit

end noncomputable section
