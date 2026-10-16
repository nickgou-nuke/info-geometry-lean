/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# The matrix corner of Markov group-inverse Petz compression

For the full, generally noncommutative matrix algebra, compression by the
group-inverse range idempotent has image exactly the corresponding corner
`E M E`.  The corner is stable under left and right multiplication by its
own elements.  This is an algebraic statement about `X ↦ E * X * E`; it does
not assert state-dependent Petz recovery, positivity, or trace preservation.
-/

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.PetzMartingale

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The image of compression by an idempotent is exactly the fixed corner. -/
theorem petzRecovery_range_iff_corner
    (E Y : Matrix ι ι ℝ) (hE : E * E = E) :
    Y ∈ Set.range (fun X : Matrix ι ι ℝ => petzRecovery E X) ↔
      E * Y * E = Y := by
  constructor
  · rintro ⟨X, rfl⟩
    exact petz_recovery_idempotent E hE X
  · intro hY
    exact ⟨Y, hY⟩

/-- Elements fixed by an idempotent compression multiply through the
compression on both sides of an arbitrary full-matrix input. -/
theorem petzRecovery_corner_bimodule
    (E C D X : Matrix ι ι ℝ) (hE : E * E = E)
    (hC : E * C * E = C) (hD : E * D * E = D) :
    petzRecovery E (C * X * D) = C * petzRecovery E X * D := by
  have hEC : E * C = C := by
    have hmul := congrArg (fun Z : Matrix ι ι ℝ => E * Z) hC
    calc
      E * C = E * (E * C * E) := hmul.symm
      _ = (E * E) * C * E := by noncomm_ring
      _ = E * C * E := by rw [hE]
      _ = C := hC
  have hCE : C * E = C := by
    have hmul := congrArg (fun Z : Matrix ι ι ℝ => Z * E) hC
    calc
      C * E = (E * C * E) * E := hmul.symm
      _ = E * C * (E * E) := by noncomm_ring
      _ = E * C * E := by rw [hE]
      _ = C := hC
  have hED : E * D = D := by
    have hmul := congrArg (fun Z : Matrix ι ι ℝ => E * Z) hD
    calc
      E * D = E * (E * D * E) := hmul.symm
      _ = (E * E) * D * E := by noncomm_ring
      _ = E * D * E := by rw [hE]
      _ = D := hD
  have hDE : D * E = D := by
    have hmul := congrArg (fun Z : Matrix ι ι ℝ => Z * E) hD
    calc
      D * E = (E * D * E) * E := hmul.symm
      _ = E * D * (E * E) := by noncomm_ring
      _ = E * D * E := by rw [hE]
      _ = D := hD
  change E * (C * X * D) * E = C * (E * X * E) * D
  calc
    E * (C * X * D) * E = C * X * D := by
      rw [show E * (C * X * D) * E = (E * C) * X * (D * E) by noncomm_ring,
        hEC, hDE]
    _ = C * (E * X * E) * D := by
      rw [show C * (E * X * E) * D = (C * E) * X * (E * D) by noncomm_ring,
        hCE, hED]

/-- The Markov range idempotent's compression has image equal to its full
matrix corner. -/
theorem markovRange_petzRecovery_range_iff_corner
    (P G Y : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    Y ∈ Set.range (fun X : Matrix ι ι ℝ =>
        petzRecovery (markovRangeIdempotent P G) X) ↔
      markovRangeIdempotent P G * Y * markovRangeIdempotent P G = Y := by
  exact petzRecovery_range_iff_corner (markovRangeIdempotent P G) Y
    (markovRangeIdempotent_idempotent P G hG)

/-- The Markov group-inverse compression obeys the corner bimodule law on
the full noncommutative matrix carrier. -/
theorem markovRange_petzRecovery_corner_bimodule
    (P G C D X : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hC : markovRangeIdempotent P G * C * markovRangeIdempotent P G = C)
    (hD : markovRangeIdempotent P G * D * markovRangeIdempotent P G = D) :
    petzRecovery (markovRangeIdempotent P G) (C * X * D) =
      C * petzRecovery (markovRangeIdempotent P G) X * D := by
  exact petzRecovery_corner_bimodule (markovRangeIdempotent P G) C D X
    (markovRangeIdempotent_idempotent P G hG) hC hD

end InfoGeometry.QuantumContext
