import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.FiniteJensenTuranKernel

/-!
# Jensen--Turán transport on the Hestenes--Krein colimit

This owner transports the finite real degree-two Jensen--Turán kernel through
the canonical maps of a filtered Hestenes--Krein cone.  Coefficient readout
compatibility is explicit data.  No entire-function, zero-location, or
analytic heat-flow theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinJensenTuranColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.FiniteJensenTuranKernel
open InfoGeometry.Krein

/-! ## Coefficient readouts and the finite kernel -/

def stageTuran
    {C : HestenesKreinCone}
    (coeff : ∀ n, Fin 3 → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  turan (coeff n 0 x) (coeff n 1 x) (coeff n 2 x)

def limitTuran
    {C : HestenesKreinCone}
    (coeff : Fin 3 → DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  turan (coeff 0 x) (coeff 1 x) (coeff 2 x)

theorem stageTuran_eq_limitTuran
    {C : HestenesKreinCone}
    (coeff : ∀ n, Fin 3 → DoubledSpace (C.Base n) → ℝ)
    (limitCoeff : Fin 3 → DoubledSpace C.LimitBase → ℝ)
    (hcoeff : ∀ n i x, coeff n i x = limitCoeff i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageTuran coeff n x = limitTuran limitCoeff (C.ι n x) := by
  unfold stageTuran limitTuran
  rw [hcoeff n 0 x, hcoeff n 1 x, hcoeff n 2 x]

theorem stageTuran_bondIterate_eq
    {C : HestenesKreinCone}
    (coeff : ∀ n, Fin 3 → DoubledSpace (C.Base n) → ℝ)
    (hcoeff : ∀ n m i x,
      coeff (n + m) i
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        coeff n i x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageTuran coeff (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stageTuran coeff n x := by
  unfold stageTuran
  rw [hcoeff n m 0 x, hcoeff n m 1 x, hcoeff n m 2 x]

theorem limitTuran_nonneg_of_stage
    {C : HestenesKreinCone}
    (coeff : ∀ n, Fin 3 → DoubledSpace (C.Base n) → ℝ)
    (limitCoeff : Fin 3 → DoubledSpace C.LimitBase → ℝ)
    (hcoeff : ∀ n i x, coeff n i x = limitCoeff i (C.ι n x))
    (hstage : ∀ n x, 0 ≤ stageTuran coeff n x)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ limitTuran limitCoeff (C.ι n x) := by
  rw [← stageTuran_eq_limitTuran coeff limitCoeff hcoeff n x]
  exact hstage n x

theorem limitTuran_nonneg_of_centered_concavity
    {C : HestenesKreinCone}
    (limitCoeff : Fin 3 → DoubledSpace C.LimitBase → ℝ)
    {x : DoubledSpace C.LimitBase}
    (ha₀ : 0 < limitCoeff 0 x)
    (ha₁ : limitCoeff 1 x = 0)
    (ha₂ : limitCoeff 2 x < 0) :
    0 < limitTuran limitCoeff x := by
  unfold limitTuran
  rw [ha₁]
  exact turan_pos_of_centered_concavity ha₀ ha₂

end InfoGeometry.Canonical.HestenesKreinJensenTuranColimit

end noncomputable section
