/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracMetricCovariance

/-! Coordinate invariance of Dirac bilinear readouts.

The carrier is the full matrix algebra. The metric transforms by congruence,
operators by conjugation, and spinors by left multiplication. These lemmas
connect `solder_change_basis` to `solder_trace_readout`; they require no
positivity, involutive metric, or claimed Zorn norm isometry.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix
variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

/-- Trace readout is preserved when the observable and Dirac ket–bra are
transported together. -/
theorem solder_trace_change_basis (S T η A : Matrix n n R)
    (hTS : T * S = 1) (l r : n → R) :
    trace ((S * A * T) *
      solder (T.conjTranspose * η * T) (S *ᵥ l) (S *ᵥ r)) =
      trace (A * solder η l r) := by
  rw [solder_change_basis S T η hTS]
  have h : (S * A * T) * (S * solder η l r * T) =
      S * (A * solder η l r) * T := by
    calc
      _ = S * A * (T * S) * solder η l r * T := by noncomm_ring
      _ = S * (A * solder η l r) * T := by rw [hTS]; noncomm_ring
  rw [h, trace_mul_comm, ← mul_assoc, hTS, one_mul]

/-- The Dirac bilinear uses the transported metric, not an ordinary
conjugate-transpose bra. -/
theorem bilinear_change_basis (S T η A : Matrix n n R)
    (hTS : T * S = 1) (l r : n → R) :
    bilinear (T.conjTranspose * η * T) (S * A * T) (S *ᵥ l) (S *ᵥ r) =
      bilinear η A l r := by
  rw [← solder_trace_readout, ← solder_trace_readout]
  exact solder_trace_change_basis S T η A hTS r l

/-- A grading inserted in the trace must be transported along with the observable. -/
theorem graded_solder_trace_change_basis (S T η A Γ : Matrix n n R)
    (hTS : T * S = 1) (l r : n → R) :
    trace ((S * Γ * T) * (S * A * T) *
      solder (T.conjTranspose * η * T) (S *ᵥ l) (S *ᵥ r)) =
      trace (Γ * A * solder η l r) := by
  have h : (S * Γ * T) * (S * A * T) = S * (Γ * A) * T := by
    calc
      _ = S * Γ * (T * S) * A * T := by noncomm_ring
      _ = S * (Γ * A) * T := by rw [hTS]; noncomm_ring
  rw [h]
  exact solder_trace_change_basis S T η (Γ * A) hTS l r

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
