/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracMetricCovariance
import InfoGeometry.CliffordWeyl.DiracPeircePerfectPairing

/-! Coordinate covariance of full-matrix Dirac trace pairing and opposite
Peirce components. The metric and its inverse transform separately; the
transported metric is not assumed involutive.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix InfoGeometry.Core.PeirceDecomposition
variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

theorem dirac_trace_pairing_change_basis (S T η ξ X Y : Matrix n n R)
    (hTS : T * S = 1) :
    trace ((S * X * T) * ((S * ξ * S.conjTranspose) *
      (S * Y * T).conjTranspose * (T.conjTranspose * η * T))) =
      trace (X * (ξ * Y.conjTranspose * η)) := by
  rw [metric_adjoint_change_basis S T η ξ Y hTS]
  have h : (S * X * T) * (S * (ξ * Y.conjTranspose * η) * T) =
      S * (X * (ξ * Y.conjTranspose * η)) * T := by
    calc
      _ = S * X * (T * S) * (ξ * Y.conjTranspose * η) * T := by noncomm_ring
      _ = _ := by rw [hTS]; noncomm_ring
  rw [h, trace_mul_comm, ← mul_assoc, hTS, one_mul]

theorem complement_change_basis (S T P : Matrix n n R) (hST : S * T = 1) :
    complementIdempotent (S * P * T) = S * complementIdempotent P * T := by
  simp only [complementIdempotent, mul_sub, mul_one, sub_mul, hST]

theorem component10_change_basis (S T P X : Matrix n n R)
    (hTS : T * S = 1) (hST : S * T = 1) :
    component10 (S * P * T) (S * X * T) = S * component10 P X * T := by
  unfold component10
  rw [complement_change_basis S T P hST]
  calc
    _ = S * P * (T * S) * X * (T * S) * complementIdempotent P * T := by
      noncomm_ring
    _ = _ := by rw [hTS]; noncomm_ring

theorem component01_change_basis (S T P X : Matrix n n R)
    (hTS : T * S = 1) (hST : S * T = 1) :
    component01 (S * P * T) (S * X * T) = S * component01 P X * T := by
  unfold component01
  rw [complement_change_basis S T P hST]
  calc
    _ = S * complementIdempotent P * (T * S) * X * (T * S) * P * T := by
      noncomm_ring
    _ = _ := by rw [hTS]; noncomm_ring

theorem metric_adjoint_fixed_change_basis (S T η ξ P : Matrix n n R)
    (hTS : T * S = 1) (hP : ξ * P.conjTranspose * η = P) :
    (S * ξ * S.conjTranspose) * (S * P * T).conjTranspose *
      (T.conjTranspose * η * T) = S * P * T := by
  rw [metric_adjoint_change_basis S T η ξ P hTS, hP]

/-- The actual Dirac pairing on projected corner matrices is coordinate invariant. -/
theorem component10_dirac_trace_pairing_change_basis (S T η ξ P X Y : Matrix n n R)
    (hTS : T * S = 1) (hST : S * T = 1) :
    trace (component10 (S * P * T) (S * X * T) *
      ((S * ξ * S.conjTranspose) *
        (component10 (S * P * T) (S * Y * T)).conjTranspose *
          (T.conjTranspose * η * T))) =
      trace (component10 P X * (ξ * (component10 P Y).conjTranspose * η)) := by
  rw [component10_change_basis S T P X hTS hST,
    component10_change_basis S T P Y hTS hST]
  exact dirac_trace_pairing_change_basis S T η ξ (component10 P X) (component10 P Y) hTS

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
