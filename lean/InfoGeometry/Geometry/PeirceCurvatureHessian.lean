/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.MatrixTraceQuadratic
import InfoGeometry.Geometry.MatrixCurvatureHessian
import InfoGeometry.Core.PeirceGrading
import Mathlib.Tactic.Linarith

/-! # Peirce grades of the retained curvature-Hessian correction

A self-adjoint idempotent makes the existing even and odd Peirce ranges
orthogonal for the real matrix trace pairing. For pointwise odd variations,
the quadratic curvature remainder is even. Consequently the actual Hessian
correction reads the even part of the background curvature.

The full matrix connection space and its native second derivative are retained.
No grade is assigned to the linearized curvature without an intertwining
hypothesis, and no sign is asserted for the background-curvature correction.
-/

noncomputable section

namespace InfoGeometry.Geometry.PeirceCurvatureHessian

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open InfoGeometry.Analysis.MatrixTraceQuadratic
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Geometry.MatrixCurvatureEnergy

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Orthogonality of the actual even and odd ranges follows from invariance
under the native unitary reflection of a self-adjoint idempotent. -/
theorem tracePair_eq_zero_of_even_odd {p X Y : Mat} (hp : IsStarProjection p)
    (hX : X ∈ LinearMap.range (even p)) (hY : Y ∈ LinearMap.range (odd p)) :
    tracePair X Y = 0 := by
  let U : unitary Mat := ⟨reflection p, reflection_mem_unitary hp⟩
  have hXr : reflection p * X * reflection p = X := by
    rw [(even_commutes_reflection hp.isIdempotentElem hX).eq,
      mul_assoc, reflection_sq hp.isIdempotentElem, mul_one]
  have hYr : reflection p * Y * reflection p = -Y := by
    have hYl : reflection p * Y = -(Y * reflection p) :=
      eq_neg_of_add_eq_zero_left (odd_anticommutes_reflection hp.isIdempotentElem hY)
    rw [hYl, neg_mul, mul_assoc, reflection_sq hp.isIdempotentElem, mul_one]
  have h := tracePair_unitary_conjugate U X Y
  change tracePair (reflection p * X * star (reflection p))
    (reflection p * Y * star (reflection p)) = tracePair X Y at h
  simp only [(reflection_star hp.isSelfAdjoint).star_eq, hXr, hYr, map_neg] at h
  linarith only [h]

/-- The two existing Peirce projection maps are orthogonal for this pairing. -/
theorem tracePair_even_odd_eq_zero {p : Mat} (hp : IsStarProjection p) (X Y : Mat) :
    tracePair (even p X) (odd p Y) = 0 :=
  tracePair_eq_zero_of_even_odd hp
    (LinearMap.mem_range_self _ X) (LinearMap.mem_range_self _ Y)

theorem tracePair_odd_even_eq_zero {p : Mat} (hp : IsStarProjection p) (X Y : Mat) :
    tracePair (odd p X) (even p Y) = 0 := by
  rw [tracePair_comm]
  exact tracePair_even_odd_eq_zero hp Y X

/-- Every matrix pairing separates into the two matching Peirce grades. -/
theorem tracePair_eq_even_add_odd {p : Mat} (hp : IsStarProjection p) (X Y : Mat) :
    tracePair X Y =
      tracePair (even p X) (even p Y) + tracePair (odd p X) (odd p Y) := by
  calc
    tracePair X Y =
        tracePair (even p X + odd p X) (even p Y + odd p Y) := by
      rw [even_add_odd, even_add_odd]
    _ = _ := by
      simp only [map_add, add_apply,
        tracePair_even_odd_eq_zero hp, tracePair_odd_even_eq_zero hp,
        add_zero, zero_add]

/-- An even test matrix reads only the even part of the other argument. -/
theorem tracePair_eq_even_left_of_mem_even {p : Mat} (hp : IsStarProjection p)
    (X C : Mat) (hC : C ∈ LinearMap.range (even p)) :
    tracePair X C = tracePair (even p X) C := by
  have hcross : tracePair (odd p X) C = 0 := by
    rw [tracePair_comm]
    exact tracePair_eq_zero_of_even_odd hp hC (LinearMap.mem_range_self _ X)
  calc
    tracePair X C = tracePair (even p X + odd p X) C := by rw [even_add_odd]
    _ = tracePair (even p X) C := by
      simp only [map_add, add_apply, hcross, add_zero]

variable {ι : Type*} [Fintype ι]
local notation "Conn" => ι → Mat

/-- Odd variations produce an even commutator remainder, so only the even
background curvature enters the retained correction to the actual Hessian.
The linearized-curvature square is unchanged and has no asserted parity. -/
theorem fderiv2_curvatureEnergy_self_of_odd {p : Mat} (hp : IsStarProjection p)
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn)
    (hB : ∀ i, B i ∈ LinearMap.range (odd p)) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B B = ∑ i, ∑ j,
      (tracePair (curvatureDifferential D A i j B) (curvatureDifferential D A i j B) +
        2 * tracePair (even p (curvatureEntry D A i j)) (B i * B j - B j * B i)) := by
  rw [fderiv2_curvatureEnergy_self]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hcomm : B i * B j - B j * B i ∈ LinearMap.range (even p) :=
    (LinearMap.range (even p)).sub_mem
      (odd_mul_odd hp.isIdempotentElem (hB i) (hB j))
      (odd_mul_odd hp.isIdempotentElem (hB j) (hB i))
  rw [tracePair_eq_even_left_of_mem_even hp (curvatureEntry D A i j) _ hcomm]

end InfoGeometry.Geometry.PeirceCurvatureHessian
