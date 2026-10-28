/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentTangent
import InfoGeometry.Clifford.ChiralProjectorBerryCurvature
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Peirce compression and the operator-valued projector curvature

The carrier is an arbitrary associative ring.  The tangent condition is the
existing first-order idempotent equation `p * x + x * p = x`.

`compressedGram p x y = p * x * (1-p) * y * p` is a bilinear two-point
compression.  On self-adjoint directions its diagonal is a star square and
its alternating part is the existing `projectorCurvature`.  These are exact
operator identities; no manifold, ordinary covariance/BKM identification,
or physical field equation is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature

open InfoGeometry.Core.PeirceTangent
open InfoGeometry.Clifford.ChiralProjectorBerryCurvature

variable {A : Type*} [Ring A]

/-- The ordered two-point compression through the complementary Peirce sector. -/
def compressedGram (p x y : A) : A := p * x * (1 - p) * y * p

/-- Compression at the left endpoint stays in the same corner. -/
theorem compressedGram_left {p : A} (hp : p * p = p) (x y : A) :
    p * compressedGram p x y = compressedGram p x y := by
  unfold compressedGram
  calc
    p * (p * x * (1 - p) * y * p) = (p * p) * x * (1 - p) * y * p := by
      noncomm_ring
    _ = p * x * (1 - p) * y * p := by rw [hp]

/-- Compression at the right endpoint stays in the same corner. -/
theorem compressedGram_right {p : A} (hp : p * p = p) (x y : A) :
    compressedGram p x y * p = compressedGram p x y := by
  unfold compressedGram
  rw [mul_assoc, hp]

/-- A tangent insertion has no intermediate contribution from the same sector. -/
theorem compressed_product_eq_compressedGram {p x : A}
    (hp : p * p = p) (hx : p * x + x * p = x) (y : A) :
    p * x * y * p = compressedGram p x y := by
  have hpxp := ((tangent_iff_diagonal_corners_zero hp).mp hx).1
  calc
    p * x * y * p = compressedGram p x y + (p * x * p) * y * p := by
      unfold compressedGram
      noncomm_ring
    _ = compressedGram p x y := by rw [hpxp]; simp

/-- Two tangent insertions have an even product.  No division by two is used. -/
theorem tangent_product_commutes {p x y : A}
    (hx : p * x + x * p = x) (hy : p * y + y * p = y) :
    p * (x * y) = (x * y) * p := by
  apply sub_eq_zero.mp
  calc
    p * (x * y) - (x * y) * p =
        (p * x + x * p - x) * y - x * (p * y + y * p - y) := by
          noncomm_ring
    _ = 0 := by rw [hx, hy]; simp

/-- Alternating the ordered intersector correlation gives the existing
projector-curvature coefficient. -/
theorem compressedGram_sub_swap_eq_projectorCurvature {p x y : A}
    (hp : p * p = p) (hx : p * x + x * p = x)
    (hy : p * y + y * p = y) :
    compressedGram p x y - compressedGram p y x =
      projectorCurvature p x y := by
  rw [← compressed_product_eq_compressedGram hp hx,
    ← compressed_product_eq_compressedGram hp hy]
  unfold projectorCurvature commutator
  noncomm_ring

/-- The curvature coefficient acts inside the projective corner on the left. -/
theorem projectorCurvature_left {p : A} (hp : p * p = p) (x y : A) :
    p * projectorCurvature p x y = projectorCurvature p x y := by
  unfold projectorCurvature
  calc
    p * (p * commutator x y * p) = (p * p) * commutator x y * p := by
      noncomm_ring
    _ = p * commutator x y * p := by rw [hp]

/-- The curvature coefficient acts inside the projective corner on the right. -/
theorem projectorCurvature_right {p : A} (hp : p * p = p) (x y : A) :
    projectorCurvature p x y * p = projectorCurvature p x y := by
  unfold projectorCurvature
  rw [mul_assoc, hp]

section Star

variable [StarRing A]

/-- Reversing a self-adjoint pair is the adjoint of the ordered compression. -/
theorem star_compressedGram {p x y : A}
    (hps : star p = p) (hxs : star x = x) (hys : star y = y) :
    star (compressedGram p x y) = compressedGram p y x := by
  unfold compressedGram
  simp only [star_mul, star_sub, star_one, hps, hxs, hys]
  noncomm_ring

/-- The diagonal compression is the Gram operator of the directed Peirce arrow. -/
theorem compressedGram_self_eq_star_mul_self {p x : A}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    compressedGram p x x =
      star ((1 - p) * x * p) * ((1 - p) * x * p) := by
  have hq : (1 - p) * (1 - p) = 1 - p := by
    calc
      (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
      _ = 1 - p := by rw [hp]; abel
  symm
  calc
    star ((1 - p) * x * p) * ((1 - p) * x * p) =
        p * x * ((1 - p) * (1 - p)) * x * p := by
          simp only [star_mul, star_sub, star_one, hps, hxs]
          noncomm_ring
    _ = compressedGram p x x := by rw [hq]; rfl

/-- Self-adjoint tangent directions produce a skew-adjoint curvature coefficient. -/
theorem star_projectorCurvature_of_selfAdjoint {p x y : A}
    (hps : star p = p) (hxs : star x = x) (hys : star y = y) :
    star (projectorCurvature p x y) = -projectorCurvature p x y := by
  unfold projectorCurvature commutator
  simp only [star_mul, star_sub, hps, hxs, hys]
  noncomm_ring

end Star

section Naturality

variable {B : Type*} [Ring B]

/-- Native ring morphisms preserve the full ordered compression. -/
theorem map_compressedGram (f : A →+* B) (p x y : A) :
    f (compressedGram p x y) = compressedGram (f p) (f x) (f y) := by
  simp [compressedGram]

/-- Projector-curvature coefficients are natural under native ring morphisms. -/
theorem map_projectorCurvature (f : A →+* B) (p x y : A) :
    f (projectorCurvature p x y) = projectorCurvature (f p) (f x) (f y) := by
  simp [projectorCurvature, commutator]

end Naturality

end InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
