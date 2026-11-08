/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Core.IdempotentCartan
import Mathlib.Tactic.NoncommRing

/-! # Algebraic tangent equations and generators for an idempotent

The generic declarations retain their names and proofs from `PeirceTangent`.
No Moore–Penrose inverse or normalized Majorana pair is required here.
-/

namespace InfoGeometry.Core.PeirceTangent

variable {R : Type*} [Ring R]

/-- The first-order idempotent equation is equivalent to both diagonal
Peirce corners vanishing, even in characteristic two. -/
theorem tangent_iff_diagonal_corners_zero {p x : R} (hp : p * p = p) :
    p * x + x * p = x ↔
      p * x * p = 0 ∧ (1 - p) * x * (1 - p) = 0 := by
  constructor
  · intro hx
    have hpxp : p * x * p = 0 := by
      have hleft := congrArg (fun y => p * y) hx
      rw [mul_add, ← mul_assoc p p x, hp, ← mul_assoc p x p] at hleft
      exact add_left_cancel (hleft.trans (add_zero (p * x)).symm)
    refine ⟨hpxp, ?_⟩
    calc
      (1 - p) * x * (1 - p) = x - (p * x + x * p) + p * x * p := by
        noncomm_ring
      _ = 0 := by rw [hx, hpxp]; abel
  · rintro ⟨hpxp, hqxq⟩
    calc
      p * x + x * p = x + p * x * p - (1 - p) * x * (1 - p) := by
        noncomm_ring
      _ = x := by rw [hpxp, hqxq]; abel

/-- The inner adjoint action of `p` on the ring, `adₚ(x) = p*x - x*p`.
Its square is the identity exactly on the linearized idempotent directions. -/
def idempotentAdjoint (p x : R) : R := p * x - x * p

/-- A tangent direction is the sum of its two off-diagonal corners. -/
theorem tangent_eq_offDiagonal {p x : R} (hp : p * p = p)
    (hx : p * x + x * p = x) :
    x = p * x * (1 - p) + (1 - p) * x * p := by
  have hpxp := ((tangent_iff_diagonal_corners_zero hp).mp hx).1
  calc
    x = p * x + x * p - (p * x * p + p * x * p) := by rw [hx, hpxp]; abel
    _ = p * x * (1 - p) + (1 - p) * x * p := by noncomm_ring

/-- The square of the inner adjoint action is the Peirce odd projection.
Consequently its fixed points are exactly the first-order idempotent
directions, over an arbitrary associative ring and in every characteristic. -/
theorem tangent_iff_adjoint_square_eq_self {p x : R} (hp : p * p = p) :
    p * x + x * p = x ↔
      idempotentAdjoint p (idempotentAdjoint p x) = x := by
  have hodd : idempotentAdjoint p (idempotentAdjoint p x) =
      IdempotentCartan.oddPart p x := by
    dsimp [idempotentAdjoint]
    exact (IdempotentCartan.odd_eq_double_commutator hp x).symm
  constructor
  · intro hx
    rw [hodd]
    dsimp [IdempotentCartan.oddPart,
      PeirceDecomposition.component10, PeirceDecomposition.component01,
      PeirceDecomposition.complementIdempotent]
    exact (tangent_eq_offDiagonal hp hx).symm
  · intro had
    rw [hodd] at had
    have hoddTangent :
        p * IdempotentCartan.oddPart p x +
            IdempotentCartan.oddPart p x * p = IdempotentCartan.oddPart p x := by
      dsimp [IdempotentCartan.oddPart,
        PeirceDecomposition.component10, PeirceDecomposition.component01,
        PeirceDecomposition.complementIdempotent]
      have hpq : p * (1 - p) = 0 := by noncomm_ring [hp]
      have hqp : (1 - p) * p = 0 := by noncomm_ring [hp]
      noncomm_ring [hp, hpq, hqp]
      simp only [← mul_assoc p p x, ← mul_assoc p p (x * p), hp]
      abel
    rw [← had]
    exact hoddTangent

/-- Reflection anticommutation measures twice the tangent-equation defect.
Its vanishing cannot be cancelled to tangency in a general ring. -/
theorem reflection_anticommutator (p x : R) :
    (2 * p - 1) * x + x * (2 * p - 1) = 2 • (p * x + x * p - x) := by
  rw [two_nsmul]
  noncomm_ring

/-- Over a ring where doubling is injective, anticommutation with the
reflection `2 * p - 1` is equivalent to the first-order Grassmannian
tangent equation.  The injectivity hypothesis is necessary: in
characteristic two the reflection identity only sees twice the tangent
defect. -/
theorem tangent_iff_reflection_anticommutes_of_two_smul_injective
    {p x : R} (h_two : Function.Injective (fun y : R => (2 : ℕ) • y)) :
    p * x + x * p = x ↔
      (2 * p - 1) * x + x * (2 * p - 1) = 0 := by
  constructor
  · intro hx
    rw [reflection_anticommutator, hx, sub_self, smul_zero]
  · intro h_reflection
    rw [reflection_anticommutator] at h_reflection
    apply sub_eq_zero.mp
    apply h_two
    simpa using h_reflection

/-- Exact reflection criterion in every characteristic: both diagonal Peirce
corners are killed by doubling. Off-diagonal corners are unrestricted.
This identifies the extra solutions without a torsion-freeness premise. -/
theorem reflection_anticommutes_iff_diagonal_corners_two_torsion
    {p x : R} (hp : p * p = p) :
    (2 * p - 1) * x + x * (2 * p - 1) = 0 ↔
      2 • (p * x * p) = 0 ∧ 2 • ((1 - p) * x * (1 - p)) = 0 := by
  have hdef : (2 * p - 1) * x + x * (2 * p - 1) =
      p * (x + x) + (x + x) * p - (x + x) := by noncomm_ring
  rw [hdef, sub_eq_zero, tangent_iff_diagonal_corners_zero hp]
  simp only [mul_add, add_mul, two_nsmul]

/-- Infinitesimal conjugation preserves the idempotent equation in any ring. -/
theorem commutator_tangent {p : R} (hp : p * p = p) (a : R) :
    p * (a * p - p * a) + (a * p - p * a) * p = a * p - p * a := by
  calc
    p * (a * p - p * a) + (a * p - p * a) * p =
        a * (p * p) - (p * p) * a := by noncomm_ring
    _ = a * p - p * a := by rw [hp]

/-- Every algebraic tangent direction has the canonical generator `[x,p]`.
This reconstruction uses no division and remains valid in characteristic two. -/
theorem tangent_eq_double_commutator {p x : R} (hp : p * p = p)
    (hx : p * x + x * p = x) :
    (x * p - p * x) * p - p * (x * p - p * x) = x := by
  have hpxp := ((tangent_iff_diagonal_corners_zero hp).mp hx).1
  calc
    (x * p - p * x) * p - p * (x * p - p * x) =
        x * (p * p) + (p * p) * x - (p * x * p + p * x * p) := by
          noncomm_ring
    _ = x := by rw [hp, hpxp, add_zero, sub_zero, add_comm, hx]

/-- Tangency is exactly membership in the image of infinitesimal conjugation. -/
theorem tangent_iff_exists_commutator {p x : R} (hp : p * p = p) :
    p * x + x * p = x ↔ ∃ a : R, a * p - p * a = x := by
  constructor
  · intro hx
    exact ⟨x * p - p * x, tangent_eq_double_commutator hp hx⟩
  · rintro ⟨a, rfl⟩
    exact commutator_tangent hp a

/-- The canonical off-diagonal generator of a tangent direction is unique.
The commutator with `p` is an involution on tangent directions, even when
doubling is not injective. No choice of a complement or division is needed. -/
theorem tangent_iff_existsUnique_tangent_generator {p x : R} (hp : p * p = p) :
    p * x + x * p = x ↔
      ∃! a : R, (p * a + a * p = a) ∧ a * p - p * a = x := by
  constructor
  · intro hx
    refine ⟨x * p - p * x,
      ⟨commutator_tangent hp x, tangent_eq_double_commutator hp hx⟩, ?_⟩
    intro a ha
    calc
      a = (a * p - p * a) * p - p * (a * p - p * a) :=
        (tangent_eq_double_commutator hp ha.1).symm
      _ = x * p - p * x := by rw [ha.2]
  · rintro ⟨a, ha, _⟩
    rw [← ha.2]
    exact commutator_tangent hp a

/-- All other infinitesimal generators differ from the canonical one by an
element commuting with `p`. This identifies the stabilizer freedom exactly. -/
theorem tangent_generator_iff_difference_commutes {p x : R}
    (hp : p * p = p) (hx : p * x + x * p = x) (a : R) :
    a * p - p * a = x ↔
      (a - (x * p - p * x)) * p = p * (a - (x * p - p * x)) := by
  have hcanonical := tangent_eq_double_commutator hp hx
  have hdefect :
      (a - (x * p - p * x)) * p - p * (a - (x * p - p * x)) =
        (a * p - p * a) - x := by
    calc
      (a - (x * p - p * x)) * p - p * (a - (x * p - p * x)) =
          (a * p - p * a) -
            ((x * p - p * x) * p - p * (x * p - p * x)) := by noncomm_ring
      _ = (a * p - p * a) - x := by rw [hcanonical]
  constructor
  · intro ha
    apply sub_eq_zero.mp
    rw [hdefect, ha, sub_self]
  · intro ha
    apply sub_eq_zero.mp
    rw [← hdefect, ha, sub_self]

variable [StarRing R]

/-- Self-adjoint tangent directions at a self-adjoint projection are precisely
commutators with skew-adjoint generators. This is the algebraic first-order
unitary-conjugation statement, without asserting an analytic flow exists. -/
theorem selfAdjoint_tangent_iff_exists_skewAdjoint_generator
    {p x : R} (hp : p * p = p) (hps : star p = p) :
    (p * x + x * p = x ∧ star x = x) ↔
      ∃ a : R, star a = -a ∧ a * p - p * a = x := by
  constructor
  · rintro ⟨hx, hxs⟩
    refine ⟨x * p - p * x, ?_, tangent_eq_double_commutator hp hx⟩
    rw [star_sub, star_mul, star_mul, hps, hxs]
    abel
  · rintro ⟨a, has, rfl⟩
    refine ⟨commutator_tangent hp a, ?_⟩
    rw [star_sub, star_mul, star_mul, hps, has]
    noncomm_ring

end InfoGeometry.Core.PeirceTangent
