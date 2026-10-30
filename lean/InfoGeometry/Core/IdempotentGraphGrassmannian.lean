/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentGraphReflectionOrder
import InfoGeometry.Core.IdempotentTangent

/-!
# Division-free graph points and reflection identities for an idempotent

This owner records the algebraic Grassmannian fragment supported by an
associative ring: graph idempotents, their absorption laws, chord coordinates,
the operator `1 - (Q₁ - Q₂)^2`, and ordered products of involutions. It makes no
manifold, positivity, angle, or geodesic claim.
-/

namespace InfoGeometry.Core.IdempotentGraphGrassmannian

open InfoGeometry.Core.IdempotentGraphReflectionOrder

variable {B : Type*} [Ring B]

/-! ## The algebraic Grassmannian and its first-order tangent equation -/

/-- The idempotent locus of a unital associative ring.  This is an algebraic
carrier; no topology or manifold structure is implied by this definition. -/
def idempotentGrassmannian (B : Type*) [Ring B] : Set B :=
  {q | q * q = q}

/-- The idempotency defect of an element of an associative ring. It is a
polynomial value, not generally a central element. -/
def idempotencyDefect (x : B) : B := x * x - x

/-- The companion defect polynomial `x² + x`, equal to the defect of `-x`. -/
def idempotencyDefectBar (x : B) : B := x * x + x

/-- Vanishing of the defect is exactly idempotency. -/
theorem idempotencyDefect_eq_zero_iff {x : B} :
    idempotencyDefect x = 0 ↔ x * x = x := by
  simp [idempotencyDefect, sub_eq_zero]

/-- Complementation preserves the idempotency defect in every ring. -/
theorem idempotencyDefect_one_sub (x : B) :
    idempotencyDefect (1 - x) = idempotencyDefect x := by
  unfold idempotencyDefect
  noncomm_ring

/-- Negation changes the linear term of the defect polynomial. -/
theorem idempotencyDefect_neg (x : B) :
    idempotencyDefect (-x) = x * x + x := by
  unfold idempotencyDefect
  noncomm_ring

/-- The companion polynomial is exactly the defect of the negative element. -/
theorem idempotencyDefectBar_eq_neg (x : B) :
    idempotencyDefectBar x = idempotencyDefect (-x) := by
  unfold idempotencyDefectBar idempotencyDefect
  noncomm_ring

/-- The defects of `x` and `-x` multiply to the defect of `x²`.
This is a polynomial identity in one element and uses no commutativity of `B`. -/
theorem idempotencyDefect_neg_mul (x : B) :
    idempotencyDefect (-x) * idempotencyDefect x =
      idempotencyDefect (x * x) := by
  unfold idempotencyDefect
  noncomm_ring

/-- The reverse ordered product has the same value, since both factors are
polynomials in `x`. -/
theorem idempotencyDefect_mul_neg (x : B) :
    idempotencyDefect x * idempotencyDefect (-x) =
      idempotencyDefect (x * x) := by
  unfold idempotencyDefect
  noncomm_ring

/-- Two successive companion factors telescope to the defect of the fourth
power. Every factor is a polynomial in the same operator, so the identity does
not require the ambient ring to be commutative. -/
theorem idempotencyDefectBar_square_tower (x : B) :
    idempotencyDefectBar (x * x) * idempotencyDefectBar x *
        idempotencyDefect x =
      idempotencyDefect ((x * x) * (x * x)) := by
  unfold idempotencyDefectBar idempotencyDefect
  noncomm_ring

/-- The dyadic geometric product telescopes in any associative ring. -/
theorem one_sub_mul_dyadic_geometricSum (x : B) :
    (1 - x) * (1 + x) * (1 + x * x) *
        (1 + (x * x) * (x * x)) =
      1 - ((x * x) * (x * x)) * ((x * x) * (x * x)) := by
  noncomm_ring

/-- The second defect iterate has a quartic polynomial expansion. -/
theorem idempotencyDefect_iterate (x : B) :
    idempotencyDefect (idempotencyDefect x) =
      x * x * x * x - (2 : ℤ) • (x * x * x) + x := by
  unfold idempotencyDefect
  noncomm_ring

/-- The defect map sends its level set at `1` to the idempotent value `0` on
the next iterate. -/
theorem idempotencyDefect_iterate_eq_zero_of_eq_one {x : B}
    (h : idempotencyDefect x = 1) :
    idempotencyDefect (idempotencyDefect x) = 0 := by
  rw [h]
  simp [idempotencyDefect]

/-- The defect of a sum of mutually orthogonal operators splits additively. -/
theorem idempotencyDefect_add_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    idempotencyDefect (x + y) = idempotencyDefect x + idempotencyDefect y := by
  unfold idempotencyDefect
  noncomm_ring [hxy, hyx]

/-- Orthogonal splitting persists under one further application of the defect
map: the two first defects remain mutually orthogonal. -/
theorem idempotencyDefect_iterate_add_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    idempotencyDefect (idempotencyDefect (x + y)) =
      idempotencyDefect (idempotencyDefect x) +
        idempotencyDefect (idempotencyDefect y) := by
  have hdefect : idempotencyDefect (x + y) =
      idempotencyDefect x + idempotencyDefect y :=
    idempotencyDefect_add_of_orthogonal hxy hyx
  have hxy' : idempotencyDefect x * idempotencyDefect y = 0 := by
    have hx_y2 : x * (y * y) = 0 := by
      calc
        x * (y * y) = (x * y) * y := by rw [mul_assoc]
        _ = 0 * y := by rw [hxy]
        _ = 0 := zero_mul _
    have hx2_y2 : (x * x) * (y * y) = 0 := by
      calc
        (x * x) * (y * y) = x * (x * (y * y)) := mul_assoc x x (y * y)
        _ = x * 0 := by rw [hx_y2]
        _ = 0 := mul_zero _
    have hx2_y : (x * x) * y = 0 := by
      calc
        (x * x) * y = x * (x * y) := mul_assoc x x y
        _ = x * 0 := by rw [hxy]
        _ = 0 := mul_zero _
    unfold idempotencyDefect
    calc
      (x * x - x) * (y * y - y) =
          (x * x) * (y * y) - (x * x) * y - x * (y * y) + x * y := by
            noncomm_ring
      _ = 0 := by rw [hx2_y2, hx2_y, hx_y2, hxy]; simp
  have hyx' : idempotencyDefect y * idempotencyDefect x = 0 := by
    have hy_x2 : y * (x * x) = 0 := by
      calc
        y * (x * x) = (y * x) * x := by rw [mul_assoc]
        _ = 0 * x := by rw [hyx]
        _ = 0 := zero_mul _
    have hy2_x2 : (y * y) * (x * x) = 0 := by
      calc
        (y * y) * (x * x) = y * (y * (x * x)) := mul_assoc y y (x * x)
        _ = y * 0 := by rw [hy_x2]
        _ = 0 := mul_zero _
    have hy2_x : (y * y) * x = 0 := by
      calc
        (y * y) * x = y * (y * x) := mul_assoc y y x
        _ = y * 0 := by rw [hyx]
        _ = 0 := mul_zero _
    unfold idempotencyDefect
    calc
      (y * y - y) * (x * x - x) =
          (y * y) * (x * x) - (y * y) * x - y * (x * x) + y * x := by
            noncomm_ring
      _ = 0 := by rw [hy2_x2, hy2_x, hy_x2, hyx]; simp
  rw [hdefect, idempotencyDefect_add_of_orthogonal hxy' hyx']

/-- Product law for the idempotency-defect polynomial.  The ordered factor
`y * x` is essential: this is a noncommutative identity, not a scalar
factorization. -/
theorem idempotencyDefect_mul (x y : B) :
    idempotencyDefect (x * y) = x * (y * x - 1) * y := by
  unfold idempotencyDefect
  noncomm_ring

/-- The degree-two geometric truncation has the exact ordered remainder
`-x³`; this is valid in every associative ring. -/
theorem one_sub_mul_geometricSum_three (x : B) :
    (1 - x) * (1 + x + x * x) = 1 - x * x * x := by
  noncomm_ring

/-- Rewriting the geometric remainder using the idempotency defect retains
the additional `-x` term: it is not just `-(1+x) * δ(x)`. -/
theorem one_sub_mul_geometricSum_three_defect (x : B) :
    (1 - x) * (1 + x + x * x) - 1 =
      -((1 + x) * idempotencyDefect x) - x := by
  unfold idempotencyDefect
  noncomm_ring

/-- The submitted remainder formula without the final `-x` holds exactly
at zero. This is a characteristic-free criterion in the ambient operator
ring; idempotency alone does not repair the missing term. -/
theorem geometricSum_three_omitted_term_iff_zero (x : B) :
    (1 - x) * (1 + x + x * x) - 1 =
      -((1 + x) * idempotencyDefect x) ↔ x = 0 := by
  rw [one_sub_mul_geometricSum_three_defect, sub_eq_self]

/-- Multiplication by the quadratic truncation `x + x²` has an exact defect
remainder. This finite polynomial identity is the operator analogue of the
claimed Mangoldt truncation; it makes no analytic-series claim. -/
theorem one_sub_mul_quadratic_sum_defect (x : B) :
    (1 - x) * (x + x * x) = -((1 + x) * idempotencyDefect x) := by
  unfold idempotencyDefect
  noncomm_ring

/-- Ring homomorphisms preserve the idempotency-defect polynomial. -/
theorem map_idempotencyDefect {C : Type*} [Ring C] (f : B →+* C) (x : B) :
    f (idempotencyDefect x) = idempotencyDefect (f x) := by
  simp [idempotencyDefect]

/-- The idempotency defect is covariant under conjugation by a left-invertible
element. This does not assert that the defect is central. -/
theorem idempotencyDefect_conj (g x gInv : B)
    (hright : gInv * g = 1) :
    idempotencyDefect (g * x * gInv) =
      g * idempotencyDefect x * gInv := by
  unfold idempotencyDefect
  calc
    (g * x * gInv) * (g * x * gInv) - g * x * gInv =
        g * x * (gInv * g) * x * gInv - g * x * gInv := by noncomm_ring
    _ = g * (x * x - x) * gInv := by rw [hright]; noncomm_ring

/-- The defect satisfies the cubic recurrence `x³ - x² = x * δ(x)` without
any commutativity assumption. -/
theorem cube_sub_square_eq_mul_idempotencyDefect (x : B) :
    x * x * x - x * x = x * idempotencyDefect x := by
  unfold idempotencyDefect
  noncomm_ring

/-- The extra `-x` in the commonly proposed recurrence is not harmless:
that equation holds exactly at `x = 0`. -/
theorem incorrect_cube_recurrence_iff_zero (x : B) :
    x * x * x - x * x - x = x * idempotencyDefect x ↔ x = 0 := by
  constructor
  · intro h
    have h' : x * x * x - x * x - x = x * x * x - x * x := by
      calc
        x * x * x - x * x - x = x * idempotencyDefect x := h
        _ = x * x * x - x * x := by
          simp only [idempotencyDefect, mul_sub]
          rw [← mul_assoc]
    calc
      x = (x * x * x - x * x) - (x * x * x - x * x - x) := by noncomm_ring
      _ = (x * x * x - x * x) - (x * x * x - x * x) := by rw [h']
      _ = 0 := sub_self _
  · rintro rfl
    simp

/-- On the level set `δ(x)=1`, the cubic relation `x³=2x+1` follows. -/
theorem cube_eq_two_smul_add_one_of_idempotencyDefect_eq_one {x : B}
    (h : idempotencyDefect x = 1) :
    x * x * x = (2 : ℤ) • x + 1 := by
  have hsq : x * x = x + 1 := by
    calc
      x * x = (x * x - x) + x := (sub_add_cancel _ _).symm
      _ = 1 + x := by simpa [idempotencyDefect] using congrArg (fun y : B => y + x) h
      _ = x + 1 := add_comm _ _
  calc
    x * x * x = (x + 1) * x := by rw [hsq]
    _ = x * x + x := by rw [add_mul, one_mul]
    _ = (x + 1) + x := by rw [hsq]
    _ = (2 : ℤ) • x + 1 := by rw [two_zsmul]; abel

theorem upperGraph_mem_idempotentGrassmannian {p : B} (hp : p * p = p) (a : B) :
    upperGraph p a ∈ idempotentGrassmannian B :=
  upperGraph_idempotent hp a

theorem lowerGraph_mem_idempotentGrassmannian {p : B} (hp : p * p = p) (c : B) :
    lowerGraph p c ∈ idempotentGrassmannian B :=
  lowerGraph_idempotent hp c

/-- The point reflection of any algebraic Grassmannian point is an involution.
This is a ring identity and carries no metric or geodesic interpretation. -/
theorem pointReflection_idempotent_involution {q : B} (hq : q * q = q) :
    pointReflection q * pointReflection q = 1 := by
  unfold pointReflection
  noncomm_ring [hq]

/-- Every solution of the algebraic first-order idempotent equation is the
sum of its two off-diagonal Peirce corners. -/
theorem tangent_eq_offDiagonal {p x : B} (hp : p * p = p)
    (hx : p * x + x * p = x) :
    x = p * x * (1 - p) + (1 - p) * x * p :=
  InfoGeometry.Core.PeirceTangent.tangent_eq_offDiagonal hp hx

/-- The displacement of an upper graph point from the base idempotent satisfies
the linearized idempotent equation. This is an algebraic tangent statement;
it does not assert the existence of a differentiable path. -/
theorem upperGraph_displacement_tangent {p : B} (hp : p * p = p) (a : B) :
    p * (upperGraph p a - p) + (upperGraph p a - p) * p =
      upperGraph p a - p := by
  have hleft := upperCorner_left hp a
  have hright := upperCorner_right hp a
  rw [show upperGraph p a - p = -upperCorner p a by
    unfold upperGraph
    abel]
  calc
    p * -upperCorner p a + -upperCorner p a * p =
        -(p * upperCorner p a) - upperCorner p a * p := by noncomm_ring
    _ = -upperCorner p a := by rw [hleft, hright]; simp

/-- The displacement of a lower graph point from the base idempotent satisfies
the linearized idempotent equation. As above, this is an algebraic tangent
criterion rather than a claim of manifold or curve structure. -/
theorem lowerGraph_displacement_tangent {p : B} (hp : p * p = p) (c : B) :
    p * (lowerGraph p c - p) + (lowerGraph p c - p) * p =
      lowerGraph p c - p := by
  have hleft := lowerCorner_left hp c
  have hright := lowerCorner_right hp c
  rw [show lowerGraph p c - p = lowerCorner p c by
    unfold lowerGraph
    abel]
  calc
    p * lowerCorner p c + lowerCorner p c * p =
        0 + lowerCorner p c := by rw [hleft, hright]
    _ = lowerCorner p c := by simp

/-! ## A₂₃: graph idempotents and their affine algebra -/

theorem upperGraph_mul_upperGraph {p : B} (hp : p * p = p) (a₁ a₂ : B) :
    upperGraph p a₁ * upperGraph p a₂ = upperGraph p a₂ := by
  have hu₁₂ : upperCorner p a₁ * upperCorner p a₂ = 0 := by
    unfold upperCorner
    calc
      p * a₁ * (1 - p) * (p * a₂ * (1 - p)) =
          p * a₁ * ((1 - p) * p) * a₂ * (1 - p) := by noncomm_ring
      _ = 0 := by rw [complement_mul_p hp]; simp
  unfold upperGraph
  calc
    (p - upperCorner p a₁) * (p - upperCorner p a₂) =
        p * p - p * upperCorner p a₂ - upperCorner p a₁ * p +
          upperCorner p a₁ * upperCorner p a₂ := by noncomm_ring
    _ = p - upperCorner p a₂ := by
      rw [hp, upperCorner_left hp, upperCorner_right hp, hu₁₂]
      simp

theorem lowerGraph_mul_lowerGraph {p : B} (hp : p * p = p) (c₁ c₂ : B) :
    lowerGraph p c₁ * lowerGraph p c₂ = lowerGraph p c₁ := by
  have hw₁₂ : lowerCorner p c₁ * lowerCorner p c₂ = 0 := by
    unfold lowerCorner
    calc
      (1 - p) * c₁ * p * ((1 - p) * c₂ * p) =
          (1 - p) * c₁ * (p * (1 - p)) * c₂ * p := by noncomm_ring
      _ = 0 := by rw [p_mul_complement hp]; simp
  unfold lowerGraph
  calc
    (p + lowerCorner p c₁) * (p + lowerCorner p c₂) =
        p * p + p * lowerCorner p c₂ + lowerCorner p c₁ * p +
          lowerCorner p c₁ * lowerCorner p c₂ := by noncomm_ring
    _ = p + lowerCorner p c₁ := by
      rw [hp, lowerCorner_left hp, lowerCorner_right hp, hw₁₂]
      simp

theorem graph_absorption {p : B} (hp : p * p = p) (a c : B) :
    p * upperGraph p a = upperGraph p a ∧
    upperGraph p a * p = p ∧
    lowerGraph p c * p = lowerGraph p c ∧
    p * lowerGraph p c = p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold upperGraph
    calc
      p * (p - upperCorner p a) = p * p - p * upperCorner p a := by noncomm_ring
      _ = p - upperCorner p a := by rw [hp, upperCorner_left hp]
  · unfold upperGraph
    calc
      (p - upperCorner p a) * p = p * p - upperCorner p a * p := by noncomm_ring
      _ = p := by rw [hp, upperCorner_right hp]; simp
  · unfold lowerGraph
    calc
      (p + lowerCorner p c) * p = p * p + lowerCorner p c * p := by noncomm_ring
      _ = p + lowerCorner p c := by rw [hp, lowerCorner_right hp]
  · unfold lowerGraph
    calc
      p * (p + lowerCorner p c) = p * p + p * lowerCorner p c := by noncomm_ring
      _ = p := by rw [hp, lowerCorner_left hp]; simp

theorem graph_complementary_units {p : B} (hp : p * p = p) (a c : B) :
    (upperGraph p a + (1 - p)) * (1 + upperCorner p a) = 1 ∧
    (1 + upperCorner p a) * (upperGraph p a + (1 - p)) = 1 ∧
    (lowerGraph p c + (1 - p)) * (1 - lowerCorner p c) = 1 ∧
    (1 - lowerCorner p c) * (lowerGraph p c + (1 - p)) = 1 := by
  have hu := upperCorner_sq hp a
  have hw := lowerCorner_sq hp c
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [upperGraph, lowerGraph] <;>
    noncomm_ring [hu, hw]

theorem graph_chord_coordinates {p : B} (a c : B) :
    lowerGraph p c - upperGraph p a = chord p a c ∧
    (p - upperGraph p a) - (lowerGraph p c - p) = midpointDefect p a c ∧
    (p - upperGraph p a) * (lowerGraph p c - p) -
      (lowerGraph p c - p) * (p - upperGraph p a) = commutatorArea p a c := by
  unfold lowerGraph upperGraph chord midpointDefect commutatorArea
  refine ⟨?_, ?_, ?_⟩ <;> noncomm_ring

/-- The chord between the two graph points is an algebraic tangent direction
at the base idempotent. This uses the linearized idempotent equation only; it
does not assert a topological Grassmannian manifold structure. -/
theorem graph_chord_tangent {p : B} (hp : p * p = p) (a c : B) :
    p * chord p a c + chord p a c * p = chord p a c := by
  have huL := upperCorner_left hp a
  have huR := upperCorner_right hp a
  have hlL := lowerCorner_left hp c
  have hlR := lowerCorner_right hp c
  unfold chord
  calc
    p * (upperCorner p a + lowerCorner p c) +
        (upperCorner p a + lowerCorner p c) * p =
      (p * upperCorner p a + upperCorner p a * p) +
        (p * lowerCorner p c + lowerCorner p c * p) := by noncomm_ring
    _ = upperCorner p a + lowerCorner p c := by rw [huL, huR, hlL, hlR]; simp

/-- The midpoint defect is also an algebraic tangent direction at the base
idempotent. Its sign distinguishes it from the graph-point chord. -/
theorem graph_midpointDefect_tangent {p : B} (hp : p * p = p) (a c : B) :
    p * midpointDefect p a c + midpointDefect p a c * p =
      midpointDefect p a c := by
  have huL := upperCorner_left hp a
  have huR := upperCorner_right hp a
  have hlL := lowerCorner_left hp c
  have hlR := lowerCorner_right hp c
  unfold midpointDefect
  calc
    p * (upperCorner p a - lowerCorner p c) +
        (upperCorner p a - lowerCorner p c) * p =
      (p * upperCorner p a + upperCorner p a * p) -
        (p * lowerCorner p c + lowerCorner p c * p) := by noncomm_ring
    _ = upperCorner p a - lowerCorner p c := by rw [huL, huR, hlL, hlR]; simp

theorem graph_chord_square {p : B} (hp : p * p = p) (a c : B) :
    (lowerGraph p c - upperGraph p a) * (lowerGraph p c - upperGraph p a) =
      overlap p a c := by
  have hchord := (graph_chord_coordinates (p := p) a c).1
  calc
    _ = chord p a c * chord p a c := by rw [hchord]
    _ = overlap p a c := by
      unfold chord overlap
      noncomm_ring [upperCorner_sq hp a, lowerCorner_sq hp c]

/-- The commutator of the two graph idempotents is the midpoint defect minus
the corner commutator area. The linear term remains because the lower corner
satisfies `lowerCorner p c * p = lowerCorner p c`. -/
theorem graph_idempotent_commutator_eq_defect_sub_area {p : B} (hp : p * p = p)
    (a c : B) :
    upperGraph p a * lowerGraph p c - lowerGraph p c * upperGraph p a =
      midpointDefect p a c - commutatorArea p a c := by
  have hUpper : upperGraph p a * lowerGraph p c =
      p - upperCorner p a * lowerCorner p c := by
    unfold upperGraph lowerGraph
    calc
      (p - upperCorner p a) * (p + lowerCorner p c) =
          p * p + p * lowerCorner p c - upperCorner p a * p -
            upperCorner p a * lowerCorner p c := by noncomm_ring
      _ = p - upperCorner p a * lowerCorner p c := by
        rw [hp, lowerCorner_left hp, upperCorner_right hp]
        simp
  have hLower : lowerGraph p c * upperGraph p a =
      p - upperCorner p a + lowerCorner p c -
        lowerCorner p c * upperCorner p a := by
    unfold lowerGraph upperGraph
    calc
      (p + lowerCorner p c) * (p - upperCorner p a) =
          p * p - p * upperCorner p a + lowerCorner p c * p -
            lowerCorner p c * upperCorner p a := by noncomm_ring
      _ = p - upperCorner p a + lowerCorner p c -
          lowerCorner p c * upperCorner p a := by
        rw [hp, upperCorner_left hp, lowerCorner_right hp]
  rw [hUpper, hLower]
  unfold midpointDefect commutatorArea
  noncomm_ring

/-! ## A₂₄: algebraic reflection and transition-operator identities -/

def transitionOperator (q r : B) : B := 1 - (q - r) * (q - r)

theorem transition_from_base_upper {p : B} (hp : p * p = p) (a : B) :
    transitionOperator p (upperGraph p a) = 1 := by
  unfold transitionOperator upperGraph
  rw [show p - (p - upperCorner p a) = upperCorner p a by noncomm_ring]
  rw [upperCorner_sq hp a]
  simp

theorem transition_from_base_lower {p : B} (hp : p * p = p) (c : B) :
    transitionOperator p (lowerGraph p c) = 1 := by
  unfold transitionOperator lowerGraph
  rw [show p - (p + lowerCorner p c) = -lowerCorner p c by noncomm_ring]
  rw [show (-lowerCorner p c) * (-lowerCorner p c) =
      lowerCorner p c * lowerCorner p c by noncomm_ring]
  rw [lowerCorner_sq hp c]
  simp

theorem transition_between_graphs {p : B} (hp : p * p = p) (a c : B) :
    transitionOperator (upperGraph p a) (lowerGraph p c) = 1 - overlap p a c := by
  unfold transitionOperator
  have hdiff : upperGraph p a - lowerGraph p c = -chord p a c := by
    calc
      upperGraph p a - lowerGraph p c = -(lowerGraph p c - upperGraph p a) := by abel
      _ = -chord p a c := by rw [(graph_chord_coordinates (p := p) a c).1]
  have hsq : (upperGraph p a - lowerGraph p c) *
      (upperGraph p a - lowerGraph p c) = overlap p a c := by
    rw [hdiff]
    rw [show (-chord p a c) * (-chord p a c) =
      chord p a c * chord p a c by noncomm_ring]
    rw [← (graph_chord_coordinates (p := p) a c).1]
    exact graph_chord_square hp a c
  change 1 - (upperGraph p a - lowerGraph p c) *
    (upperGraph p a - lowerGraph p c) = 1 - overlap p a c
  rw [hsq]

theorem pointReflection_graph_involutions {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (upperGraph p a) = 1 ∧
    pointReflection (lowerGraph p c) * pointReflection (lowerGraph p c) = 1 := by
  have hU := upperGraph_idempotent hp a
  have hW := lowerGraph_idempotent hp c
  constructor <;> unfold pointReflection <;> noncomm_ring [hU, hW]

theorem pointReflection_ordered_products {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) =
      1 + midpointDefect p a c + midpointDefect p a c -
        commutatorArea p a c - commutatorArea p a c -
        overlap p a c - overlap p a c ∧
    pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
      1 - midpointDefect p a c - midpointDefect p a c +
        commutatorArea p a c + commutatorArea p a c -
        overlap p a c - overlap p a c := by
  exact ⟨pointReflection_upper_mul_lower hp a c, pointReflection_lower_mul_upper hp a c⟩

/-- The commutator of the two graph-point reflections is orientation-sensitive:
with the upper reflection first, it is four times the midpoint defect minus
the corner commutator area. Reversing the reflection order negates this term.
This is an algebraic identity; no geodesic or metric interpretation is used. -/
theorem pointReflection_commutator_formula {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) -
      pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
        (4 : ℤ) • (midpointDefect p a c - commutatorArea p a c) := by
  rw [pointReflection_upper_mul_lower hp a c,
    pointReflection_lower_mul_upper hp a c]
  abel

theorem pointReflection_anticommutator_formula {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) +
      pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
        1 + 1 - overlap p a c - overlap p a c -
          overlap p a c - overlap p a c :=
  pointReflection_anticommutator hp a c

end InfoGeometry.Core.IdempotentGraphGrassmannian
