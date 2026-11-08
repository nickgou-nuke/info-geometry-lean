/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered self-associator components in the noncommutative Zorn formula carrier

This module formalizes the explicit four-sector multiplication from the
AI Studio note over an arbitrary associative, possibly noncommutative ring.
It gives the diagonal Nambu-cubic identity and ordered formulas for both
off-diagonal components of the self-associator. The carrier is not asserted
to be associative or alternative, and no field-theoretic meaning is attached
to these formulas.
-/

namespace InfoGeometry.Algebra.NoncommutativeZornNambu

variable {R : Type*} [Ring R]

/-- Three ordered noncommuting coordinates. -/
structure Vec3 (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  deriving DecidableEq

/-- Ordered scalar product. -/
def dot (u v : Vec3 R) : R :=
  u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2

/-- Coordinate cross expression, retaining the order of every factor. -/
def cross (u v : Vec3 R) : Vec3 R :=
  ⟨u.x1 * v.x2 - u.x2 * v.x1,
   u.x2 * v.x0 - u.x0 * v.x2,
   u.x0 * v.x1 - u.x1 * v.x0⟩

/-- The cyclic coordinate rotation on the ordered three-slot carrier. -/
def cyclicRotate (u : Vec3 R) : Vec3 R := ⟨u.x1, u.x2, u.x0⟩

/-- The coordinate rotation has order three. -/
theorem cyclicRotate_order_three {R : Type*} (u : Vec3 R) :
    cyclicRotate (cyclicRotate (cyclicRotate u)) = u := by
  cases u
  rfl

/-- Coefficient-ring commutator with the displayed factor order. -/
def comm (a b : R) : R := a * b - b * a

/-- The cubic Nambu expression `p · (p × p)`. -/
def nambu (p : Vec3 R) : R := dot p (cross p p)

/-- Four-sector vector-matrix carrier used by the transcript's explicit
noncommutative coefficient formula. -/
structure ZornNC (R : Type*) where
  α : R
  x : Vec3 R
  y : Vec3 R
  β : R
  deriving DecidableEq

/-- Its ordered bilinear multiplication formula. -/
def mul (A B : ZornNC R) : ZornNC R where
  α := A.α * B.α - dot A.x B.y
  x := ⟨A.α * B.x.x0 + A.x.x0 * B.β + (cross A.y B.y).x0,
         A.α * B.x.x1 + A.x.x1 * B.β + (cross A.y B.y).x1,
         A.α * B.x.x2 + A.x.x2 * B.β + (cross A.y B.y).x2⟩
  y := ⟨A.β * B.y.x0 + A.y.x0 * B.α + (cross A.x B.x).x0,
         A.β * B.y.x1 + A.y.x1 * B.α + (cross A.x B.x).x1,
         A.β * B.y.x2 + A.y.x2 * B.α + (cross A.x B.x).x2⟩
  β := A.β * B.β - dot A.y B.x

/-- Componentwise additive inverse. -/
def neg (A : ZornNC R) : ZornNC R :=
  ⟨-A.α, ⟨-A.x.x0, -A.x.x1, -A.x.x2⟩,
    ⟨-A.y.x0, -A.y.x1, -A.y.x2⟩, -A.β⟩

/-- Componentwise subtraction. -/
def sub (A B : ZornNC R) : ZornNC R :=
  ⟨A.α - B.α,
    ⟨A.x.x0 - B.x.x0, A.x.x1 - B.x.x1, A.x.x2 - B.x.x2⟩,
    ⟨A.y.x0 - B.y.x0, A.y.x1 - B.y.x1, A.y.x2 - B.y.x2⟩,
    A.β - B.β⟩

/-- Componentwise addition on the four-sector carrier. -/
def add (A B : ZornNC R) : ZornNC R :=
  ⟨A.α + B.α,
    ⟨A.x.x0 + B.x.x0, A.x.x1 + B.x.x1, A.x.x2 + B.x.x2⟩,
    ⟨A.y.x0 + B.y.x0, A.y.x1 + B.y.x1, A.y.x2 + B.y.x2⟩,
    A.β + B.β⟩

/-- Partial split-octonion bar involution from the source note. -/
def conj (A : ZornNC R) : ZornNC R :=
  ⟨A.β, ⟨-A.x.x0, -A.x.x1, -A.x.x2⟩,
    ⟨-A.y.x0, -A.y.x1, -A.y.x2⟩, A.α⟩

/-- Right composition norm using the partial bar from the source formula. -/
def normRight (A : ZornNC R) : ZornNC R := mul A (conj A)

/-- Diagonal supertrace of a four-sector element. -/
def superTrace (A : ZornNC R) : R := A.α - A.β

/-- Sector swap on the four-coordinate carrier. It exchanges the diagonal
coordinates and the two ordered vector slots. Its algebraic properties are
proved separately from this definition. -/
def hodgeSectorSwap (A : ZornNC R) : ZornNC R :=
  ⟨A.β, A.y, A.x, A.α⟩

/-- Simultaneous cyclic rotation of the two vector slots of the ordered
four-sector carrier. This is defined over an arbitrary associative
coefficient ring; no commutation of coefficient entries is built in. -/
def cyclicZorn (A : ZornNC R) : ZornNC R :=
  ⟨A.α, cyclicRotate A.x, cyclicRotate A.y, A.β⟩

/-- Ungraded diagonal trace on the four-coordinate carrier. -/
def ungradedTrace (A : ZornNC R) : R := A.α + A.β

/-- The Hodge sector swap is involutive. -/
theorem hodgeSectorSwap_involutive {R : Type*} (A : ZornNC R) :
    hodgeSectorSwap (hodgeSectorSwap A) = A := by
  cases A
  rfl

omit [Ring R] in
/-- Fixed points of the sector swap are exactly the four-sector elements
whose diagonal entries and vector slots agree. -/
theorem hodgeSectorSwap_fixed_iff (A : ZornNC R) :
    hodgeSectorSwap A = A ↔ A.α = A.β ∧ A.x = A.y := by
  cases A with
  | mk α x y β =>
      simp only [hodgeSectorSwap, ZornNC.mk.injEq]
      constructor
      · rintro ⟨_, _, hxy, hαβ⟩
        exact ⟨hαβ, hxy⟩
      · rintro ⟨hαβ, hxy⟩
        exact ⟨hαβ.symm, hxy.symm, hxy, hαβ⟩

/-- The sector swap is an equivalence of the four-sector carrier, with itself
as inverse. This records the proved involution in Lean's canonical
equivalence type; multiplicative and associator compatibility are recorded
as separate theorems below. -/
def hodgeSectorSwapEquiv {R : Type*} : ZornNC R ≃ ZornNC R where
  toFun := hodgeSectorSwap
  invFun := hodgeSectorSwap
  left_inv := hodgeSectorSwap_involutive
  right_inv := hodgeSectorSwap_involutive

/-- The four-sector swap preserves the explicit ordered multiplication.
This is a property of this formula over the coefficient ring; it does not
make the Zorn carrier associative or alternative. -/
theorem hodgeSectorSwap_mul (A B : ZornNC R) :
    hodgeSectorSwap (mul A B) = mul (hodgeSectorSwap A) (hodgeSectorSwap B) := by
  cases A
  cases B
  rfl

/-- The sector swap commutes with the partial bar operation. -/
theorem hodgeSectorSwap_conj (A : ZornNC R) :
    hodgeSectorSwap (conj A) = conj (hodgeSectorSwap A) := by
  cases A
  rfl

/-- The sector swap preserves the right-composition norm formed from the
defined partial bar. -/
theorem hodgeSectorSwap_normRight (A : ZornNC R) :
    hodgeSectorSwap (normRight A) = normRight (hodgeSectorSwap A) := by
  unfold normRight
  rw [hodgeSectorSwap_mul, hodgeSectorSwap_conj]

/-- The simultaneous three-coordinate rotation preserves the ordered
Zorn-type multiplication, including the order of every coefficient product.
Thus it is an algebra automorphism of this explicitly defined carrier. -/
theorem cyclicZorn_mul (A B : ZornNC R) :
    cyclicZorn (mul A B) = mul (cyclicZorn A) (cyclicZorn B) := by
  cases A with
  | mk α x y β =>
    cases B with
    | mk γ u v δ =>
      cases x with
      | mk x0 x1 x2 =>
        cases y with
        | mk y0 y1 y2 =>
          cases u with
          | mk u0 u1 u2 =>
            cases v with
            | mk v0 v1 v2 =>
              simp [cyclicZorn, cyclicRotate, mul, dot, cross]
              all_goals abel_nf
              all_goals trivial

/-- The cyclic action preserves the sectorwise partial bar operation. -/
theorem cyclicZorn_conj (A : ZornNC R) :
    cyclicZorn (conj A) = conj (cyclicZorn A) := by
  cases A
  rfl

/-- Consequently, the cyclic action preserves the defined right-composition
norm `A * conj A`. -/
theorem cyclicZorn_normRight (A : ZornNC R) :
    cyclicZorn (normRight A) = normRight (cyclicZorn A) := by
  unfold normRight
  rw [cyclicZorn_mul, cyclicZorn_conj]

/-- The multiplicative automorphism `cyclicZorn` has order three. -/
theorem cyclicZorn_order_three {R : Type*} (A : ZornNC R) :
    cyclicZorn (cyclicZorn (cyclicZorn A)) = A := by
  cases A with
  | mk α x y β =>
    cases x with
    | mk x0 x1 x2 =>
      cases y with
      | mk y0 y1 y2 =>
        rfl

omit [Ring R] in
/-- Exchanging the two vector sectors commutes with their simultaneous
coordinate cycle. This is a commuting pair of symmetries on this carrier. -/
theorem hodgeSectorSwap_cyclicZorn (A : ZornNC R) :
    hodgeSectorSwap (cyclicZorn A) = cyclicZorn (hodgeSectorSwap A) := by
  cases A
  rfl

/-- The cyclic action preserves the componentwise additive difference. -/
theorem cyclicZorn_sub (A B : ZornNC R) :
    cyclicZorn (sub A B) = sub (cyclicZorn A) (cyclicZorn B) := by
  cases A
  cases B
  rfl

/-- The sector swap preserves the ungraded diagonal trace. -/
theorem ungradedTrace_hodgeSectorSwap (A : ZornNC R) :
    ungradedTrace (hodgeSectorSwap A) = ungradedTrace A := by
  cases A
  simp [ungradedTrace, hodgeSectorSwap, add_comm]

/-- The sector swap reverses the sign of the diagonal supertrace. -/
theorem superTrace_hodgeSectorSwap (A : ZornNC R) :
    superTrace (hodgeSectorSwap A) = -superTrace A := by
  cases A
  simp [superTrace, hodgeSectorSwap, sub_eq_add_neg]

/-- The cyclic action preserves both diagonal trace functionals because it
leaves the two scalar sectors fixed. -/
theorem ungradedTrace_cyclicZorn (A : ZornNC R) :
    ungradedTrace (cyclicZorn A) = ungradedTrace A := by
  rfl

theorem superTrace_cyclicZorn (A : ZornNC R) :
    superTrace (cyclicZorn A) = superTrace A := by
  rfl

/-- Ordered sum of component commutators pairing the two vector slots. -/
def vectorCommutatorDivergence (x y : Vec3 R) : R :=
  comm x.x0 y.x0 + comm x.x1 y.x1 + comm x.x2 y.x2

/-- Componentwise left-minus-right commutator action of a ring element on a
vector. -/
def commVector (a : R) (v : Vec3 R) : Vec3 R :=
  ⟨comm a v.x0, comm a v.x1, comm a v.x2⟩

/-- Componentwise subtraction on the ordered three-coordinate carrier. -/
def vecSub (u v : Vec3 R) : Vec3 R :=
  ⟨u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2⟩

/-- Componentwise addition on the ordered three-coordinate carrier. -/
def vecAdd (u v : Vec3 R) : Vec3 R :=
  ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2⟩

/-- Left scalar action on each operator coordinate. -/
def vecLeftMul (a : R) (v : Vec3 R) : Vec3 R :=
  ⟨a * v.x0, a * v.x1, a * v.x2⟩

/-- Right scalar action on each operator coordinate. -/
def vecRightMul (v : Vec3 R) (a : R) : Vec3 R :=
  ⟨v.x0 * a, v.x1 * a, v.x2 * a⟩

/-- Right bimodule insertion defect, with the inserted coefficient acting on
the vector from the right before the ordered cross expressions are formed. -/
def rightBimoduleInsertion (a : R) (v : Vec3 R) : Vec3 R :=
  vecSub (cross (vecRightMul v a) v) (cross v (vecRightMul v a))

/-- Left bimodule insertion defect, with the coefficient acting from the left. -/
def leftBimoduleInsertion (a : R) (v : Vec3 R) : Vec3 R :=
  vecSub (cross (vecLeftMul a v) v) (cross v (vecLeftMul a v))

/-- Symmetric four-sector state used for the source's covariant norm formula. -/
def psiCov (a : R) (p : Vec3 R) : ZornNC R := ⟨a, p, p, a⟩

/-- Associator with convention `(A * B) * C - A * (B * C)`. -/
def associator (A B C : ZornNC R) : ZornNC R :=
  sub (mul (mul A B) C) (mul A (mul B C))

/-- The multiplicative cyclic action preserves the ordered associator. -/
theorem cyclicZorn_associator (A B C : ZornNC R) :
    cyclicZorn (associator A B C) =
      associator (cyclicZorn A) (cyclicZorn B) (cyclicZorn C) := by
  unfold associator
  simp only [cyclicZorn_sub, cyclicZorn_mul]

/-- Pure upper-cone element with vector coordinate `p`. -/
def pureUpper (p : Vec3 R) : ZornNC R :=
  ⟨0, p, ⟨0, 0, 0⟩, 0⟩

/-- Pure lower-sector element, dual to `pureUpper` under `hodgeSectorSwap`. -/
def pureLower (p : Vec3 R) : ZornNC R :=
  ⟨0, ⟨0, 0, 0⟩, p, 0⟩

/-- The Hodge sector swap exchanges the pure upper and lower sectors. -/
theorem hodgeSectorSwap_pureUpper (p : Vec3 R) :
    hodgeSectorSwap (pureUpper p) = pureLower p := by
  rfl

theorem hodgeSectorSwap_pureLower (p : Vec3 R) :
    hodgeSectorSwap (pureLower p) = pureUpper p := by
  rfl

/-- The sector swap respects the componentwise additive structure. -/
theorem hodgeSectorSwap_add (A B : ZornNC R) :
    hodgeSectorSwap (add A B) = add (hodgeSectorSwap A) (hodgeSectorSwap B) := by
  cases A
  cases B
  rfl

/-- The sector swap preserves componentwise subtraction. -/
theorem hodgeSectorSwap_sub (A B : ZornNC R) :
    hodgeSectorSwap (sub A B) = sub (hodgeSectorSwap A) (hodgeSectorSwap B) := by
  cases A
  cases B
  rfl

/-- The sector swap transports the ordered associator to the associator of
the swapped arguments. This compatibility does not assert that the
associator vanishes. -/
theorem hodgeSectorSwap_associator (A B C : ZornNC R) :
    hodgeSectorSwap (associator A B C) =
      associator (hodgeSectorSwap A) (hodgeSectorSwap B) (hodgeSectorSwap C) := by
  simp only [associator, hodgeSectorSwap_sub, hodgeSectorSwap_mul]

/-- Opposite pure sectors multiply into opposite diagonal coordinates. -/
theorem pureUpper_pureLower_products (x y : Vec3 R) :
    mul (pureUpper x) (pureLower y) =
      ⟨-(dot x y), ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩ ∧
    mul (pureLower y) (pureUpper x) =
      ⟨0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -(dot y x)⟩ := by
  constructor <;> cases x <;> cases y <;>
    simp [mul, pureUpper, pureLower, dot, cross]

/-- The diagonal supertrace of the anticommutator of opposite pure sectors
is the ordered sum of coordinate commutators. The result is an identity;
nonvanishing requires an additional hypothesis on the coordinates. -/
theorem superTrace_pure_sector_anticommutator (x y : Vec3 R) :
    superTrace
      (add (mul (pureUpper x) (pureLower y))
        (mul (pureLower y) (pureUpper x))) =
      vectorCommutatorDivergence y x := by
  cases x
  cases y
  simp [superTrace, add, mul, pureUpper, pureLower, dot, cross,
    vectorCommutatorDivergence, comm]
  noncomm_ring

/-- A lower-sector vector coupled to a first diagonal operator. -/
def lowerWithScalar (a : R) (p : Vec3 R) : ZornNC R :=
  ⟨a, ⟨0, 0, 0⟩, p, 0⟩

/-- The coordinate Nambu polynomial is the ordered six-term alternating
cubic; no vanishing or commutativity is assumed. -/
theorem nambu_eq_alternating_cubic (p : Vec3 R) :
    nambu p =
      p.x0 * p.x1 * p.x2 - p.x0 * p.x2 * p.x1 +
      p.x1 * p.x2 * p.x0 - p.x1 * p.x0 * p.x2 +
      p.x2 * p.x0 * p.x1 - p.x2 * p.x1 * p.x0 := by
  simp [nambu, dot, cross]
  noncomm_ring

/-- The cubic contraction is the cyclic sum of a coordinate times the
commutator of the other two coordinates. -/
theorem nambu_eq_cyclic_commutator (p : Vec3 R) :
    nambu p = p.x0 * comm p.x1 p.x2 +
      p.x1 * comm p.x2 p.x0 + p.x2 * comm p.x0 p.x1 := by
  simp [nambu, dot, cross, comm]

/-- Simultaneous cyclic rotation preserves the ordered Nambu cubic. -/
theorem nambu_cyclicRotate (p : Vec3 R) :
    nambu (cyclicRotate p) = nambu p := by
  rw [nambu_eq_cyclic_commutator, nambu_eq_cyclic_commutator]
  simp only [cyclicRotate, comm]
  abel

/-- The commutator Jacobi sum vanishes in every associative coefficient ring.
This is an algebraic consequence of associativity, not an extra hypothesis. -/
theorem commutator_jacobi_sum (a b c : R) :
    comm a (comm b c) + comm b (comm c a) + comm c (comm a b) = 0 := by
  simp only [comm]
  noncomm_ring

/-- The discrepancy between the two ordered contractions of the self-cross
is exactly the cyclic commutator Jacobi sum. This gives the intermediate
identity behind `nambu_cyclic_invariance` without imposing a commutative
coefficient model. -/
theorem nambu_contraction_difference_eq_jacobi_sum (p : Vec3 R) :
    dot p (cross p p) - dot (cross p p) p =
      comm p.x0 (comm p.x1 p.x2) +
        comm p.x1 (comm p.x2 p.x0) +
        comm p.x2 (comm p.x0 p.x1) := by
  simp [dot, cross, comm]
  noncomm_ring

/-- The supertrace of the right composition norm is the diagonal commutator
plus the ordered sum of vector-slot commutators. -/
theorem superTrace_normRight_eq_commutators (A : ZornNC R) :
    superTrace (normRight A) =
      comm A.α A.β + vectorCommutatorDivergence A.x A.y := by
  simp [superTrace, normRight, vectorCommutatorDivergence, comm,
    mul, conj, dot, cross]
  noncomm_ring

/-- Component formula for the right norm of a symmetric four-sector state.
Its two diagonal entries agree; each vector slot is the negative sum of the
left-right scalar commutator action and the self-cross term. -/
theorem normRight_psiCov_components (a : R) (p : Vec3 R) :
    (normRight (psiCov a p)).α = a * a + dot p p ∧
    (normRight (psiCov a p)).β = a * a + dot p p ∧
    (normRight (psiCov a p)).x.x0 =
      -((commVector a p).x0 + (cross p p).x0) ∧
    (normRight (psiCov a p)).x.x1 =
      -((commVector a p).x1 + (cross p p).x1) ∧
    (normRight (psiCov a p)).x.x2 =
      -((commVector a p).x2 + (cross p p).x2) ∧
    (normRight (psiCov a p)).y.x0 =
      -((commVector a p).x0 + (cross p p).x0) ∧
    (normRight (psiCov a p)).y.x1 =
      -((commVector a p).x1 + (cross p p).x1) ∧
    (normRight (psiCov a p)).y.x2 =
      -((commVector a p).x2 + (cross p p).x2) := by
  simp [normRight, psiCov, conj, mul, dot, cross, commVector, comm]
  <;> noncomm_ring
  <;> simp

/-- Self-crossing records the three ordered coefficient commutators; it need
not vanish for noncommuting coordinates. -/
theorem cross_self_eq_commutators (p : Vec3 R) :
    cross p p =
      ⟨p.x1 * p.x2 - p.x2 * p.x1,
       p.x2 * p.x0 - p.x0 * p.x2,
       p.x0 * p.x1 - p.x1 * p.x0⟩ := by
  rfl

/-- The right-ordered contraction `dot (cross p p) p` equals the same six-term
alternating cubic as `dot p (cross p p)` in every associative coefficient
ring.  This is cyclic invariance of this particular cubic polynomial; it does
not assert that arbitrary coefficient products are cyclic. -/
theorem nambu_cyclic_invariance (p : Vec3 R) :
    dot (cross p p) p = nambu p := by
  have h := nambu_contraction_difference_eq_jacobi_sum p
  rw [commutator_jacobi_sum] at h
  have hh : dot p (cross p p) = dot (cross p p) p := sub_eq_zero.mp h
  simpa [nambu] using hh.symm

/-- Right-associated cubic of a pure upper-cone element lands in the first
diagonal coordinate with coefficient `-nambu p`. -/
theorem pureUpper_right_cube (p : Vec3 R) :
    mul (pureUpper p) (mul (pureUpper p) (pureUpper p)) =
      ⟨-nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩ := by
  cases p
  simp [mul, pureUpper, dot, cross, nambu]

/-- Left-associated cubic of a pure upper-cone element lands in the opposite
diagonal coordinate. The coefficient agrees with the right-associated one by
the proved cyclic invariance of the cubic contraction. -/
theorem pureUpper_left_cube (p : Vec3 R) :
    mul (mul (pureUpper p) (pureUpper p)) (pureUpper p) =
      ⟨0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩ := by
  cases p
  simp [mul, pureUpper, dot, cross, nambu] <;> noncomm_ring

/-- The self-associator of the pure upper-cone element is the Nambu cubic
with opposite signs in the two diagonal coordinates. -/
theorem pureUpper_self_associator (p : Vec3 R) :
    associator (pureUpper p) (pureUpper p) (pureUpper p) =
      ⟨nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩ := by
  simp [associator, pureUpper_right_cube, pureUpper_left_cube, sub]

/-- The upper-vector component of the self-associator of a lower-sector
state with diagonal coefficient `a`. The two scalar insertions retain their
left/right order; the middle term records the self-cross contribution. -/
theorem lower_with_scalar_self_associator_x (a : R) (p : Vec3 R) :
    (associator (lowerWithScalar a p) (lowerWithScalar a p)
      (lowerWithScalar a p)).x =
      vecSub (vecSub (cross (vecRightMul p a) p)
        (vecLeftMul a (cross p p))) (cross p (vecRightMul p a)) := by
  cases p
  simp [associator, lowerWithScalar, mul, sub, dot, cross,
    vecSub, vecLeftMul, vecRightMul]
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  · noncomm_ring

/-- The two bimodule insertion defects reduce to ordered cross expressions
involving the coefficient commutator. No vector coordinates are assumed to
commute, and the left and right formulas retain distinct multiplication
orders. -/
theorem bimodule_insertion_commutator_forms (a : R) (p : Vec3 R) :
    rightBimoduleInsertion a p = cross p (commVector a p) ∧
    leftBimoduleInsertion a p = cross (commVector a p) p := by
  cases p
  simp [rightBimoduleInsertion, leftBimoduleInsertion, vecSub,
    cross, vecRightMul, vecLeftMul, commVector, comm]
  <;> noncomm_ring
  <;> trivial

/-- The two ordered insertion terms satisfy the inner-derivation product rule
for the self-cross: their sum is the componentwise commutator of the
coefficient with that self-cross. -/
theorem cross_commutator_derivation (a : R) (p : Vec3 R) :
    vecAdd (cross p (commVector a p)) (cross (commVector a p) p) =
      commVector a (cross p p) := by
  cases p
  simp [vecAdd, cross, commVector, comm]
  <;> noncomm_ring
  <;> trivial

/-- Combining the left and right insertion defects gives exactly the inner
commutator variation of the self-cross. This is the algebraic cancellation
statement; no temporal operator, gauge field, or differential equation is
assumed. -/
theorem bimodule_insertions_sum_eq_self_cross_variation (a : R) (p : Vec3 R) :
    vecAdd (rightBimoduleInsertion a p) (leftBimoduleInsertion a p) =
      commVector a (cross p p) := by
  obtain ⟨hr, hl⟩ := bimodule_insertion_commutator_forms a p
  rw [hr, hl]
  exact cross_commutator_derivation a p

/-- The attachment's proposed repeated-coordinate witness `(0,b,b)` has no
upper-sector insertion anomaly at all, regardless of the diagonal operator.
Thus nonvanishing requires a different vector configuration. -/
theorem repeated_lower_coordinates_have_zero_insertion
    (a b : R) :
    (associator (lowerWithScalar a ⟨0, b, b⟩)
      (lowerWithScalar a ⟨0, b, b⟩)
      (lowerWithScalar a ⟨0, b, b⟩)).x = ⟨0, 0, 0⟩ := by
  simp [lower_with_scalar_self_associator_x, vecSub,
    vecLeftMul, vecRightMul, cross]

namespace InsertionMatrixWitness

/-- A concrete two-dimensional operator algebra used to exhibit a nonzero
bimodule insertion anomaly with commuting vector coordinates. -/
abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℤ

def e₁₁ : Mat₂ := !![1, 0; 0, 0]
def e₂₂ : Mat₂ := !![0, 0; 0, 1]
def e₁₂ : Mat₂ := !![0, 1; 0, 0]
def e₂₁ : Mat₂ := !![0, 0; 1, 0]

def p : Vec3 Mat₂ := ⟨0, e₁₁, e₂₂⟩

/-- The two vector coordinates commute (indeed, their ordered products both
vanish), so their self-cross is zero. The diagonal coefficient `e₁₂`
nevertheless produces a nonzero upper-sector self-associator. -/
theorem commuting_coordinates_can_have_nonzero_insertion :
    e₁₂ * e₂₁ ≠ e₂₁ * e₁₂ ∧
    e₁₁ * e₂₂ = 0 ∧ e₂₂ * e₁₁ = 0 ∧
    cross p p = ⟨0, 0, 0⟩ ∧
    (associator (lowerWithScalar e₁₂ p) (lowerWithScalar e₁₂ p)
      (lowerWithScalar e₁₂ p)).x = ⟨e₁₂, 0, 0⟩ ∧
    (associator (lowerWithScalar e₁₂ p) (lowerWithScalar e₁₂ p)
      (lowerWithScalar e₁₂ p)).x ≠ ⟨0, 0, 0⟩ := by
  native_decide

end InsertionMatrixWitness

/-- The diagonal components of the full self-associator depend only on the
two ordered Nambu cubics. The scalar-sector terms cancel under associativity;
the two diagonal signs are opposite. -/
theorem self_associator_diagonal_nambu (A : ZornNC R) :
    (associator A A A).α = nambu A.x - nambu A.y ∧
    (associator A A A).β = nambu A.y - nambu A.x := by
  cases A
  simp [associator, mul, sub, dot, cross, nambu]
  <;> noncomm_ring
  <;> trivial

/-- The diagonal Nambu readout of the self-associator is invariant under the
order-three cyclic action on both vector slots. -/
theorem cyclicZorn_self_associator_diagonal (A : ZornNC R) :
    (associator (cyclicZorn A) (cyclicZorn A) (cyclicZorn A)).α =
      (associator A A A).α ∧
    (associator (cyclicZorn A) (cyclicZorn A) (cyclicZorn A)).β =
      (associator A A A).β := by
  have h := self_associator_diagonal_nambu (cyclicZorn A)
  have h₀ := self_associator_diagonal_nambu A
  constructor
  · rw [h.1, h₀.1]
    simp only [cyclicZorn]
    rw [nambu_cyclicRotate, nambu_cyclicRotate]
  · rw [h.2, h₀.2]
    simp only [cyclicZorn]
    rw [nambu_cyclicRotate, nambu_cyclicRotate]

/-- The upper-vector component of the full four-sector self-associator.
All dot, cross, and scalar actions retain their displayed order; this is the
general component formula, with no diagonal or commuting-coordinate
assumptions. -/
theorem self_associator_upper_component (A : ZornNC R) :
    (associator A A A).x =
      vecAdd
        (vecSub (vecRightMul A.x (dot A.y A.x))
          (vecLeftMul (dot A.x A.y) A.x))
        (vecAdd
          (vecSub (vecRightMul (cross A.y A.y) A.β)
            (vecLeftMul A.α (cross A.y A.y)))
          (vecSub
            (cross
              (vecAdd
                (vecAdd (vecLeftMul A.β A.y) (vecRightMul A.y A.α))
                (cross A.x A.x)) A.y)
            (cross A.y
              (vecAdd
                (vecAdd (vecLeftMul A.β A.y) (vecRightMul A.y A.α))
                (cross A.x A.x))))) := by
  cases A with
  | mk α x y β =>
    cases x with
    | mk x₀ x₁ x₂ =>
      cases y with
      | mk y₀ y₁ y₂ =>
        simp [associator, mul, sub, add, dot, cross, vecAdd, vecSub,
          vecLeftMul, vecRightMul]
        <;> noncomm_ring
        <;> trivial

/-- The lower-vector component of the full four-sector self-associator,
dual to the upper component while keeping the two noncommuting vector slots
and both diagonal coefficients in their original order. -/
theorem self_associator_lower_component (A : ZornNC R) :
    (associator A A A).y =
      vecAdd
        (vecSub (vecRightMul A.y (dot A.x A.y))
          (vecLeftMul (dot A.y A.x) A.y))
        (vecAdd
          (vecSub (vecRightMul (cross A.x A.x) A.α)
            (vecLeftMul A.β (cross A.x A.x)))
          (vecSub
            (cross
              (vecAdd
                (vecAdd (vecLeftMul A.α A.x) (vecRightMul A.x A.β))
                (cross A.y A.y)) A.x)
            (cross A.x
              (vecAdd
                (vecAdd (vecLeftMul A.α A.x) (vecRightMul A.x A.β))
                (cross A.y A.y))))) := by
  cases A with
  | mk α x y β =>
    cases x with
    | mk x₀ x₁ x₂ =>
      cases y with
      | mk y₀ y₁ y₂ =>
        simp [associator, mul, sub, add, dot, cross, vecAdd, vecSub,
          vecLeftMul, vecRightMul]
        <;> noncomm_ring
        <;> trivial

/-- Complete four-coordinate decomposition of the self-associator. The two
diagonal Nambu terms and both order-sensitive vector formulas are collected
without imposing associativity on the Zorn formula carrier. -/
theorem self_associator_full_components (A : ZornNC R) :
    (associator A A A).α = nambu A.x - nambu A.y ∧
    (associator A A A).x =
      vecAdd
        (vecSub (vecRightMul A.x (dot A.y A.x))
          (vecLeftMul (dot A.x A.y) A.x))
        (vecAdd
          (vecSub (vecRightMul (cross A.y A.y) A.β)
            (vecLeftMul A.α (cross A.y A.y)))
          (vecSub
            (cross
              (vecAdd
                (vecAdd (vecLeftMul A.β A.y) (vecRightMul A.y A.α))
                (cross A.x A.x)) A.y)
            (cross A.y
              (vecAdd
                (vecAdd (vecLeftMul A.β A.y) (vecRightMul A.y A.α))
                (cross A.x A.x))))) ∧
    (associator A A A).y =
      vecAdd
        (vecSub (vecRightMul A.y (dot A.x A.y))
          (vecLeftMul (dot A.y A.x) A.y))
        (vecAdd
          (vecSub (vecRightMul (cross A.x A.x) A.α)
            (vecLeftMul A.β (cross A.x A.x)))
          (vecSub
            (cross
              (vecAdd
                (vecAdd (vecLeftMul A.α A.x) (vecRightMul A.x A.β))
                (cross A.y A.y)) A.x)
            (cross A.x
              (vecAdd
                (vecAdd (vecLeftMul A.α A.x) (vecRightMul A.x A.β))
                (cross A.y A.y))))) ∧
    (associator A A A).β = nambu A.y - nambu A.x := by
  exact ⟨(self_associator_diagonal_nambu A).1,
    self_associator_upper_component A,
    self_associator_lower_component A,
    (self_associator_diagonal_nambu A).2⟩

/-- The sum of the two associated cubes has equal negative Nambu coefficients
on the two diagonal coordinates and zero off-diagonal coordinates. -/
theorem pureUpper_associated_cube_sum (p : Vec3 R) :
    add (mul (pureUpper p) (mul (pureUpper p) (pureUpper p)))
        (mul (mul (pureUpper p) (pureUpper p)) (pureUpper p)) =
      ⟨-nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩ := by
  simp [add, pureUpper_right_cube, pureUpper_left_cube]

/-- For every four-sector element, the diagonal of the norm associator is the
signed difference of the two coordinate Nambu cubics. -/
theorem norm_associator_diagonal (X : ZornNC R) :
    (associator X (conj X) X).α = nambu X.y - nambu X.x ∧
    (associator X (conj X) X).β = nambu X.x - nambu X.y := by
  constructor <;>
    simp [associator, mul, sub, conj, dot, cross, nambu] <;>
    noncomm_ring

end InfoGeometry.Algebra.NoncommutativeZornNambu
