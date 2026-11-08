/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Peirce corner conjugation calculus for elementary expansion

## i. Overview

This module records the finite ring-algebra consequences of conjugating a Peirce corner
by opposite nilpotent corner elements. It complements the categorical pushout and cylinder
owners; it does not construct a globular coherator or prove a homotopy equivalence.

## ii. Key results

- `internal_globular_boundary_squared_zero`: internal globular target `t(X) = N₊ X`, source
  `s(X) = S_P X S_P N₊`, and boundary `∂(X) = t(X) - s(X)` satisfy `t(t(X)) = 0`, `s(s(X)) = 0`,
  and `∂(∂(X)) = 0`.
- `eckmann_hilton_strict_commutativity` & `coherator_weak_vs_strict_socratic_defect`: strict
  interchange commutativity vs. off-diagonal Peirce coherence defect `P F² P - (P F P)² = N₊ N₋`.
- `cornerConjugator_mul_inverse`: the two finite Peirce shears are mutual inverses.
- `cornerConjugation_base_expansion`: the conjugate of `P * X * P` has an exact four-group
  coherator word expansion in the original corner variables.
- `cornerConjugation_even_shift`: its even-grade change is `-(N₊ N₋) x + N₋ x N₊`.
- `cornerConjugation_even_shift_eq_reverse_commutator`: without any commutation hypothesis on `x`,
  the even-grade shift is the exact single commutator `[N₋ x, N₊] = -[N₊, N₋ x]`.
- `cornerConjugation_even_shift_commutator_correction`: the right-grouped commutator `-[x N₊, N₋]`
  differs by the explicit corner commutator `[x, N₊ N₋]`.
- `cornerConjugation_base_left_inverse` & `cornerConjugation_expanded_right_inverse`: two-sided
  constructive retraction isomorphism between `P B P` and the conjugated corner.

## iii. Table of contents

1. Opposite-corner shear and inverse.
2. Base-corner conjugation expansion and even-grade readout.

## iv. References

- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic`
- `InfoGeometry.Canonical.GrothendieckElementaryExpansionPeirceCylinderPoset`

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `cornerConjugator_mul_inverse`, `cornerConjugation_base_left_inverse`,
  `cornerConjugation_expanded_right_inverse`, `cornerConjugation_mul`,
  `cornerConjugation_base_expansion`, `cornerConjugation_even_shift`,
  `cornerConjugation_even_shift_commutator_correction`,
  `cornerConjugation_even_shift_eq_commutator`,
  `cornerConjugation_even_shift_eq_reverse_commutator`,
  `internal_globular_boundary_squared_zero`, `eckmann_hilton_strict_commutativity`,
  `coherator_weak_vs_strict_socratic_defect`,
  `cornerConjugation_projection_retraction_isomorphism`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Requires only `[Ring B]` and idempotent `hP : P * P = P` (zero `Classical.choice`).

#### BUCKET 3 — Open / Un formalized
- Infinite-dimensional analytic convergence beyond finite algebraic degrees.
-/

namespace InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The product of the two elementary shears associated to an idempotent `P`. -/
def cornerConjugator (P A C : B) : B :=
  (1 - conePlus P A) * (1 + coneMinus P C)

/-- The reverse-ordered product is the inverse of `cornerConjugator`. -/
def cornerConjugatorInv (P A C : B) : B :=
  (1 - coneMinus P C) * (1 + conePlus P A)

/-- Conjugation by the corner shear, before restricting to a Peirce corner. -/
def cornerConjugation (P A C X : B) : B :=
  cornerConjugator P A C * X * cornerConjugatorInv P A C

/-- The idempotent defining the corner transported by `cornerConjugation`. -/
def conjugatedCornerIdempotent (P A C : B) : B :=
  cornerConjugation P A C P

/-- Compress conjugation by the inverse shear back to the original Peirce corner. -/
def cornerConjugationRetraction (P A C Y : B) : B :=
  P * cornerConjugatorInv P A C * Y * cornerConjugator P A C * P

/-- The forward and reverse shears multiply to the identity in either order. -/
lemma cornerConjugator_mul_inverse (P A C : B) (hP : P * P = P) :
    cornerConjugator P A C * cornerConjugatorInv P A C = 1 ∧
      cornerConjugatorInv P A C * cornerConjugator P A C = 1 := by
  refine ⟨?_, ?_⟩
  · dsimp [cornerConjugator, cornerConjugatorInv]
    peirce_nf hP
  · dsimp [cornerConjugator, cornerConjugatorInv]
    peirce_nf hP

/-- On the original corner `P B P`, inverse conjugation followed by compression is a
left inverse of `cornerConjugation`. The support equation is explicit in the hypothesis. -/
lemma cornerConjugation_base_left_inverse (P A C X : B) (hP : P * P = P)
    (hX : P * X * P = X) :
    cornerConjugationRetraction P A C (cornerConjugation P A C X) = X := by
  obtain ⟨_, hInvG⟩ := cornerConjugator_mul_inverse P A C hP
  dsimp [cornerConjugationRetraction, cornerConjugation]
  calc
    P * cornerConjugatorInv P A C *
        (cornerConjugator P A C * X * cornerConjugatorInv P A C) *
        cornerConjugator P A C * P =
      P * (cornerConjugatorInv P A C * cornerConjugator P A C) * X *
        (cornerConjugatorInv P A C * cornerConjugator P A C) * P := by
          noncomm_ring
    _ = P * X * P := by rw [hInvG]; simp
    _ = X := hX

/-- Conjugating the compressed inverse image of `Y` reconstructs `Y` whenever `Y` is
supported on the transported idempotent. This is the right inverse on the expanded corner. -/
lemma cornerConjugation_expanded_right_inverse (P A C Y : B) (hP : P * P = P)
    (hY : conjugatedCornerIdempotent P A C * Y *
      conjugatedCornerIdempotent P A C = Y) :
    cornerConjugation P A C (cornerConjugationRetraction P A C Y) = Y := by
  obtain ⟨hGInv, _⟩ := cornerConjugator_mul_inverse P A C hP
  dsimp [cornerConjugation, cornerConjugationRetraction,
    conjugatedCornerIdempotent] at hY ⊢
  calc
    cornerConjugator P A C *
        (P * cornerConjugatorInv P A C * Y * cornerConjugator P A C * P) *
        cornerConjugatorInv P A C =
      ((cornerConjugator P A C * P * cornerConjugatorInv P A C) * Y) *
        (cornerConjugator P A C * P * cornerConjugatorInv P A C) := by noncomm_ring
    _ = Y := hY

/-- Conjugation by mutually inverse shears preserves multiplication. In particular, its
restriction to either supported corner is multiplicative. -/
lemma cornerConjugation_mul (P A C X Y : B) (hP : P * P = P) :
    cornerConjugation P A C (X * Y) =
      cornerConjugation P A C X * cornerConjugation P A C Y := by
  obtain ⟨_, hInvG⟩ := cornerConjugator_mul_inverse P A C hP
  dsimp [cornerConjugation]
  calc
    cornerConjugator P A C * (X * Y) * cornerConjugatorInv P A C =
        cornerConjugator P A C * X * (cornerConjugatorInv P A C *
          cornerConjugator P A C) * Y * cornerConjugatorInv P A C := by
      rw [hInvG]
      noncomm_ring
    _ = cornerConjugator P A C * X * cornerConjugatorInv P A C *
        (cornerConjugator P A C * Y * cornerConjugatorInv P A C) := by
      noncomm_ring

/-- Conjugating a base-corner element has a finite expansion. This is an identity in an
arbitrary (possibly noncommutative) ring, conditional only on `P` being idempotent. -/
lemma cornerConjugation_base_expansion (P A C X : B) (hP : P * P = P) :
    let x := P * X * P
    let np := conePlus P A
    let nm := coneMinus P C
    cornerConjugation P A C x =
      x + (x * np + nm * x) + (nm * x * np - np * nm * x) - np * nm * x * np := by
  dsimp [cornerConjugation, cornerConjugator, cornerConjugatorInv,
    conePlus, coneMinus]
  peirce_nf hP

/-- The even-grade part of the conjugation change has the precise Peirce-corner formula
`-(N₊ N₋) x + N₋ x N₊`. In general it is **not** `-[x N₊, N₋]`; those expressions
require the additional commutation relation `x (N₊ N₋) = (N₊ N₋) x`. -/
lemma cornerConjugation_even_shift (P A C X : B) (hP : P * P = P) :
    let x := P * X * P
    let np := conePlus P A
    let nm := coneMinus P C
    evenGrade P (cornerConjugation P A C x - x) = -(np * nm * x) + nm * x * np := by
  dsimp [cornerConjugation, cornerConjugator, cornerConjugatorInv,
    evenGrade, conePlus, coneMinus]
  peirce_nf hP

/-- The even shift can be expressed using the proposed commutator plus its exact defect.
Thus it equals `-[x N₊, N₋]` whenever `x` commutes with `N₊ N₋`, and without that
hypothesis the commutator expression omits `[x, N₊ N₋]`. -/
lemma cornerConjugation_even_shift_commutator_correction
    (P A C X : B) (hP : P * P = P) :
    let x := P * X * P
    let np := conePlus P A
    let nm := coneMinus P C
    evenGrade P (cornerConjugation P A C x - x) =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (x * np) nm +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm x (np * nm) := by
  calc
    evenGrade P (cornerConjugation P A C (P * X * P) - (P * X * P)) =
        -(conePlus P A * coneMinus P C * (P * X * P)) +
          coneMinus P C * (P * X * P) * conePlus P A :=
      cornerConjugation_even_shift P A C X hP
    _ = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          ((P * X * P) * conePlus P A) (coneMinus P C) +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (P * X * P) (conePlus P A * coneMinus P C) := by
      dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
      noncomm_ring

/-- Under the additional commutation law `x (N₊ N₋) = (N₊ N₋) x`, the even shift
reduces to the commutator proposed in the intake. -/
lemma cornerConjugation_even_shift_eq_commutator
    (P A C X : B) (hP : P * P = P)
    (h_commute :
      (P * X * P) * (conePlus P A * coneMinus P C) =
        (conePlus P A * coneMinus P C) * (P * X * P)) :
    let x := P * X * P
    let np := conePlus P A
    let nm := coneMinus P C
    evenGrade P (cornerConjugation P A C x - x) =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (x * np) nm := by
  calc
    evenGrade P (cornerConjugation P A C (P * X * P) - (P * X * P)) =
        -(conePlus P A * coneMinus P C * (P * X * P)) +
          coneMinus P C * (P * X * P) * conePlus P A :=
      cornerConjugation_even_shift P A C X hP
    _ = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          ((P * X * P) * conePlus P A) (coneMinus P C) := by
      dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
      have h_commute' :
          ((P * X * P) * conePlus P A) * coneMinus P C =
            (conePlus P A * coneMinus P C) * (P * X * P) := by
        calc
          ((P * X * P) * conePlus P A) * coneMinus P C =
              (P * X * P) * (conePlus P A * coneMinus P C) := by rw [mul_assoc]
          _ = (conePlus P A * coneMinus P C) * (P * X * P) := h_commute
      rw [h_commute']
      noncomm_ring

/-- Without any commutation assumption on `x = P * X * P`, grouping the past nilpotent
`N₋ = coneMinus P C` with `x` expresses the even-grade shift as an exact single commutator
`[N₋ x, N₊] = -[N₊, N₋ x]` in every associative ring `B`. -/
lemma cornerConjugation_even_shift_eq_reverse_commutator
    (P A C X : B) (hP : P * P = P) :
    let x := P * X * P
    let np := conePlus P A
    let nm := coneMinus P C
    evenGrade P (cornerConjugation P A C x - x) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (nm * x) np ∧
    evenGrade P (cornerConjugation P A C x - x) =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm np (nm * x) := by
  have h_shift := cornerConjugation_even_shift P A C X hP
  dsimp only at h_shift ⊢
  rw [h_shift]
  constructor <;>
  · dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring

/-- Internal globular target operator `t(X) = N₊ X = conePlus P g * X`. -/
def globTarget (P g X : B) : B :=
  conePlus P g * X

/-- Internal globular chiral source operator `s(X) = S_P X S_P N₊ = invS P * X * invS P * conePlus P g`. -/
def globSource (P g X : B) : B :=
  invS P * X * invS P * conePlus P g

/-- Internal globular boundary operator `∂(X) = t(X) - s(X) = globTarget P g X - globSource P g X`. -/
def globBoundary (P g X : B) : B :=
  globTarget P g X - globSource P g X

/-- In any associative ring `B` with idempotent `P * P = P`, the internal globular target,
source, and boundary operators satisfy `t(t(X)) = 0`, `s(s(X)) = 0`,
`t(s(X)) = -s(t(X))`, and `∂(∂(X)) = 0`. -/
theorem internal_globular_boundary_squared_zero
    (P g X : B) (hP : P * P = P) :
    globTarget P g (globTarget P g X) = 0 ∧
    globSource P g (globSource P g X) = 0 ∧
    globTarget P g (globSource P g X) = -globSource P g (globTarget P g X) ∧
    globBoundary P g (globBoundary P g X) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp [globBoundary, globTarget, globSource]
    peirce_nf hP

/-- Eckmann–Hilton strict commutativity and operation collapse for any pair of binary
operations sharing a two-sided unit `e` and satisfying the middle-four interchange law. -/
theorem eckmann_hilton_strict_commutativity
    {M : Type*} (m1 m2 : M → M → M) (e : M)
    (h_u1_l : ∀ x, m1 e x = x) (h_u1_r : ∀ x, m1 x e = x)
    (h_u2_l : ∀ x, m2 e x = x) (h_u2_r : ∀ x, m2 x e = x)
    (h_interchange : ∀ a b c d, m2 (m1 a b) (m1 c d) = m1 (m2 a c) (m2 b d))
    (a b : M) :
    m2 a b = m1 a b ∧ m1 a b = m1 b a := by
  have h_eq : ∀ x y, m2 x y = m1 x y := by
    intro x y
    calc m2 x y
      _ = m2 (m1 x e) (m1 e y) := by rw [h_u1_r x, h_u1_l y]
      _ = m1 (m2 x e) (m2 e y) := h_interchange x e e y
      _ = m1 x y               := by rw [h_u2_r x, h_u2_l y]
  have h_comm : m1 a b = m1 b a := by
    calc m1 a b
      _ = m1 (m2 e a) (m2 b e) := by rw [h_u2_l a, h_u2_r b]
      _ = m2 (m1 e b) (m1 a e) := (h_interchange e b a e).symm
      _ = m2 b a               := by rw [h_u1_l b, h_u1_r a]
      _ = m1 b a               := h_eq b a
  exact ⟨h_eq a b, h_comm⟩

/-- Off-diagonal Peirce coherence defect `P (F * F) P - (P * F * P) * (P * F * P)`. -/
def coherenceDefect (P F : B) : B :=
  P * (F * F) * P - (P * F * P) * (P * F * P)

/-- The off-diagonal Peirce coherence defect equals `conePlus P F * coneMinus P F`, so any
non-zero coherence defect requires both off-diagonal nilpotent corners to be non-zero. -/
theorem coherator_weak_vs_strict_socratic_defect
    (P F : B) (hP : P * P = P) :
    coherenceDefect P F = conePlus P F * coneMinus P F ∧
    (coherenceDefect P F ≠ 0 → (conePlus P F ≠ 0 ∧ coneMinus P F ≠ 0)) := by
  have h_id : coherenceDefect P F = conePlus P F * coneMinus P F := by
    dsimp [coherenceDefect, conePlus, coneMinus]
    peirce_nf hP
  refine ⟨h_id, ?_⟩
  intro h_nz
  rw [h_id] at h_nz
  exact ⟨fun hL => h_nz (by rw [hL, zero_mul]),
         fun hR => h_nz (by rw [hR, mul_zero])⟩

/-- Unconditional two-sided retraction isomorphism on projected elements `P * X * P` and
`conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C`, together with
idempotence of `conjugatedCornerIdempotent P A C`. -/
theorem cornerConjugation_projection_retraction_isomorphism
    (P A C X Y X1 X2 : B) (hP : P * P = P) :
    let x := P * X * P
    let P_hat := conjugatedCornerIdempotent P A C
    let yh := P_hat * Y * P_hat
    P_hat * P_hat = P_hat ∧
    cornerConjugationRetraction P A C (cornerConjugation P A C x) = x ∧
    cornerConjugation P A C (cornerConjugationRetraction P A C yh) = yh ∧
    cornerConjugation P A C (X1 * X2) =
      cornerConjugation P A C X1 * cornerConjugation P A C X2 := by
  have hP_hat_idem :
      conjugatedCornerIdempotent P A C * conjugatedCornerIdempotent P A C =
        conjugatedCornerIdempotent P A C := by
    dsimp [conjugatedCornerIdempotent, cornerConjugation, cornerConjugator, cornerConjugatorInv]
    peirce_nf hP
  have hx_supp : P * (P * X * P) * P = P * X * P := by
    peirce_nf hP
  have hy_supp :
      conjugatedCornerIdempotent P A C *
        (conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C) *
        conjugatedCornerIdempotent P A C =
      conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C := by
    calc
      conjugatedCornerIdempotent P A C *
          (conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C) *
          conjugatedCornerIdempotent P A C
        = (conjugatedCornerIdempotent P A C * conjugatedCornerIdempotent P A C) * Y *
          (conjugatedCornerIdempotent P A C * conjugatedCornerIdempotent P A C) := by
            noncomm_ring
      _ = conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C := by
            rw [hP_hat_idem]
  exact ⟨hP_hat_idem,
         cornerConjugation_base_left_inverse P A C (P * X * P) hP hx_supp,
         cornerConjugation_expanded_right_inverse P A C
           (conjugatedCornerIdempotent P A C * Y * conjugatedCornerIdempotent P A C) hP hy_supp,
         cornerConjugation_mul P A C X1 X2 hP⟩

end InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
