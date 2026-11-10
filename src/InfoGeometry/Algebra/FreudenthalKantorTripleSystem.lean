/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic Freudenthal--Kantor triple-system contract

This file records the finite algebraic identities used in the supplied
Freudenthal--Kantor reference.  It is a contract for a triple system, not a
construction of a TKK or Kantor Lie algebra.  In particular, no grading or
analytic/Hermitian positivity is inferred from these fields.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTripleSystem

variable {B : Type*} [Ring B]

/-- The non-commutative associative ternary product `⟨x, y, z⟩ = x * y * z`
on any ring `[Ring B]`. -/
def assocTriple (x y z : B) : B :=
  x * y * z

/-- The symmetrized Jordan ternary product `{x, y, z} = x * y * z + z * y * x`
on any non-commutative ring `[Ring B]`. -/
def jordanTriple (x y z : B) : B :=
  x * y * z + z * y * x

/-- Outer symmetry of the Jordan ternary product over any `[Ring B]`. -/
theorem jordanTriple_symm_outer (x y z : B) :
    jordanTriple x y z = jordanTriple z y x := by
  dsimp [jordanTriple]
  abel

/-- An element `c : B` in a non-commutative ring `[Ring B]` is ternary-tripotent
when `c * c * c = c`. -/
def IsRingTripotent (c : B) : Prop :=
  assocTriple c c c = c

/-- Fundamental Freudenthal–Kantor left derivation identity for the associative
ternary product `assocTriple x y z = x * y * z` over any non-commutative ring `[Ring B]`
(with `ε = -1`):
`⟨x, y, ⟨z, w, u⟩⟩ - ⟨z, w, ⟨x, y, u⟩⟩ = ⟨⟨x, y, z⟩, w, u⟩ - ⟨z, ⟨w, x, y⟩, u⟩`. -/
theorem assocTriple_left_identity (x y z w u : B) :
    assocTriple x y (assocTriple z w u) - assocTriple z w (assocTriple x y u) =
      assocTriple (assocTriple x y z) w u - assocTriple z (assocTriple w x y) u := by
  dsimp [assocTriple]
  noncomm_ring

/-- Fundamental Jordan triple identity (Macdonald / Meyberg identity) over any
non-commutative ring `[Ring B]`:
`{x, y, {z, w, z}} = {{x, y, z}, w, z} - {z, {y, x, w}, z} + {z, w, {x, y, z}}`. -/
theorem jordanTriple_fundamental_identity (x y z w : B) :
    jordanTriple x y (jordanTriple z w z) =
      jordanTriple (jordanTriple x y z) w z -
        jordanTriple z (jordanTriple y x w) z +
        jordanTriple z w (jordanTriple x y z) := by
  dsimp [jordanTriple]
  noncomm_ring

end NonCommRingTripleSystem

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

def fktsK (delta : R) (triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U)
    (x y z : U) : U :=
  triple x z y - delta • triple y z x

structure FreudenthalKantorTripleSystem where
  epsilon : R
  delta : R
  triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U
  left_identity :
    ∀ x y z w u,
      triple x y (triple z w u) - triple z w (triple x y u) =
        triple (triple x y z) w u +
          epsilon • triple z (triple y x w) u
  k_identity :
    ∀ x y z w u,
      fktsK delta triple (triple x y z) w u +
          fktsK delta triple z (triple x y w) u +
            delta • fktsK delta triple x
              (fktsK delta triple z w y) u = 0

namespace FreudenthalKantorTripleSystem

variable (data : FreudenthalKantorTripleSystem (R := R) (U := U))

def K (x y z : U) : U :=
  fktsK data.delta data.triple x y z

def IsTripotent (c : U) : Prop :=
  data.triple c c c = c

theorem tripotent_readout {c : U} (hc : IsTripotent data c) :
    data.triple c c c = c :=
  hc

def IsBitriponent (c₁ c₂ : U) (α β γ : R) : Prop :=
    data.triple c₁ c₁ c₂ = α • c₂ ∧
    data.triple c₂ c₂ c₁ = α • c₁ ∧
    data.triple c₁ c₂ c₁ = β • c₂ ∧
    data.triple c₂ c₁ c₂ = β • c₁ ∧
    data.triple c₂ c₁ c₁ = γ • c₂ ∧
    data.triple c₁ c₂ c₂ = γ • c₁

theorem left_identity_readout (x y z w u : U) :
    data.triple x y (data.triple z w u) - data.triple z w (data.triple x y u) =
      data.triple (data.triple x y z) w u +
        data.epsilon • data.triple z (data.triple y x w) u :=
  data.left_identity x y z w u

theorem k_identity_readout (x y z w u : U) :
    K data (data.triple x y z) w u +
        K data z (data.triple x y w) u +
          data.delta • K data x (K data z w y) u = 0 :=
  data.k_identity x y z w u

end FreudenthalKantorTripleSystem

/-- Concrete ground inhabitant of `FreudenthalKantorTripleSystem` over `ℤ`. -/
def intZeroFKTS : FreudenthalKantorTripleSystem (R := ℤ) (U := ℤ) where
  epsilon := 0
  delta := 0
  triple := 0
  left_identity _ _ _ _ _ := by simp
  k_identity _ _ _ _ _ := by simp [fktsK]

end InfoGeometry.Algebra
