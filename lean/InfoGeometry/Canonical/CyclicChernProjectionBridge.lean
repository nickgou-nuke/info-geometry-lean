import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

import InfoGeometry.NCG.NoncommutativeCyclicCocycle

/-!
# Noncommutative chiral projection Chern-4 bridge

This module formalizes the algebraic projection calculus behind the proposed
chiral Chern-4 expression on top of the repository-native noncommutative
derivation and tracial-functional owners.

For an idempotent e and a derivation d:

  e (d e) e = 0,
  (1-e) (d e) (1-e) = 0,
  e (d e)^2 = (d e)^2 e.

Hence the reflection

  J = e + e - 1

satisfies J^2 = 1 and commutes with (d e)^4.

We define the finite algebraic Chern-4 representative

  Ch4(e) = J (d e)^4.

This is an algebraic representative only.  No theorem here identifies it with
the Connes--Moscovici local index formula, a Nieh--Yan integral, a Z/16 class,
or an unquenched LogCFT/BPZ pairing without a separately supplied comparison
hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.CyclicChernProjectionBridge

open InfoGeometry.NCG

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Idempotent chiral projection in a noncommutative algebra. -/
structure ChiralProjection where
  e : A
  idem : e * e = e

namespace ChiralProjection

variable
  (D : CyclicAlgebraDerivation R A)
  (P : ChiralProjection (A := A))

/-- Reflection associated with an idempotent projection. -/
def reflection : A :=
  P.e + P.e - 1

/-- Differential of the projection. -/
def de : A :=
  D P.e

/-- The reflection is an involution. -/
theorem reflection_sq_one :
    P.reflection * P.reflection = 1 := by
  unfold reflection
  calc
    (P.e + P.e - 1) * (P.e + P.e - 1)
        =
      (P.e * P.e + P.e * P.e + P.e * P.e + P.e * P.e) -
        (P.e + P.e + P.e + P.e) + 1 := by
          noncomm_ring
    _ = 1 := by
      rw [P.idem]
      abel

/-- Fundamental projection differential identity:
d(e^2) = (de)e + e(de) = de. -/
theorem de_projection_leibniz :
    P.de D * P.e + P.e * P.de D = P.de D := by
  unfold de
  have h := D.leibniz P.e P.e
  rw [P.idem] at h
  exact h.symm

/-- The differential has zero e-e Peirce block. -/
theorem e_de_e_zero :
    P.e * P.de D * P.e = 0 := by
  have h := P.de_projection_leibniz D
  have hmul := congrArg (fun x : A => P.e * x) h
  simp only [mul_add, mul_assoc, P.idem] at hmul
  have hx :
      P.e * P.de D * P.e + P.e * P.de D =
        P.e * P.de D := by
    simpa [mul_assoc] using hmul
  exact add_right_eq_self.mp hx

/-- The differential also has zero complementary diagonal block. -/
theorem one_sub_e_de_one_sub_e_zero :
    (1 - P.e) * P.de D * (1 - P.e) = 0 := by
  have h := P.de_projection_leibniz D
  have he := P.e_de_e_zero D
  calc
    (1 - P.e) * P.de D * (1 - P.e)
        =
      P.de D - P.e * P.de D - P.de D * P.e +
        P.e * P.de D * P.e := by
          noncomm_ring
    _ = P.de D - P.e * P.de D - P.de D * P.e := by
          rw [he]
          abel
    _ = P.de D - (P.de D * P.e + P.e * P.de D) := by
          abel
    _ = 0 := by
          rw [h]
          simp

/-- The square of de commutes with the projection. -/
theorem e_commutes_de_sq :
    P.e * (P.de D * P.de D) =
      (P.de D * P.de D) * P.e := by
  have h := P.de_projection_leibniz D
  have hleft :
      P.e * P.de D = P.de D - P.de D * P.e := by
    apply eq_sub_of_add_eq
    simpa [add_comm] using h
  have hright :
      P.de D * P.e = P.de D - P.e * P.de D := by
    exact eq_sub_of_add_eq h
  calc
    P.e * (P.de D * P.de D)
        = (P.e * P.de D) * P.de D := by rw [mul_assoc]
    _ = (P.de D - P.de D * P.e) * P.de D := by rw [hleft]
    _ = P.de D * P.de D - (P.de D * P.e) * P.de D := by
          rw [sub_mul]
    _ = P.de D * P.de D - P.de D * (P.e * P.de D) := by
          rw [mul_assoc]
    _ = P.de D * (P.de D - P.e * P.de D) := by
          rw [mul_sub]
    _ = P.de D * (P.de D * P.e) := by rw [← hright]
    _ = (P.de D * P.de D) * P.e := by rw [mul_assoc]

/-- If x commutes with y, then x commutes with y^2. -/
theorem commute_square
    {x y : A} (h : x * y = y * x) :
    x * (y * y) = (y * y) * x := by
  calc
    x * (y * y) = (x * y) * y := by rw [mul_assoc]
    _ = (y * x) * y := by rw [h]
    _ = y * (x * y) := by rw [mul_assoc]
    _ = y * (y * x) := by rw [h]
    _ = (y * y) * x := by rw [mul_assoc]

/-- Fourth differential power. -/
def de4 : A :=
  let q := P.de D * P.de D
  q * q

/-- The projection commutes with the fourth differential power. -/
theorem e_commutes_de4 :
    P.e * P.de4 D = P.de4 D * P.e := by
  unfold de4
  exact commute_square (P.e_commutes_de_sq D)

/-- The reflection J commutes with (de)^4. -/
theorem reflection_commutes_de4 :
    P.reflection * P.de4 D =
      P.de4 D * P.reflection := by
  unfold reflection
  have h := P.e_commutes_de4 D
  calc
    (P.e + P.e - 1) * P.de4 D
        = P.e * P.de4 D + P.e * P.de4 D - P.de4 D := by
            noncomm_ring
    _ = P.de4 D * P.e + P.de4 D * P.e - P.de4 D := by
            rw [h]
    _ = P.de4 D * (P.e + P.e - 1) := by
            noncomm_ring

/-- Algebraic degree-four Chern representative attached to the projection. -/
def chern4 : A :=
  P.reflection * P.de4 D

/-- The Chern representative commutes with the reflection. -/
theorem chern4_commutes_reflection :
    P.chern4 D * P.reflection =
      P.reflection * P.chern4 D := by
  unfold chern4
  have h := P.reflection_commutes_de4 D
  have hJ := P.reflection_sq_one
  calc
    (P.reflection * P.de4 D) * P.reflection
        = P.reflection * (P.de4 D * P.reflection) := by
            rw [mul_assoc]
    _ = P.reflection * (P.reflection * P.de4 D) := by
            rw [← h]
    _ = (P.reflection * P.reflection) * P.de4 D := by
            rw [← mul_assoc]
    _ = P.de4 D := by
            rw [hJ, one_mul]
    _ = P.reflection * (P.reflection * P.de4 D) := by
            symm
            rw [← mul_assoc, hJ, one_mul]
    _ = P.reflection * P.chern4 D := rfl

end ChiralProjection

/-! ## Tracial readout and explicit comparison boundary -/

variable
  (τ : TracialFunctional R A)
  (D : CyclicAlgebraDerivation R A)
  (P : ChiralProjection (A := A))

/-- Scalar trace readout of the algebraic Chern-4 representative. -/
def chern4Pairing : R :=
  τ (P.chern4 D)

/-- Cyclicity permits moving the reflection through the fourth differential
power inside a genuine tracial functional. -/
theorem chern4Pairing_cyclic :
    P.chern4Pairing τ D =
      τ (P.de4 D * P.reflection) := by
  unfold chern4Pairing ChiralProjection.chern4
  exact τ.cyclic _ _

/-- Any proposed geometric/topological readout remains an explicit
identification hypothesis. -/
theorem chern4Pairing_eq_of_identification
    (q : R)
    (h : P.chern4Pairing τ D = q) :
    P.chern4Pairing τ D = q :=
  h

end InfoGeometry.Canonical.CyclicChernProjectionBridge
