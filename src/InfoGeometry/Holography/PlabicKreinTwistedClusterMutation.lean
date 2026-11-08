/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# A finite two-sector matrix algebra

`Cl11Op` is the four-coordinate carrier with ordinary `2 × 2` matrix
multiplication. The results here concern its explicit upper-triangular
nilpotent element and conjugation. They do not define a plabic graph mutation,
a Krein form, a topological holonomy, or a Majorana connection.
-/

namespace InfoGeometry.Holography.PlabicKrein

variable {R : Type*} [CommRing R]

@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R

namespace Cl11Op

variable {R : Type*} [CommRing R]

def zero : Cl11Op R := ⟨0, 0, 0, 0⟩
def one : Cl11Op R := ⟨1, 0, 0, 1⟩

def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

def sub (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 - B.m11, A.m12 - B.m12, A.m21 - B.m21, A.m22 - B.m22⟩

def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21, A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21, A.m21 * B.m12 + A.m22 * B.m22⟩

def nodeBlack (x : R) : Cl11Op R := ⟨x, 0, 0, 0⟩
def nodeWhite (y : R) : Cl11Op R := ⟨0, 0, 0, y⟩
def edgeTwist (w : R) : Cl11Op R := ⟨0, w, 0, 0⟩

/-- The finite unipotent element `1 + edgeTwist w`. -/
def edgeTransport (w : R) : Cl11Op R := add one (edgeTwist w)

/-- The explicit two-sided inverse candidate `1 - edgeTwist w`. -/
def edgeTransportInv (w : R) : Cl11Op R := sub one (edgeTwist w)

/-- The upper-triangular edge operator is nilpotent of order at most two. -/
theorem edgeTwist_sq_zero (w : R) :
    mul (edgeTwist w) (edgeTwist w) = zero := by
  dsimp [edgeTwist, mul, zero]
  ext <;> ring

/-- Multiplication through the two diagonal sectors gives the displayed
upper-right matrix entry. This is a local matrix product identity. -/
theorem nodeBlack_edgeTwist_nodeWhite (x w y : R) :
    mul (mul (nodeBlack x) (edgeTwist w)) (nodeWhite y) =
      ⟨0, x * w * y, 0, 0⟩ := by
  dsimp [nodeBlack, edgeTwist, nodeWhite, mul]
  ext <;> ring

/-- Conjugating the black diagonal element by the explicit unipotent element
has this finite matrix value. -/
theorem edgeTransport_conjugation_nodeBlack (x w : R) :
    mul (mul (edgeTransport w) (nodeBlack x)) (edgeTransportInv w) =
      ⟨x, -(x * w), 0, 0⟩ := by
  dsimp [edgeTransport, edgeTransportInv, nodeBlack, edgeTwist,
    one, add, sub, mul]
  ext <;> ring

/-- Right cancellation of the two explicit unipotent factors. -/
theorem edgeTransport_mul_inv (w : R) :
    mul (edgeTransport w) (edgeTransportInv w) = one := by
  dsimp [edgeTransport, edgeTransportInv, edgeTwist, one, add, sub, mul]
  ext <;> ring

/-- Left cancellation of the two explicit unipotent factors. -/
theorem edgeTransportInv_mul (w : R) :
    mul (edgeTransportInv w) (edgeTransport w) = one := by
  dsimp [edgeTransport, edgeTransportInv, edgeTwist, one, add, sub, mul]
  ext <;> ring

end Cl11Op

end InfoGeometry.Holography.PlabicKrein
