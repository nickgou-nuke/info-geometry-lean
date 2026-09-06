import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ZornSpinor

Formalization of Zorn matrices over split-octonions, providing the algebraic
foundation for the $C\ell(4,4)$ informational gravity framework.

This module replaces the lyrical hypothesis of "Zorn spinors" with an explicit
algebraic construction.
-/

namespace InfoGeometry.Canonical

/--
The Zorn matrix representation of a split-octonion.
A Zorn matrix consists of two scalars (a, b) and two 3-vectors (x, y).
-/
@[rep_depth transport, ext]
structure ZornMatrix (R : Type*) [CommRing R] where
  a : R
  b : R
  x : Fin 3 → R
  y : Fin 3 → R

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/-- Product-coordinate carrier for the additive/module structure of Zorn matrices. -/
abbrev Coord (R : Type*) [CommRing R] :=
  R × R × (Fin 3 → R) × (Fin 3 → R)

/-- The coordinate equivalence used to transport additive and module structure. -/
def coordEquiv : ZornMatrix R ≃ Coord R where
  toFun z := (z.a, z.b, z.x, z.y)
  invFun c := { a := c.1, b := c.2.1, x := c.2.2.1, y := c.2.2.2 }
  left_inv z := by
    ext <;> rfl
  right_inv c := by
    rcases c with ⟨a, b, x, y⟩
    rfl

/-- Zorn matrices inherit their additive commutative group structure from coordinates. -/
instance : AddCommGroup (ZornMatrix R) :=
  Equiv.addCommGroup coordEquiv

/-- Zorn matrices inherit their module structure from coordinates. -/
instance : Module R (ZornMatrix R) :=
  Equiv.module R coordEquiv

/-- Standard dot product for 3-vectors. -/
def dot (v1 v2 : Fin 3 → R) : R :=
  (v1 0 * v2 0) + (v1 1 * v2 1) + (v1 2 * v2 2)

/-- Standard cross product for 3-vectors. -/
def cross (v1 v2 : Fin 3 → R) : Fin 3 → R :=
  ![v1 1 * v2 2 - v1 2 * v2 1,
    v1 2 * v2 0 - v1 0 * v2 2,
    v1 0 * v2 1 - v1 1 * v2 0]

/-- 
Zorn matrix multiplication.
This defines the split-octonion algebra structure.
-/
instance : Mul (ZornMatrix R) where
  mul z1 z2 := {
    a := z1.a * z2.a + dot z1.x z2.y
    b := z1.b * z2.b + dot z1.y z2.x
    x := z1.a • z2.x + z2.b • z1.x - cross z1.y z2.y
    y := z1.b • z2.y + z2.a • z1.y + cross z1.x z2.x
  }

/-- Zorn matrix identity. -/
instance : One (ZornMatrix R) where
  one := { a := 1, b := 1, x := 0, y := 0 }

/--
The "Reduced Owner Surface" projection.
Converts a Zorn matrix to a 2x2 matrix over R by discarding the vector parts.
This represents the thermodynamic "coarse-graining".
-/
def coarseGrain (z : ZornMatrix R) : Matrix (Fin 2) (Fin 2) R :=
  !![z.a, 0; 0, z.b]

/--
The Dirac-Souriau Intertwiner lift.
Constructs a Dirac-Souriau sector from a pair of Zorn matrices.
-/
def toDiracSouriauSector (z1 z2 : ZornMatrix R) : Matrix (Fin 2) (Fin 2) R :=
  !![z1.a, dot z1.x z2.y; dot z1.y z2.x, z2.b]

end ZornMatrix

end InfoGeometry.Canonical
