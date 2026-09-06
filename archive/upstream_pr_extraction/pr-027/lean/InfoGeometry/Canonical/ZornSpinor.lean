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
def mul (z1 z2 : ZornMatrix R) : ZornMatrix R := {
  a := z1.a * z2.a + dot z1.x z2.y
  b := z1.b * z2.b + dot z1.y z2.x
  x := z1.a • z2.x + z2.b • z1.x - cross z1.y z2.y
  y := z1.b • z2.y + z2.a • z1.y + cross z1.x z2.x
}

instance : Mul (ZornMatrix R) where
  mul := mul

@[simp] theorem mul_def (z1 z2 : ZornMatrix R) : z1 * z2 = mul z1 z2 := rfl

@[simp] theorem add_def (z1 z2 : ZornMatrix R) :
  z1 + z2 = { a := z1.a + z2.a, b := z1.b + z2.b, x := z1.x + z2.x, y := z1.y + z2.y } := rfl

@[simp] theorem sub_def (z1 z2 : ZornMatrix R) :
  z1 - z2 = { a := z1.a - z2.a, b := z1.b - z2.b, x := z1.x - z2.x, y := z1.y - z2.y } := rfl

@[simp] theorem neg_def (z : ZornMatrix R) :
  -z = { a := -z.a, b := -z.b, x := -z.x, y := -z.y } := rfl

/-- Zorn matrix identity. -/
instance : One (ZornMatrix R) where
  one := { a := 1, b := 1, x := 0, y := 0 }

/-! ## Diagonal Peirce projectors -/

/-- Upper diagonal Zorn idempotent. -/
def zornPlus : ZornMatrix R :=
  { a := 1, b := 0, x := 0, y := 0 }

/-- Lower diagonal Zorn idempotent. -/
def zornMinus : ZornMatrix R :=
  { a := 0, b := 1, x := 0, y := 0 }

/-- Labels for the two diagonal Zorn Peirce idempotents. -/
inductive ZornSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The two diagonal Peirce idempotents. -/
def idempotent : ZornSign → ZornMatrix R
  | .plus => zornPlus
  | .minus => zornMinus

/-- Double-sided Peirce component with explicit left bracketing. -/
def peirceComponent (left right Z : ZornMatrix R) : ZornMatrix R :=
  (left * Z) * right

/-- The color/triplet Zorn Peirce block. -/
def colorProject (Z : ZornMatrix R) : ZornMatrix R :=
  peirceComponent zornPlus zornMinus Z

/-- The anticolor/dual-triplet Zorn Peirce block. -/
def anticolorProject (Z : ZornMatrix R) : ZornMatrix R :=
  peirceComponent zornMinus zornPlus Z

theorem zornPlus_idempotent :
    zornPlus (R := R) * zornPlus (R := R) = zornPlus := by
  ext i <;> simp [mul_def, zornPlus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

theorem zornMinus_idempotent :
    zornMinus (R := R) * zornMinus (R := R) = zornMinus := by
  ext i <;> simp [mul_def, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

theorem zornPlus_mul_zornMinus :
    zornPlus (R := R) * zornMinus (R := R) = 0 := by
  change zornPlus (R := R) * zornMinus (R := R) =
    ({ a := 0, b := 0, x := 0, y := 0 } : ZornMatrix R)
  ext i <;> simp [mul_def, zornPlus, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

theorem zornMinus_mul_zornPlus :
    zornMinus (R := R) * zornPlus (R := R) = 0 := by
  change zornMinus (R := R) * zornPlus (R := R) =
    ({ a := 0, b := 0, x := 0, y := 0 } : ZornMatrix R)
  ext i <;> simp [mul_def, zornPlus, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

theorem zornPlus_add_zornMinus :
    zornPlus (R := R) + zornMinus (R := R) = 1 := by
  change zornPlus (R := R) + zornMinus (R := R) =
    ({ a := 1, b := 1, x := 0, y := 0 } : ZornMatrix R)
  ext i <;> simp [zornPlus, zornMinus]

/--
For the diagonal Peirce idempotents, the two possible sandwich bracketings
agree.  This theorem keeps nonassociativity explicit rather than silently
rewriting arbitrary products.
-/
theorem peirce_bracketing
    (i j : ZornSign) (Z : ZornMatrix R) :
    ((idempotent (R := R) i * Z) * idempotent (R := R) j) =
      (idempotent (R := R) i * (Z * idempotent (R := R) j)) := by
  cases i <;> cases j <;> cases Z <;> ext k <;>
    simp [mul_def, idempotent, zornPlus, zornMinus, mul, dot, cross]
  any_goals fin_cases k <;> rfl

/-- The upper diagonal Peirce component extracts the `a` scalar. -/
theorem peirce_plus_plus_apply (Z : ZornMatrix R) :
    peirceComponent (zornPlus (R := R)) zornPlus Z =
      { a := Z.a, b := 0, x := 0, y := 0 } := by
  cases Z
  ext i <;> simp [peirceComponent, mul_def, zornPlus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

/-- The color Peirce component extracts the upper vector slot. -/
theorem colorProject_apply (Z : ZornMatrix R) :
    colorProject Z =
      { a := 0, b := 0, x := Z.x, y := 0 } := by
  cases Z
  ext i <;> simp [colorProject, peirceComponent, mul_def, zornPlus, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

/-- The anticolor Peirce component extracts the lower vector slot. -/
theorem anticolorProject_apply (Z : ZornMatrix R) :
    anticolorProject Z =
      { a := 0, b := 0, x := 0, y := Z.y } := by
  cases Z
  ext i <;> simp [anticolorProject, peirceComponent, mul_def, zornPlus, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

/-- The lower diagonal Peirce component extracts the `b` scalar. -/
theorem peirce_minus_minus_apply (Z : ZornMatrix R) :
    peirceComponent (zornMinus (R := R)) zornMinus Z =
      { a := 0, b := Z.b, x := 0, y := 0 } := by
  cases Z
  ext i <;> simp [peirceComponent, mul_def, zornMinus, mul, dot, cross]
  · fin_cases i <;> rfl

/-- The color Peirce projection is idempotent. -/
theorem colorProject_idempotent (Z : ZornMatrix R) :
    colorProject (colorProject Z) = colorProject Z := by
  rw [colorProject_apply, colorProject_apply]

/-- The anticolor Peirce projection is idempotent. -/
theorem anticolorProject_idempotent (Z : ZornMatrix R) :
    anticolorProject (anticolorProject Z) = anticolorProject Z := by
  rw [anticolorProject_apply, anticolorProject_apply]

/-- The four Peirce components reconstruct the Zorn cell. -/
theorem zorn_peirce_decomposition (Z : ZornMatrix R) :
    Z = peirceComponent zornPlus zornPlus Z + colorProject Z +
      anticolorProject Z + peirceComponent zornMinus zornMinus Z := by
  cases Z
  ext i <;>
    simp [peirce_plus_plus_apply, colorProject_apply, anticolorProject_apply,
      peirce_minus_minus_apply]

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
