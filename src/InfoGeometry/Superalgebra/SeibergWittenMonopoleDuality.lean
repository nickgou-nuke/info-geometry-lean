/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 146: Seiberg-Witten Electromagnetic Duality, BPS Charge, and Monopole Condensation
Target: `InfoGeometry/Superalgebra/SeibergWittenMonopoleDuality.lean`
Ref: `QMS-DIR-SEC146-SEIBERG-WITTEN-DUALITY-2026-OCT-16`

Formalizes:
1. The negation operator `neg` in `SplitOctonion R` and CPT time inversion `J paraSymplecticK0 = neg paraSymplecticK0`.
2. Theorem 1 (Seiberg-Witten electromagnetic duality):
   The Tomita modular conjugation `J` maps an electric quark `quark u` into a magnetic monopole
   `neg (antiquark u)` and an antiquark `antiquark v` into `neg (quark v)`.
3. The Seiberg-Witten central charge `seibergWittenBpsCharge q g = add (scale q one) (scale g paraSymplecticK0)`.
4. Theorem 2 (BPS mass formula): `intervalNorm (seibergWittenBpsCharge q g) = q^2 - g^2`.
5. Theorem 3 (Monopole condensation threshold):
   On the null BPS cone `intervalNorm (seibergWittenBpsCharge q g) = 0`, electric and magnetic
   charges balance (`q^2 = g^2`).
-/

namespace InfoGeometry.Superalgebra.SeibergWitten

/-! ### 1. 3D Color Vector Carrier -/

@[ext]
structure ColorVec3 (R : Type*) where
  c1 : R
  c2 : R
  c3 : R
  deriving DecidableEq, Repr, Inhabited

namespace ColorVec3

variable {R : Type*} [CommRing R]

def zero : ColorVec3 R := ⟨0, 0, 0⟩
def add (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 + v.c1, u.c2 + v.c2, u.c3 + v.c3⟩
def sub (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 - v.c1, u.c2 - v.c2, u.c3 - v.c3⟩
def smul (k : R) (u : ColorVec3 R) : ColorVec3 R := ⟨k * u.c1, k * u.c2, k * u.c3⟩
def neg (u : ColorVec3 R) : ColorVec3 R := ⟨-u.c1, -u.c2, -u.c3⟩

def dot (u v : ColorVec3 R) : R :=
  u.c1 * v.c1 + u.c2 * v.c2 + u.c3 * v.c3

def cross (u v : ColorVec3 R) : ColorVec3 R where
  c1 := u.c2 * v.c3 - u.c3 * v.c2
  c2 := u.c3 * v.c1 - u.c1 * v.c3
  c3 := u.c1 * v.c2 - u.c2 * v.c1

end ColorVec3

/-! ### 2. 8D Split-Octonion Algebra and CPT Modular Conjugation -/

@[ext]
structure SplitOctonion (R : Type*) where
  a : R
  u : ColorVec3 R
  v : ColorVec3 R
  b : R
  deriving DecidableEq, Repr, Inhabited

namespace SplitOctonion

variable {R : Type*} [CommRing R]

def zero : SplitOctonion R := ⟨0, ColorVec3.zero, ColorVec3.zero, 0⟩
def one  : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, 1⟩
def paraSymplecticK0 : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, -1⟩

/-- Componentwise negation in `SplitOctonion R`. -/
def neg (X : SplitOctonion R) : SplitOctonion R :=
  ⟨-X.a, ColorVec3.neg X.u, ColorVec3.neg X.v, -X.b⟩

def scale (k : R) (X : SplitOctonion R) : SplitOctonion R :=
  ⟨k * X.a, ColorVec3.smul k X.u, ColorVec3.smul k X.v, k * X.b⟩

def add (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a + Y.a, ColorVec3.add X.u Y.u, ColorVec3.add X.v Y.v, X.b + Y.b⟩

def sub (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a - Y.a, ColorVec3.sub X.u Y.u, ColorVec3.sub X.v Y.v, X.b - Y.b⟩

def mul (X Y : SplitOctonion R) : SplitOctonion R where
  a := X.a * Y.a + ColorVec3.dot X.u Y.v
  u := ColorVec3.sub (ColorVec3.add (ColorVec3.smul X.a Y.u) (ColorVec3.smul Y.b X.u))
                     (ColorVec3.cross X.v Y.v)
  v := ColorVec3.add (ColorVec3.add (ColorVec3.smul Y.a X.v) (ColorVec3.smul X.b Y.v))
                     (ColorVec3.cross X.u Y.u)
  b := X.b * Y.b + ColorVec3.dot X.v Y.u

def intervalNorm (X : SplitOctonion R) : R :=
  X.a * X.b - ColorVec3.dot X.u X.v

def quark (u : ColorVec3 R) : SplitOctonion R := ⟨0, u, ColorVec3.zero, 0⟩
def antiquark (v : ColorVec3 R) : SplitOctonion R := ⟨0, ColorVec3.zero, v, 0⟩

/-- Electromagnetic duality conjugation `J(a, u, v, b) = (b, -v, -u, a)`. -/
def J (X : SplitOctonion R) : SplitOctonion R :=
  ⟨X.b, ColorVec3.neg X.v, ColorVec3.neg X.u, X.a⟩

/-- CPT time inversion: `J paraSymplecticK0 = neg paraSymplecticK0`. -/
theorem cpt_time_inversion_exact :
    J (paraSymplecticK0 (R := R)) = neg paraSymplecticK0 := by
  dsimp [J, paraSymplecticK0, neg, ColorVec3.neg, ColorVec3.zero]
  ext <;> ring

/-! ### 3. Seiberg-Witten Electromagnetic Duality via CPT Conjugation J -/

/--
Electromagnetic duality under modular conjugation:
Modular conjugation `J` exchanges electric quark states `quark u` and magnetic monopole
antiquark states `antiquark v` with a sign inversion:
`J (quark u) = neg (antiquark u)` and `J (antiquark v) = neg (quark v)`.
-/
theorem seiberg_witten_electromagnetic_duality (u v : ColorVec3 R) :
    J (quark u) = neg (antiquark u) ∧
    J (antiquark v) = neg (quark v) := by
  constructor
  · dsimp [J, quark, antiquark, neg, ColorVec3.neg, ColorVec3.zero]
    ext <;> ring
  · dsimp [J, quark, antiquark, neg, ColorVec3.neg, ColorVec3.zero]
    ext <;> ring

/-! ### 4. Seiberg-Witten Central Charge and Monopole Condensation -/

/--
Seiberg-Witten BPS central charge `Z_SW(q, g) = q • 𝟙 + g • K₀`, combining electric
charge `q` and magnetic monopole charge `g`.
-/
def seibergWittenBpsCharge (q g : R) : SplitOctonion R :=
  add (scale q one) (scale g paraSymplecticK0)

/--
BPS mass formula:
The `(4,4)` interval norm of the Seiberg-Witten central charge equals `q^2 - g^2`.
-/
theorem bps_mass_formula_exact (q g : R) :
    intervalNorm (seibergWittenBpsCharge q g) = q^2 - g^2 := by
  dsimp [intervalNorm, seibergWittenBpsCharge, add, scale, one, paraSymplecticK0,
         ColorVec3.zero, ColorVec3.dot, ColorVec3.smul, ColorVec3.add]
  ring

/--
Monopole condensation massless threshold:
When the BPS central charge lies on the null cone (`intervalNorm (seibergWittenBpsCharge q g) = 0`),
the electric and magnetic squared charges coincide (`q^2 = g^2`).
-/
theorem monopole_condensation_massless_threshold (q g : R)
    (h_bps_null : intervalNorm (seibergWittenBpsCharge q g) = 0) :
    q^2 = g^2 := by
  rw [bps_mass_formula_exact] at h_bps_null
  linear_combination h_bps_null

end SplitOctonion

/-! ### 5. Concrete Integer Instantiations and Non-Commutativity -/

def canonicalColorVec3Int : ColorVec3 ℤ := ⟨2, -1, 4⟩

theorem canonicalColorVec3Int_nondegenerate :
    canonicalColorVec3Int ≠ default := by decide

theorem colorVec3_cross_noncommutative :
    ∃ u v : ColorVec3 ℤ, ColorVec3.cross u v ≠ ColorVec3.cross v u :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by decide⟩

def canonicalSplitOctonionInt : SplitOctonion ℤ :=
  SplitOctonion.seibergWittenBpsCharge 5 3

theorem canonicalSplitOctonionInt_nondegenerate :
    canonicalSplitOctonionInt ≠ default := by decide

def octonionBasisU1Int : SplitOctonion ℤ := SplitOctonion.quark ⟨1, 0, 0⟩
def octonionBasisU2Int : SplitOctonion ℤ := SplitOctonion.quark ⟨0, 1, 0⟩

theorem splitOctonion_mul_noncommutative_concrete :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

theorem splitOctonion_mul_noncommutative :
    ∃ A B : SplitOctonion ℤ, SplitOctonion.mul A B ≠ SplitOctonion.mul B A :=
  ⟨octonionBasisU1Int, octonionBasisU2Int, splitOctonion_mul_noncommutative_concrete⟩

/-! ### 6. Master Synthesis of Section 146 -/

theorem seiberg_witten_duality_synthesis {R : Type*} [CommRing R]
    (u v : ColorVec3 R) (q g : R)
    (h_bps_null : SplitOctonion.intervalNorm (SplitOctonion.seibergWittenBpsCharge q g) = 0) :
    SplitOctonion.J (SplitOctonion.paraSymplecticK0 (R := R)) =
      SplitOctonion.neg SplitOctonion.paraSymplecticK0 ∧
    (SplitOctonion.J (SplitOctonion.quark u) = SplitOctonion.neg (SplitOctonion.antiquark u) ∧
     SplitOctonion.J (SplitOctonion.antiquark v) = SplitOctonion.neg (SplitOctonion.quark v)) ∧
    SplitOctonion.intervalNorm (SplitOctonion.seibergWittenBpsCharge q g) = q^2 - g^2 ∧
    q^2 = g^2 :=
  ⟨SplitOctonion.cpt_time_inversion_exact,
   SplitOctonion.seiberg_witten_electromagnetic_duality u v,
   SplitOctonion.bps_mass_formula_exact q g,
   SplitOctonion.monopole_condensation_massless_threshold q g h_bps_null⟩

end InfoGeometry.Superalgebra.SeibergWitten
