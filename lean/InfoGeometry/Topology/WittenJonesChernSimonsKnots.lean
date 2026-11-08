/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 148: Witten-Jones Polynomials, Chern-Simons TQFT, and Topological Cosmological Constant
Target: `InfoGeometry/Topology/WittenJonesChernSimonsKnots.lean`
Ref: `QMS-DIR-SEC148-WITTEN-JONES-KNOTS-2026-OCT-16`

Formalizes:
1. Pure data structure `ChernSimonsPhase R` with Kauffman bracket phase parameters `A` and `A_inv`.
2. Skein resolution `skeinCrossResolution`, unknot loop value `unknotVacuumLoop`, and
   topological cosmological constant `topologicalCosmoConstant CS = CS.A^2 + CS.A_inv^2 - 2`.
3. Theorem 1: Under `h_inv : CS.A * CS.A_inv = 1`, `(CS.A - CS.A_inv)^2 = topologicalCosmoConstant CS`.
4. Theorem 2: `unknotVacuumLoop CS = - topologicalCosmoConstant CS - 2`.
5. 8D Split-Octonion Kauffman skein braiding rotor theorems:
   - `octonion_skein_difference_eq_framing_anomaly`
   - `octonion_skein_trace_eq_phase_sum`
   - `octonion_cosmo_constant_from_skein_trace`.
6. Explicit $3 \times 3$ noncommutative matrix carrier `Mat3 R`, Temperley-Lieb generators
   `tlGenE1` and `tlGenE2`, quadratic and Jones cubic relations (`tlGenE1_sq`, `tlGenE2_sq`,
   `tlGen_jones_cubic_121`, `tlGen_jones_cubic_212`), and Kauffman braid operators
   `kauffmanBraidR1`, `kauffmanBraidR1Inv`, `kauffmanBraidR2`, `kauffmanBraidR2Inv` satisfying
   inversion (`kauffmanBraidR1_mul_inv`), the Kauffman skein relation (`kauffmanBraidR1_skein_relation`),
   and the Yang-Baxter braid equation (`kauffmanBraid_yang_baxter_121_eq_212`).
-/

namespace InfoGeometry.Topology.WittenJonesKnots

/-! ### 1. 3D Color Vector and 8D Split-Octonion Braiding Carriers -/

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

def trace (X : SplitOctonion R) : R :=
  X.a + X.b

def quark (u : ColorVec3 R) : SplitOctonion R := ⟨0, u, ColorVec3.zero, 0⟩
def antiquark (v : ColorVec3 R) : SplitOctonion R := ⟨0, ColorVec3.zero, v, 0⟩

/-- Forward chiral twistor projector `P₊(u) = e₁ + U(u) = ⟨1, u, 0, 0⟩`. -/
def twistorProjPlus (u : ColorVec3 R) : SplitOctonion R :=
  ⟨1, u, ColorVec3.zero, 0⟩

/-- Backward chiral twistor projector `P₋(v) = e₂ + V(v) = ⟨0, 0, v, 1⟩`. -/
def twistorProjMinus (v : ColorVec3 R) : SplitOctonion R :=
  ⟨0, ColorVec3.zero, v, 1⟩

end SplitOctonion

/-! ### 2. Chern-Simons Topological Phase Carrier (Kauffman Bracket Algebra) -/

/--
Pure data structure encoding the Kauffman bracket phase `A` and its formal inverse `A_inv`.
-/
@[ext]
structure ChernSimonsPhase (R : Type*) where
  A : R
  A_inv : R
  deriving DecidableEq, Repr, Inhabited

variable {R : Type*} [CommRing R]

/--
Kauffman skein crossing resolution `⟨L₊⟩ = A ⟨L₀⟩ + A⁻¹ ⟨L_∞⟩`.
-/
def skeinCrossResolution (CS : ChernSimonsPhase R) (L_zero L_inf : R) : R :=
  CS.A * L_zero + CS.A_inv * L_inf

/--
Unknot vacuum loop expectation value `d = - A² - A⁻²`.
-/
def unknotVacuumLoop (CS : ChernSimonsPhase R) : R :=
  - (CS.A^2) - (CS.A_inv^2)

/--
Effective topological cosmological constant `Λ_eff = A² + A⁻² - 2`.
-/
def topologicalCosmoConstant (CS : ChernSimonsPhase R) : R :=
  CS.A^2 + CS.A_inv^2 - 2

/-! ### 3. Scalar Kauffman Bracket Cosmological Constant Theorems -/

/--
Cosmological constant as knot framing anomaly:
Under `h_inv : CS.A * CS.A_inv = 1`, the squared chiral phase difference `(CS.A - CS.A_inv)^2`
equals `topologicalCosmoConstant CS`.
-/
theorem witten_cosmological_constant_is_knot_anomaly (CS : ChernSimonsPhase R)
    (h_inv : CS.A * CS.A_inv = 1) :
    (CS.A - CS.A_inv)^2 = topologicalCosmoConstant CS := by
  dsimp [topologicalCosmoConstant]
  calc (CS.A - CS.A_inv)^2
    _ = CS.A^2 + CS.A_inv^2 - 2 * (CS.A * CS.A_inv) := by ring
    _ = CS.A^2 + CS.A_inv^2 - 2 * 1 := by rw [h_inv]
    _ = CS.A^2 + CS.A_inv^2 - 2 := by ring

/--
Unknot vacuum loop and cosmological constant:
The unknot vacuum loop value satisfies `unknotVacuumLoop CS = - topologicalCosmoConstant CS - 2`.
-/
theorem unknot_vacuum_is_negative_cosmo_energy (CS : ChernSimonsPhase R) :
    unknotVacuumLoop CS = - topologicalCosmoConstant CS - 2 := by
  dsimp [unknotVacuumLoop, topologicalCosmoConstant]
  ring

/-! ### 4. 8D Split-Octonion Kauffman Skein Braiding Rotor Theorems -/

/--
8D Split-Octonion forward skein braiding operator:
`R₊(u, v) = A • P₊(u) + A⁻¹ • P₋(v)`.
-/
def octonionSkeinBraiding (CS : ChernSimonsPhase R) (u v : ColorVec3 R) : SplitOctonion R :=
  SplitOctonion.add (SplitOctonion.scale CS.A (SplitOctonion.twistorProjPlus u))
                    (SplitOctonion.scale CS.A_inv (SplitOctonion.twistorProjMinus v))

/--
8D Split-Octonion inverse skein braiding operator:
`R₋(u, v) = A⁻¹ • P₊(u) + A • P₋(v)`.
-/
def octonionSkeinInverse (CS : ChernSimonsPhase R) (u v : ColorVec3 R) : SplitOctonion R :=
  SplitOctonion.add (SplitOctonion.scale CS.A_inv (SplitOctonion.twistorProjPlus u))
                    (SplitOctonion.scale CS.A (SplitOctonion.twistorProjMinus v))

/--
Octonion skein difference equals framing anomaly:
The difference between the forward and inverse 8D skein braiding rotors equals
`(A - A⁻¹) • (K₀ + U(u) - V(v))`.
-/
theorem octonion_skein_difference_eq_framing_anomaly (CS : ChernSimonsPhase R) (u v : ColorVec3 R) :
    SplitOctonion.sub (octonionSkeinBraiding CS u v) (octonionSkeinInverse CS u v) =
      SplitOctonion.scale (CS.A - CS.A_inv)
        (SplitOctonion.add (SplitOctonion.paraSymplecticK0)
                           (SplitOctonion.sub (SplitOctonion.quark u) (SplitOctonion.antiquark v))) := by
  dsimp [octonionSkeinBraiding, octonionSkeinInverse, SplitOctonion.sub, SplitOctonion.add,
         SplitOctonion.scale, SplitOctonion.twistorProjPlus, SplitOctonion.twistorProjMinus,
         SplitOctonion.paraSymplecticK0, SplitOctonion.quark, SplitOctonion.antiquark,
         ColorVec3.zero, ColorVec3.add, ColorVec3.sub, ColorVec3.smul]
  ext <;> ring

/--
Octonion skein trace equals chiral phase sum:
The split-octonion trace of `octonionSkeinBraiding CS u v` equals `CS.A + CS.A_inv`.
-/
theorem octonion_skein_trace_eq_phase_sum (CS : ChernSimonsPhase R) (u v : ColorVec3 R) :
    SplitOctonion.trace (octonionSkeinBraiding CS u v) = CS.A + CS.A_inv := by
  dsimp [octonionSkeinBraiding, SplitOctonion.trace, SplitOctonion.add,
         SplitOctonion.scale, SplitOctonion.twistorProjPlus, SplitOctonion.twistorProjMinus]
  ring

/--
Cosmological constant from 8D octonion skein trace:
Under `h_inv : CS.A * CS.A_inv = 1`, the squared trace of the 8D skein braiding operator
minus `4` recovers `topologicalCosmoConstant CS`.
-/
theorem octonion_cosmo_constant_from_skein_trace (CS : ChernSimonsPhase R) (u v : ColorVec3 R)
    (h_inv : CS.A * CS.A_inv = 1) :
    (SplitOctonion.trace (octonionSkeinBraiding CS u v))^2 - 4 = topologicalCosmoConstant CS := by
  rw [octonion_skein_trace_eq_phase_sum]
  dsimp [topologicalCosmoConstant]
  calc (CS.A + CS.A_inv)^2 - 4
    _ = CS.A^2 + CS.A_inv^2 + 2 * (CS.A * CS.A_inv) - 4 := by ring
    _ = CS.A^2 + CS.A_inv^2 + 2 * 1 - 4 := by rw [h_inv]
    _ = CS.A^2 + CS.A_inv^2 - 2 := by ring

/-! ### 4b. 3x3 Noncommutative Matrix Carrier, Temperley-Lieb Algebra, and Kauffman Braid Group -/

/--
Explicit $3 \times 3$ matrix carrier over `R` for noncommutative Temperley-Lieb and
Kauffman-Jones braid representations.
-/
@[ext]
structure Mat3 (R : Type*) where
  m00 : R
  m01 : R
  m02 : R
  m10 : R
  m11 : R
  m12 : R
  m20 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace Mat3

variable {R : Type*} [CommRing R]

def zero : Mat3 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def one  : Mat3 R := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

def add (X Y : Mat3 R) : Mat3 R where
  m00 := X.m00 + Y.m00
  m01 := X.m01 + Y.m01
  m02 := X.m02 + Y.m02
  m10 := X.m10 + Y.m10
  m11 := X.m11 + Y.m11
  m12 := X.m12 + Y.m12
  m20 := X.m20 + Y.m20
  m21 := X.m21 + Y.m21
  m22 := X.m22 + Y.m22

def sub (X Y : Mat3 R) : Mat3 R where
  m00 := X.m00 - Y.m00
  m01 := X.m01 - Y.m01
  m02 := X.m02 - Y.m02
  m10 := X.m10 - Y.m10
  m11 := X.m11 - Y.m11
  m12 := X.m12 - Y.m12
  m20 := X.m20 - Y.m20
  m21 := X.m21 - Y.m21
  m22 := X.m22 - Y.m22

def smul (k : R) (X : Mat3 R) : Mat3 R where
  m00 := k * X.m00
  m01 := k * X.m01
  m02 := k * X.m02
  m10 := k * X.m10
  m11 := k * X.m11
  m12 := k * X.m12
  m20 := k * X.m20
  m21 := k * X.m21
  m22 := k * X.m22

def mul (X Y : Mat3 R) : Mat3 R where
  m00 := X.m00 * Y.m00 + X.m01 * Y.m10 + X.m02 * Y.m20
  m01 := X.m00 * Y.m01 + X.m01 * Y.m11 + X.m02 * Y.m21
  m02 := X.m00 * Y.m02 + X.m01 * Y.m12 + X.m02 * Y.m22
  m10 := X.m10 * Y.m00 + X.m11 * Y.m10 + X.m12 * Y.m20
  m11 := X.m10 * Y.m01 + X.m11 * Y.m11 + X.m12 * Y.m21
  m12 := X.m10 * Y.m02 + X.m11 * Y.m12 + X.m12 * Y.m22
  m20 := X.m20 * Y.m00 + X.m21 * Y.m10 + X.m22 * Y.m20
  m21 := X.m20 * Y.m01 + X.m21 * Y.m11 + X.m22 * Y.m21
  m22 := X.m20 * Y.m02 + X.m21 * Y.m12 + X.m22 * Y.m22

end Mat3

/-- Top-left $2 \times 2$ block embedding into `Mat3 R`. -/
def tlBlockE1 (a b c d : R) : Mat3 R :=
  ⟨a, b, 0, c, d, 0, 0, 0, 0⟩

/-- Bottom-right $2 \times 2$ block embedding into `Mat3 R`. -/
def tlBlockE2 (a b c d : R) : Mat3 R :=
  ⟨0, 0, 0, 0, d, b, 0, c, a⟩

/--
First noncommutative Temperley-Lieb generator $E_1(d)$ in `Mat3 R` with loop parameter $d$.
-/
def tlGenE1 (d : R) : Mat3 R :=
  ⟨d, 1, 0, 0, 0, 0, 0, 0, 0⟩

/--
Second noncommutative Temperley-Lieb generator $E_2(d)$ in `Mat3 R` with loop parameter $d$.
-/
def tlGenE2 (d : R) : Mat3 R :=
  ⟨0, 0, 0, 1, d, 0, 0, 0, 0⟩

/-- Temperley-Lieb quadratic loop relation for $E_1(d)$: $E_1(d)^2 = d \cdot E_1(d)$. -/
theorem tlGenE1_sq (d : R) :
    Mat3.mul (tlGenE1 d) (tlGenE1 d) = Mat3.smul d (tlGenE1 d) := by
  dsimp [tlGenE1, Mat3.mul, Mat3.smul]
  ext <;> ring

/-- Temperley-Lieb quadratic loop relation for $E_2(d)$: $E_2(d)^2 = d \cdot E_2(d)$. -/
theorem tlGenE2_sq (d : R) :
    Mat3.mul (tlGenE2 d) (tlGenE2 d) = Mat3.smul d (tlGenE2 d) := by
  dsimp [tlGenE2, Mat3.mul, Mat3.smul]
  ext <;> ring

/-- First Jones cubic Temperley-Lieb relation: $E_1(d) E_2(d) E_1(d) = E_1(d)$. -/
theorem tlGen_jones_cubic_121 (d : R) :
    Mat3.mul (Mat3.mul (tlGenE1 d) (tlGenE2 d)) (tlGenE1 d) = tlGenE1 d := by
  dsimp [tlGenE1, tlGenE2, Mat3.mul]
  ext <;> ring

/-- Second Jones cubic Temperley-Lieb relation: $E_2(d) E_1(d) E_2(d) = E_2(d)$. -/
theorem tlGen_jones_cubic_212 (d : R) :
    Mat3.mul (Mat3.mul (tlGenE2 d) (tlGenE1 d)) (tlGenE2 d) = tlGenE2 d := by
  dsimp [tlGenE1, tlGenE2, Mat3.mul]
  ext <;> ring

/--
Forward Kauffman braid generator $R_1 = A \cdot I + A^{-1} E_1(d)$ on strands $(1, 2)$,
where $d = -A^2 - A^{-2}$ is the unknot vacuum loop value.
-/
def kauffmanBraidR1 (CS : ChernSimonsPhase R) : Mat3 R :=
  Mat3.add (Mat3.smul CS.A Mat3.one) (Mat3.smul CS.A_inv (tlGenE1 (unknotVacuumLoop CS)))

/--
Inverse Kauffman braid generator $R_1^{-1} = A^{-1} \cdot I + A E_1(d)$ on strands $(1, 2)$.
-/
def kauffmanBraidR1Inv (CS : ChernSimonsPhase R) : Mat3 R :=
  Mat3.add (Mat3.smul CS.A_inv Mat3.one) (Mat3.smul CS.A (tlGenE1 (unknotVacuumLoop CS)))

/--
Forward Kauffman braid generator $R_2 = A \cdot I + A^{-1} E_2(d)$ on strands $(2, 3)$.
-/
def kauffmanBraidR2 (CS : ChernSimonsPhase R) : Mat3 R :=
  Mat3.add (Mat3.smul CS.A Mat3.one) (Mat3.smul CS.A_inv (tlGenE2 (unknotVacuumLoop CS)))

/--
Inverse Kauffman braid generator $R_2^{-1} = A^{-1} \cdot I + A E_2(d)$ on strands $(2, 3)$.
-/
def kauffmanBraidR2Inv (CS : ChernSimonsPhase R) : Mat3 R :=
  Mat3.add (Mat3.smul CS.A_inv Mat3.one) (Mat3.smul CS.A (tlGenE2 (unknotVacuumLoop CS)))

/--
Kauffman Braid Inversion Theorem (Reidemeister II Move):
Under `h_inv : CS.A * CS.A_inv = 1`, the braid generator `kauffmanBraidR1 CS` and its formal
inverse `kauffmanBraidR1Inv CS` multiply to the identity matrix `Mat3.one`.
-/
theorem kauffmanBraidR1_mul_inv (CS : ChernSimonsPhase R) (h_inv : CS.A * CS.A_inv = 1) :
    Mat3.mul (kauffmanBraidR1 CS) (kauffmanBraidR1Inv CS) = Mat3.one := by
  dsimp [kauffmanBraidR1, kauffmanBraidR1Inv, tlGenE1, unknotVacuumLoop,
         Mat3.mul, Mat3.add, Mat3.smul, Mat3.one]
  ext
  · linear_combination (1 + (-CS.A ^ 2 - CS.A_inv ^ 2) ^ 2) * h_inv
  · linear_combination (-CS.A ^ 2 - CS.A_inv ^ 2) * h_inv
  · ring
  · ring
  · linear_combination h_inv
  · ring
  · ring
  · ring
  · linear_combination h_inv

/--
Kauffman Skein Relation in `Mat3 R`:
The difference between the positive and negative braid generators satisfies
$R_1 - R_1^{-1} = (A - A^{-1})(I - E_1(d))$.
-/
theorem kauffmanBraidR1_skein_relation (CS : ChernSimonsPhase R) :
    Mat3.sub (kauffmanBraidR1 CS) (kauffmanBraidR1Inv CS) =
      Mat3.smul (CS.A - CS.A_inv) (Mat3.sub Mat3.one (tlGenE1 (unknotVacuumLoop CS))) := by
  dsimp [kauffmanBraidR1, kauffmanBraidR1Inv, tlGenE1, unknotVacuumLoop,
         Mat3.sub, Mat3.add, Mat3.smul, Mat3.one]
  ext <;> ring

/--
Exact Yang-Baxter Braid Equation (Reidemeister III Move) for Kauffman Bracket Operators:
Under `h_inv : CS.A * CS.A_inv = 1`, the Kauffman braid generators satisfy the noncommutative
Artin braid group relation $R_1 R_2 R_1 = R_2 R_1 R_2$ in `Mat3 R`.
-/
theorem kauffmanBraid_yang_baxter_121_eq_212
    (CS : ChernSimonsPhase R) (h_inv : CS.A * CS.A_inv = 1) :
    Mat3.mul (Mat3.mul (kauffmanBraidR1 CS) (kauffmanBraidR2 CS)) (kauffmanBraidR1 CS) =
      Mat3.mul (Mat3.mul (kauffmanBraidR2 CS) (kauffmanBraidR1 CS)) (kauffmanBraidR2 CS) := by
  dsimp [kauffmanBraidR1, kauffmanBraidR2, tlGenE1, tlGenE2, unknotVacuumLoop,
         Mat3.mul, Mat3.add, Mat3.smul, Mat3.one]
  ext
  · linear_combination (CS.A_inv * (CS.A ^ 2 + CS.A_inv ^ 2) ^ 2) * h_inv
  · linear_combination (-CS.A_inv * (CS.A ^ 2 + CS.A_inv ^ 2)) * h_inv
  · ring
  · linear_combination (CS.A_inv * (CS.A ^ 2 + CS.A_inv ^ 2)) * h_inv
  · linear_combination (-CS.A_inv * (CS.A ^ 2 + CS.A_inv ^ 2) ^ 2) * h_inv
  · ring
  · ring
  · ring
  · ring

/-! ### 5. Concrete Integer Instantiations and Non-Commutativity -/

def canonicalMat3Int : Mat3 ℤ := tlGenE1 (-2)

theorem canonicalMat3Int_nondegenerate :
    canonicalMat3Int ≠ default := by decide

theorem mat3_mul_noncommutative :
    ∃ A B : Mat3 ℤ, Mat3.mul A B ≠ Mat3.mul B A :=
  ⟨tlGenE1 (-2), tlGenE2 (-2), by decide⟩

def canonicalColorVec3Int : ColorVec3 ℤ := ⟨1, -1, 2⟩

theorem canonicalColorVec3Int_nondegenerate :
    canonicalColorVec3Int ≠ default := by decide

theorem colorVec3_cross_noncommutative :
    ∃ u v : ColorVec3 ℤ, ColorVec3.cross u v ≠ ColorVec3.cross v u :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by decide⟩

def canonicalChernSimonsPhaseInt : ChernSimonsPhase ℤ := ⟨-1, -1⟩

theorem canonicalChernSimonsPhaseInt_nondegenerate :
    canonicalChernSimonsPhaseInt ≠ default := by decide

def canonicalSplitOctonionInt : SplitOctonion ℤ :=
  octonionSkeinBraiding canonicalChernSimonsPhaseInt ⟨1, 0, 0⟩ ⟨0, 1, 0⟩

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

/-! ### 6. Master Synthesis of Section 148 -/

theorem witten_jones_cosmology_synthesis
    (CS : ChernSimonsPhase R) (u v : ColorVec3 R) (h_inv : CS.A * CS.A_inv = 1) :
    (CS.A - CS.A_inv)^2 = topologicalCosmoConstant CS ∧
    unknotVacuumLoop CS = - topologicalCosmoConstant CS - 2 ∧
    SplitOctonion.sub (octonionSkeinBraiding CS u v) (octonionSkeinInverse CS u v) =
      SplitOctonion.scale (CS.A - CS.A_inv)
        (SplitOctonion.add (SplitOctonion.paraSymplecticK0)
                           (SplitOctonion.sub (SplitOctonion.quark u) (SplitOctonion.antiquark v))) ∧
    SplitOctonion.trace (octonionSkeinBraiding CS u v) = CS.A + CS.A_inv ∧
    (SplitOctonion.trace (octonionSkeinBraiding CS u v))^2 - 4 = topologicalCosmoConstant CS :=
  ⟨witten_cosmological_constant_is_knot_anomaly CS h_inv,
   unknot_vacuum_is_negative_cosmo_energy CS,
   octonion_skein_difference_eq_framing_anomaly CS u v,
   octonion_skein_trace_eq_phase_sum CS u v,
   octonion_cosmo_constant_from_skein_trace CS u v h_inv⟩

end InfoGeometry.Topology.WittenJonesKnots
