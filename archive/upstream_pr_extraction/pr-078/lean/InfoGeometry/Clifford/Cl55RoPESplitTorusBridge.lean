import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Hyperbolic.Basic
import InfoGeometry.Clifford.Cl55EllipticRotors
import InfoGeometry.Clifford.Cl55OperatorZ2Grading

/-!
# Elliptic RoPE and split-hyperbolic rotor identities in `Cl(5,5)`

This owner formalizes the exact common algebraic mechanism behind planar
rotary position encodings and their split/hyperbolic analogue.  It does not
claim that any neural architecture was designed from Clifford theory.

The existing native axes satisfy

* `ellipticAxis55 i ^ 2 = -1`,
* `hyperbolicAxis55 i ^ 2 = +1`.

Consequently the trigonometric and hyperbolic normal forms obey the expected
one-parameter subgroup laws.  A genuine square-minus-one bivector is also
constructed as the product of two distinct hyperbolic axes.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

/-- Local elliptic rotary packet `cos θ + B sin θ`, with `B² = -1`. -/
def ropeRotor55 (i : Fin 5) (theta : ℝ) : Cl55 :=
  ellipticRotor55 i (Real.cos theta) (Real.sin theta)

@[simp] theorem ropeRotor55_zero (i : Fin 5) :
    ropeRotor55 i 0 = (1 : Cl55) := by
  simp [ropeRotor55, ellipticRotor55]

/-- Exact angle-addition law for the native elliptic Clifford rotor. -/
theorem ropeRotor55_add (i : Fin 5) (a b : ℝ) :
    ropeRotor55 i a * ropeRotor55 i b = ropeRotor55 i (a + b) := by
  rw [ropeRotor55, ropeRotor55, ropeRotor55, ellipticRotor55_mul]
  rw [Real.cos_add, Real.sin_add]

/-- The inverse rotary packet is obtained by negating the angle. -/
theorem ropeRotor55_mul_neg (i : Fin 5) (theta : ℝ) :
    ropeRotor55 i theta * ropeRotor55 i (-theta) = (1 : Cl55) := by
  rw [← ropeRotor55_add]
  simp

/-- Split/hyperbolic packet `cosh t + K sinh t`, with `K² = +1`. -/
def splitRotor55 (i : Fin 5) (t : ℝ) : Cl55 :=
  Real.cosh t • (1 : Cl55) + Real.sinh t • hyperbolicAxis55 i

@[simp] theorem splitRotor55_zero (i : Fin 5) :
    splitRotor55 i 0 = (1 : Cl55) := by
  simp [splitRotor55]

/-- Multiplication law for arbitrary split packets `a + bK`, `K² = 1`. -/
theorem splitPacket55_mul
    (i : Fin 5) (a b c d : ℝ) :
    (a • (1 : Cl55) + b • hyperbolicAxis55 i) *
      (c • (1 : Cl55) + d • hyperbolicAxis55 i) =
    (a * c + b * d) • (1 : Cl55) +
      (a * d + b * c) • hyperbolicAxis55 i := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hyperbolicAxis55_sq]
  module

/-- Exact rapidity-addition law for the split Clifford rotor. -/
theorem splitRotor55_add (i : Fin 5) (s t : ℝ) :
    splitRotor55 i s * splitRotor55 i t = splitRotor55 i (s + t) := by
  rw [splitRotor55, splitRotor55, splitRotor55, splitPacket55_mul]
  rw [Real.cosh_add, Real.sinh_add]

/-- The inverse split packet is obtained by reversing rapidity. -/
theorem splitRotor55_mul_neg (i : Fin 5) (t : ℝ) :
    splitRotor55 i t * splitRotor55 i (-t) = (1 : Cl55) := by
  rw [← splitRotor55_add]
  simp

/-- Genuine Clifford bivector formed from two distinct split axes. -/
def ropeBivector55 (i j : Fin 5) : Cl55 :=
  hyperbolicAxis55 i * hyperbolicAxis55 j

/-- Two distinct square-plus-one orthogonal axes generate a square-minus-one
bivector, the geometric-algebra generator of an elliptic plane rotation. -/
theorem ropeBivector55_sq {i j : Fin 5} (hij : i ≠ j) :
    ropeBivector55 i j * ropeBivector55 i j = -(1 : Cl55) := by
  have hanti := hyperbolicAxis55_anticommute_distinct hij
  have hswap :
      hyperbolicAxis55 j * hyperbolicAxis55 i =
        -(hyperbolicAxis55 i * hyperbolicAxis55 j) := by
    exact eq_neg_of_add_eq_zero_right hanti
  unfold ropeBivector55
  calc
    (hyperbolicAxis55 i * hyperbolicAxis55 j) *
        (hyperbolicAxis55 i * hyperbolicAxis55 j) =
      hyperbolicAxis55 i *
        (hyperbolicAxis55 j * hyperbolicAxis55 i) *
          hyperbolicAxis55 j := by simp only [mul_assoc]
    _ = hyperbolicAxis55 i *
        (-(hyperbolicAxis55 i * hyperbolicAxis55 j)) *
          hyperbolicAxis55 j := by rw [hswap]
    _ = -((hyperbolicAxis55 i * hyperbolicAxis55 i) *
        (hyperbolicAxis55 j * hyperbolicAxis55 j)) := by
      noncomm_ring
    _ = -(1 : Cl55) := by rw [hyperbolicAxis55_sq, hyperbolicAxis55_sq]; simp

/-- Elliptic rotor built from a genuine two-axis Clifford bivector. -/
def bivectorRoPERotor55 (i j : Fin 5) (theta : ℝ) : Cl55 :=
  Real.cos theta • (1 : Cl55) +
    Real.sin theta • ropeBivector55 i j

/-- Generic trigonometric multiplication law for any supplied square-minus-one
bivector.  This is the reusable local RoPE theorem. -/
theorem bivectorRoPERotor55_add
    {i j : Fin 5} (hij : i ≠ j) (a b : ℝ) :
    bivectorRoPERotor55 i j a * bivectorRoPERotor55 i j b =
      bivectorRoPERotor55 i j (a + b) := by
  unfold bivectorRoPERotor55
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, ropeBivector55_sq hij, smul_neg]
  rw [Real.cos_add, Real.sin_add]
  module

/-- The two exact one-parameter laws side by side: elliptic angle addition and
split rapidity addition. -/
theorem elliptic_split_rotor_packet
    (i : Fin 5) (a b s t : ℝ) :
    ropeRotor55 i a * ropeRotor55 i b = ropeRotor55 i (a + b) ∧
    splitRotor55 i s * splitRotor55 i t = splitRotor55 i (s + t) := by
  exact ⟨ropeRotor55_add i a b, splitRotor55_add i s t⟩

end

end InfoGeometry.Clifford.Clifford55
