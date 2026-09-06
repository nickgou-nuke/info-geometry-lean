import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# Chiral Zorn four-vector and cubic-saturation layer

This file isolates the kernel-checked algebraic content behind the proposed
"four-vectors as parafermions" interpretation.

The proved statements are deliberately narrower than Green parafermi statistics:

* the upper chiral spatial sheet multiplies into the lower sheet by the
  three-dimensional cross product;
* three left-associated upper spatial factors collapse to the scalar `E22`
  channel through the scalar triple product;
* four left-associated upper spatial factors vanish;
* every pure upper/lower spatial element is square-zero;
* the naive paravector lift `t • E11 + upperZorn q` is Zorn-null for every
  `t,q`, independently of the Minkowski light-cone equation, and obeys
  `P * P = t • P` rather than generic nilpotence.

Thus cubic saturation is a genuine theorem of the current split-octonion
carrier, while identification with Green order-3 parafermions, QCD color,
fractional Dirac roots, or a light-cone nilpotent carrier requires additional
structures and is not asserted here.
-/

namespace InfoGeometry.QuantumPhysics.ParafermionicFourVector

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

noncomputable section

/-- A real coordinate four-vector. -/
@[ext]
structure FourVector where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace FourVector

/-- Minkowski quadratic form in signature `(+, -, -, -)`. -/
def minkowskiNorm (p : FourVector) : ℝ :=
  p.t ^ 2 - (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)

/-- Spatial part as the repository's native three-vector carrier. -/
def spatial (p : FourVector) : Vec :=
  ![p.x, p.y, p.z]

/-- Positive Peirce/chiral lift into the Zorn carrier. -/
def positiveChiral (p : FourVector) : Carrier :=
  p.t • (E11 : Carrier) + upperZorn p.spatial

/-- Negative Peirce/chiral lift into the Zorn carrier. -/
def negativeChiral (p : FourVector) : Carrier :=
  p.t • (E22 : Carrier) + lowerZorn p.spatial

/-- The usual light-cone predicate for the coordinate four-vector. -/
def IsNull (p : FourVector) : Prop :=
  p.minkowskiNorm = 0

end FourVector

/-! ## Exact chiral-sheet multiplication -/

/-- Two upper spatial elements multiply into the lower sheet by the vector
cross product. -/
theorem upperZorn_mul_upperZorn (q r : Vec) :
    upperZorn q * upperZorn r = lowerZorn (Vec3.cross q r) := by
  apply ZornMatrix.ext
  · simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot]
  · funext i
    fin_cases i <;>
      simp [upperZorn, lowerZorn, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · funext i
    fin_cases i <;>
      simp [upperZorn, lowerZorn, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot]

/-- Two lower spatial elements multiply into the upper sheet with the sign
fixed by the repository's Zorn multiplication convention. -/
theorem lowerZorn_mul_lowerZorn (q r : Vec) :
    lowerZorn q * lowerZorn r = upperZorn (-Vec3.cross q r) := by
  apply ZornMatrix.ext
  · simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot]
  · funext i
    fin_cases i <;>
      simp [upperZorn, lowerZorn, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · funext i
    fin_cases i <;>
      simp [upperZorn, lowerZorn, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot]

/-- Pure upper spatial elements are square-zero. -/
@[simp] theorem upperZorn_sq (q : Vec) :
    upperZorn q * upperZorn q = 0 := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, ZornMatrix.mul, Vec3.dot,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero] <;>
    ring

/-- Pure lower spatial elements are square-zero. -/
@[simp] theorem lowerZorn_sq (q : Vec) :
    lowerZorn q * lowerZorn q = 0 := by
  apply ZornMatrix.ext <;>
    simp [lowerZorn, ZornMatrix.mul, Vec3.dot,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero] <;>
    ring

/-- The left-associated product of three upper spatial elements is the scalar
triple product in the `E22` channel. -/
theorem upperZorn_triple_left (q r s : Vec) :
    (upperZorn q * upperZorn r) * upperZorn s =
      chiralPairing s (Vec3.cross q r) • (E22 : Carrier) := by
  rw [upperZorn_mul_upperZorn]
  exact lowerZorn_mul_upperZorn (Vec3.cross q r) s

/-- `E22` annihilates the upper spatial sheet on the left. -/
@[simp] theorem E22_mul_upperZorn (q : Vec) :
    (E22 : Carrier) * upperZorn q = 0 := by
  apply ZornMatrix.ext <;>
    simp [E22, upperZorn, ZornMatrix.mul, Vec3.dot,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero]

/-- Any scalar multiple of `E22` also annihilates the upper spatial sheet. -/
@[simp] theorem smul_E22_mul_upperZorn (a : ℝ) (q : Vec) :
    (a • (E22 : Carrier)) * upperZorn q = 0 := by
  apply ZornMatrix.ext <;>
    simp [E22, upperZorn, ZornMatrix.mul, Vec3.dot,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero,
      ZornMatrix.smul]

/-- Genuine cubic saturation of the left-associated pure upper spatial chain:
four upper factors vanish identically. -/
theorem upperZorn_fourfold_left (q r s t : Vec) :
    ((upperZorn q * upperZorn r) * upperZorn s) * upperZorn t = 0 := by
  rw [upperZorn_triple_left]
  exact smul_E22_mul_upperZorn _ _

/-! ## Audit of the naive four-vector lift -/

/-- The positive Peirce lift is Zorn-null for every coordinate four-vector,
not only for Minkowski-null vectors.  Hence this lift alone does not encode the
Minkowski quadratic form. -/
@[simp] theorem positiveChiral_zornNorm (p : FourVector) :
    ZornMatrix.zornNorm p.positiveChiral = 0 := by
  simp [FourVector.positiveChiral, FourVector.spatial, ZornMatrix.zornNorm,
    upperZorn, E11, Vec3.dot, ZornMatrix.add, ZornMatrix.smul,
    Vec3.add, Vec3.smul]

/-- The positive Peirce lift is quasi-idempotent rather than generically
nilpotent: `P² = p⁰ P`. -/
theorem positiveChiral_sq (p : FourVector) :
    p.positiveChiral * p.positiveChiral = p.t • p.positiveChiral := by
  apply ZornMatrix.ext <;>
    simp [FourVector.positiveChiral, FourVector.spatial,
      upperZorn, E11, ZornMatrix.mul, ZornMatrix.add, ZornMatrix.smul,
      Vec3.dot, Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross] <;>
    ring

/-- The purely spatial specialization of the positive lift is square-zero. -/
theorem positiveChiral_sq_zero_of_time_zero
    (p : FourVector) (ht : p.t = 0) :
    p.positiveChiral * p.positiveChiral = 0 := by
  rw [positiveChiral_sq, ht]
  simp

end
end InfoGeometry.QuantumPhysics.ParafermionicFourVector
