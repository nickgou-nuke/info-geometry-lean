import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# Chiral four-vector readout for the native split-Zorn carrier

This file records only the finite algebraic facts supplied by the existing
real Zorn/Peirce owner.  In particular, the chiral lift is a one-sided Peirce
readout; its Zorn norm is therefore not the Minkowski quadratic form.
-/

namespace InfoGeometry.QuantumPhysics.ParafermionicFourVector

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

noncomputable section

structure FourVector where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace FourVector

def spatial (p : FourVector) : Vec := ![p.x, p.y, p.z]

def minkowskiNorm (p : FourVector) : ℝ :=
  p.t ^ 2 - (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)

def positiveChiral (p : FourVector) : Carrier :=
  p.t • (E11 : Carrier) + upperZorn (spatial p)

def negativeChiral (p : FourVector) : Carrier :=
  p.t • (E22 : Carrier) + lowerZorn (spatial p)

def IsNull (p : FourVector) : Prop := minkowskiNorm p = 0

theorem upperZorn_mul_upperZorn (q r : Vec) :
    upperZorn q * upperZorn r = lowerZorn (Vec3.cross q r) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

theorem lowerZorn_mul_lowerZorn (q r : Vec) :
    lowerZorn q * lowerZorn r = upperZorn (-Vec3.cross q r) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

theorem mixedChiralContraction (i j : Fin 3) :
    (upperZorn (Vec3.basis i) * lowerZorn (Vec3.basis j)).a =
      if i = j then 1 else 0 := by
  rw [upperZorn_mul_lowerZorn]
  fin_cases i <;> fin_cases j <;>
    simp [chiralPairing, Vec3.dot, Vec3.basis, E11, ZornMatrix.smul]

@[simp] theorem upperZorn_sq (q : Vec) :
    upperZorn q * upperZorn q = 0 := by
  rw [upperZorn_mul_upperZorn]
  apply ZornMatrix.ext <;>
    simp [lowerZorn, ZornMatrix.zero, Vec3.cross, mul_comm]

@[simp] theorem lowerZorn_sq (q : Vec) :
    lowerZorn q * lowerZorn q = 0 := by
  rw [lowerZorn_mul_lowerZorn]
  apply ZornMatrix.ext <;>
    simp [upperZorn, ZornMatrix.zero, Vec3.cross, mul_comm]

end FourVector
end
end InfoGeometry.QuantumPhysics.ParafermionicFourVector
