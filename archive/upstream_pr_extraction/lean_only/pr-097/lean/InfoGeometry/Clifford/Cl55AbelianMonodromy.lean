import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Clifford.AbelianMonodromy

variable {n : ℕ}
abbrev AlgMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

structure RealifiedComplexStructure (n : ℕ) where
  B : AlgMat n
  sq_neg_one : B * B = -1

def rotor (cs : RealifiedComplexStructure n) (theta : ℝ) : AlgMat n :=
  Real.cos theta • 1 + Real.sin theta • cs.B

theorem rotor_add (cs : RealifiedComplexStructure n) (a b : ℝ) :
    rotor cs (a + b) = rotor cs a * rotor cs b := by
  unfold rotor
  rw [Real.cos_add, Real.sin_add]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_mul, mul_one, smul_smul, cs.sq_neg_one, smul_neg]
  module

def discreteRotor (cs : RealifiedComplexStructure n) (theta : ℝ) (m : ℤ) : AlgMat n :=
  rotor cs ((m : ℝ) * theta)

theorem discreteRotor_add (cs : RealifiedComplexStructure n) (theta : ℝ) (m k : ℤ) :
    discreteRotor cs theta (m + k) =
      discreteRotor cs theta m * discreteRotor cs theta k := by
  unfold discreteRotor
  rw [Int.cast_add, add_mul, rotor_add]

variable {Pi1 : Type*} [Group Pi1]

structure WindingMap where
  w : Pi1 → ℤ
  map_mul : ∀ a b, w (a * b) = w a + w b

def monodromyRep (cs : RealifiedComplexStructure n) (theta : ℝ)
    (wm : WindingMap (Pi1 := Pi1)) (g : Pi1) : AlgMat n :=
  discreteRotor cs theta (wm.w g)

theorem monodromyRep_mul (cs : RealifiedComplexStructure n) (theta : ℝ)
    (wm : WindingMap (Pi1 := Pi1)) (a b : Pi1) :
    monodromyRep cs theta wm (a * b) =
      monodromyRep cs theta wm a * monodromyRep cs theta wm b := by
  unfold monodromyRep
  rw [wm.map_mul, discreteRotor_add]

end InfoGeometry.Clifford.AbelianMonodromy
