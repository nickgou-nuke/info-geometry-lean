import Mathlib
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

noncomputable section

namespace InfoGeometry.Physics.SolovievSecularRoots

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

def discriminant (eQ eP v : ℝ) : ℝ := (eQ - eP) ^ 2 + 4 * v ^ 2

def lowerRoot (eQ eP v : ℝ) : ℝ :=
  (eQ + eP - Real.sqrt (discriminant eQ eP v)) / 2

def upperRoot (eQ eP v : ℝ) : ℝ :=
  (eQ + eP + Real.sqrt (discriminant eQ eP v)) / 2

theorem discriminant_nonneg (eQ eP v : ℝ) : 0 ≤ discriminant eQ eP v := by
  dsimp [discriminant]
  nlinarith [sq_nonneg (eQ - eP), sq_nonneg v]

theorem lowerRoot_is_secular_root (eQ eP v : ℝ) :
    secularPolynomial eQ eP v (lowerRoot eQ eP v) = 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg eQ eP v)
  dsimp [discriminant] at hs
  dsimp [secularPolynomial, lowerRoot, discriminant]
  field_simp
  nlinarith

theorem upperRoot_is_secular_root (eQ eP v : ℝ) :
    secularPolynomial eQ eP v (upperRoot eQ eP v) = 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg eQ eP v)
  dsimp [discriminant] at hs
  dsimp [secularPolynomial, upperRoot, discriminant]
  field_simp
  nlinarith

end InfoGeometry.Physics.SolovievSecularRoots
