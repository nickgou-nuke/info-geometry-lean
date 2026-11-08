import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2TwoPCPolynomialCertificate

noncomputable section

abbrev F2 := ZMod 2
abbrev P := MvPolynomial (Fin 12) F2

def v (i : Fin 12) : P := MvPolynomial.X i

def e (i : Fin 6) : P := v ⟨i.1, by omega⟩
def f (i : Fin 6) : P := v ⟨6 + i.1, by omega⟩

def g0 : P := e 0 + f 0
def g1 : P := e 1 + f 1
def g2 : P := e 1 * f 0 + e 2 + f 2
def g3 : P := e 1 * f 0 + e 3 + e 4 * f 0 + f 3
def g4 : P := e 4 + f 4
def g5 : P :=
  e 1 * e 2 * f 0 + e 1 * f 0 * f 1 + e 1 * f 0 * f 2 +
    e 1 * f 0 + e 1 * f 1 + e 2 * f 0 + e 2 * f 2 + e 3 * f 1 +
    e 4 * f 0 * f 1 + e 4 * f 1 + e 4 * f 2 + e 5 + f 5

def q0 : P := e 0
def q1 : P := e 1
def q2 : P := e 0 * e 1 + e 2
def q3 : P := e 0 * e 1 + e 0 * e 4 + e 3
def q4 : P := e 4
def q5 : P :=
  e 0 * e 1 * e 2 + e 0 * e 1 + e 0 * e 2 + e 1 * e 3 +
    e 1 * e 4 + e 1 + e 2 * e 4 + e 2 + e 5

theorem g0_formula : g0 = e 0 + f 0 := by rfl
theorem g1_formula : g1 = e 1 + f 1 := by rfl
theorem g2_formula : g2 = e 1 * f 0 + e 2 + f 2 := by rfl
theorem g3_formula : g3 = e 1 * f 0 + e 3 + e 4 * f 0 + f 3 := by rfl
theorem g4_formula : g4 = e 4 + f 4 := by rfl
theorem g5_formula :
    g5 = e 1 * e 2 * f 0 + e 1 * f 0 * f 1 + e 1 * f 0 * f 2 +
      e 1 * f 0 + e 1 * f 1 + e 2 * f 0 + e 2 * f 2 + e 3 * f 1 +
      e 4 * f 0 * f 1 + e 4 * f 1 + e 4 * f 2 + e 5 + f 5 := by rfl

theorem q0_formula : q0 = e 0 := by rfl
theorem q1_formula : q1 = e 1 := by rfl
theorem q2_formula : q2 = e 0 * e 1 + e 2 := by rfl
theorem q3_formula : q3 = e 0 * e 1 + e 0 * e 4 + e 3 := by rfl
theorem q4_formula : q4 = e 4 := by rfl
theorem q5_formula :
    q5 = e 0 * e 1 * e 2 + e 0 * e 1 + e 0 * e 2 + e 1 * e 3 +
      e 1 * e 4 + e 1 + e 2 * e 4 + e 2 + e 5 := by rfl

theorem g5_reordered :
    g5 = e 1 * e 2 * f 0 + e 1 * f 0 * f 1 + e 1 * f 0 * f 2 +
      e 1 * f 0 + e 1 * f 1 + e 2 * f 0 + e 2 * f 2 + e 3 * f 1 +
      e 4 * f 0 * f 1 + e 4 * f 1 + e 4 * f 2 + e 5 + f 5 := by
  rfl

theorem q5_reordered :
    q5 = e 0 * e 1 * e 2 + e 0 * e 1 + e 0 * e 2 + e 1 * e 3 +
      e 1 * e 4 + e 1 + e 2 * e 4 + e 2 + e 5 := by
  rfl

end

end InfoGeometry.Algebra.Zorn.G2TwoPCPolynomialCertificate
