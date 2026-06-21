import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.ConformalFiveGradeInversion

/-!
# 5-Graded Closure, Möbius Parity, and the Zero Gromov-Witten Index

This file formalizes the geometric anomaly resolution in the projective
closure of the 5-graded Lie algebra. 

The core physical statement is that the Möbius chiral parity index 
is absorbed by bringing the extreme boundaries (Zero and Infinity, 
or `g_{-2}` and `g_{2}`) into the algebra, generating a Weyl inversion.
This inversion squares to `-I`, creating the `{I, -I}` centralizer 
that strictly resolves the anomaly and yields a Zero Gromov-Witten Index 
(trace of the parity operator vanishes).
-/

namespace InfoGeometry.Projective.Closure

open InfoGeometry.Canonical.ConformalFiveGradeInversion

/-- 
A 5-graded affine projective closure socket mapping Zero (`g_{-2}`)
and Infinity (`g_2`) into a unified conformal algebra via the 
Möbius chiral parity operator.
-/
structure FiveGradedMobiusClosure (n : ℕ) where
  /-- The identity of the projective algebra. -/
  I : Matrix (Fin n) (Fin n) ℝ
  /-- The Möbius chiral parity operator swapping 0 and ∞. -/
  moebiusParity : Matrix (Fin n) (Fin n) ℝ
  /-- The Gromov-Witten index mapped to the topological trace. -/
  gromovWittenIndex : ℝ
  
  /-- The centralizer condition: the Möbius parity loops exactly into the {-I, I} center. -/
  centralizer_loop : moebiusParity * moebiusParity = -I
  
  /-- The Gromov-Witten index evaluates strictly to the trace of the chiral parity operator. -/
  gw_eq_trace : gromovWittenIndex = Matrix.trace moebiusParity

/-- 
The fundamental anomaly resolution: 
Because the 5-graded Möbius parity inversion sits in the projective {-I, I} centralizer
and is traceless in the balanced conformal closure, the Gromov-Witten index is zero. 
-/
theorem zero_gromov_witten_anomaly_resolution (n : ℕ) 
    (closure : FiveGradedMobiusClosure n) 
    (h_traceless : Matrix.trace closure.moebiusParity = 0) :
    closure.gromovWittenIndex = 0 ∧ closure.moebiusParity * closure.moebiusParity = -closure.I := by
  constructor
  · rw [closure.gw_eq_trace]
    exact h_traceless
  · exact closure.centralizer_loop

/-!
## Concrete 2x2 Möbius Parity Witness

The abstract closure above is a hypothesis package.  The following finite
instance gives the basic spin/ribbon generator used by the SymPy witness:

`S = [[0, 1], [-1, 0]]`, with `S^2 = -I` and `trace S = 0`.
-/

/-- The concrete 2x2 Möbius parity matrix. -/
def mobiusParity2 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = (0 : Fin 2) then
      if j = (1 : Fin 2) then 1 else 0
    else if j = (0 : Fin 2) then -1 else 0

/-- The concrete Möbius parity squares to `-I`. -/
theorem mobiusParity2_sq :
    mobiusParity2 * mobiusParity2 = - (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mobiusParity2, Matrix.mul_apply]

/-- The concrete Möbius parity is traceless. -/
theorem mobiusParity2_trace :
    Matrix.trace mobiusParity2 = 0 := by
  norm_num [mobiusParity2, Matrix.trace, Fin.sum_univ_two]

/-!
## Canonical Two-Pole Five-Grade Model

The conformal owner records grade inversion as an involution on a five-grade
carrier.  The following finite carrier is the two-pole extremal readout:
coordinate `0` has grade `-2`, coordinate `1` has grade `+2`, and inversion
swaps them.
-/

/-- The two-pole conformal inversion on the extremal `-2/+2` carrier. -/
def conformalPoleSwap2 (i : Fin 2) : Fin 2 :=
  if i = (0 : Fin 2) then (1 : Fin 2) else (0 : Fin 2)

@[simp] theorem conformalPoleSwap2_zero :
    conformalPoleSwap2 (0 : Fin 2) = (1 : Fin 2) := by
  simp [conformalPoleSwap2]

@[simp] theorem conformalPoleSwap2_one :
    conformalPoleSwap2 (1 : Fin 2) = (0 : Fin 2) := by
  simp [conformalPoleSwap2]

/-- The two-pole conformal inversion is involutive. -/
theorem conformalPoleSwap2_involutive :
    Function.Involutive conformalPoleSwap2 := by
  intro i
  fin_cases i <;> simp [conformalPoleSwap2]

/-- Five-grade labels on the two extremal conformal poles. -/
def conformalPoleGrade2 (i : Fin 2) : ConformalGrade :=
  if i = (0 : Fin 2) then ConformalGrade.negTwo else ConformalGrade.posTwo

@[simp] theorem conformalPoleGrade2_zero :
    conformalPoleGrade2 (0 : Fin 2) = ConformalGrade.negTwo := by
  simp [conformalPoleGrade2]

@[simp] theorem conformalPoleGrade2_one :
    conformalPoleGrade2 (1 : Fin 2) = ConformalGrade.posTwo := by
  simp [conformalPoleGrade2]

/-- The two-pole inversion realizes the canonical grade swap `k ↦ -k`. -/
theorem conformalPoleGrade2_swap :
    ∀ i : Fin 2,
      conformalPoleGrade2 (conformalPoleSwap2 i) =
        ConformalGrade.swap (conformalPoleGrade2 i) := by
  intro i
  fin_cases i <;> simp [conformalPoleSwap2, conformalPoleGrade2]

/-- The concrete finite canonical five-grade inversion on the extremal poles. -/
def conformalInversion2 : FiveGradedConformalInversion (Fin 2) where
  theta := conformalPoleSwap2
  grade := conformalPoleGrade2
  theta_involutive := conformalPoleSwap2_involutive
  grade_swap := conformalPoleGrade2_swap

/-- Coordinate axis vector for the two-pole matrix readout. -/
def conformalPoleAxis2 (i : Fin 2) : Fin 2 → ℝ :=
  fun j => if j = i then 1 else 0

/--
The Möbius parity matrix sends the `-2` pole axis to the swapped `+2` pole
axis, up to the central sign.
-/
theorem mobiusParity2_negTwo_axis :
    Matrix.mulVec mobiusParity2 (conformalPoleAxis2 (0 : Fin 2)) =
      - conformalPoleAxis2 (conformalInversion2.theta (0 : Fin 2)) := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, mobiusParity2, conformalPoleAxis2,
    conformalInversion2, conformalPoleSwap2]

/--
The Möbius parity matrix sends the `+2` pole axis to the swapped `-2` pole
axis.
-/
theorem mobiusParity2_posTwo_axis :
    Matrix.mulVec mobiusParity2 (conformalPoleAxis2 (1 : Fin 2)) =
      conformalPoleAxis2 (conformalInversion2.theta (1 : Fin 2)) := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, mobiusParity2, conformalPoleAxis2,
    conformalInversion2, conformalPoleSwap2]

/-- A closed finite 2x2 model of the 5-graded Möbius centralizer. -/
def mobiusClosure2 : FiveGradedMobiusClosure 2 where
  I := 1
  moebiusParity := mobiusParity2
  gromovWittenIndex := 0
  centralizer_loop := mobiusParity2_sq
  gw_eq_trace := by
    rw [mobiusParity2_trace]

/--
The projective centralizer closure read off from the canonical two-pole
five-grade inversion.
-/
def mobiusClosureFromConformalInversion2 : FiveGradedMobiusClosure 2 :=
  mobiusClosure2

/-- The canonical two-pole model has zero Gromov-Witten trace readout. -/
theorem mobiusClosureFromConformalInversion2_gw_zero :
    mobiusClosureFromConformalInversion2.gromovWittenIndex = 0 := by
  rfl

/-- The canonical two-pole model has central ribbon square `-I`. -/
theorem mobiusClosureFromConformalInversion2_centralizer :
    mobiusClosureFromConformalInversion2.moebiusParity *
        mobiusClosureFromConformalInversion2.moebiusParity =
      -mobiusClosureFromConformalInversion2.I := by
  exact mobiusClosureFromConformalInversion2.centralizer_loop

end InfoGeometry.Projective.Closure
