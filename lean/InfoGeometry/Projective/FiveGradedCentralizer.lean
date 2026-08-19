import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.ConformalFiveGradeInversion

/-!
# Finite Möbius phase certificate

This file records a finite noncommutative phase certificate. It does not
construct the native `Cl(5,5)` Pin action, an `O(5,5)` group, a TKK algebra,
or a five-graded Lie closure. Those structures are owned by the native
Clifford modules. The matrix packet below is retained as a small, explicit
`M₂(ℝ)` witness for the square-minus-identity and trace calculations used by
downstream finite readouts.
-/

namespace InfoGeometry.Projective.Closure

open InfoGeometry.Canonical.ConformalFiveGradeInversion

/-- 
A 5-graded affine projective closure interface mapping Zero (`g_{-2}`)
and Infinity (`g_2`) into a unified conformal algebra via the 
Möbius chiral parity operator.
-/
structure FiniteMobiusPhaseData (n : ℕ) where
  /-- The identity of the finite matrix algebra. -/
  I : Matrix (Fin n) (Fin n) ℝ
  /-- A finite Möbius phase matrix. -/
  moebiusParity : Matrix (Fin n) (Fin n) ℝ
  /-- A scalar finite readout attached to the phase matrix. -/
  gromovWittenIndex : ℝ
  
  /-- The finite square-minus-identity certificate. -/
  centralizer_loop : moebiusParity * moebiusParity = -I
  
  /-- The scalar readout is defined by the finite matrix trace. -/
  gw_eq_trace : gromovWittenIndex = Matrix.trace moebiusParity

/-- Compatibility name for downstream finite readouts.

This alias does not promote the finite certificate to a native five-graded
or Pin/O(5,5) closure. -/
abbrev FiveGradedMobiusClosure (n : ℕ) := FiniteMobiusPhaseData n

/-- Finite readout from the explicitly supplied phase certificate.

This theorem is conditional on `closure`; it is not an anomaly-resolution
theorem and does not identify the matrix with a native `O(5,5)` or Pin action.
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
## Concrete 2x2 finite phase witness

The abstract certificate above is a property package. The following finite
instance gives the basic noncommutative matrix generator:

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
## Finite two-pole label readout

The existing label owner records grade inversion abstractly. The following
finite carrier is only its two-pole label readout: coordinate `0` is labelled
`-2`, coordinate `1` is labelled `+2`, and the involution swaps them. No
five-graded Lie algebra is inferred from this two-point carrier.
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

/-- The canonical two-pole model has central ribbon square `-I`. -/
theorem mobiusClosureFromConformalInversion2_centralizer :
    mobiusClosureFromConformalInversion2.moebiusParity *
        mobiusClosureFromConformalInversion2.moebiusParity =
      -mobiusClosureFromConformalInversion2.I := by
  exact mobiusClosureFromConformalInversion2.centralizer_loop

section Complexification

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Define scalar multiplication by ℂ using the almost complex structure S. -/
def complexSMul (S : V →ₗ[ℝ] V) : SMul ℂ V where
  smul z v := (z.re : ℝ) • v + (z.im : ℝ) • S v

theorem complex_one_smul (S : V →ₗ[ℝ] V) (v : V) :
    (complexSMul S).smul 1 v = v := by
  dsimp [complexSMul]
  simp

theorem complex_mul_smul (S : V →ₗ[ℝ] V) (hS : S.comp S = - LinearMap.id) (z1 z2 : ℂ) (v : V) :
    (complexSMul S).smul (z1 * z2) v = (complexSMul S).smul z1 ((complexSMul S).smul z2 v) := by
  dsimp [complexSMul]
  have hS_linear : S ((z2.re : ℝ) • v + (z2.im : ℝ) • S v) = (z2.re : ℝ) • S v + (z2.im : ℝ) • S (S v) := by
    rw [S.map_add, S.map_smul, S.map_smul]
  have hS_sq : S (S v) = -v := by
    have h_comp : S (S v) = (S.comp S) v := rfl
    rw [h_comp, hS]
    simp
  rw [hS_linear, hS_sq]
  simp only [sub_smul, add_smul, smul_add, smul_smul, smul_neg]
  abel

theorem complex_add_smul (S : V →ₗ[ℝ] V) (z1 z2 : ℂ) (v : V) :
    (complexSMul S).smul (z1 + z2) v = (complexSMul S).smul z1 v + (complexSMul S).smul z2 v := by
  dsimp [complexSMul]
  simp only [add_smul]
  abel

theorem complex_smul_add (S : V →ₗ[ℝ] V) (z : ℂ) (v1 v2 : V) :
    (complexSMul S).smul z (v1 + v2) = (complexSMul S).smul z v1 + (complexSMul S).smul z v2 := by
  dsimp [complexSMul]
  rw [S.map_add]
  simp only [smul_add]
  abel

theorem complex_zero_smul (S : V →ₗ[ℝ] V) (v : V) :
    (complexSMul S).smul 0 v = 0 := by
  dsimp [complexSMul]
  simp

theorem complex_smul_zero (S : V →ₗ[ℝ] V) (z : ℂ) :
    (complexSMul S).smul z 0 = 0 := by
  dsimp [complexSMul]
  rw [S.map_zero]
  simp

/-- The complex module structure induced by the almost complex structure S. -/
def complexModule (S : V →ₗ[ℝ] V) (hS : S.comp S = - LinearMap.id) : Module ℂ V where
  smul := (complexSMul S).smul
  one_smul := complex_one_smul S
  mul_smul := complex_mul_smul S hS
  smul_add := complex_smul_add S
  smul_zero := complex_smul_zero S
  add_smul := complex_add_smul S
  zero_smul := complex_zero_smul S

end Complexification

end InfoGeometry.Projective.Closure
