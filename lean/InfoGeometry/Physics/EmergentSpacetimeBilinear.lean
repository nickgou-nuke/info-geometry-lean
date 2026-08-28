import Mathlib

/-!
# Matrix-level bilinear readbacks

This file records only definitional matrix constructions.  It does not assert
that the matrices are Clifford generators, nor any physical interpretation.
-/
namespace InfoGeometry.Physics.EmergentSpacetime

abbrev Dim32 := Fin 32
abbrev Cl55Mat := Matrix Dim32 Dim32 ℝ

def kreinEta : Cl55Mat :=
  Matrix.diagonal (fun i => if i.1 < 16 then (1 : ℝ) else -1)

theorem kreinEta_mul_self : kreinEta * kreinEta = 1 := by
  classical
  rw [kreinEta, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply]
    by_cases hi : i.1 < 16 <;> simp [hi]
  · simp [Matrix.diagonal_apply_ne, h]

def diracKreinAdjoint (psi : Cl55Mat) : Cl55Mat :=
  psi.transpose * kreinEta

def kreinAdj (A : Cl55Mat) : Cl55Mat :=
  kreinEta * A.transpose * kreinEta

theorem kreinAdj_mul (A B : Cl55Mat) :
    kreinAdj (A * B) = kreinAdj B * kreinAdj A := by
  dsimp [kreinAdj]
  rw [Matrix.transpose_mul]
  simp only [mul_assoc]
  have h : B.transpose * (kreinEta * (kreinEta * (A.transpose * kreinEta))) =
      B.transpose * (A.transpose * kreinEta) := by
    rw [← mul_assoc kreinEta, kreinEta_mul_self, one_mul]
  rw [h]

theorem kreinAdj_sub (A B : Cl55Mat) :
    kreinAdj (A - B) = kreinAdj A - kreinAdj B := by
  dsimp [kreinAdj]
  rw [Matrix.transpose_sub]
  simp only [mul_sub, sub_mul]

def spacetimeCoordinate (psi gamma : Cl55Mat) : ℝ :=
  Matrix.trace (diracKreinAdjoint psi * gamma * psi)

def modularFlowGenerator (K A : Cl55Mat) : Cl55Mat :=
  K * A - A * K

theorem modularFlowGenerator_trace (K A : Cl55Mat) :
    Matrix.trace (modularFlowGenerator K A) = 0 := by
  dsimp [modularFlowGenerator]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

theorem modularFlowGenerator_krein_antisymm (K A : Cl55Mat)
    (hK : kreinAdj K = K) (hA : kreinAdj A = A) :
    kreinAdj (modularFlowGenerator K A) =
      -modularFlowGenerator K A := by
  rw [modularFlowGenerator, kreinAdj_sub, kreinAdj_mul, kreinAdj_mul,
    hK, hA]
  module

theorem spacetimeCoordinate_eq_trace (psi gamma : Cl55Mat) :
    spacetimeCoordinate psi gamma =
      Matrix.trace (diracKreinAdjoint psi * gamma * psi) := rfl

noncomputable def emergentMetric (psi gammaMu gammaNu : Cl55Mat) : ℝ :=
  (1 / 2 : ℝ) *
    (spacetimeCoordinate psi (gammaMu * gammaNu) +
      spacetimeCoordinate psi (gammaNu * gammaMu))

theorem emergentMetric_symm (psi gammaMu gammaNu : Cl55Mat) :
    emergentMetric psi gammaMu gammaNu =
      emergentMetric psi gammaNu gammaMu := by
  dsimp [emergentMetric]
  rw [add_comm]

end InfoGeometry.Physics.EmergentSpacetime
