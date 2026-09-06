import InfoGeometry.Lie.CanonicalZornDerivation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

noncomputable section
namespace InfoGeometry.Lie.CanonicalZornDerivationDimension

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev Params := Fin 14 → ℝ
abbrev VZ := ZornVectorMatrix ℝ
abbrev VDer := ZornVectorMatrix.Derivation (R := ℝ)

def parameterAction (p : Params) (X : VZ) : VZ :=
  ⟨p 0 * X.v 0 + p 3 * X.v 1 + p 8 * X.v 2 - p 10 * X.w 0 + p 9 * X.w 1 - p 4 * X.w 2,
   fun i => if i = 0 then
      p 10 * X.a - p 10 * X.b + (p 6 + p 13) * X.v 0 - p 5 * X.v 1 - p 11 * X.v 2 + p 8 * X.w 1 - p 3 * X.w 2
    else if i = 1 then
      -p 9 * X.a + p 9 * X.b - p 1 * X.v 0 - p 6 * X.v 1 - p 12 * X.v 2 - p 8 * X.w 0 + p 0 * X.w 2
    else
      p 4 * X.a - p 4 * X.b - p 2 * X.v 0 - p 7 * X.v 1 - p 13 * X.v 2 + p 3 * X.w 0 - p 0 * X.w 1,
   fun i => if i = 0 then
      -p 0 * X.a + p 0 * X.b - p 4 * X.v 1 - p 9 * X.v 2 - (p 6 + p 13) * X.w 0 + p 1 * X.w 1 + p 2 * X.w 2
    else if i = 1 then
      -p 3 * X.a + p 3 * X.b + p 4 * X.v 0 - p 10 * X.v 2 + p 5 * X.w 0 + p 6 * X.w 1 + p 7 * X.w 2
    else
      -p 8 * X.a + p 8 * X.b + p 9 * X.v 0 + p 10 * X.v 1 + p 11 * X.w 0 + p 12 * X.w 1 + p 13 * X.w 2,
   -(p 0 * X.v 0 + p 3 * X.v 1 + p 8 * X.v 2 - p 10 * X.w 0 + p 9 * X.w 1 - p 4 * X.w 2)⟩

noncomputable def parameterDerivation (p : Params) : VDer where
  toFun := parameterAction p
  map_add' X Y := by
    ext i <;> try { funext i }
    all_goals try fin_cases i
    all_goals simp [parameterAction, ZornVectorMatrix.add]
    all_goals ring
  map_smul' r X := by
    ext i <;> try { funext i }
    all_goals try fin_cases i
    all_goals simp [parameterAction, ZornVectorMatrix.smul]
    all_goals ring
  map_mul' X Y := by
    unfold ZornVectorMatrix.add
    apply ZornVectorMatrix.ext
    · simp [parameterAction, ZornVectorMatrix.mul,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · funext i
      fin_cases i <;>
        simp [parameterAction, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · funext i
      fin_cases i <;>
        simp [parameterAction, ZornVectorMatrix.mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · simp [parameterAction, ZornVectorMatrix.mul,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring

/-- Read the fourteen canonical coordinates of a vector-Zorn derivation. -/
def derivationParameters (D : VDer) : Params := fun i =>
  if i = 0 then (D E22).w 0
  else if i = 1 then (D (V 1)).w 0
  else if i = 2 then (D (V 2)).w 0
  else if i = 3 then (D E22).w 1
  else if i = 4 then (D (U 0)).w 1
  else if i = 5 then (D (V 0)).w 1
  else if i = 6 then (D (V 1)).w 1
  else if i = 7 then (D (V 2)).w 1
  else if i = 8 then (D E22).w 2
  else if i = 9 then (D (U 0)).w 2
  else if i = 10 then (D (U 1)).w 2
  else if i = 11 then (D (V 0)).w 2
  else if i = 12 then (D (V 1)).w 2
  else (D (V 2)).w 2

theorem derivationParameters_parameterDerivation (p : Params) :
    derivationParameters (parameterDerivation p) = p := by
  funext i
  fin_cases i <;>
    simp [derivationParameters, parameterDerivation, parameterAction,
      E22, U, V, ZornVec3.basis]

private def coord8 (X : VZ) (i : Fin 8) : ℝ :=
  if i = 0 then X.a
  else if i = 1 then X.b
  else if i = 2 then X.v 0
  else if i = 3 then X.v 1
  else if i = 4 then X.v 2
  else if i = 5 then X.w 0
  else if i = 6 then X.w 1
  else X.w 2

private example (D : VDer) :
    (parameterAction (derivationParameters D) E11).a = (D E11).a := by
  have h := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  simp [coord8, E11, ZornVectorMatrix.mul, ZornVectorMatrix.add,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h
  simp [parameterAction, E11]
  linarith

private theorem p00 : ZornVectorMatrix.mul E11 E11 = (E11 : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p01 : ZornVectorMatrix.mul E11 E22 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p02 : ZornVectorMatrix.mul E11 (U 0) = ((U 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p03 : ZornVectorMatrix.mul E11 (U 1) = ((U 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p04 : ZornVectorMatrix.mul E11 (U 2) = ((U 2) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p05 : ZornVectorMatrix.mul E11 (V 0) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p06 : ZornVectorMatrix.mul E11 (V 1) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p07 : ZornVectorMatrix.mul E11 (V 2) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p10 : ZornVectorMatrix.mul E22 E11 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p11 : ZornVectorMatrix.mul E22 E22 = (E22 : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p20 : ZornVectorMatrix.mul (U 0) E11 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p23 : ZornVectorMatrix.mul (U 0) (U 1) = ((V 2) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p24 : ZornVectorMatrix.mul (U 0) (U 2) = (neg (V 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p25 : ZornVectorMatrix.mul (U 0) (V 0) = (E11 : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p30 : ZornVectorMatrix.mul (U 1) E11 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p34 : ZornVectorMatrix.mul (U 1) (U 2) = ((V 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem p40 : ZornVectorMatrix.mul (U 2) E11 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem reconstruct_basis_0 (D : VDer) :
    parameterAction (derivationParameters D) E11 = D E11 := by
  have h0 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  have h1 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul E11 E11)
  have h8 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 0))
  have h9 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 0))
  have h13 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 1))
  have h30 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E22 E11)
  have h31 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E22 E11)
  have h32 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E22 E11)
  rw [p00] at h0 h1
  rw [p02] at h8 h9
  rw [p03] at h13
  rw [p10] at h30 h31 h32
  simp only [D.map_zero, D.map_neg] at h0 h1 h8 h9 h13 h30 h31 h32
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h0 h1 h8 h9 h13 h30 h31 h32
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h0]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h13]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h9]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h8]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h30]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h31]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h32]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h1]

private theorem reconstruct_basis_1 (D : VDer) :
    parameterAction (derivationParameters D) E22 = D E22 := by
  have h2 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E22)
  have h3 := congrArg (fun Z : VZ => coord8 Z 2) (D.map_mul E11 E22)
  have h4 := congrArg (fun Z : VZ => coord8 Z 3) (D.map_mul E11 E22)
  have h5 := congrArg (fun Z : VZ => coord8 Z 4) (D.map_mul E11 E22)
  have h8 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 0))
  have h9 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 0))
  have h13 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 1))
  have h33 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul E22 E22)
  rw [p01] at h2 h3 h4 h5
  rw [p02] at h8 h9
  rw [p03] at h13
  rw [p11] at h33
  simp only [D.map_zero, D.map_neg] at h2 h3 h4 h5 h8 h9 h13 h33
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h2 h3 h4 h5 h8 h9 h13 h33
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h2]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h3, h13]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h4, h9]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h5, h8]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h33]

private theorem reconstruct_basis_2 (D : VDer) :
    parameterAction (derivationParameters D) (U 0) = D (U 0) := by
  have h0 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  have h6 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul E11 (U 0))
  have h7 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E11 (U 0))
  have h30 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E22 E11)
  have h34 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 0) E11)
  have h36 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 0) (U 1))
  have h38 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul (U 0) (U 1))
  have h40 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 0) (U 2))
  have h41 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul (U 0) (U 2))
  have h43 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 0) (V 0))
  have h46 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 1) (U 2))
  rw [p00] at h0
  rw [p02] at h6 h7
  rw [p10] at h30
  rw [p20] at h34
  rw [p23] at h36 h38
  rw [p24] at h40 h41
  rw [p25] at h43
  rw [p34] at h46
  simp only [D.map_zero, D.map_neg] at h0 h6 h7 h30 h34 h36 h38 h40 h41 h43 h46
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h0 h6 h7 h30 h34 h36 h38 h40 h41 h43 h46
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h30, h34]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h0, h38, h41, h43, h46]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h40]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h36]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h7]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h6, h30]

private theorem reconstruct_basis_3 (D : VDer) :
    parameterAction (derivationParameters D) (U 1) = D (U 1) := by
  have h0 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  have h8 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 0))
  have h10 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul E11 (U 1))
  have h11 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E11 (U 1))
  have h12 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 1))
  have h31 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E22 E11)
  have h37 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul (U 0) (U 1))
  have h41 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul (U 0) (U 2))
  have h43 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 0) (V 0))
  have h45 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 1) E11)
  have h46 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 1) (U 2))
  have h47 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul (U 1) (U 2))
  rw [p00] at h0
  rw [p02] at h8
  rw [p03] at h10 h11 h12
  rw [p10] at h31
  rw [p23] at h37
  rw [p24] at h41
  rw [p25] at h43
  rw [p30] at h45
  rw [p34] at h46 h47
  simp only [D.map_zero, D.map_neg] at h0 h8 h10 h11 h12 h31 h37 h41 h43 h45 h46 h47
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h0 h8 h10 h11 h12 h31 h37 h41 h43 h45 h46 h47
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h31, h45]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h47]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h0, h41, h43, h46]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h37]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h8, h11]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h12]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h10, h31]

private theorem reconstruct_basis_4 (D : VDer) :
    parameterAction (derivationParameters D) (U 2) = D (U 2) := by
  have h0 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  have h9 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 0))
  have h13 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 1))
  have h14 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul E11 (U 2))
  have h15 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E11 (U 2))
  have h16 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 2))
  have h17 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 2))
  have h32 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E22 E11)
  have h38 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul (U 0) (U 1))
  have h42 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul (U 0) (U 2))
  have h43 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 0) (V 0))
  have h46 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 1) (U 2))
  have h48 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul (U 1) (U 2))
  have h49 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 2) E11)
  rw [p00] at h0
  rw [p02] at h9
  rw [p03] at h13
  rw [p04] at h14 h15 h16 h17
  rw [p10] at h32
  rw [p23] at h38
  rw [p24] at h42
  rw [p25] at h43
  rw [p34] at h46 h48
  rw [p40] at h49
  simp only [D.map_zero, D.map_neg] at h0 h9 h13 h14 h15 h16 h17 h32 h38 h42 h43 h46 h48 h49
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h0 h9 h13 h14 h15 h16 h17 h32 h38 h42 h43 h46 h48 h49
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h32, h49]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h48]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h42]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h0, h38, h43, h46]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h9, h15]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h13, h16]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h17]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h14, h32]

private theorem reconstruct_basis_5 (D : VDer) :
    parameterAction (derivationParameters D) (V 0) = D (V 0) := by
  have h0 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 E11)
  have h13 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 1))
  have h18 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 (V 0))
  have h19 := congrArg (fun Z : VZ => coord8 Z 2) (D.map_mul E11 (V 0))
  have h20 := congrArg (fun Z : VZ => coord8 Z 3) (D.map_mul E11 (V 0))
  have h21 := congrArg (fun Z : VZ => coord8 Z 4) (D.map_mul E11 (V 0))
  have h31 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E22 E11)
  have h32 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E22 E11)
  have h38 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul (U 0) (U 1))
  have h41 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul (U 0) (U 2))
  have h43 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul (U 0) (V 0))
  have h44 := congrArg (fun Z : VZ => coord8 Z 2) (D.map_mul (U 0) (V 0))
  have h46 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul (U 1) (U 2))
  rw [p00] at h0
  rw [p03] at h13
  rw [p05] at h18 h19 h20 h21
  rw [p10] at h31 h32
  rw [p23] at h38
  rw [p24] at h41
  rw [p25] at h43 h44
  rw [p34] at h46
  simp only [D.map_zero, D.map_neg] at h0 h13 h18 h19 h20 h21 h31 h32 h38 h41 h43 h44 h46
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h0 h13 h18 h19 h20 h21 h31 h32 h38 h41 h43 h44 h46
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h13, h18]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h19]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h20, h32]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h21, h31]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h0, h38, h41, h43, h46]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h13, h44]

private theorem reconstruct_basis_6 (D : VDer) :
    parameterAction (derivationParameters D) (V 1) = D (V 1) := by
  have h9 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E11 (U 0))
  have h22 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 (V 1))
  have h23 := congrArg (fun Z : VZ => coord8 Z 2) (D.map_mul E11 (V 1))
  have h24 := congrArg (fun Z : VZ => coord8 Z 3) (D.map_mul E11 (V 1))
  have h25 := congrArg (fun Z : VZ => coord8 Z 4) (D.map_mul E11 (V 1))
  have h30 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E22 E11)
  have h32 := congrArg (fun Z : VZ => coord8 Z 7) (D.map_mul E22 E11)
  have h39 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul (U 0) (U 2))
  rw [p02] at h9
  rw [p06] at h22 h23 h24 h25
  rw [p10] at h30 h32
  rw [p24] at h39
  simp only [D.map_zero, D.map_neg] at h9 h22 h23 h24 h25 h30 h32 h39
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h9 h22 h23 h24 h25 h30 h32 h39
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h9, h22]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h23, h32]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h24]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h25, h30]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h39]

private theorem reconstruct_basis_7 (D : VDer) :
    parameterAction (derivationParameters D) (V 2) = D (V 2) := by
  have h8 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E11 (U 0))
  have h26 := congrArg (fun Z : VZ => coord8 Z 0) (D.map_mul E11 (V 2))
  have h27 := congrArg (fun Z : VZ => coord8 Z 2) (D.map_mul E11 (V 2))
  have h28 := congrArg (fun Z : VZ => coord8 Z 3) (D.map_mul E11 (V 2))
  have h29 := congrArg (fun Z : VZ => coord8 Z 4) (D.map_mul E11 (V 2))
  have h30 := congrArg (fun Z : VZ => coord8 Z 5) (D.map_mul E22 E11)
  have h31 := congrArg (fun Z : VZ => coord8 Z 6) (D.map_mul E22 E11)
  have h35 := congrArg (fun Z : VZ => coord8 Z 1) (D.map_mul (U 0) (U 1))
  rw [p02] at h8
  rw [p07] at h26 h27 h28 h29
  rw [p10] at h30 h31
  rw [p23] at h35
  simp only [D.map_zero, D.map_neg] at h8 h26 h27 h28 h29 h30 h31 h35
  simp [coord8, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h8 h26 h27 h28 h29 h30 h31 h35
  apply ZornVectorMatrix.ext
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h8, h26]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h27, h31]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h28, h30]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
      linarith only [h29]
  · funext i
    fin_cases i
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
  · simp [parameterAction, derivationParameters, E11, E22, U, V, ZornVec3.basis]
    linarith only [h35]

private def basisCombination (f : VZ → VZ) (X : VZ) : VZ :=
  ZornVectorMatrix.add (ZornVectorMatrix.smul X.a (f E11))
    (ZornVectorMatrix.add (ZornVectorMatrix.smul X.b (f E22))
      (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 0) (f (U 0)))
        (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 1) (f (U 1)))
          (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 2) (f (U 2)))
            (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.w 0) (f (V 0)))
              (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.w 1) (f (V 1)))
                (ZornVectorMatrix.smul (X.w 2) (f (V 2)))))))))

private theorem basisCombination_id (X : VZ) : basisCombination id X = X := by
  apply ZornVectorMatrix.ext
  · simp [basisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      E11, E22, U, V, ZornVec3.basis]
  · funext i
    fin_cases i <;>
      simp [basisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
        E11, E22, U, V, ZornVec3.basis]
  · funext i
    fin_cases i <;>
      simp [basisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
        E11, E22, U, V, ZornVec3.basis]
  · simp [basisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      E11, E22, U, V, ZornVec3.basis]

private theorem derivation_eq_basisCombination (D : VDer) (X : VZ) :
    D X = basisCombination D X := by
  calc
    D X = D (basisCombination id X) := congrArg D (basisCombination_id X).symm
    _ = basisCombination D X := by
      simp only [basisCombination, D.map_add, D.map_smul, id_eq]

private theorem parameterDerivation_derivationParameters (D : VDer) :
    parameterDerivation (derivationParameters D) = D := by
  apply InfoGeometry.Algebra.ZornVectorMatrix.Derivation.ext
  intro X
  rw [derivation_eq_basisCombination, derivation_eq_basisCombination]
  change basisCombination (parameterAction (derivationParameters D)) X =
    basisCombination D X
  simp only [basisCombination]
  rw [reconstruct_basis_0 D, reconstruct_basis_1 D, reconstruct_basis_2 D,
    reconstruct_basis_3 D, reconstruct_basis_4 D, reconstruct_basis_5 D,
    reconstruct_basis_6 D, reconstruct_basis_7 D]

noncomputable def parameterLinearEquiv : Params ≃ₗ[ℝ] VDer where
  toFun := parameterDerivation
  invFun := derivationParameters
  left_inv := derivationParameters_parameterDerivation
  right_inv := parameterDerivation_derivationParameters
  map_add' p q := by
    change parameterDerivation (p + q) =
      InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add
        (parameterDerivation p) (parameterDerivation q)
    apply InfoGeometry.Algebra.ZornVectorMatrix.Derivation.ext
    intro X
    apply ZornVectorMatrix.ext
    · simp [parameterDerivation, parameterAction,
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add, ZornVectorMatrix.add]
      ring
    · funext i
      fin_cases i <;>
        simp [parameterDerivation, parameterAction,
          InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add, ZornVectorMatrix.add] <;>
        ring
    · funext i
      fin_cases i <;>
        simp [parameterDerivation, parameterAction,
          InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add, ZornVectorMatrix.add] <;>
        ring
    · simp [parameterDerivation, parameterAction,
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add, ZornVectorMatrix.add]
      ring
  map_smul' r p := by
    change parameterDerivation (r • p) =
      InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul r
        (parameterDerivation p)
    apply InfoGeometry.Algebra.ZornVectorMatrix.Derivation.ext
    intro X
    apply ZornVectorMatrix.ext
    · simp [parameterDerivation, parameterAction,
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul, ZornVectorMatrix.smul]
      ring
    · funext i
      fin_cases i <;>
        simp [parameterDerivation, parameterAction,
          InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul, ZornVectorMatrix.smul] <;>
        ring
    · funext i
      fin_cases i <;>
        simp [parameterDerivation, parameterAction,
          InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul, ZornVectorMatrix.smul] <;>
        ring
    · simp [parameterDerivation, parameterAction,
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul, ZornVectorMatrix.smul]
      ring

theorem finrank_vectorDerivations : Module.finrank ℝ VDer = 14 := by
  rw [← parameterLinearEquiv.finrank_eq]
  simp [Params]

/-- The explicit fourteen-parameter model transported to canonical Zorn
derivations.  Its inverse is the canonical coordinate readout used by the
standard-derivation spanning proof. -/
noncomputable def canonicalParameterLinearEquiv :
    Params ≃ₗ[ℝ] CanonicalZornDerivation.canonicalZornDerivations :=
  parameterLinearEquiv.trans CanonicalZornDerivation.vectorCanonicalLinearEquiv

theorem finrank_canonicalZornDerivations :
    Module.finrank ℝ CanonicalZornDerivation.canonicalZornDerivations = 14 := by
  rw [← CanonicalZornDerivation.vectorCanonicalLinearEquiv.finrank_eq]
  exact finrank_vectorDerivations

end InfoGeometry.Lie.CanonicalZornDerivationDimension
