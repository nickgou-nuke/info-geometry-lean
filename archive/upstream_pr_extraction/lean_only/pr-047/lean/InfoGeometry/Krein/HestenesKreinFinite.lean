import InfoGeometry.Canonical.HestenesCircularSheetCAR
import InfoGeometry.Krein.TwoSheetKreinIdealBridge

/-!
# Native finite Hestenes--Krein two-sheet bridge

This owner promotes the already native Pauli sheet matrices into the Krein
ideal-transport API.  It remains a finite matrix theorem package; no
Clifford-algebra identification is asserted here.
-/

namespace InfoGeometry.Krein.HestenesKreinFinite

open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Krein

noncomputable section

abbrev Sheet := SheetMatrix

abbrev fundamentalSymmetry : Sheet := sheetFlip
abbrev fPlus : Sheet := uPlus
abbrev fMinus : Sheet := uMinus

@[simp] theorem fundamentalSymmetry_sq :
    fundamentalSymmetry * fundamentalSymmetry = (1 : Sheet) := by
  unfold fundamentalSymmetry
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two]

theorem fundamentalSymmetry_selfAdjoint :
    Matrix.conjTranspose fundamentalSymmetry = fundamentalSymmetry := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalSymmetry, sheetFlip, Matrix.conjTranspose, Matrix.transpose,
      Matrix.conjTranspose_apply]

@[simp] theorem fPlus_idempotent : fPlus * fPlus = fPlus :=
  uPlus_idempotent

@[simp] theorem fMinus_idempotent : fMinus * fMinus = fMinus :=
  uMinus_idempotent

@[simp] theorem fPlus_mul_fMinus : fPlus * fMinus = 0 :=
  uPlus_mul_uMinus

@[simp] theorem fMinus_mul_fPlus : fMinus * fPlus = 0 :=
  uMinus_mul_uPlus

@[simp] theorem fPlus_add_fMinus : fPlus + fMinus = (1 : Sheet) :=
  by
    unfold fPlus fMinus uPlus uMinus
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetIdentity, sheetParity] <;> norm_num [div_eq_mul_inv]

@[simp] theorem fundamentalSymmetry_fPlus_fundamentalSymmetry :
    fundamentalSymmetry * fPlus * fundamentalSymmetry = fMinus := by
  unfold fundamentalSymmetry fPlus fMinus uPlus uMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, sheetIdentity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

@[simp] theorem fundamentalSymmetry_fMinus_fundamentalSymmetry :
    fundamentalSymmetry * fMinus * fundamentalSymmetry = fPlus := by
  unfold fundamentalSymmetry fPlus fMinus uPlus uMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, sheetIdentity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem kreinConjugate_fPlus_leftPrincipal_iff {x : Sheet} :
    x ∈ leftPrincipal fPlus ↔
      kreinConjugate fundamentalSymmetry x ∈ leftPrincipal fMinus :=
  kreinConjugate_leftPrincipal_iff fundamentalSymmetry fPlus fMinus
    fundamentalSymmetry_sq fundamentalSymmetry_fPlus_fundamentalSymmetry

theorem kreinConjugate_fPlus_fMinus_corner_iff {x : Sheet} :
    x ∈ peirceCorner fPlus fMinus ↔
      kreinConjugate fundamentalSymmetry x ∈ peirceCorner fMinus fPlus :=
  kreinConjugate_peirceCorner_iff fundamentalSymmetry fPlus fMinus
    fundamentalSymmetry_sq fundamentalSymmetry_fPlus_fundamentalSymmetry
    fundamentalSymmetry_fMinus_fundamentalSymmetry

end

end InfoGeometry.Krein.HestenesKreinFinite
