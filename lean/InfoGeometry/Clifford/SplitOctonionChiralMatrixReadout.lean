import Mathlib

/-!
# A non-Zorn chiral matrix readout of the split-octonion vector space

The entries are actual quaternionic operator atoms `1, i, j, k`; the
`2 × 2` matrix space is a chiral operator carrier.  This is a linear chiral
readout only; ordinary associative matrix multiplication is deliberately not
declared to be the split-octonion product.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

noncomputable section

open scoped Matrix

abbrev ChiralEntry := Quaternion ℝ

abbrev ChiralMatrix := Matrix (Fin 2) (Fin 2) ChiralEntry

def entryOne : ChiralEntry := ⟨1, 0, 0, 0⟩

def entryI : ChiralEntry := ⟨0, 1, 0, 0⟩

def entryJ : ChiralEntry := ⟨0, 0, 1, 0⟩

def entryK : ChiralEntry := ⟨0, 0, 0, 1⟩

def entryZero : ChiralEntry := 0

def rhoPlus : ChiralMatrix := !![entryOne, entryZero; entryZero, entryZero]

def rhoMinus : ChiralMatrix := !![entryZero, entryZero; entryZero, entryOne]

def uOne : ChiralMatrix := !![entryZero, entryI; entryZero, entryZero]

def uTwo : ChiralMatrix := !![entryZero, entryJ; entryZero, entryZero]

def uThree : ChiralMatrix := !![entryZero, entryK; entryZero, entryZero]

def vOne : ChiralMatrix := !![entryZero, entryZero; entryI, entryZero]

def vTwo : ChiralMatrix := !![entryZero, entryZero; entryJ, entryZero]

def vThree : ChiralMatrix := !![entryZero, entryZero; entryK, entryZero]

abbrev uPlus : ChiralMatrix := rhoPlus
abbrev uMinus : ChiralMatrix := rhoMinus

def chiralOne : ChiralMatrix := uPlus + uMinus

/-! The hyperbolic element is reconstructed from the two chiral poles. -/
def ell : ChiralMatrix := uPlus - uMinus

def operatorE (a : Fin 3) : ChiralMatrix :=
  match a with
  | 0 => uOne + vOne
  | 1 => uTwo + vTwo
  | 2 => uThree + vThree

/- The quaternion multiplication packet and ordinary block-product tests are
   intentionally kept out of this readout owner; native quaternion laws
   belong to the dedicated quaternion owner. -/
/- theorem quaternion_atom_square_packet :
    entryI * entryI = -entryOne ∧
    entryJ * entryJ = -entryOne ∧
    entryK * entryK = -entryOne ∧
    entryI * entryJ = entryK ∧
    entryJ * entryK = entryI ∧
    entryK * entryI = entryJ := by
  constructor
  · apply QuaternionAlgebra.ext <;> norm_num [entryI, entryOne]
  constructor
  · apply QuaternionAlgebra.ext <;> norm_num [entryJ, entryOne]
  constructor
  · apply QuaternionAlgebra.ext <;> norm_num [entryK, entryOne]
  constructor
  · apply QuaternionAlgebra.ext <;> norm_num [entryI, entryJ, entryK]

  constructor
  · apply QuaternionAlgebra.ext <;> norm_num [entryI, entryJ, entryK]
  · apply QuaternionAlgebra.ext <;> norm_num [entryI, entryJ, entryK]

private theorem entryOne_mul : entryOne * entryOne = entryOne := by
  apply Quaternion.ext <;> simp [entryOne, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem entryI_mul : entryI * entryI = -entryOne := by
  apply Quaternion.ext <;> simp [entryI, entryOne, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem entryJ_mul : entryJ * entryJ = -entryOne := by
  apply Quaternion.ext <;> simp [entryJ, entryOne, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem entryK_mul : entryK * entryK = -entryOne := by
  apply Quaternion.ext <;> simp [entryK, entryOne, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

theorem ordinary_matrix_chiral_idempotents :
    uPlus * uPlus = uPlus ∧
    uMinus * uMinus = uMinus ∧
    uPlus * uMinus = 0 ∧
    uMinus * uPlus = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, rhoPlus, rhoMinus, Matrix.mul_apply,
      Fin.sum_univ_two, entryZero, entryOne_mul]

theorem ordinary_matrix_cl11_packet (a : Fin 3) :
    operatorE a * operatorE a = -chiralOne ∧
    ell * operatorE a = -(operatorE a * ell) := by
  fin_cases a
  all_goals constructor <;> native_decide

-/

def chiralBasis : Fin 8 → ChiralMatrix
  | 0 => uPlus
  | 1 => uOne
  | 2 => uTwo
  | 3 => uThree
  | 4 => uMinus
  | 5 => vOne
  | 6 => vTwo
  | 7 => vThree
  | _ => 0

def chiralCoordinates (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) : ChiralMatrix :=
  a₀ • uPlus + a₁ • uOne + a₂ • uTwo + a₃ • uThree +
    b₀ • uMinus + b₁ • vOne + b₂ • vTwo + b₃ • vThree

theorem chiralOne_eq_uPlus_add_uMinus :
    chiralOne = uPlus + uMinus := rfl

theorem ell_eq_uPlus_sub_uMinus :
    ell = uPlus - uMinus := rfl

theorem chiralOne_apply :
    chiralOne = !![entryOne, entryZero; entryZero, entryOne] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralOne, uPlus, uMinus, rhoPlus, rhoMinus, entryOne, entryZero]

theorem ell_apply :
    ell = !![entryOne, entryZero; entryZero, -entryOne] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ell, uPlus, uMinus, rhoPlus, rhoMinus, entryOne, entryZero]

theorem chiralBasis_zero : chiralBasis 0 = uPlus := rfl
theorem chiralBasis_one : chiralBasis 1 = uOne := rfl
theorem chiralBasis_two : chiralBasis 2 = uTwo := rfl
theorem chiralBasis_three : chiralBasis 3 = uThree := rfl
theorem chiralBasis_four : chiralBasis 4 = uMinus := rfl
theorem chiralBasis_five : chiralBasis 5 = vOne := rfl
theorem chiralBasis_six : chiralBasis 6 = vTwo := rfl
theorem chiralBasis_seven : chiralBasis 7 = vThree := rfl

theorem chiralCoordinates_readout :
    chiralCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ =
      !![a₀ • entryOne, a₁ • entryI + a₂ • entryJ + a₃ • entryK;
        b₁ • entryI + b₂ • entryJ + b₃ • entryK, b₀ • entryOne] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCoordinates, uPlus, uMinus, uOne, uTwo, uThree,
      vOne, vTwo, vThree, rhoPlus, rhoMinus, entryOne, entryI, entryJ, entryK,
      entryZero]

theorem rhoPlus_ne_rhoMinus : rhoPlus ≠ rhoMinus := by
  intro h
  have h00 := congrArg (fun M : ChiralMatrix => M 0 0) h
  have h00' := congrArg (fun q : ChiralEntry => q.re) h00
  norm_num [rhoPlus, rhoMinus, entryOne, entryZero] at h00'

theorem uOne_ne_zero : uOne ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : ChiralMatrix => M 0 1) h
  have h01' := congrArg (fun q : ChiralEntry => q.imI) h01
  norm_num [uOne, entryI, entryZero] at h01'

theorem vOne_ne_zero : vOne ≠ 0 := by
  intro h
  have h10 := congrArg (fun M : ChiralMatrix => M 1 0) h
  have h10' := congrArg (fun q : ChiralEntry => q.imI) h10
  norm_num [vOne, entryI, entryZero] at h10'

end

end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
