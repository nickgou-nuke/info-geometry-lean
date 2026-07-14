import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitQ11Projectors
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Clifford.SplitQ11CausalCone

Matrix-facing local causal-cone closure inside the split `Cl(1,1)` atom.

This module fixes the prose convention

* `i² = -1`,
* `j² = 1`,
* `k² = 1`,
* `ij = k = -ji`,

with `K := k` as the Krein involution.  It proves the associated sector
projectors, null hops, finite inner dilation shadow, and off-diagonal mass
bridge directly in the repo's split Clifford algebra.

The facts here are finite algebraic facts only.  No physical completeness claim
or infinite-dimensional modular/Virasoro conclusion is inferred from this local
matrix atom alone.
-/

open scoped Matrix

namespace SplitQ11CausalCone

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors

/-! ## Split-quaternion dictionary -/

/-- Matrix-facing square-minus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionI : Alg :=
  kGen

/-- Matrix-facing first square-plus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionJ : Alg :=
  epsGen

/-- Matrix-facing Krein involution, the second square-plus split-quaternion unit. -/
@[rep_depth krein]
noncomputable def splitQuaternionK : Alg :=
  jGen

@[rep_depth krein]
theorem split_quaternion_basis_laws :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionJ * splitQuaternionJ = (1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ splitQuaternionI * splitQuaternionJ = splitQuaternionK
      ∧ splitQuaternionJ * splitQuaternionI = -splitQuaternionK := by
  exact ⟨by simp [splitQuaternionI], by simp [splitQuaternionJ],
    by simp [splitQuaternionK], by simp [splitQuaternionI, splitQuaternionJ,
      splitQuaternionK], by simp [splitQuaternionI, splitQuaternionJ, splitQuaternionK]⟩

@[rep_depth krein]
theorem matrix_split_quaternion_basis_laws :
    Eminus * Eminus = -(1 : Mat2)
      ∧ J1 * J1 = (1 : Mat2)
      ∧ Eplus * Eplus = (1 : Mat2)
      ∧ Eminus * J1 = Eplus
      ∧ J1 * Eminus = -Eplus := by
  refine ⟨by simpa using Eminus_sq, J1_sq, Eplus_sq, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Eminus, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Eminus, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Krein projectors and null causal hops -/

/-- The `K = +1` local Krein projector. -/
@[rep_depth krein]
noncomputable def kreinPlusProjector : Alg :=
  (1 / 2 : ℝ) • ((1 : Alg) + splitQuaternionK)

/-- The `K = -1` local Krein projector. -/
@[rep_depth krein]
noncomputable def kreinMinusProjector : Alg :=
  (1 / 2 : ℝ) • ((1 : Alg) - splitQuaternionK)

/-- Matrix-side `K = +1` projector. -/
@[rep_depth krein]
noncomputable def matrixKreinPlusProjector : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) + Eplus)

/-- Matrix-side `K = -1` projector. -/
@[rep_depth krein]
noncomputable def matrixKreinMinusProjector : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) - Eplus)

/-- Matrix-side null causal hop from the negative Krein sector to the positive sector. -/
@[rep_depth krein]
noncomputable def matrixCausalNullPlus : Mat2 :=
  (1 / 2 : ℝ) • (J1 + Eminus)

/-- Matrix-side null causal hop from the positive Krein sector to the negative sector. -/
@[rep_depth krein]
noncomputable def matrixCausalNullMinus : Mat2 :=
  (1 / 2 : ℝ) • (J1 - Eminus)

@[rep_depth krein]
theorem matrix_krein_projectors_explicit :
    matrixKreinPlusProjector = !![(1 : ℝ), 0; 0, 0]
      ∧ matrixKreinMinusProjector = !![0, 0; 0, (1 : ℝ)] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixKreinPlusProjector, Eplus]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixKreinMinusProjector, Eplus]

@[rep_depth krein]
theorem matrix_causal_nulls_explicit :
    matrixCausalNullPlus = !![(0 : ℝ), 1; 0, 0]
      ∧ matrixCausalNullMinus = !![0, 0; (1 : ℝ), 0] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixCausalNullPlus, J1, Eminus]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixCausalNullMinus, J1, Eminus]

@[rep_depth krein]
theorem matrix_causal_null_closure_laws :
    matrixCausalNullPlus * matrixCausalNullPlus = 0
      ∧ matrixCausalNullMinus * matrixCausalNullMinus = 0
      ∧ matrixCausalNullPlus * matrixCausalNullMinus = matrixKreinPlusProjector
      ∧ matrixCausalNullMinus * matrixCausalNullPlus = matrixKreinMinusProjector
      ∧ matrixCausalNullPlus * matrixCausalNullMinus
          + matrixCausalNullMinus * matrixCausalNullPlus = (1 : Mat2)
      ∧ matrixCausalNullPlus * matrixCausalNullMinus
          - matrixCausalNullMinus * matrixCausalNullPlus = Eplus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [matrixCausalNullPlus, matrixCausalNullMinus, matrixKreinPlusProjector,
        matrixKreinMinusProjector, J1, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

@[rep_depth krein]
theorem matrix_krein_projectors_noncentral :
    matrixKreinPlusProjector * matrixCausalNullPlus
        ≠ matrixCausalNullPlus * matrixKreinPlusProjector
      ∧ matrixKreinMinusProjector * matrixCausalNullMinus
        ≠ matrixCausalNullMinus * matrixKreinMinusProjector := by
  constructor
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num [matrixKreinPlusProjector, matrixCausalNullPlus, J1, Eminus, Eplus,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  · intro h
    have h10 := congr_fun (congr_fun h 1) 0
    norm_num [matrixKreinMinusProjector, matrixCausalNullMinus, J1, Eminus, Eplus,
      Matrix.mul_apply, Fin.sum_univ_two] at h10

/-! ## Two-component matrix readout -/

/-- Two-component real carrier for the finite matrix readout. -/
abbrev Spinor2 : Type :=
  Fin 2 → ℝ

/-- Left action of a `2 × 2` real matrix on a two-component real carrier. -/
@[rep_depth krein]
def matrixAct (M : Mat2) (ψ : Spinor2) : Spinor2 :=
  fun i => ∑ j : Fin 2, M i j * ψ j

@[rep_depth krein]
theorem matrix_projector_spinor_action (ψ : Spinor2) :
    matrixAct matrixKreinPlusProjector ψ 0 = ψ 0
      ∧ matrixAct matrixKreinPlusProjector ψ 1 = 0
      ∧ matrixAct matrixKreinMinusProjector ψ 0 = 0
      ∧ matrixAct matrixKreinMinusProjector ψ 1 = ψ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [matrixAct, matrixKreinPlusProjector, matrixKreinMinusProjector, Eplus,
      Fin.sum_univ_two]

@[rep_depth krein]
theorem matrix_null_spinor_action (ψ : Spinor2) :
    matrixAct matrixCausalNullPlus ψ 0 = ψ 1
      ∧ matrixAct matrixCausalNullPlus ψ 1 = 0
      ∧ matrixAct matrixCausalNullMinus ψ 0 = 0
      ∧ matrixAct matrixCausalNullMinus ψ 1 = ψ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [matrixAct, matrixCausalNullPlus, matrixCausalNullMinus, J1, Eminus,
      Fin.sum_univ_two]

@[rep_depth krein]
theorem krein_projector_laws :
    kreinPlusProjector * kreinPlusProjector = kreinPlusProjector
      ∧ kreinMinusProjector * kreinMinusProjector = kreinMinusProjector
      ∧ kreinPlusProjector * kreinMinusProjector = 0
      ∧ kreinMinusProjector * kreinPlusProjector = 0
      ∧ kreinPlusProjector + kreinMinusProjector = (1 : Alg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [kreinPlusProjector, splitQuaternionK, mul_add, add_mul, smul_add]
    module
  · simp [kreinMinusProjector, splitQuaternionK, sub_eq_add_neg, mul_add, add_mul,
      smul_add]
    module
  · simp [kreinPlusProjector, kreinMinusProjector, splitQuaternionK, sub_eq_add_neg,
      mul_add, add_mul, smul_add]
    module
  · simp [kreinPlusProjector, kreinMinusProjector, splitQuaternionK, sub_eq_add_neg,
      mul_add, add_mul, smul_add]
    module
  · simp [kreinPlusProjector, kreinMinusProjector, splitQuaternionK]
    module

/-- Null causal hop from the negative Krein sector to the positive sector. -/
@[rep_depth krein]
noncomputable def causalNullPlus : Alg :=
  (1 / 2 : ℝ) • (splitQuaternionJ + splitQuaternionI)

/-- Null causal hop from the positive Krein sector to the negative sector. -/
@[rep_depth krein]
noncomputable def causalNullMinus : Alg :=
  (1 / 2 : ℝ) • (splitQuaternionJ - splitQuaternionI)

@[rep_depth krein]
theorem causal_null_closure_laws :
    causalNullPlus * causalNullPlus = 0
      ∧ causalNullMinus * causalNullMinus = 0
      ∧ causalNullPlus * causalNullMinus = kreinPlusProjector
      ∧ causalNullMinus * causalNullPlus = kreinMinusProjector
      ∧ causalNullPlus * causalNullMinus + causalNullMinus * causalNullPlus = (1 : Alg)
      ∧ causalNullPlus * causalNullMinus - causalNullMinus * causalNullPlus =
          splitQuaternionK := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [causalNullPlus, splitQuaternionI, splitQuaternionJ, mul_add, add_mul,
      smul_add]
    module
  · simp [causalNullMinus, splitQuaternionI, splitQuaternionJ, sub_eq_add_neg,
      mul_add, add_mul, smul_add]
    module
  · simp [causalNullPlus, causalNullMinus, kreinPlusProjector, splitQuaternionI,
      splitQuaternionJ, splitQuaternionK, sub_eq_add_neg, mul_add, add_mul,
      smul_add]
    module
  · simp [causalNullPlus, causalNullMinus, kreinMinusProjector, splitQuaternionI,
      splitQuaternionJ, splitQuaternionK, sub_eq_add_neg, mul_add, add_mul,
      smul_add]
    module
  · simp [causalNullPlus, causalNullMinus, splitQuaternionI, splitQuaternionJ,
      sub_eq_add_neg, mul_add, add_mul, smul_add]
    module
  · simp [causalNullPlus, causalNullMinus, splitQuaternionI, splitQuaternionJ,
      splitQuaternionK, sub_eq_add_neg, mul_add, add_mul, smul_add]
    module

@[rep_depth krein]
theorem causalNullPlus_sq :
    causalNullPlus * causalNullPlus = 0 :=
  causal_null_closure_laws.1

@[rep_depth krein]
theorem causalNullMinus_sq :
    causalNullMinus * causalNullMinus = 0 :=
  causal_null_closure_laws.2.1

@[rep_depth krein]
theorem causalNullPlus_mul_causalNullMinus :
    causalNullPlus * causalNullMinus = kreinPlusProjector :=
  causal_null_closure_laws.2.2.1

@[rep_depth krein]
theorem causalNullMinus_mul_causalNullPlus :
    causalNullMinus * causalNullPlus = kreinMinusProjector :=
  causal_null_closure_laws.2.2.2.1

@[rep_depth krein]
theorem kreinProjector_sum :
    kreinPlusProjector + kreinMinusProjector = (1 : Alg) :=
  krein_projector_laws.2.2.2.2

@[rep_depth krein]
theorem kreinMinusProjector_mul_causalNullPlus :
    kreinMinusProjector * causalNullPlus = 0 := by
  rw [← causalNullMinus_mul_causalNullPlus, mul_assoc, causalNullPlus_sq, mul_zero]

@[rep_depth krein]
theorem causalNullPlus_mul_kreinPlusProjector :
    causalNullPlus * kreinPlusProjector = 0 := by
  rw [← causalNullPlus_mul_causalNullMinus, ← mul_assoc, causalNullPlus_sq, zero_mul]

@[rep_depth krein]
theorem kreinPlusProjector_mul_causalNullMinus :
    kreinPlusProjector * causalNullMinus = 0 := by
  rw [← causalNullPlus_mul_causalNullMinus, mul_assoc, causalNullMinus_sq, mul_zero]

@[rep_depth krein]
theorem causalNullMinus_mul_kreinMinusProjector :
    causalNullMinus * kreinMinusProjector = 0 := by
  rw [← causalNullMinus_mul_causalNullPlus, ← mul_assoc, causalNullMinus_sq, zero_mul]

@[rep_depth krein]
theorem kreinPlusProjector_mul_causalNullPlus :
    kreinPlusProjector * causalNullPlus = causalNullPlus := by
  have h :
      kreinPlusProjector * causalNullPlus + kreinMinusProjector * causalNullPlus =
        causalNullPlus := by
    calc
      kreinPlusProjector * causalNullPlus + kreinMinusProjector * causalNullPlus
          = (kreinPlusProjector + kreinMinusProjector) * causalNullPlus := by
              rw [add_mul]
      _ = (1 : Alg) * causalNullPlus := by rw [kreinProjector_sum]
      _ = causalNullPlus := by simp
  simpa [kreinMinusProjector_mul_causalNullPlus] using h

@[rep_depth krein]
theorem causalNullPlus_mul_kreinMinusProjector :
    causalNullPlus * kreinMinusProjector = causalNullPlus := by
  have h :
      causalNullPlus * kreinPlusProjector + causalNullPlus * kreinMinusProjector =
        causalNullPlus := by
    calc
      causalNullPlus * kreinPlusProjector + causalNullPlus * kreinMinusProjector
          = causalNullPlus * (kreinPlusProjector + kreinMinusProjector) := by
              rw [mul_add]
      _ = causalNullPlus * (1 : Alg) := by rw [kreinProjector_sum]
      _ = causalNullPlus := by simp
  simpa [causalNullPlus_mul_kreinPlusProjector] using h

@[rep_depth krein]
theorem kreinMinusProjector_mul_causalNullMinus :
    kreinMinusProjector * causalNullMinus = causalNullMinus := by
  have h :
      kreinPlusProjector * causalNullMinus + kreinMinusProjector * causalNullMinus =
        causalNullMinus := by
    calc
      kreinPlusProjector * causalNullMinus + kreinMinusProjector * causalNullMinus
          = (kreinPlusProjector + kreinMinusProjector) * causalNullMinus := by
              rw [add_mul]
      _ = (1 : Alg) * causalNullMinus := by rw [kreinProjector_sum]
      _ = causalNullMinus := by simp
  simpa [kreinPlusProjector_mul_causalNullMinus] using h

@[rep_depth krein]
theorem causalNullMinus_mul_kreinPlusProjector :
    causalNullMinus * kreinPlusProjector = causalNullMinus := by
  have h :
      causalNullMinus * kreinPlusProjector + causalNullMinus * kreinMinusProjector =
        causalNullMinus := by
    calc
      causalNullMinus * kreinPlusProjector + causalNullMinus * kreinMinusProjector
          = causalNullMinus * (kreinPlusProjector + kreinMinusProjector) := by
              rw [mul_add]
      _ = causalNullMinus * (1 : Alg) := by rw [kreinProjector_sum]
      _ = causalNullMinus := by simp
  simpa [causalNullMinus_mul_kreinMinusProjector] using h

@[rep_depth krein]
theorem sector_hopping_laws :
    kreinPlusProjector * causalNullPlus = causalNullPlus
      ∧ causalNullPlus * kreinMinusProjector = causalNullPlus
      ∧ kreinMinusProjector * causalNullMinus = causalNullMinus
      ∧ causalNullMinus * kreinPlusProjector = causalNullMinus
      ∧ kreinMinusProjector * causalNullPlus = 0
      ∧ causalNullPlus * kreinPlusProjector = 0
      ∧ kreinPlusProjector * causalNullMinus = 0
      ∧ causalNullMinus * kreinMinusProjector = 0 := by
  exact ⟨kreinPlusProjector_mul_causalNullPlus, causalNullPlus_mul_kreinMinusProjector,
    kreinMinusProjector_mul_causalNullMinus, causalNullMinus_mul_kreinPlusProjector,
    kreinMinusProjector_mul_causalNullPlus, causalNullPlus_mul_kreinPlusProjector,
    kreinPlusProjector_mul_causalNullMinus, causalNullMinus_mul_kreinMinusProjector⟩

/-! ## Finite dilation shadow -/

/-- The finite inner derivation generated by the Krein involution. -/
@[rep_depth krein]
noncomputable def finiteDilatonDerivation (A : Alg) : Alg :=
  (1 / 2 : ℝ) • (splitQuaternionK * A - A * splitQuaternionK)

@[rep_depth krein]
theorem splitQuaternionK_eq_projector_diff :
    splitQuaternionK = kreinPlusProjector - kreinMinusProjector := by
  simp [kreinPlusProjector, kreinMinusProjector, splitQuaternionK, sub_eq_add_neg]
  module

@[rep_depth krein]
theorem splitQuaternionK_mul_causalNullPlus :
    splitQuaternionK * causalNullPlus = causalNullPlus := by
  rw [splitQuaternionK_eq_projector_diff]
  simp [sub_mul, kreinPlusProjector_mul_causalNullPlus,
    kreinMinusProjector_mul_causalNullPlus]

@[rep_depth krein]
theorem causalNullPlus_mul_splitQuaternionK :
    causalNullPlus * splitQuaternionK = -causalNullPlus := by
  rw [splitQuaternionK_eq_projector_diff]
  simp [mul_sub, causalNullPlus_mul_kreinPlusProjector,
    causalNullPlus_mul_kreinMinusProjector]

@[rep_depth krein]
theorem splitQuaternionK_mul_causalNullMinus :
    splitQuaternionK * causalNullMinus = -causalNullMinus := by
  rw [splitQuaternionK_eq_projector_diff]
  simp [sub_mul, kreinPlusProjector_mul_causalNullMinus,
    kreinMinusProjector_mul_causalNullMinus]

@[rep_depth krein]
theorem causalNullMinus_mul_splitQuaternionK :
    causalNullMinus * splitQuaternionK = causalNullMinus := by
  rw [splitQuaternionK_eq_projector_diff]
  simp [mul_sub, causalNullMinus_mul_kreinPlusProjector,
    causalNullMinus_mul_kreinMinusProjector]

@[rep_depth krein]
theorem finite_dilaton_action_on_nulls :
    finiteDilatonDerivation causalNullPlus = causalNullPlus
      ∧ finiteDilatonDerivation causalNullMinus = -causalNullMinus := by
  refine ⟨?_, ?_⟩
  · simp [finiteDilatonDerivation, splitQuaternionK_mul_causalNullPlus,
      causalNullPlus_mul_splitQuaternionK]
    module
  · simp [finiteDilatonDerivation, splitQuaternionK_mul_causalNullMinus,
      causalNullMinus_mul_splitQuaternionK]
    module

/-- Finite `K`-squeeze written in the Krein projector basis. -/
@[rep_depth krein]
noncomputable def kreinSqueeze (σ : ℝ) : Alg :=
  Real.exp σ • kreinPlusProjector + Real.exp (-σ) • kreinMinusProjector

@[rep_depth krein]
theorem krein_squeeze_projector_decomposition (σ : ℝ) :
    kreinSqueeze σ =
      Real.exp σ • kreinPlusProjector + Real.exp (-σ) • kreinMinusProjector := by
  rfl

@[rep_depth krein]
theorem krein_squeeze_left_right_null_scaling (σ : ℝ) :
    kreinSqueeze σ * causalNullPlus = Real.exp σ • causalNullPlus
      ∧ kreinSqueeze σ * causalNullMinus = Real.exp (-σ) • causalNullMinus
      ∧ causalNullPlus * kreinSqueeze (-σ) = Real.exp σ • causalNullPlus
      ∧ causalNullMinus * kreinSqueeze (-σ) = Real.exp (-σ) • causalNullMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [kreinSqueeze, add_mul, kreinPlusProjector_mul_causalNullPlus,
      kreinMinusProjector_mul_causalNullPlus]
  · simp [kreinSqueeze, add_mul, kreinPlusProjector_mul_causalNullMinus,
      kreinMinusProjector_mul_causalNullMinus]
  · simp [kreinSqueeze, mul_add, causalNullPlus_mul_kreinPlusProjector,
      causalNullPlus_mul_kreinMinusProjector]
  · simp [kreinSqueeze, mul_add, causalNullMinus_mul_kreinPlusProjector,
      causalNullMinus_mul_kreinMinusProjector]

@[rep_depth krein]
theorem krein_squeeze_half_conjugates_nulls (σ : ℝ) :
    kreinSqueeze (σ / 2) * causalNullPlus * kreinSqueeze (-(σ / 2)) =
        Real.exp σ • causalNullPlus
      ∧ kreinSqueeze (σ / 2) * causalNullMinus * kreinSqueeze (-(σ / 2)) =
        Real.exp (-σ) • causalNullMinus := by
  refine ⟨?_, ?_⟩
  · have hL := (krein_squeeze_left_right_null_scaling (σ / 2)).1
    have hR := (krein_squeeze_left_right_null_scaling (σ / 2)).2.2.1
    calc
      kreinSqueeze (σ / 2) * causalNullPlus * kreinSqueeze (-(σ / 2))
          = (Real.exp (σ / 2) • causalNullPlus) * kreinSqueeze (-(σ / 2)) := by
              rw [hL]
      _ = Real.exp (σ / 2) • (causalNullPlus * kreinSqueeze (-(σ / 2))) := by
            rw [smul_mul_assoc]
      _ = Real.exp (σ / 2) • (Real.exp (σ / 2) • causalNullPlus) := by
            rw [hR]
      _ = Real.exp σ • causalNullPlus := by
            rw [smul_smul, ← Real.exp_add]
            ring_nf
  · have hL := (krein_squeeze_left_right_null_scaling (σ / 2)).2.1
    have hR := (krein_squeeze_left_right_null_scaling (σ / 2)).2.2.2
    calc
      kreinSqueeze (σ / 2) * causalNullMinus * kreinSqueeze (-(σ / 2))
          = (Real.exp (-(σ / 2)) • causalNullMinus) * kreinSqueeze (-(σ / 2)) := by
              rw [hL]
      _ = Real.exp (-(σ / 2)) • (causalNullMinus * kreinSqueeze (-(σ / 2))) := by
            rw [smul_mul_assoc]
      _ = Real.exp (-(σ / 2)) • (Real.exp (-(σ / 2)) • causalNullMinus) := by
            rw [hR]
      _ = Real.exp (-σ) • causalNullMinus := by
            rw [smul_smul, ← Real.exp_add]
            ring_nf

/-! ## Off-diagonal mass bridge -/

/-- Off-diagonal mass bridge: it anticommutes with the Krein involution. -/
@[rep_depth krein]
noncomputable def massBridgeBeta : Alg :=
  splitQuaternionJ

@[rep_depth krein]
noncomputable def massTerm (m : ℝ) : Alg :=
  m • massBridgeBeta

@[rep_depth krein]
theorem mass_bridge_beta_laws :
    massBridgeBeta * massBridgeBeta = (1 : Alg)
      ∧ splitQuaternionK * massBridgeBeta + massBridgeBeta * splitQuaternionK = 0
      ∧ massBridgeBeta * kreinPlusProjector = kreinMinusProjector * massBridgeBeta
      ∧ massBridgeBeta * kreinMinusProjector = kreinPlusProjector * massBridgeBeta := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [massBridgeBeta, splitQuaternionJ]
  · simp [massBridgeBeta, splitQuaternionJ, splitQuaternionK]
  · simp [massBridgeBeta, kreinPlusProjector, kreinMinusProjector, splitQuaternionJ,
      splitQuaternionK, sub_eq_add_neg, mul_add, add_mul, smul_add]
  · simp [massBridgeBeta, kreinPlusProjector, kreinMinusProjector, splitQuaternionJ,
      splitQuaternionK, sub_eq_add_neg, mul_add, add_mul, smul_add]

@[rep_depth krein]
theorem mass_term_laws (m : ℝ) :
    splitQuaternionK * massTerm m + massTerm m * splitQuaternionK = 0
      ∧ massTerm m * kreinPlusProjector = kreinMinusProjector * massTerm m
      ∧ massTerm m * kreinMinusProjector = kreinPlusProjector * massTerm m := by
  refine ⟨?_, ?_, ?_⟩
  · simp [massTerm, massBridgeBeta, splitQuaternionJ, splitQuaternionK]
  · simp [massTerm, mass_bridge_beta_laws.2.2.1]
  · simp [massTerm, mass_bridge_beta_laws.2.2.2]

/-! ## Null first-order wave symbol -/

/--
Finite algebraic shadow of the massless null Dirac operator
`ℓ₊ ∂₊ + ℓ₋ ∂₋`, with the two derivative directions represented by commuting
real scalar symbols.
-/
@[rep_depth krein]
noncomputable def masslessNullDiracSymbol (dPlus dMinus : ℝ) : Alg :=
  dPlus • causalNullPlus + dMinus • causalNullMinus

/--
Squaring the finite null Dirac symbol collapses to the scalar wave symbol
`∂₊∂₋`, because the nilpotent diagonal terms vanish and the two closed null
loops sum to the identity.
-/
@[rep_depth krein]
theorem massless_null_dirac_symbol_sq (dPlus dMinus : ℝ) :
    masslessNullDiracSymbol dPlus dMinus * masslessNullDiracSymbol dPlus dMinus =
      (dPlus * dMinus) • (1 : Alg) := by
  simp [masslessNullDiracSymbol, mul_add, add_mul, causalNullPlus_sq,
    causalNullMinus_sq, causalNullPlus_mul_causalNullMinus,
    causalNullMinus_mul_causalNullPlus]
  rw [smul_smul, smul_smul, mul_comm dMinus dPlus, ← smul_add, add_comm,
    kreinProjector_sum]

/--
Compressed local closure packet for the fixed causal-cone convention.
-/
structure LocalCausalConeClosure : Prop where
  split_quaternion_basis :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionJ * splitQuaternionJ = (1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ splitQuaternionI * splitQuaternionJ = splitQuaternionK
      ∧ splitQuaternionJ * splitQuaternionI = -splitQuaternionK
  matrix_basis :
    Eminus * Eminus = -(1 : Mat2)
      ∧ J1 * J1 = (1 : Mat2)
      ∧ Eplus * Eplus = (1 : Mat2)
      ∧ Eminus * J1 = Eplus
      ∧ J1 * Eminus = -Eplus
  matrix_projectors :
    matrixKreinPlusProjector = !![(1 : ℝ), 0; 0, 0]
      ∧ matrixKreinMinusProjector = !![0, 0; 0, (1 : ℝ)]
  matrix_nulls :
    matrixCausalNullPlus = !![(0 : ℝ), 1; 0, 0]
      ∧ matrixCausalNullMinus = !![0, 0; (1 : ℝ), 0]
  matrix_null_closure :
    matrixCausalNullPlus * matrixCausalNullPlus = 0
      ∧ matrixCausalNullMinus * matrixCausalNullMinus = 0
      ∧ matrixCausalNullPlus * matrixCausalNullMinus = matrixKreinPlusProjector
      ∧ matrixCausalNullMinus * matrixCausalNullPlus = matrixKreinMinusProjector
      ∧ matrixCausalNullPlus * matrixCausalNullMinus
          + matrixCausalNullMinus * matrixCausalNullPlus = (1 : Mat2)
      ∧ matrixCausalNullPlus * matrixCausalNullMinus
          - matrixCausalNullMinus * matrixCausalNullPlus = Eplus
  matrix_projectors_noncentral :
    matrixKreinPlusProjector * matrixCausalNullPlus
        ≠ matrixCausalNullPlus * matrixKreinPlusProjector
      ∧ matrixKreinMinusProjector * matrixCausalNullMinus
        ≠ matrixCausalNullMinus * matrixKreinMinusProjector
  matrix_projector_spinor_readout :
    ∀ ψ : Spinor2,
      matrixAct matrixKreinPlusProjector ψ 0 = ψ 0
        ∧ matrixAct matrixKreinPlusProjector ψ 1 = 0
        ∧ matrixAct matrixKreinMinusProjector ψ 0 = 0
        ∧ matrixAct matrixKreinMinusProjector ψ 1 = ψ 1
  matrix_null_spinor_readout :
    ∀ ψ : Spinor2,
      matrixAct matrixCausalNullPlus ψ 0 = ψ 1
        ∧ matrixAct matrixCausalNullPlus ψ 1 = 0
        ∧ matrixAct matrixCausalNullMinus ψ 0 = 0
        ∧ matrixAct matrixCausalNullMinus ψ 1 = ψ 0
  krein_projectors :
    kreinPlusProjector * kreinPlusProjector = kreinPlusProjector
      ∧ kreinMinusProjector * kreinMinusProjector = kreinMinusProjector
      ∧ kreinPlusProjector * kreinMinusProjector = 0
      ∧ kreinMinusProjector * kreinPlusProjector = 0
      ∧ kreinPlusProjector + kreinMinusProjector = (1 : Alg)
  null_closure :
    causalNullPlus * causalNullPlus = 0
      ∧ causalNullMinus * causalNullMinus = 0
      ∧ causalNullPlus * causalNullMinus = kreinPlusProjector
      ∧ causalNullMinus * causalNullPlus = kreinMinusProjector
      ∧ causalNullPlus * causalNullMinus + causalNullMinus * causalNullPlus = (1 : Alg)
      ∧ causalNullPlus * causalNullMinus - causalNullMinus * causalNullPlus =
          splitQuaternionK
  sector_hopping :
    kreinPlusProjector * causalNullPlus = causalNullPlus
      ∧ causalNullPlus * kreinMinusProjector = causalNullPlus
      ∧ kreinMinusProjector * causalNullMinus = causalNullMinus
      ∧ causalNullMinus * kreinPlusProjector = causalNullMinus
      ∧ kreinMinusProjector * causalNullPlus = 0
      ∧ causalNullPlus * kreinPlusProjector = 0
      ∧ kreinPlusProjector * causalNullMinus = 0
      ∧ causalNullMinus * kreinMinusProjector = 0
  finite_dilaton :
    finiteDilatonDerivation causalNullPlus = causalNullPlus
      ∧ finiteDilatonDerivation causalNullMinus = -causalNullMinus
  squeeze_scaling :
    ∀ σ : ℝ,
      kreinSqueeze σ * causalNullPlus = Real.exp σ • causalNullPlus
        ∧ kreinSqueeze σ * causalNullMinus = Real.exp (-σ) • causalNullMinus
        ∧ causalNullPlus * kreinSqueeze (-σ) = Real.exp σ • causalNullPlus
        ∧ causalNullMinus * kreinSqueeze (-σ) = Real.exp (-σ) • causalNullMinus
  squeeze_conjugation :
    ∀ σ : ℝ,
      kreinSqueeze (σ / 2) * causalNullPlus * kreinSqueeze (-(σ / 2)) =
          Real.exp σ • causalNullPlus
        ∧ kreinSqueeze (σ / 2) * causalNullMinus * kreinSqueeze (-(σ / 2)) =
          Real.exp (-σ) • causalNullMinus
  mass_bridge :
    massBridgeBeta * massBridgeBeta = (1 : Alg)
      ∧ splitQuaternionK * massBridgeBeta + massBridgeBeta * splitQuaternionK = 0
      ∧ massBridgeBeta * kreinPlusProjector = kreinMinusProjector * massBridgeBeta
      ∧ massBridgeBeta * kreinMinusProjector = kreinPlusProjector * massBridgeBeta
  null_dirac_square :
    ∀ dPlus dMinus : ℝ,
      masslessNullDiracSymbol dPlus dMinus * masslessNullDiracSymbol dPlus dMinus =
        (dPlus * dMinus) • (1 : Alg)

@[rep_depth krein]
theorem localCausalConeClosure : LocalCausalConeClosure where
  split_quaternion_basis := split_quaternion_basis_laws
  matrix_basis := matrix_split_quaternion_basis_laws
  matrix_projectors := matrix_krein_projectors_explicit
  matrix_nulls := matrix_causal_nulls_explicit
  matrix_null_closure := matrix_causal_null_closure_laws
  matrix_projectors_noncentral := matrix_krein_projectors_noncentral
  matrix_projector_spinor_readout := matrix_projector_spinor_action
  matrix_null_spinor_readout := matrix_null_spinor_action
  krein_projectors := krein_projector_laws
  null_closure := causal_null_closure_laws
  sector_hopping := sector_hopping_laws
  finite_dilaton := finite_dilaton_action_on_nulls
  squeeze_scaling := krein_squeeze_left_right_null_scaling
  squeeze_conjugation := krein_squeeze_half_conjugates_nulls
  mass_bridge := mass_bridge_beta_laws
  null_dirac_square := massless_null_dirac_symbol_sq

/--
Compressed readback of the final finite causal-cone identities.

This theorem is intentionally local: it records the split-quaternion phase
axis, Krein involution, null projectors, finite squeeze, and off-diagonal mass
bridge.  It does not assert any global physical necessity or current/conformal
algebra construction.
-/
@[rep_depth krein]
theorem final_local_causal_cone_identities :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ causalNullPlus * causalNullPlus = 0
      ∧ causalNullMinus * causalNullMinus = 0
      ∧ kreinPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + splitQuaternionK)
      ∧ kreinMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - splitQuaternionK)
      ∧ causalNullPlus * causalNullMinus = kreinPlusProjector
      ∧ causalNullMinus * causalNullPlus = kreinMinusProjector
      ∧ causalNullPlus * causalNullMinus + causalNullMinus * causalNullPlus = (1 : Alg)
      ∧ causalNullPlus * causalNullMinus - causalNullMinus * causalNullPlus =
          splitQuaternionK
      ∧ (∀ σ : ℝ,
          kreinSqueeze σ =
            Real.exp σ • kreinPlusProjector + Real.exp (-σ) • kreinMinusProjector)
      ∧ splitQuaternionK * massBridgeBeta + massBridgeBeta * splitQuaternionK = 0 := by
  rcases split_quaternion_basis_laws with ⟨hI, _hJ, hK, _hIJ, _hJI⟩
  rcases causal_null_closure_laws with ⟨hNp, hNm, hpm, hmp, hsum, hdiff⟩
  rcases mass_bridge_beta_laws with ⟨_hβsq, hβanti, _hβp, _hβm⟩
  exact ⟨hI, hK, hNp, hNm, rfl, rfl, hpm, hmp, hsum, hdiff,
    krein_squeeze_projector_decomposition, hβanti⟩

end SplitQ11CausalCone
