import InfoGeometry.Canonical.ChiralCausalCone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Two-sheet chiral factor times three-colour Weyl factor

This module keeps the finite operator realization separate from the
nonassociative split-octonion carrier.  The sheet factor is `M₂(ℂ)` and the
colour factor is the finite Weyl pair in `M₃(ℂ)`; their tensor product acts on
six states.
-/

noncomputable section
namespace TwoSheetThreeColorWeyl

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev SixIndex := Fin 2 × Fin 3
abbrev M6C := Matrix SixIndex SixIndex ℂ

local notation A "⊗ₖ" B => Matrix.kroneckerMap (fun a b : ℂ => a * b) A B

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)

def sheetPlus : M2C := !![1, 0; 0, 0]
def sheetMinus : M2C := !![0, 0; 0, 1]
def sheetFlip : M2C := !![0, 1; 1, 0]
def sheetGamma : M2C := sheetPlus - sheetMinus
def sheetRaise : M2C := !![0, 1; 0, 0]
def sheetLower : M2C := !![0, 0; 1, 0]

def colorShift : M3C := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
def colorClock (ω : ℂ) : M3C := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
def colorReflection : M3C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

def tensor (A : M2C) (B : M3C) : M6C :=
  A ⊗ₖ B

theorem omega_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  calc
    ω ^ 3 = ω * (ω ^ 2 + ω + 1) - (ω ^ 2 + ω) := by ring
    _ = 1 := by
      have h : ω ^ 2 + ω = -1 := by linear_combination hω
      rw [h]
      ring

theorem omega_sum (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : 1 + ω + ω ^ 2 = 0 := by
  simpa [add_comm, add_left_comm, add_assoc] using hω

theorem omega_mul_three (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω * ω * ω = 1 := by
  simpa [pow_succ] using omega_cube ω hω

theorem omega_mul_six (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω * ω * (ω * ω) * (ω * ω) = 1 := by
  calc
    ω * ω * (ω * ω) * (ω * ω) = (ω * ω * ω) ^ 2 := by ring
    _ = 1 := by rw [omega_mul_three ω hω]; norm_num

theorem omega_mul_square (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω * ω ^ 2 = 1 := by
  simpa [pow_two, mul_assoc] using omega_mul_three ω hω

theorem omega_square_mul (ω : ℂ) : ω ^ 2 = ω * ω := by ring

theorem tensor_mul (A C : M2C) (B D : M3C) :
    tensor A B * tensor C D = tensor (A * C) (B * D) := by
  unfold tensor
  exact (Matrix.mul_kronecker_mul A C B D).symm

theorem sheet_projectors :
    sheetPlus * sheetPlus = sheetPlus ∧
    sheetMinus * sheetMinus = sheetMinus ∧
    sheetPlus * sheetMinus = 0 ∧
    sheetMinus * sheetPlus = 0 ∧
    sheetPlus + sheetMinus = (1 : M2C) := by
  repeat' constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sheetPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sheetMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sheetPlus, sheetMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sheetPlus, sheetMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sheetPlus, sheetMinus]

theorem sheet_parity :
    sheetGamma * sheetGamma = (1 : M2C) ∧
    sheetFlip * sheetFlip = (1 : M2C) ∧
    sheetFlip * sheetGamma * sheetFlip = -sheetGamma := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetGamma, sheetPlus, sheetMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetGamma, sheetPlus, sheetMinus,
        Matrix.mul_apply, Fin.sum_univ_two]

theorem sheet_CAR :
    sheetRaise * sheetRaise = 0 ∧
    sheetLower * sheetLower = 0 ∧
    sheetRaise * sheetLower + sheetLower * sheetRaise = (1 : M2C) ∧
    sheetRaise * sheetLower - sheetLower * sheetRaise = sheetGamma := by
  repeat' constructor
  all_goals
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetRaise, sheetLower, sheetGamma, sheetPlus, sheetMinus,
        Matrix.mul_apply, Fin.sum_univ_two]

theorem sheet_projector_parity :
    sheetPlus * sheetGamma = sheetPlus ∧
    sheetMinus * sheetGamma = -sheetMinus := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sheetPlus, sheetMinus, sheetGamma, Matrix.mul_apply, Fin.sum_univ_two]

theorem color_weyl (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    colorShift ^ 3 = (1 : M3C) ∧
    colorClock ω ^ 3 = (1 : M3C) ∧
    colorClock ω * colorShift = ω • (colorShift * colorClock ω) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorShift, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorClock, pow_succ, Matrix.mul_apply, Fin.sum_univ_three,
        omega_mul_three ω hω, omega_mul_six ω hω]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorShift, colorClock, Matrix.mul_apply, Fin.sum_univ_three,
        pow_two, omega_mul_three ω hω]
    simpa [mul_assoc] using (omega_mul_three ω hω).symm

theorem color_reflection_relations (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    colorReflection * colorReflection = (1 : M3C) ∧
    colorReflection * colorShift * colorReflection = colorShift ^ 2 ∧
    colorReflection * colorClock ω * colorReflection = colorClock ω ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorReflection, Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorReflection, colorShift, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorReflection, colorClock, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
        omega_mul_three ω hω]
    calc
      ω = ω * 1 := by ring
      _ = ω * (ω * ω * ω) := by rw [omega_mul_three ω hω]
      _ = ω * ω * (ω * ω) := by ring

theorem tensor_factor_commute (A : M2C) (B : M3C) :
    tensor A (1 : M3C) * tensor (1 : M2C) B =
      tensor (1 : M2C) B * tensor A (1 : M3C) := by
  simp only [tensor]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp [mul_comm]

@[simp] theorem tensor_one : tensor (1 : M2C) (1 : M3C) = (1 : M6C) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    simp [tensor, Matrix.kroneckerMap_apply]

theorem six_state_relations :
    tensor sheetGamma (1 : M3C) * tensor sheetGamma (1 : M3C) = (1 : M6C) ∧
    tensor sheetFlip (1 : M3C) * tensor sheetFlip (1 : M3C) = (1 : M6C) ∧
    tensor (1 : M2C) colorShift * tensor (1 : M2C) (colorClock ω) =
      tensor (1 : M2C) (colorShift * colorClock ω) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul, sheet_parity.1]
    simpa using tensor_one
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul, sheet_parity.2.1]
    simpa using tensor_one
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul]
    simp

theorem orientation_reversing_relations (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    tensor sheetFlip colorReflection * tensor sheetFlip colorReflection = (1 : M6C) ∧
    tensor sheetFlip colorReflection * tensor (1 : M2C) colorShift *
        tensor sheetFlip colorReflection = tensor (1 : M2C) (colorShift ^ 2) ∧
    tensor sheetFlip colorReflection * tensor (1 : M2C) (colorClock ω) *
        tensor sheetFlip colorReflection = tensor (1 : M2C) (colorClock ω ^ 2) := by
  rcases sheet_parity with ⟨_, hJ, _⟩
  rcases color_reflection_relations ω hω with ⟨hR, hRX, hRZ⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul, hJ, hR]
    exact tensor_one
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_assoc, hJ, hRX, Matrix.one_mul]
  · simp only [tensor]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_assoc, hJ, hRZ, Matrix.one_mul]

theorem commuting_Z2_Z3_actions (A : M2C) (B : M3C) :
    tensor A (1 : M3C) * tensor (1 : M2C) B =
      tensor (1 : M2C) B * tensor A (1 : M3C) :=
  tensor_factor_commute A B

/-- Sheet parity times colour triality. -/
def sixfoldTriality : M6C := tensor sheetGamma colorShift

theorem sixfoldTriality_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    sixfoldTriality ^ 3 = tensor sheetGamma (1 : M3C) := by
  have hX : colorShift ^ 3 = (1 : M3C) := (color_weyl ω hω).1
  have hΓ : sheetGamma * sheetGamma = (1 : M2C) := sheet_parity.1
  calc
    sixfoldTriality ^ 3 =
        tensor (sheetGamma ^ 3) (colorShift ^ 3) := by
      simp [sixfoldTriality, pow_succ, tensor_mul, Matrix.mul_assoc]
    _ = tensor sheetGamma (1 : M3C) := by
      rw [hX]
      simp [pow_succ, hΓ]

theorem sixfoldTriality_sixth (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    sixfoldTriality ^ 6 = (1 : M6C) := by
  calc
    sixfoldTriality ^ 6 = (sixfoldTriality ^ 3) * (sixfoldTriality ^ 3) := by
      rw [← pow_add]
    _ = tensor sheetGamma (1 : M3C) * tensor sheetGamma (1 : M3C) := by
      rw [sixfoldTriality_cube ω hω]
    _ = tensor (sheetGamma * sheetGamma) ((1 : M3C) * 1) :=
      tensor_mul _ _ _ _
    _ = (1 : M6C) := by rw [sheet_parity.1]; simp

theorem sixfoldTriality_sheet_cubes (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    tensor sheetPlus (1 : M3C) * sixfoldTriality ^ 3 =
        tensor sheetPlus (1 : M3C) ∧
    tensor sheetMinus (1 : M3C) * sixfoldTriality ^ 3 =
        -tensor sheetMinus (1 : M3C) := by
  rw [sixfoldTriality_cube ω hω]
  constructor
  · rw [tensor_mul, sheet_projector_parity.1]
    simp
  · rw [tensor_mul, sheet_projector_parity.2]
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [tensor, Matrix.kroneckerMap_apply]

end TwoSheetThreeColorWeyl

end noncomputable section
