import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Attention.SymplecticDefectInvariance

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The canonical symplectic matrix J = !![0, 1; -1, 0]. -/
def J_symp : Mat2R :=
  !![0,  1;
     -1, 0]

/-- The Dirac grading operator G = !![1, 0; 0, -1]. -/
def G_grading : Mat2R :=
  !![1,  0;
     0, -1]

/-- The symmetric cross-attention generator C_sym = !![0, 1; 1, 0]. -/
def C_symm : Mat2R :=
  !![0, 1;
     1, 0]

/-- The 2x2 identity matrix. -/
def I_2 : Mat2R :=
  (1 : Mat2R)

/-- The Frobenius / Killing-Cartan inner product on Mat_{2x2}(ℝ): ⟨A, B⟩ = tr(Aᵀ * B). -/
def frobenius_inner (A B : Mat2R) : ℝ :=
  Matrix.trace (Aᵀ * B)

/-!
# Archetype 913: The Fundamental Symplectic Defect Identity
For ANY real 2x2 matrix X, the failure to be infinitesimal symplectic evaluates
identically to the trace of X scaled by the symplectic matrix J:
  Xᵀ * J + J * X = tr(X) • J.
-/

/-- Master Theorem 1: The Fundamental Symplectic Defect Identity. -/
theorem transpose_mul_J_add_J_mul (X : Mat2R) :
    Xᵀ * J_symp + J_symp * X = (Matrix.trace X) • J_symp := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [J_symp, Matrix.trace, Matrix.mul_apply, transpose_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons, smul_apply]
    ring
  }

/-!
# Archetype 914: The 2D Symplectic-Traceless Equivalence Theorem
In 2 dimensions, being an infinitesimal symplectic transformation (𝔰𝔭(2, ℝ))
is mathematically identical to being traceless (𝔰𝔩₂(ℝ)):
  Xᵀ * J + J * X = 0 ↔ tr(X) = 0.
-/

/-- Master Theorem 2: Equivalence of Symplectic and Traceless Conditions in 2D. -/
theorem traceless_iff_infinitesimal_symplectic (X : Mat2R) :
    Xᵀ * J_symp + J_symp * X = 0 ↔ Matrix.trace X = 0 := by
  rw [transpose_mul_J_add_J_mul]
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp only [J_symp, smul_apply, cons_val_zero, cons_val_one, head_cons, mul_one] at h01
    simpa using h01
  · intro h
    rw [h, zero_smul]

/-!
# Archetype 915: Traceless Symplectic Canonical Projection
Subtracting half the trace times the identity projects any matrix into 𝔰𝔭(2, ℝ).
-/

/-- The canonical projection of a matrix onto its traceless / symplectic component. -/
noncomputable def traceless_proj (X : Mat2R) : Mat2R :=
  X - ((1 / 2 : ℝ) * Matrix.trace X) • I_2

/-- Master Theorem 3: The Traceless Projection is Strictly Infinitesimal Symplectic. -/
theorem traceless_proj_is_symplectic (X : Mat2R) :
    (traceless_proj X)ᵀ * J_symp + J_symp * (traceless_proj X) = 0 := by
  rw [traceless_iff_infinitesimal_symplectic]
  dsimp [Matrix.trace, traceless_proj, I_2]
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
             Matrix.one_apply_eq, Matrix.one_apply_ne,
             cons_val_zero, cons_val_one, head_cons]
  ring

/-!
# Archetype 916: 4-Component Operator Tetrad Decomposition
Every matrix M decomposes uniquely into:
  M = c₀ • 𝕀₂ + c₁ • G + c₂ • C_sym + c₃ • J
where:
  - c₀ = (1/2) * (M₀₀ + M₁₁) = (1/2) * tr(M)  (Dissipative Entropy Trace)
  - c₁ = (1/2) * (M₀₀ - M₁₁)                 (Longitudinal Grading Dilation)
  - c₂ = (1/2) * (M₀₁ + M₁₀)                 (Dirac Mass Transport)
  - c₃ = (1/2) * (M₀₁ - M₁₀)                 (Symplectic Rotation Phase)
-/

/-- Master Theorem 4: Exact Operator Tetrad Reconstruction. -/
theorem operator_tetrad_decomposition (M : Mat2R) :
    let c0 := (1 / 2 : ℝ) * (M 0 0 + M 1 1)
    let c1 := (1 / 2 : ℝ) * (M 0 0 - M 1 1)
    let c2 := (1 / 2 : ℝ) * (M 0 1 + M 1 0)
    let c3 := (1 / 2 : ℝ) * (M 0 1 - M 1 0)
    M = c0 • I_2 + c1 • G_grading + c2 • C_symm + c3 • J_symp := by
  intro c0 c1 c2 c3
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [c0, c1, c2, c3, I_2, G_grading, C_symm, J_symp]
    ring
  }

/-!
# Archetype 917: Complete Frobenius Orthogonality of the Tetrad
The 4 basis operators {𝕀₂, G, C_sym, J} are mutually pairwise orthogonal
under the Frobenius trace inner product: ⟨A, B⟩ = tr(Aᵀ B) = 0 for all A ≠ B.
-/

/-- Master Theorem 5: Mutual Orthogonality of the Operator Tetrad. -/
theorem tetrad_pairwise_orthogonal :
    frobenius_inner I_2 G_grading = 0 ∧
    frobenius_inner I_2 C_symm = 0 ∧
    frobenius_inner I_2 J_symp = 0 ∧
    frobenius_inner G_grading C_symm = 0 ∧
    frobenius_inner G_grading J_symp = 0 ∧
    frobenius_inner C_symm J_symp = 0 := by
  dsimp [frobenius_inner, I_2, G_grading, C_symm, J_symp, Matrix.trace]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    simp only [Fin.sum_univ_two, Matrix.mul_apply, transpose_apply,
               Matrix.one_apply_eq, Matrix.one_apply_ne,
               cons_val_zero, cons_val_one, head_cons]
    ring
  }

/-- Master Theorem 6: The Norms of the Tetrad Elements.
    ⟨𝕀₂, 𝕀₂⟩ = 2, ⟨G, G⟩ = 2, ⟨C_sym, C_sym⟩ = 2, ⟨J, J⟩ = 2. -/
theorem tetrad_norms_squared :
    frobenius_inner I_2 I_2 = 2 ∧
    frobenius_inner G_grading G_grading = 2 ∧
    frobenius_inner C_symm C_symm = 2 ∧
    frobenius_inner J_symp J_symp = 2 := by
  dsimp [frobenius_inner, I_2, G_grading, C_symm, J_symp, Matrix.trace]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    simp only [Fin.sum_univ_two, Matrix.mul_apply, transpose_apply,
               Matrix.one_apply_eq, Matrix.one_apply_ne,
               cons_val_zero, cons_val_one, head_cons]
    ring
  }

end InfoGeometry.Attention.SymplecticDefectInvariance
