import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Attention.AttentionCurvatureHolonomy

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The Dirac grading operator G = diag(1, -1). -/
def G_grading : Mat2R :=
  !![1,  0;
     0, -1]

/-- The off-diagonal chiral bipolar operator: C(M) = !![0, M₀₁; M₁₀, 0]. -/
def chiral_bipolar (M : Mat2R) : Mat2R :=
  !![0, M 0 1;
     M 1 0, 0]

/-- The diagonal dissipative core: diag(M) = !![M₀₀, 0; 0, M₁₁]. -/
def diag_core (M : Mat2R) : Mat2R :=
  !![M 0 0, 0;
     0, M 1 1]

/-- The Lie bracket (matrix commutator): [A, B] = A * B - B * A. -/
def commutator (A B : Mat2R) : Mat2R :=
  A * B - B * A

/-!
# Archetype 906: Cross-Attention Symplectic Area 2-Form
The canonical symplectic 2-form evaluated on the off-diagonal cross-attentions
of two distinct layers:
  ω(M₁, M₂) = (M₁)₀₁ * (M₂)₁₀ - (M₂)₀₁ * (M₁)₁₀.
-/

/-- The symplectic area 2-form of two attention matrices. -/
def symplectic_area (M₁ M₂ : Mat2R) : ℝ :=
  M₁ 0 1 * M₂ 1 0 - M₂ 0 1 * M₁ 1 0

/-- Master Theorem 1: Antisymmetry of the Symplectic Area.
    ω(M₁, M₂) = - ω(M₂, M₁). -/
theorem symplectic_area_antisymm (M₁ M₂ : Mat2R) :
    symplectic_area M₁ M₂ = - symplectic_area M₂ M₁ := by
  dsimp [symplectic_area]
  ring

/-!
# Archetype 907: Chiral Commutator Identity
The commutator of two pure chiral channels collapses strictly onto the
Dirac grading operator G:
  [C(M₁), C(M₂)] = ω(M₁, M₂) • G.
-/

/-- Master Theorem 2: The Curvature-Grading Collapse.
    The commutator of two chiral attention layers is identically equal to the
    symplectic area scaled by the grading operator G. -/
theorem chiral_commutator_eq_symplectic_grading (M₁ M₂ : Mat2R) :
    commutator (chiral_bipolar M₁) (chiral_bipolar M₂) =
    (symplectic_area M₁ M₂) • G_grading := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [commutator, chiral_bipolar, G_grading, symplectic_area, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    simp [Matrix.smul_apply]
    ring
  }

/-- Master Theorem 3: Vanishing Trace of the Latent Curvature.
    Because [C₁, C₂] ∝ G, its trace is identically zero.
    Curvature produces zero net entropy generation. -/
theorem chiral_curvature_traceless (M₁ M₂ : Mat2R) :
    Matrix.trace (commutator (chiral_bipolar M₁) (chiral_bipolar M₂)) = 0 := by
  rw [chiral_commutator_eq_symplectic_grading]
  dsimp [Matrix.trace, G_grading]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons, smul_apply]
  ring

/-!
# Archetype 908: Scalar Holonomy Invariant
The square of the latent curvature tensor is a pure scalar proportional to 𝕀₂:
  [C₁, C₂]² = ω(M₁, M₂)² • 𝕀₂.
-/

/-- Master Theorem 4: The Holonomy Square Invariant.
    Squaring the curvature commutator yields an exact scalar multiple of the identity. -/
theorem chiral_curvature_sq_scalar (M₁ M₂ : Mat2R) :
    (commutator (chiral_bipolar M₁) (chiral_bipolar M₂)) *
    (commutator (chiral_bipolar M₁) (chiral_bipolar M₂)) =
    ((symplectic_area M₁ M₂) ^ 2) • (1 : Mat2R) := by
  rw [chiral_commutator_eq_symplectic_grading]
  have h_smul : ((symplectic_area M₁ M₂) • G_grading) * ((symplectic_area M₁ M₂) • G_grading) =
      ((symplectic_area M₁ M₂) * (symplectic_area M₁ M₂)) • (G_grading * G_grading) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h_smul]
  have h_G_sq : G_grading * G_grading = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      dsimp [G_grading, Matrix.mul_apply]
      simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
      simp [Matrix.one_apply]
      ring
    }
  rw [h_G_sq]
  congr 1
  ring

/-!
# Archetype 909: Flatness Condition (Layer Alignment)
Two consecutive chiral attention channels commute IF AND ONLY IF their
cross-attention coefficients are collinear (zero symplectic area).
-/

/-- Master Theorem 5: The Symplectic Flatness Criterion.
    [C(M₁), C(M₂)] = 0 ↔ ω(M₁, M₂) = 0. -/
theorem latent_space_flat_iff_zero_area (M₁ M₂ : Mat2R) :
    commutator (chiral_bipolar M₁) (chiral_bipolar M₂) = 0 ↔
    symplectic_area M₁ M₂ = 0 := by
  rw [chiral_commutator_eq_symplectic_grading]
  constructor
  · intro h
    have h00 : ((symplectic_area M₁ M₂) • G_grading) 0 0 = 0 := by rw [h]; rfl
    dsimp [G_grading, smul_apply] at h00
    linarith
  · intro h
    rw [h, zero_smul]

/-!
# Archetype 910: Full Metriplectic Commutator Decomposition
When we commute the full attention matrices M₁ and M₂, the Lie bracket
decomposes into:
  [M₁, M₂] = [diag₁, diag₂] + [C₁, C₂] + ([diag₁, C₂] + [C₁, diag₂])
Since diagonal matrices commute identically ([diag₁, diag₂] = 0),
the diagonal part of the full commutator is PURELY the curvature ω • G!
-/

/-- Master Theorem 6: Diagonal Commutators Vanish Identically.
    The dissipative heat sinks of any two layers commute unconditionally. -/
theorem diag_cores_commute (M₁ M₂ : Mat2R) :
    commutator (diag_core M₁) (diag_core M₂) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [commutator, diag_core, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    ring
  }

/-- Master Theorem 7: Complete Commutator Decomposition.
    The full commutator decomposes into the chiral curvature plus the
    dissipation-transport cross-commutators. -/
theorem full_attention_commutator_split (M₁ M₂ : Mat2R) :
    commutator M₁ M₂ =
    (symplectic_area M₁ M₂) • G_grading +
    (commutator (diag_core M₁) (chiral_bipolar M₂) +
     commutator (chiral_bipolar M₁) (diag_core M₂)) := by
  have h_split1 : M₁ = diag_core M₁ + chiral_bipolar M₁ := by
    ext i j; fin_cases i <;> fin_cases j <;> { dsimp [diag_core, chiral_bipolar]; ring }
  have h_split2 : M₂ = diag_core M₂ + chiral_bipolar M₂ := by
    ext i j; fin_cases i <;> fin_cases j <;> { dsimp [diag_core, chiral_bipolar]; ring }
  nth_rw 1 [h_split1]
  nth_rw 1 [h_split2]
  dsimp [commutator]
  have h_alg : (diag_core M₁ + chiral_bipolar M₁) * (diag_core M₂ + chiral_bipolar M₂) -
               (diag_core M₂ + chiral_bipolar M₂) * (diag_core M₁ + chiral_bipolar M₁) =
               (diag_core M₁ * diag_core M₂ - diag_core M₂ * diag_core M₁) +
               (chiral_bipolar M₁ * chiral_bipolar M₂ - chiral_bipolar M₂ * chiral_bipolar M₁) +
               ((diag_core M₁ * chiral_bipolar M₂ - chiral_bipolar M₂ * diag_core M₁) +
                (chiral_bipolar M₁ * diag_core M₂ - diag_core M₂ * chiral_bipolar M₁)) := by
    ext i j; fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    }
  rw [h_alg]
  have h_diag_comm : diag_core M₁ * diag_core M₂ - diag_core M₂ * diag_core M₁ = 0 :=
    diag_cores_commute M₁ M₂
  rw [h_diag_comm, zero_add]
  have h_chiral_comm : chiral_bipolar M₁ * chiral_bipolar M₂ - chiral_bipolar M₂ * chiral_bipolar M₁ =
      (symplectic_area M₁ M₂) • G_grading :=
    chiral_commutator_eq_symplectic_grading M₁ M₂
  rw [h_chiral_comm]
  rfl

end InfoGeometry.Attention.AttentionCurvatureHolonomy
