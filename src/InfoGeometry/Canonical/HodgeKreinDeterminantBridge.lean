import InfoGeometry.Canonical.DeterminantCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Canonical.ManifoldDegreeCore
import InfoGeometry.Cocycle.MatrixDetExpTrace

/-!
# InfoGeometry.Canonical.HodgeKreinDeterminantBridge

Hodge-Krein-facing determinant bridge.

This file does not reprove the determinant facts. It collects the existing
owner theorems that matter for the Hodge-Krein narrative:

* determinant as signed volume / Jacobian readout;
* Jacobian chain rule and logarithmic volume additivity;
* matrix determinant/exponential trace identity;
* the finite Krein/Fredholm trace defect contract.
-/

namespace InfoGeometry.Canonical.HodgeKreinDeterminantBridge

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Hodge-Krein-facing Jacobian determinant readout on finite real automorphisms. -/
noncomputable abbrev jacobianDet : InfoGeometry.Canonical.Determinant.«GL» ℝ V →* ℝˣ :=
  InfoGeometry.Canonical.Determinant.jacDet ℝ V

/-- Signed-volume / Jacobian chain rule. -/
theorem jacobianDet_mul
    (f g : InfoGeometry.Canonical.Determinant.«GL» ℝ V) :
    jacobianDet (V := V) (f * g) = jacobianDet (V := V) f * jacobianDet (V := V) g :=
  InfoGeometry.Canonical.Determinant.jac_det_comp ℝ V f g

/-- Logarithmic signed-volume additivity. -/
theorem logAbsDet_mul
    (f g : InfoGeometry.Canonical.Determinant.«GL» ℝ V) :
    InfoGeometry.Canonical.Determinant.logAbsDet V (f * g) =
      InfoGeometry.Canonical.Determinant.logAbsDet V f +
        InfoGeometry.Canonical.Determinant.logAbsDet V g :=
  InfoGeometry.Canonical.Determinant.logAbsDet_mul V f g

section MatrixFacts

variable {R : Type*} [CommRing R]
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Transpose invariance of determinant. -/
theorem det_transpose_eq (M : Matrix n n R) :
    Matrix.det Mᵀ = Matrix.det M :=
  Matrix.det_transpose M

/-- Determinant of a diagonal matrix is the product of the diagonal entries. -/
theorem det_diagonal_eq_prod {d : n → R} :
    Matrix.det (Matrix.diagonal d) = ∏ i, d i :=
  Matrix.det_diagonal

/-- Conjugation invariance of determinant by a unit matrix. -/
theorem det_conj_eq_det (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    Matrix.det (M.val * N * M⁻¹.val) = Matrix.det N :=
  Matrix.det_units_conj M N

/-- Adjugate on the right gives the determinant scalar. -/
theorem mul_adjugate_eq_det_smul_one (A : Matrix n n R) :
    A * Matrix.adjugate A = A.det • (1 : Matrix n n R) :=
  Matrix.mul_adjugate A

/-- Adjugate on the left gives the determinant scalar. -/
theorem adjugate_mul_eq_det_smul_one (A : Matrix n n R) :
    Matrix.adjugate A * A = A.det • (1 : Matrix n n R) :=
  Matrix.adjugate_mul A

/-- Determinant of a `2 × 2` matrix in closed form. -/
theorem det_fin_two_eq (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c :=
  Matrix.det_fin_two_of a b c d

/-- Block determinant identity around an invertible lower-right block. -/
theorem det_fromBlocks₂₂_eq
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix m n R) (D : Matrix m m R)
    [Invertible D] :
    Matrix.det (Matrix.fromBlocks A B C D) = Matrix.det D * Matrix.det (A - B * ⅟D * C) :=
  Matrix.det_fromBlocks₂₂ A B C D

/-- Weinstein–Aronszajn / Sylvester determinant identity. -/
theorem det_one_add_mul_comm_eq
    (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (1 + A * B) = Matrix.det (1 + B * A) :=
  Matrix.det_one_add_mul_comm A B

/-- A nilpotent 2x2 shear has determinant 1 when shifted by identity (measure preservation). -/
theorem det_one_add_nilpotent_2x2 (a : R) :
    Matrix.det (1 + !![0, a; 0, 0]) = 1 := by
  simp [Matrix.det_fin_two]

/-- Trace-determinant sum identity for 2x2 real matrices. -/
theorem det_add_trace_relation_2x2 (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.det (A + B) = Matrix.det A + Matrix.det B + Matrix.trace A * Matrix.trace B - Matrix.trace (A * B) := by
  simp [Matrix.det_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end MatrixFacts

/-- Determinant/trace law for arbitrary complex matrices. -/
theorem det_exp_eq_exp_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A) :=
  InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace A

/-- Determinant/trace law for arbitrary real matrices. -/
theorem det_exp_eq_exp_trace_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A) :=
  InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real A

/-- Finite Krein/Fredholm trace defect readout. -/
theorem kreinFredholm_determinant_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : InfoGeometry.Canonical.HestenesKreinModularGeometry.RealEnd E}
    (F : InfoGeometry.Canonical.HestenesKreinModularGeometry.KreinFredholmDeterminantContract T) :
    F.determinant = 1 + F.kreinTrace :=
  F.determinant_eq

/-- For any linear involution `J` (such as the fundamental symmetry in a Krein space),
    the determinant of `J` squared is `1`, representing conservation of absolute volume. -/
theorem det_involution_sq_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [Module.Free ℝ V]
    (J : V →ₗ[ℝ] V) (hJ : J.comp J = LinearMap.id (R := ℝ)) :
    ((LinearMap.det (A := ℝ) (M := V)) J) ^ 2 = 1 := by
  have hdet_comp : (LinearMap.det (A := ℝ) (M := V)) (J.comp J) = (LinearMap.det (A := ℝ) (M := V)) J * (LinearMap.det (A := ℝ) (M := V)) J :=
    (LinearMap.det (A := ℝ) (M := V)).map_mul J J
  have hdet_id : (LinearMap.det (A := ℝ) (M := V)) (LinearMap.id (R := ℝ)) = 1 := by
    simp
  have hdet_JJ : (LinearMap.det (A := ℝ) (M := V)) (J.comp J) = 1 := by
    rw [hJ, hdet_id]
  rw [hdet_comp] at hdet_JJ
  have : ((LinearMap.det (A := ℝ) (M := V)) J) ^ 2 = 1 := by
    nlinarith
  exact this

end InfoGeometry.Canonical.HodgeKreinDeterminantBridge
