import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Algebra.TensorAlgebraCanonical
import InfoGeometry.Algebra.FiniteTensorDeterminantStabilization
import Mathlib.LinearAlgebra.TensorProduct.Map

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker
open Matrix

namespace InfoGeometry.Clifford.Cl11TensorTower

abbrev Cl11 : Type := CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11

/-- Repo-native binary matrix stages for the executable Cl(1,1) tower. -/
abbrev MatStage (n : ℕ) : Type := InfoGeometry.Clifford.TowerMatrix.Mat n

/-- Matrix-side one-step embedding `A ↦ A ⊗ I₂`. -/
noncomputable def matStageEmbed (n : ℕ) (A : MatStage n) : MatStage (n + 1) :=
  A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

@[simp] theorem matStageEmbed_zero (n : ℕ) :
    matStageEmbed n (0 : MatStage n) = 0 := by
  simp [matStageEmbed]

@[simp] theorem matStageEmbed_one (n : ℕ) :
    matStageEmbed n (1 : MatStage n) = (1 : MatStage (n + 1)) := by
  simpa [matStageEmbed] using
    (Matrix.one_kronecker_one (α := ℝ) (m := InfoGeometry.Clifford.TowerMatrix.Idx n) (n := Fin 2))

@[simp] theorem matStageEmbed_add (n : ℕ) (A B : MatStage n) :
    matStageEmbed n (A + B) = matStageEmbed n A + matStageEmbed n B := by
  simpa [matStageEmbed] using Matrix.add_kronecker A B (1 : Matrix (Fin 2) (Fin 2) ℝ)

@[simp] theorem matStageEmbed_mul (n : ℕ) (A B : MatStage n) :
    matStageEmbed n (A * B) = matStageEmbed n A * matStageEmbed n B := by
  simpa [matStageEmbed] using
    (Matrix.mul_kronecker_mul A B (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- The one-step matrix embedding `A ↦ A ⊗ I₂` is injective. -/
theorem matStageEmbed_injective (n : ℕ) : Function.Injective (matStageEmbed n) := by
  intro A B h
  ext i j
  have h' := congrArg (fun M : MatStage (n + 1) => M (i, (0 : Fin 2)) (j, (0 : Fin 2))) h
  simpa [matStageEmbed] using h'

/-- Algebra-hom form of the one-step matrix embedding. -/
noncomputable def stageEmbed (n : ℕ) : MatStage n →ₐ[ℝ] MatStage (n + 1) where
  toFun := matStageEmbed n
  map_one' := matStageEmbed_one n
  map_mul' := matStageEmbed_mul n
  map_zero' := matStageEmbed_zero n
  map_add' := matStageEmbed_add n
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [matStageEmbed, Matrix.smul_kronecker, Matrix.one_kronecker_one]

@[simp] theorem stageEmbed_apply {n : ℕ} (A : MatStage n) :
    stageEmbed n A = matStageEmbed n A := rfl

@[simp] theorem stageEmbed_comp_apply {n : ℕ} (A : MatStage n) :
    stageEmbed (n + 1) (stageEmbed n A) =
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rfl

/-- Canonical matrix-unit basis atom at stage `n`. -/
abbrev matrixUnit (n : ℕ) (i j : InfoGeometry.Clifford.TowerMatrix.Idx n) : MatStage n :=
  Matrix.single i j (1 : ℝ)

/-- The one-step embedding sends a matrix unit to the corresponding diagonal tensor sum. -/
@[simp] theorem stageEmbed_matrixUnit (n : ℕ)
    (i j : InfoGeometry.Clifford.TowerMatrix.Idx n) :
    stageEmbed n (Matrix.single i j (1 : ℝ)) =
      Matrix.single (i, (0 : Fin 2)) (j, (0 : Fin 2)) (1 : ℝ) +
      Matrix.single (i, (1 : Fin 2)) (j, (1 : Fin 2)) (1 : ℝ) := by
  ext a b
  cases a with
  | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
          fin_cases a2 <;> fin_cases b2 <;>
            simp [stageEmbed_apply, matStageEmbed, Matrix.single]

/-- The one-step embedding is a Lie algebra homomorphism for the commutator Lie structure. -/
noncomputable def stageEmbedLieHom (n : ℕ) : MatStage n →ₗ⁅ℝ⁆ MatStage (n + 1) :=
  (stageEmbed n).toLieHom

@[simp] theorem stageEmbedLieHom_apply (n : ℕ) (A : MatStage n) :
    stageEmbedLieHom n A = stageEmbed n A := rfl

@[simp] theorem stageEmbed_lie (n : ℕ) (A B : MatStage n) :
    stageEmbed n ⁅A, B⁆ = ⁅stageEmbed n A, stageEmbed n B⁆ := by
  exact (stageEmbedLieHom n).map_lie A B

/-- Binary-volume normalized matrix trace. -/
def normalizedTrace (n : ℕ) (A : MatStage n) : ℝ :=
  Matrix.trace A / (2 : ℝ) ^ n

@[simp] theorem trace_fin_two_one :
    Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
  simp [Matrix.trace, Matrix.diag]

@[simp] theorem matStageEmbed_trace (n : ℕ) (A : MatStage n) :
    Matrix.trace (matStageEmbed n A) = 2 * Matrix.trace A := by
  rw [matStageEmbed, Matrix.trace_kronecker, trace_fin_two_one]
  ring

@[simp] theorem normalizedTrace_matStageEmbed (n : ℕ) (A : MatStage n) :
    normalizedTrace (n + 1) (matStageEmbed n A) = normalizedTrace n A := by
  unfold normalizedTrace
  rw [matStageEmbed_trace, pow_succ]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

@[simp] theorem matStageEmbed_det (n : ℕ) (A : MatStage n) :
    Matrix.det (matStageEmbed n A) = Matrix.det A ^ (2 : ℕ) := by
  rw [matStageEmbed, Matrix.det_kronecker]
  simp

/-- Binary-volume normalized logarithmic determinant readout. -/
def normalizedLogAbsDet (n : ℕ) (A : MatStage n) : ℝ :=
  InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet n
    (Real.log |Matrix.det A|)

@[simp] theorem matStageEmbed_logAbsDet_double (n : ℕ) (A : MatStage n) :
    Real.log |Matrix.det (matStageEmbed n A)| = 2 * Real.log |Matrix.det A| := by
  rw [matStageEmbed_det, abs_pow, Real.log_pow]
  ring

@[simp] theorem normalizedLogAbsDet_matStageEmbed (n : ℕ) (A : MatStage n) :
    normalizedLogAbsDet (n + 1) (matStageEmbed n A) = normalizedLogAbsDet n A := by
  unfold normalizedLogAbsDet
  exact InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet_tensor_embedding_stable
    n (matStageEmbed_logAbsDet_double n A)

/-- Wigner-Johnson symmetry atoms live in degree `1` of the tensor algebra on `Vec11`. -/
abbrev SymmetryAtom : Type := InfoGeometry.Clifford.Cl11Matrix.Vec11

abbrev SymmetryWord : Type := TensorAlgebra ℝ SymmetryAtom

abbrev atom : SymmetryAtom →ₗ[ℝ] SymmetryWord :=
  InfoGeometry.Algebra.TensorAlgebraCanonical.includeLinear

/-- Finite symmetry word as a tensor word of length `n`. -/
def word (n : ℕ) (x : Fin n → SymmetryAtom) : SymmetryWord :=
  TensorAlgebra.tprod ℝ SymmetryAtom n x

@[simp] theorem atom_toTensorPowerSum (x : SymmetryAtom) :
    InfoGeometry.Algebra.TensorAlgebraCanonical.toTensorPowerSum (R := ℝ) (M := SymmetryAtom)
        (atom x) =
      DirectSum.of (fun n : ℕ => ⨂[ℝ]^n SymmetryAtom) 1 (PiTensorProduct.tprod ℝ fun _ : Fin 1 => x) := by
  simpa [atom, InfoGeometry.Algebra.TensorAlgebraCanonical.includeLinear] using
    InfoGeometry.Algebra.TensorAlgebraCanonical.toTensorPowerSum_include
      (R := ℝ) (M := SymmetryAtom) x

@[simp] theorem word_toTensorPowerSum {n : ℕ} (x : Fin n → SymmetryAtom) :
    InfoGeometry.Algebra.TensorAlgebraCanonical.toTensorPowerSum (R := ℝ) (M := SymmetryAtom)
        (word n x) =
      DirectSum.of (fun m : ℕ => ⨂[ℝ]^m SymmetryAtom) n (PiTensorProduct.tprod ℝ x) := by
  simpa [word] using
    InfoGeometry.Algebra.TensorAlgebraCanonical.toTensorPowerSum_tprod
      (R := ℝ) (M := SymmetryAtom) x

@[elab_as_elim]
theorem symmetryWord_induction {C : SymmetryWord → Prop}
    (h_scalar : ∀ r : ℝ, C (algebraMap ℝ SymmetryWord r))
    (h_atom : ∀ x : SymmetryAtom, C (TensorAlgebra.ι ℝ x))
    (h_mul : ∀ a b : SymmetryWord, C a → C b → C (a * b))
    (h_add : ∀ a b : SymmetryWord, C a → C b → C (a + b))
    (a : SymmetryWord) : C a := by
  exact InfoGeometry.Algebra.TensorAlgebraCanonical.tensorAlgebra_induction
    (R := ℝ) (M := SymmetryAtom) h_scalar h_atom h_mul h_add a

end InfoGeometry.Clifford.Cl11TensorTower
