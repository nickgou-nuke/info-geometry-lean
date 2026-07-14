import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Algebra.TensorAlgebraCanonical
import InfoGeometry.Algebra.FiniteTensorDeterminantStabilization
import Mathlib.LinearAlgebra.TensorProduct.Map

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker
open Matrix

namespace Cl11TensorTower

abbrev Cl11 : Type := CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11

/-- Repo-native binary matrix stages for the executable Cl(1,1) tower. -/
abbrev MatStage (n : ℕ) : Type := InfoGeometry.Clifford.TowerMatrix.Mat n

/-- Real gamma_0 base matrix for the Cl(1,1) atom: Pauli X. -/
def gamma_0_base : Matrix (Fin 2) (Fin 2) ℝ := InfoGeometry.Clifford.Cl11Matrix.J1

/-- Real gamma_1 base matrix for the Cl(1,1) atom: Pauli iY. -/
def gamma_1_base : Matrix (Fin 2) (Fin 2) ℝ := InfoGeometry.Clifford.Cl11Matrix.Eminus

/-- Internal real phase axis for the Cl(1,1) atom. -/
def phaseAxisBase : Matrix (Fin 2) (Fin 2) ℝ := gamma_1_base

@[simp] theorem phaseAxisBase_sq :
    phaseAxisBase * phaseAxisBase = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [phaseAxisBase, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral volume element base matrix for the Cl(1,1) atom: gamma_0 * gamma_1 = Pauli -Z. -/
def gamma_chiral_base : Matrix (Fin 2) (Fin 2) ℝ := gamma_0_base * gamma_1_base


/-- Hestenes-Krein geometric bivector phase base matrix.
It is chosen as a pure rotation generator (isomorphic to the imaginary unit)
that squares to -I in the real tensor tower. -/
def bivector_J_base : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; -1, 0]

/-- The geometric bivector base inherently squares to -I. -/
theorem bivector_J_base_sq :
    bivector_J_base * bivector_J_base = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [bivector_J_base]

/-- Local Witt creation atom `a† = !![0, 1; 0, 0]` for the matrix CAR tower. -/
def wittCreationBase : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 0, 0]

/-- The Witt creation atom squares to zero: (a†)² = 0. -/
theorem wittCreationBase_sq :
    wittCreationBase * wittCreationBase = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local Witt annihilation atom `a = !![0, 0; 1, 0]` for the matrix CAR tower. -/
def wittAnnihilationBase : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 0; 1, 0]

/-- Real Hestenes phase-plane atom.  This is the standard real rotation matrix
representing multiplication by the internal geometric unit `J`; it is kept as a
matrix-tower operator, not as an external scalar `Complex.I`. -/
def hestenesPhaseBase : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), -1; 1, 0]

/-- The Hestenes phase atom squares to `-1`. -/
theorem hestenesPhaseBase_sq :
    hestenesPhaseBase * hestenesPhaseBase = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesPhaseBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two real phase bases differ by a sign. -/
theorem hestenesPhaseBase_eq_neg_bivector_J_base :
    hestenesPhaseBase = -bivector_J_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesPhaseBase, bivector_J_base]

/-- The creation atom is the split-Witt half-sum `(γ₀ + γ₁)/2`. -/
theorem wittCreationBase_eq_half_gamma_sum :
    wittCreationBase = (1 / 2 : ℝ) • (gamma_0_base + gamma_1_base) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus]

/-- The annihilation atom is the split-Witt half-difference `(γ₀ - γ₁)/2`. -/
theorem wittAnnihilationBase_eq_half_gamma_sub :
    wittAnnihilationBase = (1 / 2 : ℝ) • (gamma_0_base - gamma_1_base) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [wittAnnihilationBase, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus]

/-- The creation atom is the split-Witt half-sum with the internal phase axis. -/
theorem wittCreationBase_eq_half_gamma_plus_phaseAxis :
    wittCreationBase = (1 / 2 : ℝ) • (gamma_0_base + phaseAxisBase) := by
  simpa [phaseAxisBase] using wittCreationBase_eq_half_gamma_sum

/-- The annihilation atom is the split-Witt half-difference with the internal phase axis. -/
theorem wittAnnihilationBase_eq_half_gamma_sub_phaseAxis :
    wittAnnihilationBase = (1 / 2 : ℝ) • (gamma_0_base - phaseAxisBase) := by
  simpa [phaseAxisBase] using wittAnnihilationBase_eq_half_gamma_sub

/-- Real-encoded Witt creation atom using the internal Hestenes--Krein bivector
phase axis instead of an external complex scalar. -/
def realEncodedWittCreationBase : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (gamma_0_base + bivector_J_base)

/-- Real-encoded Witt annihilation atom using the internal Hestenes--Krein
bivector phase axis instead of an external complex scalar. -/
def realEncodedWittAnnihilationBase : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (gamma_0_base - bivector_J_base)

/-- The real-encoded creation atom is the native Witt creation matrix. -/
theorem realEncodedWittCreationBase_eq :
    realEncodedWittCreationBase = wittCreationBase := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [realEncodedWittCreationBase, wittCreationBase, bivector_J_base,
      gamma_0_base, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- The real-encoded annihilation atom is the native Witt annihilation matrix. -/
theorem realEncodedWittAnnihilationBase_eq :
    realEncodedWittAnnihilationBase = wittAnnihilationBase := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [realEncodedWittAnnihilationBase, wittAnnihilationBase, bivector_J_base,
      gamma_0_base, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- Real-encoded creation is nilpotent. -/
theorem realEncodedWittCreationBase_sq :
    realEncodedWittCreationBase * realEncodedWittCreationBase = 0 := by
  rw [realEncodedWittCreationBase_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- Real-encoded annihilation is nilpotent. -/
theorem realEncodedWittAnnihilationBase_sq :
    realEncodedWittAnnihilationBase * realEncodedWittAnnihilationBase = 0 := by
  rw [realEncodedWittAnnihilationBase_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- The real-encoded Witt atoms satisfy the single-site CAR anticommutator. -/
theorem realEncodedWitt_anticomm :
    realEncodedWittCreationBase * realEncodedWittAnnihilationBase +
      realEncodedWittAnnihilationBase * realEncodedWittCreationBase =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [realEncodedWittCreationBase_eq, realEncodedWittAnnihilationBase_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply]

/-- Real gamma_0 matrix for the Cl(1,1) atom at stage 1. -/
noncomputable def gamma_0 : MatStage 1 := InfoGeometry.Clifford.TowerMatrix.kronPow gamma_0_base 1

/-- Real gamma_1 matrix for the Cl(1,1) atom at stage 1. -/
noncomputable def gamma_1 : MatStage 1 := InfoGeometry.Clifford.TowerMatrix.kronPow gamma_1_base 1

/-- Chiral volume element for the Cl(1,1) atom at stage 1. -/
noncomputable def gamma_chiral : MatStage 1 := InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base 1

/-- Global volume element `Γ_n = ⨂_{k=1}^n Γ_{(1,1)}` -/
noncomputable def globalChirality (n : ℕ) : MatStage n :=
  InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n

/-- Coherent Hestenes phase string based at the head tensor factor.  At every
positive stage this is `J ⊗ I ⊗ ⋯ ⊗ I`, so it is preserved by the tower
embedding `A ↦ A ⊗ I₂`. -/
noncomputable def hestenesPhaseHead : (n : ℕ) → MatStage (n + 1)
  | 0 => InfoGeometry.Clifford.TowerMatrix.kronPow hestenesPhaseBase 1
  | n + 1 => hestenesPhaseHead n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Positive chiral projection operator. -/
noncomputable def chiralProjPlus (n : ℕ) : MatStage n :=
  (1 / 2 : ℝ) • (1 + globalChirality n)

/-- Negative chiral projection operator. -/
noncomputable def chiralProjMinus (n : ℕ) : MatStage n :=
  (1 / 2 : ℝ) • (1 - globalChirality n)

/-- Matrix-side one-step embedding `A ↦ A ⊗ I₂`. -/
noncomputable def matStageEmbed (n : ℕ) (A : MatStage n) : MatStage (n + 1) :=
  A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Recursive Jordan-Wigner string with a chosen local matrix at the indexed site.
For site `k : Fin n`, this is the tensor product with `gamma_chiral_base` on
all positions before `k`, `localMat` at `k`, and identity padding after `k`.
The recursion follows the tower shape, so appending one site preserves the index. -/
noncomputable def jwStringWithBase
    (localMat : Matrix (Fin 2) (Fin 2) ℝ) : (n : ℕ) → Fin n → MatStage n
  | 0, k => Fin.elim0 k
  | n + 1, k =>
      if h : (k : ℕ) < n then
        (jwStringWithBase localMat n ⟨k, h⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
      else
        globalChirality n ⊗ₖ localMat

/-- Indexed finite-stage Jordan-Wigner creation operator. -/
noncomputable def jwCreation (n : ℕ) (k : Fin n) : MatStage n :=
  jwStringWithBase wittCreationBase n k

/-- Indexed finite-stage Jordan-Wigner annihilation operator. -/
noncomputable def jwAnnihilation (n : ℕ) (k : Fin n) : MatStage n :=
  jwStringWithBase wittAnnihilationBase n k

/-- Indexed finite-stage Jordan-Wigner creation operator using the real-encoded
Hestenes bivector phase presentation. -/
noncomputable def jwRealEncodedCreation (n : ℕ) (k : Fin n) : MatStage n :=
  jwStringWithBase realEncodedWittCreationBase n k

/-- Indexed finite-stage Jordan-Wigner annihilation operator using the real-encoded
Hestenes bivector phase presentation. -/
noncomputable def jwRealEncodedAnnihilation (n : ℕ) (k : Fin n) : MatStage n :=
  jwStringWithBase realEncodedWittAnnihilationBase n k

/-- The real-encoded creation string is the native creation string. -/
theorem jwRealEncodedCreation_eq (n : ℕ) (k : Fin n) :
    jwRealEncodedCreation n k = jwCreation n k := by
  simp [jwRealEncodedCreation, jwCreation, realEncodedWittCreationBase_eq]

/-- The real-encoded annihilation string is the native annihilation string. -/
theorem jwRealEncodedAnnihilation_eq (n : ℕ) (k : Fin n) :
    jwRealEncodedAnnihilation n k = jwAnnihilation n k := by
  simp [jwRealEncodedAnnihilation, jwAnnihilation, realEncodedWittAnnihilationBase_eq]

/-- Indexed finite-stage Jordan-Wigner creation string `u_k^(n)`. -/
abbrev u (n : ℕ) (k : Fin n) : MatStage n :=
  jwCreation n k

/-- Indexed finite-stage Jordan-Wigner annihilation string `v_k^(n)`. -/
abbrev v (n : ℕ) (k : Fin n) : MatStage n :=
  jwAnnihilation n k

/-- At the last site the recursive string is exactly the chiral prefix tensored
with the chosen local matrix. -/
@[simp] theorem jwStringWithBase_last
    (localMat : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    jwStringWithBase localMat (n + 1) ⟨n, Nat.lt_succ_self n⟩ =
      globalChirality n ⊗ₖ localMat := by
  simp [jwStringWithBase]

@[simp] theorem matStageEmbed_jwStringWithBase
    (localMat : Matrix (Fin 2) (Fin 2) ℝ) {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwStringWithBase localMat n k) =
      jwStringWithBase localMat (n + 1) k.castSucc := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
      have hk : (k : ℕ) < n + 1 := k.isLt
      by_cases h : (k : ℕ) < n
      · simp [matStageEmbed, jwStringWithBase, h, hk]
      · simp [matStageEmbed, jwStringWithBase, h, hk]

@[simp] theorem matStageEmbed_jwCreation {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwCreation n k) = jwCreation (n + 1) k.castSucc := by
  simp [jwCreation]

@[simp] theorem matStageEmbed_jwAnnihilation {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwAnnihilation n k) = jwAnnihilation (n + 1) k.castSucc := by
  simp [jwAnnihilation]

@[simp] theorem matStageEmbed_jwRealEncodedCreation {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwRealEncodedCreation n k) =
      jwRealEncodedCreation (n + 1) k.castSucc := by
  simp [jwRealEncodedCreation]

@[simp] theorem matStageEmbed_jwRealEncodedAnnihilation {n : ℕ} (k : Fin n) :
    matStageEmbed n (jwRealEncodedAnnihilation n k) =
      jwRealEncodedAnnihilation (n + 1) k.castSucc := by
  simp [jwRealEncodedAnnihilation]

@[simp] theorem matStageEmbed_u {n : ℕ} (k : Fin n) :
    matStageEmbed n (u n k) = u (n + 1) k.castSucc := by
  simp [u]

@[simp] theorem matStageEmbed_v {n : ℕ} (k : Fin n) :
    matStageEmbed n (v n k) = v (n + 1) k.castSucc := by
  simp [v]

@[simp] theorem matStageEmbed_zero (n : ℕ) :
    matStageEmbed n (0 : MatStage n) = 0 := by
  simp [matStageEmbed]

@[simp] theorem matStageEmbed_one (n : ℕ) :
    matStageEmbed n (1 : MatStage n) = (1 : MatStage (n + 1)) := by
  simp [matStageEmbed]

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

@[simp] theorem stageEmbed_star (n : ℕ) (A : MatStage n) :
    stageEmbed n (star A) = star (stageEmbed n A) := by
  ext i j
  cases i with
  | mk i1 i2 =>
      cases j with
      | mk j1 j2 =>
          fin_cases i2 <;> fin_cases j2 <;>
            simp [stageEmbed_apply, matStageEmbed, Matrix.star_apply]

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
  simp [atom, InfoGeometry.Algebra.TensorAlgebraCanonical.includeLinear,
    InfoGeometry.Algebra.TensorAlgebraCanonical.toTensorPowerSum_include
      (R := ℝ) (M := SymmetryAtom) x]

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

end Cl11TensorTower
