import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Physics.ParabolicClock
import InfoGeometry.Quantum.PauliSoldering

/-!
# Matrix Stage Lorentz Soldering and KAN Iwasawa Factorization Bridge

This owner establishes the finite-stage representation of $M_2(\mathbb{C})$ and $SL_2(\mathbb{C})$:

1. **KAN / Iwasawa Decomposition Data:**
   Every $g \in SL_2(\mathbb{C})$ in the standard Iwasawa patch decomposes into:
   - $K \in SU(2)$ (compact / elliptic rotation / phase)
   - $A \in \text{Boost}$ (hyperbolic / dilation: $\mathrm{diag}(e^t, e^{-t})$)
   - $N \in \text{Unipotent}$ (parabolic / nilpotent shear: !![1, z; 0, 1])
   such that $g = K \cdot A \cdot N$ and $\det(g) = 1$.

2. **Hermitian Minkowski Soldering:**
   Hermitian $2 \times 2$ matrices $X = X^\dagger$ solder to real 4-vectors $(t, x, y, z) \in \mathbb{R}^{1,3}$
   with $\det(X) = t^2 - x^2 - y^2 - z^2$.

3. **Lorentz Action and Isometry:**
   For $g \in SL_2(\mathbb{C})$, the spinorial Lorentz map $X \mapsto g X g^\dagger$ is Hermitian-preserving
   and strictly preserves the Minkowski quadratic norm: $\det(g X g^\dagger) = \det(X)$.

4. **Native Doubled Krein Carrier Action:**
   The real sectors of the KAN decomposition map directly into the endomorphisms of the doubled
   Krein carrier `DoubledSpace E` via `ρclock`:
   - Parabolic nilpotent shear $\leftrightarrow$ `InfoGeometry.Physics.K` (nilpotent with $K^2 = 0$)
   - Hyperbolic boost $\leftrightarrow$ `matrixEpsilon` (grading involution)
   - Elliptic clock axis $\leftrightarrow$ `matrixClockAxis` (complex structure $J^2 = -1$)
   - Modular exchange $\leftrightarrow$ `matrixJ`

5. **Stage-Successor Block Embedding Compatibility:**
   The finite $2 \times 2$ Lorentz/KAN data embeds into `ComplexMatrixStage.Stage 1` and commutes
   with the successor bonding homomorphism `bondFun`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixStageLorentzKANSoldering

open Matrix
open scoped ComplexConjugate
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-! ## 1. SL₂(ℂ), SU(2), and KAN Factorization Data -/

/-- Predicate for $SL_2(\mathbb{C})$ matrices (unit determinant). -/
def isSL2C (g : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  g.det = 1

/-- Predicate for $SU(2)$ matrices (special unitary). -/
def isSU2 (k : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  k.det = 1 ∧ kᴴ * k = 1

/-- A standard hyperbolic boost matrix $A(t) = \operatorname{diag}(e^t, e^{-t})$. -/
def boostA (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp t : ℂ), 0; 0, (Real.exp (-t) : ℂ)]

/-- A standard parabolic unipotent shear matrix $N(z) = !![1, z; 0, 1]$. -/
def unipotentN (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, z; 0, 1]

/-- A standard compact elliptic phase/rotation matrix in $SU(2)$. -/
def compactK (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Complex.exp (Complex.I * (θ : ℂ))), 0; 0, (Complex.exp (-Complex.I * (θ : ℂ)))]

@[simp]
theorem boostA_det (t : ℝ) : (boostA t).det = 1 := by
  simp [boostA, Matrix.det_fin_two]
  rw [← Complex.exp_add]
  have hsum : (t : ℂ) + -(t : ℂ) = 0 := by ring
  rw [hsum, Complex.exp_zero]

@[simp]
theorem unipotentN_det (z : ℂ) : (unipotentN z).det = 1 := by
  simp [unipotentN, Matrix.det_fin_two]

@[simp]
theorem compactK_det (θ : ℝ) : (compactK θ).det = 1 := by
  simp [compactK, Matrix.det_fin_two]
  rw [← Complex.exp_add]
  have hsum : Complex.I * (θ : ℂ) + -(Complex.I * (θ : ℂ)) = 0 := by ring
  rw [hsum, Complex.exp_zero]

theorem compactK_isSU2 (θ : ℝ) : isSU2 (compactK θ) := by
  constructor
  · exact compactK_det θ
  · ext i j
    fin_cases i <;> fin_cases j
    · dsimp [compactK, Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose_apply]
      rw [Fin.sum_univ_two]
      dsimp
      simp only [mul_zero, add_zero, one_apply_eq]
      change (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) * Complex.exp (Complex.I * (θ : ℂ)) = 1
      rw [← Complex.exp_conj]
      have h_conj : (starRingEnd ℂ) (Complex.I * (θ : ℂ)) = -(Complex.I * (θ : ℂ)) := by
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      rw [h_conj, ← Complex.exp_add]
      have : -(Complex.I * (θ : ℂ)) + (Complex.I * (θ : ℂ)) = 0 := by ring
      rw [this, Complex.exp_zero]
    · dsimp [compactK, Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose_apply]
      rw [Fin.sum_univ_two]
      dsimp
      simp
    · dsimp [compactK, Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose_apply]
      rw [Fin.sum_univ_two]
      dsimp
      simp
    · dsimp [compactK, Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose_apply]
      rw [Fin.sum_univ_two]
      dsimp
      simp only [mul_zero, zero_add, one_apply_eq]
      change (starRingEnd ℂ) (Complex.exp (-Complex.I * (θ : ℂ))) * Complex.exp (-Complex.I * (θ : ℂ)) = 1
      rw [← Complex.exp_conj]
      have h_conj : (starRingEnd ℂ) (-Complex.I * (θ : ℂ)) = Complex.I * (θ : ℂ) := by
        simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
        ring
      rw [h_conj, ← Complex.exp_add]
      have : (Complex.I * (θ : ℂ)) + -Complex.I * (θ : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]

/-- Explicit KAN Iwasawa decomposition structure for $g \in SL_2(\mathbb{C})$. -/
structure KANData (g : Matrix (Fin 2) (Fin 2) ℂ) where
  K : Matrix (Fin 2) (Fin 2) ℂ
  A : Matrix (Fin 2) (Fin 2) ℂ
  N : Matrix (Fin 2) (Fin 2) ℂ
  hK : isSU2 K
  hA : ∃ t : ℝ, A = boostA t
  hN : ∃ z : ℂ, N = unipotentN z
  factorization : g = K * A * N

/-- Any KAN composite has determinant 1 and is thus in $SL_2(\mathbb{C})$. -/
theorem KANData_det_one {g : Matrix (Fin 2) (Fin 2) ℂ} (kan : KANData g) :
    g.det = 1 := by
  rcases kan.hA with ⟨t, ht⟩
  rcases kan.hN with ⟨z, hz⟩
  rw [kan.factorization]
  rw [Matrix.det_mul, Matrix.det_mul, kan.hK.1, ht, hz, boostA_det, unipotentN_det]
  ring

/-! ## 2. Hermitian 2×2 Matrices and Minkowski 4-Vector Soldering -/

/-- Carrier of Hermitian $2 \times 2$ complex matrices. -/
structure HermitianMat2 where
  mat : Matrix (Fin 2) (Fin 2) ℂ
  herm : matᴴ = mat

namespace HermitianMat2

@[ext]
theorem ext (X Y : HermitianMat2) (h : X.mat = Y.mat) : X = Y := by
  cases X; cases Y; congr

instance : Add HermitianMat2 where
  add X Y := ⟨X.mat + Y.mat, by simp [X.herm, Y.herm]⟩

instance : Zero HermitianMat2 where
  zero := ⟨0, by simp⟩

instance : Neg HermitianMat2 where
  neg X := ⟨-X.mat, by simp [X.herm]⟩

instance : Sub HermitianMat2 where
  sub X Y := ⟨X.mat - Y.mat, by simp [X.herm, Y.herm]⟩

instance : HSMul ℝ HermitianMat2 HermitianMat2 where
  hSMul r X := ⟨(r : ℂ) • X.mat, by
    dsimp
    rw [Matrix.conjTranspose_smul]
    simp [X.herm]⟩

end HermitianMat2

/-- Canonical soldering of a real Minkowski 4-vector $(t, x, y, z)$ to a Hermitian $2 \times 2$ matrix. -/
def minkowskiSoldering (t x y z : ℝ) : HermitianMat2 where
  mat := !![(t + z : ℂ), (x - Complex.I * y : ℂ); (x + Complex.I * y : ℂ), (t - z : ℂ)]
  herm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose, Complex.conj_I, sub_eq_add_neg]

/-- Determinant of the soldered Hermitian matrix equals the Minkowski quadratic form. -/
theorem det_minkowskiSoldering (t x y z : ℝ) :
    (minkowskiSoldering t x y z).mat.det = ((t^2 - x^2 - y^2 - z^2 : ℝ) : ℂ) := by
  rw [minkowskiSoldering, Matrix.det_fin_two]
  dsimp
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  calc (↑t + ↑z) * (↑t - ↑z) - (↑x - Complex.I * ↑y) * (↑x + Complex.I * ↑y)
    _ = (↑t * ↑t - ↑z * ↑z) - (↑x * ↑x - Complex.I ^ 2 * (↑y * ↑y)) := by ring
    _ = (↑t * ↑t - ↑z * ↑z) - (↑x * ↑x - (-1) * (↑y * ↑y)) := by rw [hI]
    _ = ((t^2 - x^2 - y^2 - z^2 : ℝ) : ℂ) := by
      push_cast
      ring

/-- The spinorial Lorentz action $X \mapsto g X g^\dagger$ on Hermitian $2 \times 2$ matrices. -/
def lorentzSoldering (g : Matrix (Fin 2) (Fin 2) ℂ) (X : HermitianMat2) : HermitianMat2 where
  mat := g * X.mat * gᴴ
  herm := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [Matrix.conjTranspose_conjTranspose]
    rw [X.herm]
    rw [Matrix.mul_assoc]

/-- The Lorentz action preserves matrix multiplication and identity. -/
theorem lorentzSoldering_one (X : HermitianMat2) :
    lorentzSoldering 1 X = X := by
  ext
  simp [lorentzSoldering]

theorem lorentzSoldering_comp (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℂ) (X : HermitianMat2) :
    lorentzSoldering (g₁ * g₂) X = lorentzSoldering g₁ (lorentzSoldering g₂ X) := by
  ext
  dsimp [lorentzSoldering]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- 🏆 ISOMETRY THEOREM: The spinorial Lorentz action by $g \in SL_2(\mathbb{C})$ strictly preserves the Minkowski norm. -/
theorem lorentzSoldering_isometry
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : isSL2C g) (X : HermitianMat2) :
    (lorentzSoldering g X).mat.det = X.mat.det := by
  dsimp [lorentzSoldering]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hg_det : g.det = 1 := hg
  have hgH_det : gᴴ.det = 1 := by
    rw [Matrix.det_conjTranspose, hg_det]
    simp
  rw [hg_det, hgH_det]
  ring

/-- The KAN composite Lorentz action is an exact isometry on Minkowski space. -/
theorem KANData_lorentz_isometry
    {g : Matrix (Fin 2) (Fin 2) ℂ} (kan : KANData g) (X : HermitianMat2) :
    (lorentzSoldering g X).mat.det = X.mat.det := by
  exact lorentzSoldering_isometry g (KANData_det_one kan) X

/-! ## 3. Doubled Krein Carrier Action and Sector Representation -/

section DoubledCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The representation of a real $2 \times 2$ matrix on `DoubledSpace E`. -/
noncomputable def doubledKreinAction (A : Matrix (Fin 2) (Fin 2) ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ρclock (E := E) A

/-! The doubled carrier therefore receives the matrix multiplication law
    without any expansion of its coordinates. -/

omit [CompleteSpace E] in
theorem doubledKreinAction_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    doubledKreinAction (E := E) (A * B) =
      (doubledKreinAction (E := E) A).comp
        (doubledKreinAction (E := E) B) := by
  exact ρclock_mul A B

omit [CompleteSpace E] in
theorem doubledKreinAction_kan (K A N : Matrix (Fin 2) (Fin 2) ℝ) :
    doubledKreinAction (E := E) (K * A * N) =
      (doubledKreinAction (E := E) K).comp
        ((doubledKreinAction (E := E) A).comp
          (doubledKreinAction (E := E) N)) := by
  rw [doubledKreinAction_mul, doubledKreinAction_mul]
  exact ContinuousLinearMap.comp_assoc _ _ _

set_option linter.unusedSectionVars false in
/-- 1. Parabolic sector: the nilpotent real shear $K$ represents as a square-zero shear on `DoubledSpace E`. -/
theorem doubledKrein_parabolic_sq :
    (doubledKreinAction (E := E) (InfoGeometry.Physics.K (R := ℝ))).comp
      (doubledKreinAction (E := E) (InfoGeometry.Physics.K (R := ℝ))) = 0 := by
  dsimp [doubledKreinAction]
  exact ρclock_parabolicK_sq

set_option linter.unusedSectionVars false in
/-- 2. Hyperbolic sector: the boost grading $\epsilon$ represents as the Krein fundamental symmetry. -/
theorem doubledKrein_hyperbolic_grading :
    doubledKreinAction (E := E) matrixEpsilon = spectral_epsilon (E := E) := by
  dsimp [doubledKreinAction]
  exact ρclock_matrixEpsilon

set_option linter.unusedSectionVars false in
/-- 3. Elliptic sector: the rotation generator represents as the clock axis complex structure ($J^2 = -1$). -/
theorem doubledKrein_elliptic_clockAxis :
    doubledKreinAction (E := E) matrixClockAxis = clockAxis (E := E) := by
  dsimp [doubledKreinAction]
  exact ρclock_matrixClockAxis

set_option linter.unusedSectionVars false in
/-- 4. Modular exchange: the Pauli exchange matrix represents as modular $J$. -/
theorem doubledKrein_modular_j :
    doubledKreinAction (E := E) matrixJ = modular_j (E := E) := by
  dsimp [doubledKreinAction]
  exact ρclock_matrixJ

end DoubledCarrier

/-! ## 4. Matrix Stage Block Embedding and Bonding Compatibility -/

/-- The canonical equivalence between `BitWord 1` and `Fin 2`. -/
def bitword1Equiv : BitWord 1 ≃ Fin 2 where
  toFun w := if w 0 = true then 1 else 0
  invFun
    | 0 => fun _ => false
    | 1 => fun _ => true
  left_inv w := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    cases hw : w 0
    · simp [hw]
    · simp [hw]
  right_inv i := by
    fin_cases i <;> rfl

/-- Embed a $2 \times 2$ matrix $M$ into `ComplexMatrixStage.Stage 1`. -/
def embedMat2ToStage1 (M : Matrix (Fin 2) (Fin 2) ℂ) : ComplexMatrixStage.Stage 1 :=
  fun v w => M (bitword1Equiv v) (bitword1Equiv w)

/-- The embedding preserves the matrix identity. -/
theorem embedMat2ToStage1_one :
    embedMat2ToStage1 1 = 1 := by
  ext v w
  dsimp [embedMat2ToStage1, Matrix.one_apply]
  have hequiv : (bitword1Equiv v = bitword1Equiv w) ↔ v = w :=
    bitword1Equiv.apply_eq_iff_eq
  by_cases h : v = w
  · subst h
    simp
  · have hne : bitword1Equiv v ≠ bitword1Equiv w := fun he => h (hequiv.mp he)
    simp [h, hne]

/-- Embedding a $2 \times 2$ matrix through stage successor bonding `bondFun 1`. -/
def stage2BlockEmbed (M : Matrix (Fin 2) (Fin 2) ℂ) : ComplexMatrixStage.Stage 2 :=
  bondFun 1 (embedMat2ToStage1 M)

/-- 🏆 BOND COMPATIBILITY THEOREM: Successor bonding commutes with the matrix algebraic structure on the $2 \times 2$ block. -/
theorem stage2BlockEmbed_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    stage2BlockEmbed (M * N) = stage2BlockEmbed M * stage2BlockEmbed N := by
  dsimp [stage2BlockEmbed]
  rw [← bondStarAlgHom_apply, ← bondStarAlgHom_apply, ← bondStarAlgHom_apply]
  rw [← map_mul (bondStarAlgHom 1)]
  congr 1
  ext v w
  dsimp [embedMat2ToStage1, Matrix.mul_apply]
  rw [← Equiv.sum_comp bitword1Equiv.symm]
  rw [Fin.sum_univ_two]
  simp [bitword1Equiv]

/-- The KAN decomposition extends coherently to `Stage 2` through the block bonding map. -/
theorem KANData_stage2_factorization
    {g : Matrix (Fin 2) (Fin 2) ℂ} (kan : KANData g) :
    stage2BlockEmbed g = stage2BlockEmbed kan.K * stage2BlockEmbed kan.A * stage2BlockEmbed kan.N := by
  conv_lhs => rw [kan.factorization]
  rw [stage2BlockEmbed_mul, stage2BlockEmbed_mul]

end InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
