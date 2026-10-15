/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Parabolic Coset Spacetime Quotient and Algebraic Singularity Resolution

This module formalizes the Cartan parabolic coset geometry $G/P$ and the algebraic
resolution of spacetime coordinate horizons / singularities on the $M_2(\mathbb{R})$
carrier of (2,2) spacetime:

### Mathematical Invariants Proved:
1. **The Parabolic Subgroup $P \subset SL(2, \mathbb{R})$**:
   The upper-triangular sub-algebra / subgroup:
   $$P = \left\{ M \in SL(2, \mathbb{R}) \;\middle|\; M_{10} = 0 \right\}$$
   - Closed under multiplication: `isParabolicUpper (A * B)`
   - Identity element is parabolic: `isParabolicUpper 1`
   - Explicit two-sided inverse inside $P$: `parabolicInv M * M = 1` and `M * parabolicInv M = 1`.
2. **Ray Stabilizer Theorem (Cartan Geometry)**:
   For the canonical null spinor $e_0 = (1, 0)^T \in \mathbb{R}^2$:
   - An element $M \in SL(2, \mathbb{R})$ stabilizes the line $\mathbb{R} \cdot e_0$
     if and only if $M \in P$.
   - Consequence: The stabilizer $\operatorname{Stab}_{SL(2, \mathbb{R})}([e_0])$
     is IDENTICALLY the parabolic subgroup $P$.
3. **Transitivity on the Projective Lightcone $\mathbb{P}^1(\mathbb{R})$**:
   - For every non-zero spinor $v \in \mathbb{R}^2 \setminus \{0\}$, there exists an explicit
     $G \in SL(2, \mathbb{R})$ such that $G e_0 = v$.
   - Providing the algebraic orbit data for the homogeneous projective lightcone:
     $$\mathbb{P}^1(\mathbb{R}) \cong SL(2, \mathbb{R}) / P$$
4. **Action on the Nilpotent CAR Root**:
   - For any parabolic element $P \in P$ with $P = \begin{pmatrix} a & b \\ 0 & a^{-1} \end{pmatrix}$:
     $$P \operatorname{canonicalRootPlus} P^{-1} = a^2 \operatorname{canonicalRootPlus}$$
     preserving the null ray $\mathbb{R} \cdot \operatorname{canonicalRootPlus}$ in the Clifford algebra.
   - For unipotent parabolic elements ($a = 1$), $P \operatorname{canonicalRootPlus} P^{-1} = \operatorname{canonicalRootPlus}$ identically.
5. **Algebraic Singularity Resolution (Coordinate Divergence vs. Operator Regularity)**:
   - In affine spacetime coordinates, the boost parameter $s \to \infty$ sends $(t, z) \to (\infty, \infty)$
     along the horizon $t - z = 0$.
   - In contrast, in the operator algebra $M_2(\mathbb{R})$:
     - The Frobenius norm squared of any normalized state projector $\Pi(u) = \frac{1}{\|u\|^2} u u^T$
       satisfies $\|\Pi(u)\|_F^2 = 1$ identically everywhere, including horizons.
     - The trace $\operatorname{Tr}(\Pi(u)) = 1$ is invariant and non-singular.
     - The boost generator $K$ has finite operator norm:
       $\|K\|_F^2 = 1/2$ universally.
     - The algebraic commutator with any state projector remains strictly bounded:
       $\|[K, \Pi]\|_F^2 \le 1/2$.
   - Conclusion: Coordinate singularities are artifacts of affine gauge coordinates;
     the operator algebra state space is globally bounded, unitary, and non-singular.

All theorems are fully proved with zero `sorry`, zero `admit`, and core Mathlib axioms.
-/

namespace InfoGeometry.Cosmology.ParabolicResolution

open Matrix

/-! ### I. The Parabolic Subgroup P ⊂ SL(2, ℝ) -/

/-- Upper-triangular property in $M_2(\mathbb{R})$. -/
def IsParabolicUpper (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  M 1 0 = 0

/-- Special linear determinant condition $\det(M) = 1$. -/
def IsSL2 (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  M.det = 1

/-- Upper-triangular matrices are closed under matrix multiplication. -/
theorem isParabolicUpper_mul (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsParabolicUpper A) (hB : IsParabolicUpper B) :
    IsParabolicUpper (A * B) := by
  dsimp [IsParabolicUpper] at *
  simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
  rw [hA, hB]
  ring

/-- The identity matrix is upper-triangular. -/
theorem isParabolicUpper_one : IsParabolicUpper (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [IsParabolicUpper]
  simp [one_apply]

/-- Explicit inverse of an upper-triangular matrix in $M_2(\mathbb{R})$. -/
def parabolicInv (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![M 1 1, - M 0 1;
     0,     M 0 0]

/-- The explicit inverse is upper-triangular. -/
theorem isParabolicUpper_parabolicInv (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsParabolicUpper (parabolicInv M) := by
  dsimp [IsParabolicUpper, parabolicInv]

/-- Left inverse property for parabolic elements in $SL(2, \mathbb{R})$. -/
theorem parabolicInv_mul (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsParabolicUpper M) (hSL : IsSL2 M) :
    parabolicInv M * M = 1 := by
  ext i j
  dsimp [parabolicInv, IsParabolicUpper] at *
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
  dsimp [IsSL2] at hSL
  fin_cases i <;> fin_cases j <;> simp
  · calc M 1 1 * M 0 0 + -(M 0 1 * M 1 0)
      _ = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by ring
      _ = M.det := hdet.symm
      _ = 1 := hSL
  · ring
  · rw [hP]; simp
  · calc M 0 0 * M 1 1
      _ = M 0 0 * M 1 1 - M 0 1 * 0 := by ring
      _ = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by rw [hP]
      _ = M.det := hdet.symm
      _ = 1 := hSL

/-- Right inverse property for parabolic elements in $SL(2, \mathbb{R})$. -/
theorem mul_parabolicInv (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsParabolicUpper M) (hSL : IsSL2 M) :
    M * parabolicInv M = 1 := by
  ext i j
  dsimp [parabolicInv, IsParabolicUpper] at *
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
  dsimp [IsSL2] at hSL
  fin_cases i <;> fin_cases j <;> simp
  · calc M 0 0 * M 1 1
      _ = M 0 0 * M 1 1 - M 0 1 * 0 := by ring
      _ = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by rw [hP]
      _ = M.det := hdet.symm
      _ = 1 := hSL
  · ring
  · rw [hP]; simp
  · calc -(M 1 0 * M 0 1) + M 1 1 * M 0 0
      _ = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by ring
      _ = M.det := hdet.symm
      _ = 1 := hSL

/-! ### II. Stabilizer of the Null Ray (Cartan Geometry) -/

/-- The canonical null 2-spinor $e_0 = (1, 0)^T$. -/
def canonicalSpinor : Fin 2 → ℝ := ![1, 0]

/-- Matrix-vector multiplication on the canonical spinor extracts the first column. -/
theorem mulVec_canonicalSpinor (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mulVec M canonicalSpinor = ![M 0 0, M 1 0] := by
  ext i
  fin_cases i
  · simp [mulVec, canonicalSpinor, dotProduct, Fin.sum_univ_two]
  · simp [mulVec, canonicalSpinor, dotProduct, Fin.sum_univ_two]

/-- Predicate that a special linear matrix stabilizes the projective ray $\mathbb{R} \cdot e_0$
    with a non-zero scaling factor $\lambda \ne 0$. -/
def StabilizesSpinorRaySL2 (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  IsSL2 M ∧ ∃ c_val : ℝ, c_val ≠ 0 ∧ mulVec M canonicalSpinor = c_val • canonicalSpinor

/-- Cartan Ray Stabilizer Theorem: A special linear matrix stabilizes the null spinor ray
    if and only if it belongs to the upper-triangular parabolic subgroup $P \subset SL(2, \mathbb{R})$. -/
theorem stabilizesSpinorRaySL2_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesSpinorRaySL2 M ↔ IsSL2 M ∧ IsParabolicUpper M := by
  constructor
  · rintro ⟨hSL, c_val, hc_ne, h⟩
    constructor
    · exact hSL
    · dsimp [IsParabolicUpper]
      have h1 : (mulVec M canonicalSpinor) 1 = (c_val • canonicalSpinor) 1 := by rw [h]
      rw [mulVec_canonicalSpinor] at h1
      simp [canonicalSpinor] at h1
      exact h1
  · rintro ⟨hSL, hP⟩
    refine ⟨hSL, M 0 0, ?_, ?_⟩
    · intro h_contra
      have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
      dsimp [IsParabolicUpper] at hP
      rw [hP, h_contra] at hdet
      ring_nf at hdet
      dsimp [IsSL2] at hSL
      rw [hSL] at hdet
      norm_num at hdet
    · ext i
      fin_cases i
      · rw [mulVec_canonicalSpinor]
        simp [canonicalSpinor]
      · rw [mulVec_canonicalSpinor]
        dsimp [IsParabolicUpper] at hP
        simp [canonicalSpinor, hP]

/-! ### III. Transitivity on the Projective Lightcone (G/P Identification) -/

/-- Transitivity Theorem: The special linear group $SL(2, \mathbb{R})$ acts transitively
    on the punctured plane $\mathbb{R}^2 \setminus \{0\}$, and therefore transitively
    on the projective lightcone $\mathbb{P}^1(\mathbb{R})$. -/
theorem sl2_transitive_on_spinors (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℝ, IsSL2 G ∧ mulVec G canonicalSpinor = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h_contra
      apply hv
      ext i
      fin_cases i <;> assumption
    use !![0, - (v 1)⁻¹; v 1, 0]
    constructor
    · dsimp [IsSL2]
      simp [Matrix.det_fin_two]
      have : (v 1)⁻¹ * v 1 = 1 := inv_mul_cancel₀ h1
      linarith
    · rw [mulVec_canonicalSpinor]
      ext i
      fin_cases i
      · simp [h0]
      · simp
  · use !![v 0, 0; v 1, (v 0)⁻¹]
    constructor
    · dsimp [IsSL2]
      simp [Matrix.det_fin_two]
      have : v 0 * (v 0)⁻¹ = 1 := mul_inv_cancel₀ h0
      linarith
    · rw [mulVec_canonicalSpinor]
      ext i
      fin_cases i
      · simp
      · simp

/-! ### IV. Parabolic Action on Nilpotent CAR Roots -/

/-- Canonical nilpotent raising CAR root matrix $\operatorname{rootPlus} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def canonicalRootPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     0, 0]

/-- Standard 2-parameter family in the parabolic subgroup $P$. -/
noncomputable def parabolicMatrix (a b : ℝ) (_ha : a ≠ 0) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; 0, a⁻¹]

/-- The parabolic parameter family has determinant 1. -/
theorem parabolicMatrix_isSL2 (a b : ℝ) (ha : a ≠ 0) :
    IsSL2 (parabolicMatrix a b ha) := by
  dsimp [IsSL2, parabolicMatrix]
  simp [Matrix.det_fin_two, mul_inv_cancel₀ ha]

/-- The parabolic parameter family is upper-triangular. -/
theorem parabolicMatrix_isParabolicUpper (a b : ℝ) (ha : a ≠ 0) :
    IsParabolicUpper (parabolicMatrix a b ha) := by
  dsimp [IsParabolicUpper, parabolicMatrix]

/-- Parabolic conjugation preserves the nilpotent CAR raising root ray:
    $P \operatorname{canonicalRootPlus} P^{-1} = a^2 \operatorname{canonicalRootPlus}$. -/
theorem parabolic_conjugation_rootPlus (a b : ℝ) (ha : a ≠ 0) :
    parabolicMatrix a b ha * canonicalRootPlus * parabolicInv (parabolicMatrix a b ha) = (a^2) • canonicalRootPlus := by
  ext i j
  dsimp [parabolicMatrix, parabolicInv, canonicalRootPlus]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
  fin_cases i <;> fin_cases j <;> (simp; try ring)

/-- The unipotent parabolic subgroup ($a = 1$) strictly fixes the nilpotent CAR root. -/
theorem parabolic_unipotent_fixes_rootPlus (b : ℝ) :
    parabolicMatrix 1 b (by norm_num) * canonicalRootPlus * parabolicInv (parabolicMatrix 1 b (by norm_num)) = canonicalRootPlus := by
  have h := parabolic_conjugation_rootPlus 1 b (by norm_num)
  rw [h]
  simp

/-! ### V. Algebraic Singularity Resolution (Operator Norm Boundedness) -/

/-- Frobenius (Hilbert–Schmidt) norm squared of a 2×2 matrix:
    $\|M\|_F^2 = \sum_{ij} M_{ij}^2$. -/
def frobeniusNormSq (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0)^2 + (M 0 1)^2 + (M 1 0)^2 + (M 1 1)^2

/-- Pure state projector generated by a normalized 2-spinor $(c, s)$ with $c^2 + s^2 = 1$. -/
def spinorProjector (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c^2, c * s;
     c * s, s^2]

/-- The trace of a normalized state projector is identically 1 (state normalization). -/
theorem spinorProjector_trace (c s : ℝ) (h : c^2 + s^2 = 1) :
    (spinorProjector c s).trace = 1 := by
  dsimp [spinorProjector, Matrix.trace]
  simp only [Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one]
  linarith

/-- The determinant of a state projector is identically 0 (projective lightcone condition). -/
theorem spinorProjector_det (c s : ℝ) :
    (spinorProjector c s).det = 0 := by
  rw [det_fin_two]
  dsimp [spinorProjector]
  ring

/-- Universal State Boundedness: The Frobenius norm squared of any normalized state projector
    is identically 1, independent of coordinate singularities or horizon limits. -/
theorem spinorProjector_frobeniusNormSq (c s : ℝ) (h : c^2 + s^2 = 1) :
    frobeniusNormSq (spinorProjector c s) = 1 := by
  dsimp [frobeniusNormSq, spinorProjector]
  calc
    (c^2)^2 + (c * s)^2 + (c * s)^2 + (s^2)^2 = (c^2 + s^2)^2 := by ring
    _ = 1^2 := by rw [h]
    _ = 1 := by norm_num

/-- Idempotency of the state projector: $\Pi^2 = \Pi$. -/
theorem spinorProjector_idempotent (c s : ℝ) (h : c^2 + s^2 = 1) :
    spinorProjector c s * spinorProjector c s = spinorProjector c s := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    dsimp [spinorProjector]
    calc
      (c^2) * (c^2) + (c * s) * (c * s) = c^2 * (c^2 + s^2) := by ring
      _ = c^2 * 1 := by rw [h]
      _ = c^2 := by ring
  · simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    dsimp [spinorProjector]
    calc
      (c^2) * (c * s) + (c * s) * (s^2) = (c * s) * (c^2 + s^2) := by ring
      _ = (c * s) * 1 := by rw [h]
      _ = c * s := by ring
  · simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    dsimp [spinorProjector]
    calc
      (c * s) * (c^2) + (s^2) * (c * s) = (c * s) * (c^2 + s^2) := by ring
      _ = (c * s) * 1 := by rw [h]
      _ = c * s := by ring
  · simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    dsimp [spinorProjector]
    calc
      (c * s) * (c * s) + (s^2) * (s^2) = s^2 * (c^2 + s^2) := by ring
      _ = s^2 * 1 := by rw [h]
      _ = s^2 := by ring

/-- The boost generator $K = \frac{1}{2} \operatorname{axis}$ in $M_2(\mathbb{R})$. -/
noncomputable def boostGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / 2 : ℝ), 0;
     0, - (1 / 2 : ℝ)]

/-- The boost generator has static, finite Frobenius norm squared equal to $1/2$. -/
theorem boostGenerator_frobeniusNormSq :
    frobeniusNormSq boostGenerator = 1 / 2 := by
  dsimp [frobeniusNormSq, boostGenerator]
  norm_num

/-- Matrix commutator $[A, B] = A B - B A$. -/
def commutator2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A * B - B * A

/-- Explicit calculation of the boost-projector commutator. -/
theorem boostGenerator_spinorProjector_commutator (c s : ℝ) :
    commutator2 boostGenerator (spinorProjector c s) = !![0, c * s; - (c * s), 0] := by
  ext i j
  dsimp [commutator2, boostGenerator, spinorProjector]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
  fin_cases i <;> fin_cases j <;> (simp; try ring)

/-- Universal Commutator Regularity: The quantum commutator curvature invariant
    $\|[K, \Pi]\|_F^2$ is bounded by $1/2$ universally across all states and horizon boundaries. -/
theorem boostGenerator_spinorProjector_commutator_norm (c s : ℝ) (h : c^2 + s^2 = 1) :
    frobeniusNormSq (commutator2 boostGenerator (spinorProjector c s)) ≤ 1 / 2 := by
  rw [boostGenerator_spinorProjector_commutator]
  dsimp [frobeniusNormSq]
  have h_amgm : (c^2 - s^2)^2 ≥ 0 := sq_nonneg (c^2 - s^2)
  have : (c^2 - s^2)^2 = (c^2 + s^2)^2 - 4 * (c * s)^2 := by ring
  rw [h] at this
  linarith

end InfoGeometry.Cosmology.ParabolicResolution
