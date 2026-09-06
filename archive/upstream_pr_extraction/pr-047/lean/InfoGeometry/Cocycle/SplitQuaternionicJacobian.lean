import InfoGeometry.Cocycle.ActionCocycle
import InfoGeometry.Cocycle.GroupoidCocycle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic
import Mathlib.Topology.Constructions

/-!
# Split-Quaternionic Jacobian Cocycle

This file formalizes the finite matrix model of split quaternions used by the
frame-Jacobian branch:

* `HPrime = Matrix (Fin 2) (Fin 2) ℝ`;
* the split norm is the determinant;
* invertible split quaternions are `GL (Fin 2) ℝ`;
* norm-one split quaternions are `SL (Fin 2) ℝ`;
* `log |det|` is an additive scalar cocycle;
* the induced four-real-dimensional Jacobian of left/right/two-sided
  multiplication is computed by mathlib's Kronecker determinant theorem.

The Radon-Nikodym density remains scalar-valued here: the nonabelian
split-quaternionic object is the frame cocycle, and the scalar density is
extracted by the determinant/norm.
-/

noncomputable section

namespace InfoGeometry.Cocycle
namespace SplitQuaternionicJacobian

open CategoryTheory
open scoped Kronecker Matrix

/-! ## The matrix model of split quaternions -/

/-- The split-quaternion algebra in its canonical matrix model `ℍ' ≅ M₂(ℝ)`. -/
abbrev HPrime : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- The split norm, represented by the determinant in the `M₂(ℝ)` model. -/
def splitNorm (q : HPrime) : ℝ :=
  Matrix.det q

/-- Multiplicativity of the split norm. -/
theorem splitNorm_mul (a b : HPrime) :
    splitNorm (a * b) = splitNorm a * splitNorm b := by
  exact Matrix.det_mul a b

@[simp]
theorem splitNorm_one :
    splitNorm (1 : HPrime) = 1 := by
  simp [splitNorm]

@[simp]
theorem splitNorm_transpose (a : HPrime) :
    splitNorm (aᵀ) = splitNorm a := by
  simp [splitNorm]

/-! ## The four-coordinate split-quaternion chart -/

/-- The scalar basis element in the `M₂(ℝ)` split-quaternion model. -/
def coordOne : HPrime :=
  !![1, 0; 0, 1]

/-- The split-quaternion basis element `i`, with `i^2 = -1`. -/
def coordI : HPrime :=
  !![0, -1; 1, 0]

/-- The split-quaternion basis element `j`, with `j^2 = 1`. -/
def coordJ : HPrime :=
  !![0, 1; 1, 0]

/-- The split-quaternion basis element `k = i*j`, with `k^2 = 1`. -/
def coordK : HPrime :=
  !![-1, 0; 0, 1]

/-- The coordinate chart `w + x i + y j + z k` in the `M₂(ℝ)` model. -/
def ofCoords (w x y z : ℝ) : HPrime :=
  !![w - z, -x + y; x + y, w + z]

theorem coordI_sq :
    coordI * coordI = -(1 : HPrime) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coordI, Matrix.mul_apply, Fin.sum_univ_two]

theorem coordJ_sq :
    coordJ * coordJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coordJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem coordK_sq :
    coordK * coordK = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coordK, Matrix.mul_apply, Fin.sum_univ_two]

theorem coordI_mul_coordJ :
    coordI * coordJ = coordK := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coordI, coordJ, coordK, Matrix.mul_apply, Fin.sum_univ_two]

theorem coordJ_mul_coordI :
    coordJ * coordI = -coordK := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coordI, coordJ, coordK, Matrix.mul_apply, Fin.sum_univ_two]

/-- The coordinate chart is exactly the basis expansion `w + x*i + y*j + z*k`. -/
theorem ofCoords_eq_basis (w x y z : ℝ) :
    ofCoords w x y z =
      w • coordOne + x • coordI + y • coordJ + z • coordK := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [ofCoords, coordOne, coordI, coordJ, coordK]
  all_goals ring

/--
The determinant model realizes the split-quaternion norm
`N(w + x*i + y*j + z*k) = w² + x² - y² - z²`.
-/
theorem splitNorm_ofCoords (w x y z : ℝ) :
    splitNorm (ofCoords w x y z) = w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [splitNorm, ofCoords, Matrix.det_fin_two]
  ring

/-- The split-quaternionic light cone `N(q)=0` is exactly the nonunit locus. -/
theorem isUnit_iff_splitNorm_ne_zero (q : HPrime) :
    IsUnit q ↔ splitNorm q ≠ 0 := by
  rw [splitNorm, Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero

/-- The singular split-quaternionic boundary is the determinant-zero boundary. -/
theorem not_isUnit_iff_splitNorm_eq_zero (q : HPrime) :
    ¬ IsUnit q ↔ splitNorm q = 0 := by
  rw [isUnit_iff_splitNorm_ne_zero]
  exact not_ne_iff

/-- The group of invertible split quaternions, `ℍ'ˣ ≅ GL₂(ℝ)`. -/
abbrev HPrimeUnit : Type :=
  Matrix.GeneralLinearGroup (Fin 2) ℝ

/-- The determinant/norm of an invertible split quaternion. -/
def unitNorm (a : HPrimeUnit) : ℝ :=
  splitNorm (a : HPrime)

@[simp]
theorem unitNorm_one :
    unitNorm (1 : HPrimeUnit) = 1 := by
  simp [unitNorm, splitNorm]

/-- Invertible split quaternions have nonzero split norm. -/
theorem unitNorm_ne_zero (a : HPrimeUnit) :
    unitNorm a ≠ 0 := by
  simpa [unitNorm, splitNorm] using Matrix.GeneralLinearGroup.det_ne_zero a

/-- Multiplicativity of the split norm on invertible split quaternions. -/
theorem unitNorm_mul (a b : HPrimeUnit) :
    unitNorm (a * b) = unitNorm a * unitNorm b := by
  simp [unitNorm, splitNorm, Matrix.det_mul]

/-- The norm-one split-quaternion sector, `SL₂(ℝ)`, imported directly from mathlib. -/
abbrev HPrimeNormOne : Type :=
  Matrix.SpecialLinearGroup (Fin 2) ℝ

@[simp]
theorem unitNorm_coe_normOne (a : HPrimeNormOne) :
    unitNorm (a : HPrimeUnit) = 1 := by
  simp [unitNorm, splitNorm]

/-! ## Scalar log-density extracted from the nonabelian frame -/

/--
The positive scalar Radon-Nikodym density extracted from an invertible
split-quaternionic frame.

The nonabelian frame lives in `GL₂(ℝ)`; its scalar density is `|N| = |det|`.
-/
def scalarRN (a : HPrimeUnit) : ℝ :=
  |unitNorm a|

theorem scalarRN_pos (a : HPrimeUnit) :
    0 < scalarRN a :=
  abs_pos.mpr (unitNorm_ne_zero a)

theorem scalarRN_ne_zero (a : HPrimeUnit) :
    scalarRN a ≠ 0 :=
  ne_of_gt (scalarRN_pos a)

theorem scalarRN_mul (a b : HPrimeUnit) :
    scalarRN (a * b) = scalarRN a * scalarRN b := by
  simp [scalarRN, unitNorm_mul, abs_mul]

/-- The scalar log-density extracted from an invertible split-quaternionic frame. -/
def logAbsSplitNorm (a : HPrimeUnit) : ℝ :=
  Real.log (scalarRN a)

/--
The split-quaternionic scalar log-density chain rule.

This is the determinant/log-Radon-Nikodym part of the nonabelian frame
cocycle: the frame multiplies in `GL₂(ℝ)`, while the scalar density is
`log |det|`.
-/
theorem logAbsSplitNorm_mul (a b : HPrimeUnit) :
    logAbsSplitNorm (a * b) = logAbsSplitNorm a + logAbsSplitNorm b := by
  unfold logAbsSplitNorm
  rw [scalarRN_mul]
  exact Real.log_mul (scalarRN_ne_zero a) (scalarRN_ne_zero b)

/-- The four-real-dimensional Jacobian density of left multiplication. -/
def jac4D (a : HPrimeUnit) : ℝ :=
  scalarRN a ^ 2

@[simp]
theorem jac4D_ne_zero (a : HPrimeUnit) :
    jac4D a ≠ 0 := by
  exact pow_ne_zero 2 (scalarRN_ne_zero a)

theorem jac4D_mul (a b : HPrimeUnit) :
    jac4D (a * b) = jac4D a * jac4D b := by
  simp [jac4D, scalarRN_mul]
  ring

/-- The four-real-dimensional log-Jacobian of left multiplication. -/
def logJac4D (a : HPrimeUnit) : ℝ :=
  Real.log (jac4D a)

/-- `log J₄ = 2 log |N|` for the split-quaternionic left action. -/
theorem logJac4D_eq_two_logAbsSplitNorm (a : HPrimeUnit) :
    logJac4D a = 2 * logAbsSplitNorm a := by
  simp [logJac4D, jac4D, logAbsSplitNorm, Real.log_pow]

/-- The four-real-dimensional split-quaternionic log-Jacobian chain rule. -/
theorem logJac4D_mul (a b : HPrimeUnit) :
    logJac4D (a * b) = logJac4D a + logJac4D b := by
  unfold logJac4D
  rw [jac4D_mul, Real.log_mul (jac4D_ne_zero a) (jac4D_ne_zero b)]

/-- Norm-one split-quaternionic frames are four-volume preserving. -/
theorem logJac4D_eq_zero_of_unitNorm_eq_one {a : HPrimeUnit} (ha : unitNorm a = 1) :
    logJac4D a = 0 := by
  simp [logJac4D, jac4D, scalarRN, ha]

@[simp]
theorem logJac4D_normOne (a : HPrimeNormOne) :
    logJac4D (a : HPrimeUnit) = 0 :=
  logJac4D_eq_zero_of_unitNorm_eq_one (unitNorm_coe_normOne a)

@[simp]
theorem scalarRN_eq_one_of_unitNorm_eq_one {a : HPrimeUnit} (ha : unitNorm a = 1) :
    scalarRN a = 1 := by
  simp [scalarRN, ha]

@[simp]
theorem scalarRN_normOne (a : HPrimeNormOne) :
    scalarRN (a : HPrimeUnit) = 1 :=
  scalarRN_eq_one_of_unitNorm_eq_one (unitNorm_coe_normOne a)

theorem logAbsSplitNorm_eq_zero_of_unitNorm_eq_one {a : HPrimeUnit} (ha : unitNorm a = 1) :
    logAbsSplitNorm a = 0 := by
  simp [logAbsSplitNorm, scalarRN, ha]

@[simp]
theorem logAbsSplitNorm_normOne (a : HPrimeNormOne) :
    logAbsSplitNorm (a : HPrimeUnit) = 0 :=
  logAbsSplitNorm_eq_zero_of_unitNorm_eq_one (unitNorm_coe_normOne a)

@[simp]
theorem jac4D_eq_one_of_unitNorm_eq_one {a : HPrimeUnit} (ha : unitNorm a = 1) :
    jac4D a = 1 := by
  simp [jac4D, scalarRN, ha]

@[simp]
theorem jac4D_normOne (a : HPrimeNormOne) :
    jac4D (a : HPrimeUnit) = 1 :=
  jac4D_eq_one_of_unitNorm_eq_one (unitNorm_coe_normOne a)

/-! ## Split-quaternionic frame cocycles with explicit action -/

/--
A nonabelian split-quaternionic frame-Jacobian cocycle.

The frame cocycle is `GL₂(ℝ)`-valued.  Scalar Radon-Nikodym/log-Jacobian data
is extracted by applying the split norm/determinant.
-/
abbrev HPrimeJacobianCocycle {G : Type} [Group G] (α : G →* MulAut HPrimeUnit) :
    Type :=
  TwistedGroupCocycle G HPrimeUnit α

section TwistedFrameCocycle

variable {G : Type} [Group G] {α : G →* MulAut HPrimeUnit}

/-- The positive scalar density extracted from a split-quaternionic frame cocycle. -/
def scalarRNOfCocycle (C : HPrimeJacobianCocycle α) (g : G) : ℝ :=
  scalarRN (C g)

theorem scalarRNOfCocycle_pos (C : HPrimeJacobianCocycle α) (g : G) :
    0 < scalarRNOfCocycle C g :=
  scalarRN_pos (C g)

theorem scalarRNOfCocycle_ne_zero (C : HPrimeJacobianCocycle α) (g : G) :
    scalarRNOfCocycle C g ≠ 0 :=
  ne_of_gt (scalarRNOfCocycle_pos C g)

/--
If the explicit coefficient action preserves the split norm, the scalar density
extracted from a split-quaternionic frame cocycle is multiplicative.
-/
theorem scalarRNOfCocycle_mul
    (C : HPrimeJacobianCocycle α)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (α g u) = unitNorm u)
    (g h : G) :
    scalarRNOfCocycle C (g * h) =
      scalarRNOfCocycle C g * scalarRNOfCocycle C h := by
  unfold scalarRNOfCocycle
  rw [TwistedGroupCocycle.chain_rule]
  simp [scalarRN, unitNorm_mul, hpres g (C h), abs_mul]

/-- The scalar log-Radon-Nikodym density extracted from a frame cocycle. -/
def logRNOfCocycle (C : HPrimeJacobianCocycle α) (g : G) : ℝ :=
  logAbsSplitNorm (C g)

/--
If the explicit coefficient action preserves the split norm, the extracted
scalar log-density is additive.
-/
theorem logRNOfCocycle_mul
    (C : HPrimeJacobianCocycle α)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (α g u) = unitNorm u)
    (g h : G) :
    logRNOfCocycle C (g * h) = logRNOfCocycle C g + logRNOfCocycle C h := by
  have hrn := scalarRNOfCocycle_mul C hpres g h
  unfold scalarRNOfCocycle at hrn
  unfold logRNOfCocycle logAbsSplitNorm
  rw [hrn]
  exact Real.log_mul (scalarRN_ne_zero (C g)) (scalarRN_ne_zero (C h))

/-- The four-dimensional log-Jacobian extracted from a frame cocycle. -/
def logJac4DOfCocycle (C : HPrimeJacobianCocycle α) (g : G) : ℝ :=
  logJac4D (C g)

/--
If the explicit coefficient action preserves the split norm, the extracted
four-dimensional log-Jacobian is additive.
-/
theorem logJac4DOfCocycle_mul
    (C : HPrimeJacobianCocycle α)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (α g u) = unitNorm u)
    (g h : G) :
    logJac4DOfCocycle C (g * h) =
      logJac4DOfCocycle C g + logJac4DOfCocycle C h := by
  unfold logJac4DOfCocycle
  rw [logJac4D_eq_two_logAbsSplitNorm, logJac4D_eq_two_logAbsSplitNorm,
    logJac4D_eq_two_logAbsSplitNorm]
  have hlog := logRNOfCocycle_mul C hpres g h
  unfold logRNOfCocycle at hlog
  rw [hlog]
  ring

end TwistedFrameCocycle

/-! ## The explicit four-dimensional Kronecker representatives -/

/-- Column-vectorization as a real-linear equivalence. -/
def vecLinearEquiv : HPrime ≃ₗ[ℝ] (Fin 2 × Fin 2 → ℝ) where
  toFun := Matrix.vec
  invFun v i j := v (j, i)
  left_inv q := by
    ext i j
    rfl
  right_inv v := by
    ext ij
    rcases ij with ⟨j, i⟩
    rfl
  map_add' q r := by
    rfl
  map_smul' c q := by
    rfl

/-- Left multiplication by a split quaternion as a real-linear map. -/
def leftMulLinear (a : HPrime) : HPrime →ₗ[ℝ] HPrime :=
  LinearMap.mulLeft ℝ a

@[simp]
theorem leftMulLinear_apply (a q : HPrime) :
    leftMulLinear a q = a * q :=
  rfl

/-- Right multiplication by a split quaternion as a real-linear map. -/
def rightMulLinear (b : HPrime) : HPrime →ₗ[ℝ] HPrime :=
  LinearMap.mulRight ℝ b

@[simp]
theorem rightMulLinear_apply (b q : HPrime) :
    rightMulLinear b q = q * b :=
  rfl

/-- Two-sided multiplication `q ↦ a*q*b` as a real-linear map. -/
def twoSidedMulLinear (a b : HPrime) : HPrime →ₗ[ℝ] HPrime :=
  (rightMulLinear b).comp (leftMulLinear a)

@[simp]
theorem twoSidedMulLinear_apply (a b q : HPrime) :
    twoSidedMulLinear a b q = a * q * b :=
  rfl

/--
The Kronecker matrix representing `q ↦ a*q` after mathlib column vectorization
`Matrix.vec`.
-/
def leftMulMatrix4 (a : HPrime) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  1 ⊗ₖ a

/--
The Kronecker matrix representing `q ↦ q*b` after mathlib column vectorization
`Matrix.vec`.
-/
def rightMulMatrix4 (b : HPrime) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (bᵀ) ⊗ₖ 1

/--
The Kronecker matrix representing `q ↦ a*q*b` after mathlib column
vectorization `Matrix.vec`.
-/
def twoSidedMulMatrix4 (a b : HPrime) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (bᵀ) ⊗ₖ a

/--
The Kronecker matrix representing split-quaternionic conjugation
`q ↦ a*q*a⁻¹`.
-/
def conjugationMatrix4 (a : HPrimeUnit) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  twoSidedMulMatrix4 (a : HPrime) ((a⁻¹ : HPrimeUnit) : HPrime)

/-- The Kronecker representative of left multiplication acts as left multiplication. -/
theorem leftMulMatrix4_mulVec_vec (a q : HPrime) :
    leftMulMatrix4 a *ᵥ Matrix.vec q = Matrix.vec (a * q) := by
  simpa [leftMulMatrix4] using (Matrix.vec_mul_eq_mulVec a q).symm

/-- The Kronecker representative of right multiplication acts as right multiplication. -/
theorem rightMulMatrix4_mulVec_vec (b q : HPrime) :
    rightMulMatrix4 b *ᵥ Matrix.vec q = Matrix.vec (q * b) := by
  simpa [rightMulMatrix4] using
    (Matrix.kronecker_mulVec_vec (A := (1 : HPrime)) (X := q) (B := (bᵀ)))

/-- The Kronecker representative of two-sided multiplication acts as `q ↦ a*q*b`. -/
theorem twoSidedMulMatrix4_mulVec_vec (a b q : HPrime) :
    twoSidedMulMatrix4 a b *ᵥ Matrix.vec q = Matrix.vec (a * q * b) := by
  simpa [twoSidedMulMatrix4, Matrix.mul_assoc] using
    (Matrix.kronecker_mulVec_vec (A := a) (X := q) (B := (bᵀ)))

/--
The vectorized linear map of left multiplication is represented by
`leftMulMatrix4`.
-/
theorem vecLinearEquiv_conj_leftMulLinear (a : HPrime) :
    (vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
        leftMulLinear a ∘ₗ
        (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)
      =
    Matrix.mulVecLin (leftMulMatrix4 a) := by
  apply LinearMap.ext
  intro v
  ext ij
  have hv : Matrix.vec (vecLinearEquiv.symm v) = v :=
    vecLinearEquiv.right_inv v
  change Matrix.vec (a * vecLinearEquiv.symm v) ij = (leftMulMatrix4 a *ᵥ v) ij
  have h := congr_fun (leftMulMatrix4_mulVec_vec a (vecLinearEquiv.symm v)) ij
  rw [hv] at h
  exact h.symm

/--
The vectorized linear map of right multiplication is represented by
`rightMulMatrix4`.
-/
theorem vecLinearEquiv_conj_rightMulLinear (b : HPrime) :
    (vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
        rightMulLinear b ∘ₗ
        (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)
      =
    Matrix.mulVecLin (rightMulMatrix4 b) := by
  apply LinearMap.ext
  intro v
  ext ij
  have hv : Matrix.vec (vecLinearEquiv.symm v) = v :=
    vecLinearEquiv.right_inv v
  change Matrix.vec (vecLinearEquiv.symm v * b) ij = (rightMulMatrix4 b *ᵥ v) ij
  have h := congr_fun (rightMulMatrix4_mulVec_vec b (vecLinearEquiv.symm v)) ij
  rw [hv] at h
  exact h.symm

/--
The vectorized linear map of two-sided multiplication is represented by
`twoSidedMulMatrix4`.
-/
theorem vecLinearEquiv_conj_twoSidedMulLinear (a b : HPrime) :
    (vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
        twoSidedMulLinear a b ∘ₗ
        (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)
      =
    Matrix.mulVecLin (twoSidedMulMatrix4 a b) := by
  apply LinearMap.ext
  intro v
  ext ij
  have hv : Matrix.vec (vecLinearEquiv.symm v) = v :=
    vecLinearEquiv.right_inv v
  change Matrix.vec (a * vecLinearEquiv.symm v * b) ij =
    (twoSidedMulMatrix4 a b *ᵥ v) ij
  have h := congr_fun (twoSidedMulMatrix4_mulVec_vec a b (vecLinearEquiv.symm v)) ij
  rw [hv] at h
  exact h.symm

/-- The Kronecker representative of conjugation acts as `q ↦ a*q*a⁻¹`. -/
theorem conjugationMatrix4_mulVec_vec (a : HPrimeUnit) (q : HPrime) :
    conjugationMatrix4 a *ᵥ Matrix.vec q =
      Matrix.vec ((a : HPrime) * q * ((a⁻¹ : HPrimeUnit) : HPrime)) := by
  simpa [conjugationMatrix4] using
    twoSidedMulMatrix4_mulVec_vec (a : HPrime) ((a⁻¹ : HPrimeUnit) : HPrime) q

/-- The four-dimensional determinant of left multiplication is `N(a)^2`. -/
theorem det_leftMulMatrix4_eq_norm_sq (a : HPrime) :
    Matrix.det (leftMulMatrix4 a) = splitNorm a ^ 2 := by
  simp [leftMulMatrix4, splitNorm, Matrix.det_kronecker]

/--
For invertible split quaternions, the absolute determinant of the explicit
four-dimensional left-multiplication representative is the scalar `J₄ = |N|²`.
-/
theorem abs_det_leftMulMatrix4_eq_jac4D (a : HPrimeUnit) :
    |Matrix.det (leftMulMatrix4 (a : HPrime))| = jac4D a := by
  rw [det_leftMulMatrix4_eq_norm_sq]
  simp [jac4D, scalarRN, unitNorm, splitNorm]

/-- The four-dimensional determinant of right multiplication is `N(b)^2`. -/
theorem det_rightMulMatrix4_eq_norm_sq (b : HPrime) :
    Matrix.det (rightMulMatrix4 b) = splitNorm b ^ 2 := by
  simp [rightMulMatrix4, splitNorm, Matrix.det_kronecker]

/--
For invertible split quaternions, the absolute determinant of the explicit
four-dimensional right-multiplication representative is the scalar `J₄ = |N|²`.
-/
theorem abs_det_rightMulMatrix4_eq_jac4D (b : HPrimeUnit) :
    |Matrix.det (rightMulMatrix4 (b : HPrime))| = jac4D b := by
  rw [det_rightMulMatrix4_eq_norm_sq]
  simp [jac4D, scalarRN, unitNorm, splitNorm]

/-- The four-dimensional determinant of `q ↦ a*q*b` is `(N(a)N(b))^2`. -/
theorem det_twoSidedMulMatrix4_eq_norm_mul_sq (a b : HPrime) :
    Matrix.det (twoSidedMulMatrix4 a b) = (splitNorm a * splitNorm b) ^ 2 := by
  simp [twoSidedMulMatrix4, splitNorm, Matrix.det_kronecker]
  ring

/-- The real-linear determinant of left multiplication is `N(a)^2`. -/
theorem det_leftMulLinear_eq_norm_sq (a : HPrime) :
    LinearMap.det (leftMulLinear a) = splitNorm a ^ 2 := by
  calc
    LinearMap.det (leftMulLinear a)
        = LinearMap.det
            ((vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
              leftMulLinear a ∘ₗ
              (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)) := by
          rw [LinearMap.det_conj]
    _ = LinearMap.det (Matrix.mulVecLin (leftMulMatrix4 a)) := by
          rw [vecLinearEquiv_conj_leftMulLinear]
    _ = Matrix.det (leftMulMatrix4 a) := by
          change LinearMap.det (Matrix.toLin' (leftMulMatrix4 a)) =
            Matrix.det (leftMulMatrix4 a)
          simp
    _ = splitNorm a ^ 2 :=
          det_leftMulMatrix4_eq_norm_sq a

/-- The real-linear determinant of right multiplication is `N(b)^2`. -/
theorem det_rightMulLinear_eq_norm_sq (b : HPrime) :
    LinearMap.det (rightMulLinear b) = splitNorm b ^ 2 := by
  calc
    LinearMap.det (rightMulLinear b)
        = LinearMap.det
            ((vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
              rightMulLinear b ∘ₗ
              (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)) := by
          rw [LinearMap.det_conj]
    _ = LinearMap.det (Matrix.mulVecLin (rightMulMatrix4 b)) := by
          rw [vecLinearEquiv_conj_rightMulLinear]
    _ = Matrix.det (rightMulMatrix4 b) := by
          change LinearMap.det (Matrix.toLin' (rightMulMatrix4 b)) =
            Matrix.det (rightMulMatrix4 b)
          simp
    _ = splitNorm b ^ 2 :=
          det_rightMulMatrix4_eq_norm_sq b

/-- The real-linear determinant of `q ↦ a*q*b` is `(N(a)N(b))^2`. -/
theorem det_twoSidedMulLinear_eq_norm_mul_sq (a b : HPrime) :
    LinearMap.det (twoSidedMulLinear a b) = (splitNorm a * splitNorm b) ^ 2 := by
  calc
    LinearMap.det (twoSidedMulLinear a b)
        = LinearMap.det
            ((vecLinearEquiv : HPrime →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ)) ∘ₗ
              twoSidedMulLinear a b ∘ₗ
              (vecLinearEquiv.symm : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] HPrime)) := by
          rw [LinearMap.det_conj]
    _ = LinearMap.det (Matrix.mulVecLin (twoSidedMulMatrix4 a b)) := by
          rw [vecLinearEquiv_conj_twoSidedMulLinear]
    _ = Matrix.det (twoSidedMulMatrix4 a b) := by
          change LinearMap.det (Matrix.toLin' (twoSidedMulMatrix4 a b)) =
            Matrix.det (twoSidedMulMatrix4 a b)
          simp
    _ = (splitNorm a * splitNorm b) ^ 2 :=
          det_twoSidedMulMatrix4_eq_norm_mul_sq a b

/-- The real-linear determinant of conjugation `q ↦ a*q*a⁻¹` is `1`. -/
theorem det_conjMulLinear_eq_one (a : HPrimeUnit) :
    LinearMap.det (twoSidedMulLinear (a : HPrime) ((a⁻¹ : HPrimeUnit) : HPrime)) = 1 := by
  rw [det_twoSidedMulLinear_eq_norm_mul_sq]
  have hmul : splitNorm (a : HPrime) *
      splitNorm ((a⁻¹ : HPrimeUnit) : HPrime) = 1 := by
    calc
      splitNorm (a : HPrime) * splitNorm ((a⁻¹ : HPrimeUnit) : HPrime)
          = unitNorm a * unitNorm (a⁻¹ : HPrimeUnit) := rfl
      _ = unitNorm (a * a⁻¹) := (unitNorm_mul a (a⁻¹ : HPrimeUnit)).symm
      _ = 1 := by simp
  rw [hmul, one_pow]

/-- The four-dimensional Jacobian density of two-sided multiplication. -/
def jac4DTwoSided (a b : HPrimeUnit) : ℝ :=
  (scalarRN a * scalarRN b) ^ 2

/--
For invertible split quaternions, the absolute determinant of `q ↦ a*q*b` is
`|N(a)N(b)|²`.
-/
theorem abs_det_twoSidedMulMatrix4_eq_jac4DTwoSided (a b : HPrimeUnit) :
    |Matrix.det (twoSidedMulMatrix4 (a : HPrime) (b : HPrime))| =
      jac4DTwoSided a b := by
  rw [det_twoSidedMulMatrix4_eq_norm_mul_sq]
  simp [jac4DTwoSided, scalarRN, unitNorm, splitNorm, abs_mul]

/-- Split-quaternionic conjugation is four-volume preserving. -/
theorem det_conjugationMatrix4_eq_one (a : HPrimeUnit) :
    Matrix.det (conjugationMatrix4 a) = 1 := by
  rw [conjugationMatrix4, det_twoSidedMulMatrix4_eq_norm_mul_sq]
  have hmul : unitNorm a * unitNorm a⁻¹ = 1 := by
    have hleft : unitNorm (a * a⁻¹) = 1 := by simp
    rw [unitNorm_mul] at hleft
    exact hleft
  have hsplit : splitNorm (a : HPrime) *
      splitNorm ((a⁻¹ : HPrimeUnit) : HPrime) = 1 := by
    simpa [unitNorm] using hmul
  rw [hsplit]
  norm_num

/-- The absolute Jacobian of split-quaternionic conjugation is `1`. -/
theorem abs_det_conjugationMatrix4_eq_one (a : HPrimeUnit) :
    |Matrix.det (conjugationMatrix4 a)| = 1 := by
  rw [det_conjugationMatrix4_eq_one]
  norm_num

/-! ## Coordinate convergence and linear sector splitting -/

/--
Topological convergence in the finite split-quaternionic matrix model is
entrywise convergence.

This is the formal version of the finite-dimensional correction: convergence
splits through the underlying real coordinates.
-/
theorem tendsto_hprime_iff_entries {ι : Type*} {l : Filter ι} {qSeq : ι → HPrime}
    {q : HPrime} :
    Filter.Tendsto qSeq l (nhds q) ↔
      ∀ i j : Fin 2, Filter.Tendsto (fun n => qSeq n i j) l (nhds (q i j)) := by
  rw [tendsto_pi_nhds]
  constructor
  · intro h i j
    exact tendsto_pi_nhds.mp (h i) j
  · intro h i
    exact tendsto_pi_nhds.mpr fun j => h i j

/-- The first column sector in the `M₂(ℝ)` model. -/
def firstColumn (q : HPrime) : Fin 2 → ℝ :=
  fun i => q i 0

/-- The second column sector in the `M₂(ℝ)` model. -/
def secondColumn (q : HPrime) : Fin 2 → ℝ :=
  fun i => q i 1

/--
Convergence in `HPrime` is equivalent to convergence of the two column
sectors.

The theorem is purely topological.  It does not assert algebraic independence:
matrix multiplication still couples the sectors.
-/
theorem tendsto_hprime_iff_columns {ι : Type*} {l : Filter ι} {qSeq : ι → HPrime}
    {q : HPrime} :
    Filter.Tendsto qSeq l (nhds q) ↔
      Filter.Tendsto (fun n => firstColumn (qSeq n)) l (nhds (firstColumn q)) ∧
        Filter.Tendsto (fun n => secondColumn (qSeq n)) l (nhds (secondColumn q)) := by
  rw [tendsto_hprime_iff_entries]
  constructor
  · intro h
    constructor
    · rw [tendsto_pi_nhds]
      intro i
      exact h i 0
    · rw [tendsto_pi_nhds]
      intro i
      exact h i 1
  · intro h i j
    fin_cases j
    · exact tendsto_pi_nhds.mp h.1 i
    · exact tendsto_pi_nhds.mp h.2 i

/-! ## Abstract extraction from a nonabelian frame cocycle -/

section FrameCocycle

variable {G : Type*} [Monoid G] [MulDistribMulAction G HPrimeUnit]

/--
If the coefficient action preserves the split norm, the scalar
Radon-Nikodym density extracted from a split-quaternionic frame cocycle is a
multiplicative scalar cocycle.
-/
theorem scalarRN_cocycle_chain_rule
    (C : MultiplicativeOneCocycle G HPrimeUnit)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (g • u) = unitNorm u)
    (g h : G) :
    scalarRN (C (g * h)) = scalarRN (C g) * scalarRN (C h) := by
  rw [C.chain_rule]
  simp [scalarRN, unitNorm_mul, hpres g (C h), abs_mul]

/--
If the coefficient action preserves the split norm, the scalar log-density
extracted from a split-quaternionic frame cocycle is additive.
-/
theorem logAbsSplitNorm_cocycle_chain_rule
    (C : MultiplicativeOneCocycle G HPrimeUnit)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (g • u) = unitNorm u)
    (g h : G) :
    logAbsSplitNorm (C (g * h)) =
      logAbsSplitNorm (C g) + logAbsSplitNorm (C h) := by
  unfold logAbsSplitNorm
  rw [scalarRN_cocycle_chain_rule C hpres g h]
  exact Real.log_mul (scalarRN_ne_zero (C g)) (scalarRN_ne_zero (C h))

/--
The corresponding four-dimensional log-Jacobian extracted from a
split-quaternionic frame cocycle is additive.
-/
theorem logJac4D_cocycle_chain_rule
    (C : MultiplicativeOneCocycle G HPrimeUnit)
    (hpres : ∀ g : G, ∀ u : HPrimeUnit, unitNorm (g • u) = unitNorm u)
    (g h : G) :
    logJac4D (C (g * h)) = logJac4D (C g) + logJac4D (C h) := by
  rw [logJac4D_eq_two_logAbsSplitNorm, logJac4D_eq_two_logAbsSplitNorm,
    logJac4D_eq_two_logAbsSplitNorm]
  have hlog := logAbsSplitNorm_cocycle_chain_rule C hpres g h
  rw [hlog]
  ring

end FrameCocycle

/-! ## Groupoid-valued split-quaternionic frame cocycles -/

section GroupoidFrameCocycle

variable {Γ : Type*} [Category Γ]

/--
A split-quaternionic coefficient system over a category/groupoid.

Every fiber is the nonabelian frame group `GL₂(ℝ)`, and arrows transport
frames by group homomorphisms.
-/
structure HPrimeGroupoidCoefficientSystem (Γ : Type*) [Category Γ] where
  transport : ∀ {X Y : Γ}, (X ⟶ Y) → HPrimeUnit →* HPrimeUnit
  transport_id : ∀ X : Γ, transport (𝟙 X) = MonoidHom.id HPrimeUnit
  transport_comp :
    ∀ {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z),
      transport (f ≫ g) = (transport f).comp (transport g)

namespace HPrimeGroupoidCoefficientSystem

variable (S : HPrimeGroupoidCoefficientSystem Γ)

/-- Realize the split-quaternionic coefficient system as the generic groupoid cocycle substrate. -/
def toGroupoidMultiplicativeCoefficientSystem :
    GroupoidMultiplicativeCoefficientSystem Γ where
  coeff _ := HPrimeUnit
  instGroup _ := inferInstance
  transport := S.transport
  transport_id := S.transport_id
  transport_comp := S.transport_comp

end HPrimeGroupoidCoefficientSystem

/--
A split-quaternionic frame Jacobian cocycle over a category/groupoid.

The generic owner is `GroupoidMultiplicativeCocycle`; this abbrev specializes
its coefficient fibers to `GL₂(ℝ)`.
-/
abbrev HPrimeGroupoidCocycle (S : HPrimeGroupoidCoefficientSystem Γ) :=
  GroupoidMultiplicativeCocycle S.toGroupoidMultiplicativeCoefficientSystem

/-- Constant split-quaternionic coefficients, with trivial arrow transport. -/
def constantHPrimeGroupoidCoefficientSystem (Γ : Type*) [Category Γ] :
    HPrimeGroupoidCoefficientSystem Γ where
  transport _ := MonoidHom.id HPrimeUnit
  transport_id _ := rfl
  transport_comp _ _ := rfl

/-- The groupoid chain rule for split-quaternionic frame cocycles. -/
theorem hprimeGroupoidCocycle_chain_rule
    {S : HPrimeGroupoidCoefficientSystem Γ}
    (C : HPrimeGroupoidCocycle S)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    C.toFun (f ≫ g) =
      C.toFun f *
        S.toGroupoidMultiplicativeCoefficientSystem.transport f (C.toFun g) :=
  C.chain_rule f g

/--
If arrow transport preserves the split norm, the extracted scalar
Radon-Nikodym density is multiplicative along groupoid composition.
-/
theorem scalarRN_groupoidCocycle_chain_rule
    {S : HPrimeGroupoidCoefficientSystem Γ}
    (C : HPrimeGroupoidCocycle S)
    (hpres : ∀ {X Y : Γ} (f : X ⟶ Y) (u : HPrimeUnit),
      unitNorm (S.transport f u) = unitNorm u)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    scalarRN (C.toFun (f ≫ g)) = scalarRN (C.toFun f) * scalarRN (C.toFun g) := by
  rw [hprimeGroupoidCocycle_chain_rule C f g]
  simp [HPrimeGroupoidCoefficientSystem.toGroupoidMultiplicativeCoefficientSystem,
    scalarRN, unitNorm_mul, hpres f (C.toFun g), abs_mul]

/--
If arrow transport preserves the split norm, the extracted logarithmic
Radon-Nikodym density is additive along groupoid composition.
-/
theorem logAbsSplitNorm_groupoidCocycle_chain_rule
    {S : HPrimeGroupoidCoefficientSystem Γ}
    (C : HPrimeGroupoidCocycle S)
    (hpres : ∀ {X Y : Γ} (f : X ⟶ Y) (u : HPrimeUnit),
      unitNorm (S.transport f u) = unitNorm u)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    logAbsSplitNorm (C.toFun (f ≫ g)) =
      logAbsSplitNorm (C.toFun f) + logAbsSplitNorm (C.toFun g) := by
  unfold logAbsSplitNorm
  rw [scalarRN_groupoidCocycle_chain_rule C hpres f g]
  exact Real.log_mul (scalarRN_ne_zero (C.toFun f)) (scalarRN_ne_zero (C.toFun g))

/--
The four-dimensional log-Jacobian extracted from a split-quaternionic
groupoid frame cocycle is additive along groupoid composition.
-/
theorem logJac4D_groupoidCocycle_chain_rule
    {S : HPrimeGroupoidCoefficientSystem Γ}
    (C : HPrimeGroupoidCocycle S)
    (hpres : ∀ {X Y : Γ} (f : X ⟶ Y) (u : HPrimeUnit),
      unitNorm (S.transport f u) = unitNorm u)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    logJac4D (C.toFun (f ≫ g)) =
      logJac4D (C.toFun f) + logJac4D (C.toFun g) := by
  rw [logJac4D_eq_two_logAbsSplitNorm, logJac4D_eq_two_logAbsSplitNorm,
    logJac4D_eq_two_logAbsSplitNorm]
  rw [logAbsSplitNorm_groupoidCocycle_chain_rule C hpres f g]
  ring

end GroupoidFrameCocycle

end SplitQuaternionicJacobian
end InfoGeometry.Cocycle
