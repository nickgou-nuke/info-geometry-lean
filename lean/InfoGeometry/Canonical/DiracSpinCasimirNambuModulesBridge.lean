/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.Algebra.AssociativeNambuOperators
import InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Real Majorana–Dirac Vector Lift, Doubled Chiral Spin Casimirs, & Noncommutative Nambu Modules

Formalizes the four-stage purely real (`0` complex `i`) operator chain, reusing committed
repository owners `DoubledMinkowskiBdGColimitBridge` (`zCut2`, `xMir2`),
`DoubledMinkowskiRotatingSpinInstability` (`eps2`), `AssociativeNambuOperators`
(`alternatingProduct3`, `ad_comm_mem_derivations`, `squareZero_sandwich_mul`,
`alternatingProduct3_sandwich_range`), and `PeirceSpine`:

1. **Real Majorana–Dirac Volume & Clifford Relations (`Cl(3,1) ≅ M₄(ℝ)`)**:
   `diracOmega4 = γ₀ γ₁ γ₂ γ₃` (`ω₄² = -I₄`) and the complete anticommutation relations
   `{γ_μ, γ_ν} = -2 η_μν I₄`.
2. **Faithful Vector-to-Dirac Lift & Null Isotropy**:
   `diracVectorLift : (Fin 4 → ℝ) →ₗ[ℝ] M₄(ℝ)` is injective (`diracVectorLift_faithful_and_isotropic`),
   turns the Lorentz inner product into `{ι(u), ι(v)} = (-2 * η(u, v)) • I₄`, and equates
   square-zero nilpotency `ι(v)² = 0` with Lorentz isotropy `η(v, v) = 0` (`Tr(ι(v)²) = 0`).
3. **Lorentz `so(3,1)` Spin Algebra & Doubled 8D Chiral Spin Algebras**:
   In `M₄(ℝ)`, `(spinJ1..3, boostK1..3)` satisfy `so(3,1)` with Casimirs `C₁ = J² - K² = -3/2 I₄`
   and `C₂ = J · K = -3/4 ω₄`. Passing to the doubled chiral bispinor carrier `M₈(ℝ) ≅ M₂(M₄(ℝ))`
   recovers two commuting `su(2)` algebras `A_i = P₋ ⊗ J_i`, `B_i = P₊ ⊗ J_i` (`[A_i, B_j] = 0`),
   exchanged by the Mirror involution `J_mir = X ⊗ I₄`, with independent Casimirs `C_A, C_B`.
4. **Noncommutative Nambu 3-Brackets, Multiplication Modules, & Isotropic Collapse**:
   Bridges `nambuBracket3` to `PeirceSpine.alternatingProduct3`, proves the Spin-Nambu-Casimir law
   `[J₁, J₂, J₃]_Nambu = J₁² + J₂² + J₃²`, the right-module & Leibniz laws (`nambuLeftMul`,
   `nambuDeriv`), Peirce corner isotropy `P B (1 - P)`, and null-vector Dirac sandwich collapse.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `diracGamma_clifford_relations`
* `diracVectorLift_faithful_and_isotropic`, `diracVectorLift_null_trace_zero`
* `exists_noncomm_mat8_bispinor`, `lorentz_spin_algebra_and_two_casimirs`,
  `two_chiral_spin_algebras_and_casimirs`
* `nambuBracket3_eq_alternatingProduct3`, `nambuBracket3_alt_skew_and_spin_casimir`,
  `noncommutative_nambu_module_and_isotropic_collapse`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* General ring / SU(2) Casimir & Peirce/null sandwich laws hold under their explicit algebraic
  commutator/idempotent/null hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
* Infinite-dimensional curved-spacetime spin-connection bundles and unbounded trace-class Nambu
  operator modules remain outside this finite-matrix canonical module.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.AssociativeNambuOperators

/-! ### Part 1: Real Cl(3,1) Clifford Relations & Volume Element -/

/-- Chiral idempotent projectors `P₊, P₋ ∈ M₂(ℝ)`. -/
def pPlus2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def pMinus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- Real Majorana–Dirac Clifford matrices in `M₄(ℝ) ≅ M₂(ℝ) ⊗ M₂(ℝ)` built from
`zCut2`, `xMir2`, and `eps2` (`γ₀² = -1`, `γ₁² = γ₂² = γ₃² = +1`). -/
def diracGamma0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := eps2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
def diracGamma1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := xMir2 ⊗ₖ zCut2
def diracGamma2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := xMir2 ⊗ₖ xMir2
def diracGamma3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Real Clifford volume element `ω₄ = γ₀ γ₁ γ₂ γ₃` in `M₄(ℝ)` (`ω₄² = -I₄`). -/
def diracOmega4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3

private lemma kron_add_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A₁ A₂ : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, add_mul]

private lemma kron_add_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B₁ B₂ : Matrix m₂ n₂ R) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_add]

private lemma kron_sub_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A₁ A₂ : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, sub_mul]

private lemma kron_sub_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B₁ B₂ : Matrix m₂ n₂ R) :
    A ⊗ₖ (B₁ - B₂) = A ⊗ₖ B₁ - A ⊗ₖ B₂ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_sub]

private lemma one_kron_one_real4 :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
  Matrix.one_kronecker_one

private lemma one_kron_one_real8 :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) = 1 :=
  Matrix.one_kronecker_one

private lemma kron_neg_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_neg {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : (-A) ⊗ₖ (-B) = A ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_smul_left {m₁ n₁ m₂ n₂ : Type*}
    (c : ℝ) (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) :
    (c • A) ⊗ₖ B = c • (A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_assoc]

private lemma kron_smul_right {m₁ n₁ m₂ n₂ : Type*}
    (c : ℝ) (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) :
    A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_left_comm]

private lemma pauli2_mul_table :
    (zCut2 * zCut2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (xMir2 * xMir2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (zCut2 * xMir2 = eps2) ∧ (xMir2 * zCut2 = -eps2) ∧
    (zCut2 * eps2 = xMir2) ∧ (eps2 * zCut2 = -xMir2) ∧
    (xMir2 * eps2 = -zCut2) ∧ (eps2 * xMir2 = zCut2) ∧
    (pPlus2 * pPlus2 = pPlus2) ∧ (pMinus2 * pMinus2 = pMinus2) ∧
    (pPlus2 * pMinus2 = 0) ∧ (pMinus2 * pPlus2 = 0) ∧
    (xMir2 * pMinus2 * xMir2 = pPlus2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [pPlus2, pMinus2, zCut2, xMir2, eps2, Matrix.mul_apply,
          Fin.sum_univ_two] }

private lemma chiral_proj_zCut2 :
    (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - zCut2) = pMinus2 ∧
    (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + zCut2) = pPlus2 := by
  constructor <;>
    { ext i j; fin_cases i <;> fin_cases j <;> (simp [zCut2, pPlus2, pMinus2]; try norm_num) }

lemma diracGamma_clifford_relations :
    diracGamma0 * diracGamma0 = -1 ∧
    diracGamma1 * diracGamma1 = 1 ∧
    diracGamma2 * diracGamma2 = 1 ∧
    diracGamma3 * diracGamma3 = 1 ∧
    diracGamma0 * diracGamma1 + diracGamma1 * diracGamma0 = 0 ∧
    diracGamma0 * diracGamma2 + diracGamma2 * diracGamma0 = 0 ∧
    diracGamma0 * diracGamma3 + diracGamma3 * diracGamma0 = 0 ∧
    diracGamma1 * diracGamma2 + diracGamma2 * diracGamma1 = 0 ∧
    diracGamma1 * diracGamma3 + diracGamma3 * diracGamma1 = 0 ∧
    diracGamma2 * diracGamma3 + diracGamma3 * diracGamma2 = 0 := by
  have hT := pauli2_mul_table
  have hZ2 := hT.1
  have hX2 := hT.2.1
  have hE2 := hT.2.2.1
  have hZX : zCut2 * xMir2 + xMir2 * zCut2 = 0 := by
    rw [hT.2.2.2.1, hT.2.2.2.2.1, add_neg_cancel]
  have hZE : zCut2 * eps2 + eps2 * zCut2 = 0 := by
    rw [hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, add_neg_cancel]
  have hXE : xMir2 * eps2 + eps2 * xMir2 = 0 := by
    rw [hT.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.1, neg_add_cancel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [diracGamma0]
    rw [← Matrix.mul_kronecker_mul, hE2, Matrix.one_mul, kron_neg_left, Matrix.one_kronecker_one]
  · dsimp [diracGamma1]
    rw [← Matrix.mul_kronecker_mul, hX2, hZ2, Matrix.one_kronecker_one]
  · dsimp [diracGamma2]
    rw [← Matrix.mul_kronecker_mul, hX2, Matrix.one_kronecker_one]
  · dsimp [diracGamma3]
    rw [← Matrix.mul_kronecker_mul, hZ2, Matrix.one_mul, Matrix.one_kronecker_one]
  · dsimp [diracGamma0, diracGamma1]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← kron_add_left, add_comm (eps2 * xMir2), hXE, Matrix.zero_kronecker]
  · dsimp [diracGamma0, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← kron_add_left, add_comm (eps2 * xMir2), hXE, Matrix.zero_kronecker]
  · dsimp [diracGamma0, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← kron_add_left, add_comm (eps2 * zCut2), hZE, Matrix.zero_kronecker]
  · dsimp [diracGamma1, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX2,
      ← kron_add_right, hZX, Matrix.kronecker_zero]
  · dsimp [diracGamma1, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← kron_add_left, add_comm (xMir2 * zCut2), hZX, Matrix.zero_kronecker]
  · dsimp [diracGamma2, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← kron_add_left, add_comm (xMir2 * zCut2), hZX, Matrix.zero_kronecker]

/-! ### Part 2: Lifting Spacetime Vectors to Dirac Operators & Null Isotropy -/

/-- The `ℝ`-linear lift `ι : (Fin 4 → ℝ) →ₗ[ℝ] M₄(ℝ)` mapping a 4-vector `v` to its real
Majorana–Dirac operator `v 0 • γ₀ + v 1 • γ₁ + v 2 • γ₂ + v 3 • γ₃`. -/
def diracVectorLift : (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ where
  toFun v := v 0 • diracGamma0 + v 1 • diracGamma1 + v 2 • diracGamma2 + v 3 • diracGamma3
  map_add' u v := by simp only [Pi.add_apply, add_smul]; module
  map_smul' c u := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module

/-- Lorentzian bilinear pairing on `Fin 4 → ℝ` in `(+,-,-,-)` convention. -/
def lorentzInner (u v : Fin 4 → ℝ) : ℝ :=
  u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

private lemma scalar_lorentz_jordan_coeff (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) :
    -2 * (a₀ * b₀ - a₁ * b₁ - a₂ * b₂ - a₃ * b₃) =
      -(a₀ * b₀ + b₀ * a₀) + (a₁ * b₁ + b₁ * a₁) + (a₂ * b₂ + b₂ * a₂) + (a₃ * b₃ + b₃ * a₃) := by
  ring

private lemma scalar_two_mul_neg (x : ℝ) :
    2 * (-x) = -2 * x := by
  ring

private lemma sub_eq_zero_of_rev {x y : ℝ} (h : y - x = 0) : x - y = 0 := by
  linarith [h]

/-- **Theorem 1 (Faithful Vector-to-Dirac-Operator Lift & Isotropic Null Equivalence)**:
1. `diracVectorLift` is strictly injective (`ℝ⁴ ↪ M₄(ℝ)`).
2. The Jordan anticommutator of two lifted vectors equals `(-2 * η(u, v)) • I₄`.
3. A lifted vector operator squares to zero (`ι(v)² = 0`) if and only if `v` is Lorentz-isotropic
   (`lorentzInner v v = 0`). -/
theorem diracVectorLift_faithful_and_isotropic (u v : Fin 4 → ℝ) :
    Function.Injective diracVectorLift ∧
    (diracVectorLift u * diracVectorLift v + diracVectorLift v * diracVectorLift u =
      (-2 * lorentzInner u v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (diracVectorLift v * diracVectorLift v = 0 ↔ lorentzInner v v = 0) := by
  obtain ⟨h00, h11, h22, h33, h01, h02, h03, h12, h13, h23⟩ := diracGamma_clifford_relations
  have hAnti01 : diracGamma1 * diracGamma0 = -(diracGamma0 * diracGamma1) :=
    eq_neg_of_add_eq_zero_right h01
  have hAnti02 : diracGamma2 * diracGamma0 = -(diracGamma0 * diracGamma2) :=
    eq_neg_of_add_eq_zero_right h02
  have hAnti03 : diracGamma3 * diracGamma0 = -(diracGamma0 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h03
  have hAnti12 : diracGamma2 * diracGamma1 = -(diracGamma1 * diracGamma2) :=
    eq_neg_of_add_eq_zero_right h12
  have hAnti13 : diracGamma3 * diracGamma1 = -(diracGamma1 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h13
  have hAnti23 : diracGamma3 * diracGamma2 = -(diracGamma2 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h23
  have hJordan : ∀ a b : Fin 4 → ℝ,
      diracVectorLift a * diracVectorLift b + diracVectorLift b * diracVectorLift a =
      (-2 * lorentzInner a b) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    intro a b
    dsimp [diracVectorLift, lorentzInner]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    rw [h00, h11, h22, h33, hAnti01, hAnti02, hAnti03, hAnti12, hAnti13, hAnti23]
    simp only [smul_neg]
    rw [scalar_lorentz_jordan_coeff (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2) (b 3)]
    module
  have hInj : Function.Injective diracVectorLift := by
    intro a b hab
    have hDiff : diracVectorLift (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h0eq : a 0 - b 0 = 0 := by
      have hJ := hJordan (a - b) ![1, 0, 0, 0]
      rw [show diracVectorLift ![1, 0, 0, 0] = diracGamma0 by simp [diracVectorLift],
        hDiff, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hJ
      have h00' := congrFun (congrFun hJ (0, 0)) (0, 0)
      simp [lorentzInner] at h00'
      exact h00'
    have h1eq : a 1 - b 1 = 0 := by
      have hJ := hJordan (a - b) ![0, 1, 0, 0]
      rw [show diracVectorLift ![0, 1, 0, 0] = diracGamma1 by simp [diracVectorLift],
        hDiff, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hJ
      have h00' := congrFun (congrFun hJ (0, 0)) (0, 0)
      simp [lorentzInner] at h00'
      exact sub_eq_zero_of_rev h00'
    have h2eq : a 2 - b 2 = 0 := by
      have hJ := hJordan (a - b) ![0, 0, 1, 0]
      rw [show diracVectorLift ![0, 0, 1, 0] = diracGamma2 by simp [diracVectorLift],
        hDiff, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hJ
      have h00' := congrFun (congrFun hJ (0, 0)) (0, 0)
      simp [lorentzInner] at h00'
      exact sub_eq_zero_of_rev h00'
    have h3eq : a 3 - b 3 = 0 := by
      have hJ := hJordan (a - b) ![0, 0, 0, 1]
      rw [show diracVectorLift ![0, 0, 0, 1] = diracGamma3 by simp [diracVectorLift],
        hDiff, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hJ
      have h00' := congrFun (congrFun hJ (0, 0)) (0, 0)
      simp [lorentzInner] at h00'
      exact sub_eq_zero_of_rev h00'
    ext μ
    fin_cases μ
    · exact sub_eq_zero.mp h0eq
    · exact sub_eq_zero.mp h1eq
    · exact sub_eq_zero.mp h2eq
    · exact sub_eq_zero.mp h3eq
  refine ⟨hInj, hJordan u v, ?_⟩
  have hSq : diracVectorLift v * diracVectorLift v =
      (-lorentzInner v v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    have h2 := hJordan v v
    have h2' : (2 : ℝ) • (diracVectorLift v * diracVectorLift v) =
        (2 : ℝ) • ((-lorentzInner v v) •
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) := by
      rw [two_smul, h2, smul_smul, scalar_two_mul_neg]
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) h2'
  rw [hSq]
  constructor
  · intro h0
    have h00' := congrFun (congrFun h0 (0, 0)) (0, 0)
    simp at h00'
    exact h00'
  · intro hl
    rw [hl, neg_zero, zero_smul]

/-- Every Lorentz-null 4-vector produces a square-zero Dirac operator with vanishing trace
pairing `Tr(ι(v)²) = 0`. -/
theorem diracVectorLift_null_trace_zero {v : Fin 4 → ℝ} (hNull : lorentzInner v v = 0) :
    diracVectorLift v * diracVectorLift v = 0 ∧
    Matrix.trace (diracVectorLift v * diracVectorLift v) = 0 := by
  have hSq : diracVectorLift v * diracVectorLift v = 0 :=
    (diracVectorLift_faithful_and_isotropic v v).2.2.mpr hNull
  exact ⟨hSq, by rw [hSq, Matrix.trace_zero]⟩

/-! ### Part 3: Spin Algebra Representation, Two Chiral Spin Algebras, & Casimirs -/

/-- Spin-`1/2` spatial rotation generators `J₁, J₂, J₃` in `Cl(3,1) ≅ M₄(ℝ)`. -/
def spinJ1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := -(1 / 2 : ℝ) • (diracGamma2 * diracGamma3)
def spinJ2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := -(1 / 2 : ℝ) • (diracGamma3 * diracGamma1)
def spinJ3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := -(1 / 2 : ℝ) • (diracGamma1 * diracGamma2)

/-- Lorentz boost generators `K₁, K₂, K₃` in `Cl(3,1) ≅ M₄(ℝ)`. -/
def boostK1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma1)
def boostK2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma2)
def boostK3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma3)

private lemma spinJ1_kron : spinJ1 = (1 / 2 : ℝ) • (eps2 ⊗ₖ xMir2) := by
  have hT := pauli2_mul_table
  unfold spinJ1 diracGamma2 diracGamma3
  rw [← Matrix.mul_kronecker_mul, hT.2.2.2.2.1, Matrix.mul_one, kron_neg_left, smul_neg]
  module

private lemma spinJ2_kron : spinJ2 = (-(1 / 2 : ℝ)) • (eps2 ⊗ₖ zCut2) := by
  have hT := pauli2_mul_table
  unfold spinJ2 diracGamma3 diracGamma1
  rw [← Matrix.mul_kronecker_mul, hT.2.2.2.1, Matrix.one_mul, neg_smul]

private lemma spinJ3_kron :
    spinJ3 = (-(1 / 2 : ℝ)) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
  have hT := pauli2_mul_table
  unfold spinJ3 diracGamma1 diracGamma2
  rw [← Matrix.mul_kronecker_mul, hT.2.1, hT.2.2.2.1, neg_smul]

private lemma boostK1_kron : boostK1 = (1 / 2 : ℝ) • (zCut2 ⊗ₖ zCut2) := by
  have hT := pauli2_mul_table
  unfold boostK1 diracGamma0 diracGamma1
  rw [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.1, Matrix.one_mul]

private lemma boostK2_kron : boostK2 = (1 / 2 : ℝ) • (zCut2 ⊗ₖ xMir2) := by
  have hT := pauli2_mul_table
  unfold boostK2 diracGamma0 diracGamma2
  rw [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.1, Matrix.one_mul]

private lemma boostK3_kron :
    boostK3 = (-(1 / 2 : ℝ)) • (xMir2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hT := pauli2_mul_table
  unfold boostK3 diracGamma0 diracGamma3
  rw [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.1, Matrix.one_mul, kron_neg_left, smul_neg,
    neg_smul]

private lemma diracOmega4_kron : diracOmega4 = -(xMir2 ⊗ₖ eps2) := by
  have hT := pauli2_mul_table
  unfold diracOmega4 diracGamma0 diracGamma1 diracGamma2 diracGamma3
  rw [mul_assoc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hT.2.2.2.2.2.2.2.2.1, Matrix.one_mul, hT.2.2.2.2.1, Matrix.mul_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_neg, hT.2.2.2.2.2.1, hT.2.2.2.1, kron_neg_left]

private lemma lorentz_spin_sq_rules :
    (spinJ1 * spinJ1 = (-(1 / 4 : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (spinJ2 * spinJ2 = (-(1 / 4 : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (spinJ3 * spinJ3 = (-(1 / 4 : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (boostK1 * boostK1 = (1 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (boostK2 * boostK2 = (1 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (boostK3 * boostK3 = (1 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) := by
  have hT := pauli2_mul_table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spinJ1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.2.1, hT.2.1, kron_neg_left, smul_neg, one_kron_one_real4]
    module
  · rw [spinJ2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.2.1, hT.1, kron_neg_left, smul_neg, one_kron_one_real4]
    module
  · rw [spinJ3_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hT.2.2.1, kron_neg_right, smul_neg, one_kron_one_real4]
    module
  · rw [boostK1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hT.1, one_kron_one_real4]
    module
  · rw [boostK2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hT.1, hT.2.1, one_kron_one_real4]
    module
  · rw [boostK3_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.1, Matrix.one_mul, one_kron_one_real4]
    module

private lemma lorentz_spin_full_brackets :
    (spinJ1 * spinJ2 - spinJ2 * spinJ1 = spinJ3) ∧
    (spinJ2 * spinJ3 - spinJ3 * spinJ2 = spinJ1) ∧
    (spinJ3 * spinJ1 - spinJ1 * spinJ3 = spinJ2) ∧
    (boostK1 * boostK2 - boostK2 * boostK1 = -spinJ3) ∧
    (spinJ1 * boostK2 - boostK2 * spinJ1 = boostK3) := by
  have hT := pauli2_mul_table
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h12 : spinJ1 * spinJ2 = (-(1 / 4 : ℝ)) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
      rw [spinJ1_kron, spinJ2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.2.2.1, hT.2.2.2.2.1, kron_neg_neg]
      module
    have h21 : spinJ2 * spinJ1 = (1 / 4 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
      rw [spinJ2_kron, spinJ1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.2.2.1, hT.2.2.2.1, kron_neg_left, smul_neg]
      module
    rw [h12, h21, spinJ3_kron]
    module
  · have h23 : spinJ2 * spinJ3 = (1 / 4 : ℝ) • (eps2 ⊗ₖ xMir2) := by
      rw [spinJ2_kron, spinJ3_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one, hT.2.2.2.2.2.1]
      module
    have h32 : spinJ3 * spinJ2 = (-(1 / 4 : ℝ)) • (eps2 ⊗ₖ xMir2) := by
      rw [spinJ3_kron, spinJ2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, hT.2.2.2.2.2.2.1, kron_neg_right, smul_neg]
      module
    rw [h23, h32, spinJ1_kron]
    module
  · have h31 : spinJ3 * spinJ1 = (-(1 / 4 : ℝ)) • (eps2 ⊗ₖ zCut2) := by
      rw [spinJ3_kron, spinJ1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, hT.2.2.2.2.2.2.2.2.1]
      module
    have h13 : spinJ1 * spinJ3 = (1 / 4 : ℝ) • (eps2 ⊗ₖ zCut2) := by
      rw [spinJ1_kron, spinJ3_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one, hT.2.2.2.2.2.2.2.1, kron_neg_right, smul_neg]
      module
    rw [h31, h13, spinJ2_kron]
    module
  · have h12 : boostK1 * boostK2 = (1 / 4 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
      rw [boostK1_kron, boostK2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.1, hT.2.2.2.1]
      module
    have h21 : boostK2 * boostK1 = (-(1 / 4 : ℝ)) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
      rw [boostK2_kron, boostK1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.1, hT.2.2.2.2.1, kron_neg_right, smul_neg]
      module
    rw [h12, h21, spinJ3_kron]
    module
  · have h12 : spinJ1 * boostK2 = (-(1 / 4 : ℝ)) • (xMir2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      rw [spinJ1_kron, boostK2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.1, hT.2.1, kron_neg_left, smul_neg]
      module
    have h21 : boostK2 * spinJ1 = (1 / 4 : ℝ) • (xMir2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      rw [boostK2_kron, spinJ1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.1, hT.2.1]
      module
    rw [h12, h21, boostK3_kron]
    module

/-- **Theorem 2A (Lorentz `so(3,1)` Spin Algebra & Two Casimirs on the 4D Majorana Carrier)**:
1. `[J₁, J₂] = J₃`, `[J₂, J₃] = J₁`, `[J₃, J₁] = J₂` (`su(2)` rotation subalgebra).
2. `[K₁, K₂] = -J₃` and `[J₁, K₂] = K₃` (Lorentz boost brackets).
3. `ω₄² = -I₄`, `C₁ = J² - K² = (-3/2) • I₄`, and `C₂ = J · K = (-3/4) • ω₄`. -/
theorem lorentz_spin_algebra_and_two_casimirs :
    (spinJ1 * spinJ2 - spinJ2 * spinJ1 = spinJ3) ∧
    (spinJ2 * spinJ3 - spinJ3 * spinJ2 = spinJ1) ∧
    (spinJ3 * spinJ1 - spinJ1 * spinJ3 = spinJ2) ∧
    (boostK1 * boostK2 - boostK2 * boostK1 = -spinJ3) ∧
    (spinJ1 * boostK2 - boostK2 * spinJ1 = boostK3) ∧
    (diracOmega4 * diracOmega4 = -1) ∧
    ((spinJ1 * spinJ1 + spinJ2 * spinJ2 + spinJ3 * spinJ3) -
      (boostK1 * boostK1 + boostK2 * boostK2 + boostK3 * boostK3) =
      (-3 / 2 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (spinJ1 * boostK1 + spinJ2 * boostK2 + spinJ3 * boostK3 = (-3 / 4 : ℝ) • diracOmega4) := by
  have hT := pauli2_mul_table
  have hB := lorentz_spin_full_brackets
  have hSq := lorentz_spin_sq_rules
  have hOmSq : diracOmega4 * diracOmega4 = -1 := by
    rw [diracOmega4_kron, neg_mul_neg, ← Matrix.mul_kronecker_mul, hT.2.1, hT.2.2.1,
      kron_neg_right, one_kron_one_real4]
  have hC1 : (spinJ1 * spinJ1 + spinJ2 * spinJ2 + spinJ3 * spinJ3) -
      (boostK1 * boostK1 + boostK2 * boostK2 + boostK3 * boostK3) =
      (-3 / 2 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    rw [hSq.1, hSq.2.1, hSq.2.2.1, hSq.2.2.2.1, hSq.2.2.2.2.1, hSq.2.2.2.2.2]
    module
  have hJK1 : spinJ1 * boostK1 = (1 / 4 : ℝ) • (xMir2 ⊗ₖ eps2) := by
    rw [spinJ1_kron, boostK1_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.1, hT.2.2.2.2.1, kron_neg_neg]
    module
  have hJK2 : spinJ2 * boostK2 = (1 / 4 : ℝ) • (xMir2 ⊗ₖ eps2) := by
    rw [spinJ2_kron, boostK2_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.1, hT.2.2.2.1, kron_neg_left, smul_neg]
    module
  have hJK3 : spinJ3 * boostK3 = (1 / 4 : ℝ) • (xMir2 ⊗ₖ eps2) := by
    rw [spinJ3_kron, boostK3_kron, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    module
  have hC2 : spinJ1 * boostK1 + spinJ2 * boostK2 + spinJ3 * boostK3 = (-3 / 4 : ℝ) • diracOmega4 := by
    rw [hJK1, hJK2, hJK3, diracOmega4_kron]
    module
  exact ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2, hOmSq, hC1, hC2⟩

/-- Doubled 8D real chiral bispinor carrier `M₈(ℝ) ≅ M₂(M₄(ℝ))` (`N₊ ⊕ N₋`). -/
def bispinorCut : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := zCut2 ⊗ₖ 1
def bispinorMir : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := xMir2 ⊗ₖ 1
def bispinorIcplx : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := 1 ⊗ₖ diracOmega4

def bispinorJ (J : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := 1 ⊗ₖ J
def bispinorK (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := zCut2 ⊗ₖ K

def chiralSpinA (J K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ :=
  (1 / 2 : ℝ) • (bispinorJ J + bispinorIcplx * bispinorK K)

def chiralSpinB (J K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ :=
  (1 / 2 : ℝ) • (bispinorJ J - bispinorIcplx * bispinorK K)

/-- Non-commutativity witness on the 8D real chiral bispinor carrier `Fin 2 × (Fin 2 × Fin 2)`. -/
theorem exists_noncomm_mat8_bispinor :
    ∃ A B : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ, A * B ≠ B * A := by
  refine ⟨bispinorCut, bispinorMir, fun h => ?_⟩
  dsimp [bispinorCut, bispinorMir] at h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul] at h
  have h01 := congrArg (fun M : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ =>
    M (0, (0, 0)) (1, (0, 0))) h
  simp [Matrix.kroneckerMap_apply, zCut2, xMir2] at h01
  norm_num at h01

private lemma diracOmega4_mul_boosts :
    diracOmega4 * boostK1 = -spinJ1 ∧
    diracOmega4 * boostK2 = -spinJ2 ∧
    diracOmega4 * boostK3 = -spinJ3 := by
  have hT := pauli2_mul_table
  refine ⟨?_, ?_, ?_⟩
  · rw [diracOmega4_kron, boostK1_kron, neg_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.2.2.2.1, hT.2.2.2.2.2.2.1, kron_neg_neg, spinJ1_kron]
  · rw [diracOmega4_kron, boostK2_kron, neg_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.1, kron_neg_left, smul_neg, neg_neg, spinJ2_kron]
    module
  · rw [diracOmega4_kron, boostK3_kron, neg_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
      hT.2.1, Matrix.mul_one, spinJ3_kron]

private lemma chiral_split_kron (J K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (hOK : diracOmega4 * K = -J) :
    chiralSpinA J K = pMinus2 ⊗ₖ J ∧ chiralSpinB J K = pPlus2 ⊗ₖ J := by
  have hP := chiral_proj_zCut2
  have hProd : bispinorIcplx * bispinorK K = -(zCut2 ⊗ₖ J) := by
    unfold bispinorIcplx bispinorK
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hOK, kron_neg_right]
  constructor
  · unfold chiralSpinA bispinorJ
    rw [hProd, ← sub_eq_add_neg, ← kron_sub_left, ← kron_smul_left, hP.1]
  · unfold chiralSpinB bispinorJ
    rw [hProd, sub_neg_eq_add, ← kron_add_left, ← kron_smul_left, hP.2]

/-- **Theorem 2B (Two Commuting Chiral Spin Algebras, Mirror Swap, & Independent Chiral Casimirs)**:
On the doubled 8D real carrier `N₊ ⊕ N₋`:
1. `A_i = P₋ ⊗ J_i` and `B_i = P₊ ⊗ J_i` form **two mutually commuting `su(2)` spin algebras**.
2. The Mirror involution `J_mir` exchanges `A_i` and `B_i`.
3. Their independent Casimirs `C_A = (-3/4) • (P₋ ⊗ I₄)` and `C_B = (-3/4) • (P₊ ⊗ I₄)`
   reconstruct `C₁ = 2(C_A + C_B) = (-3/2) • I₈` and `J_tot · K_tot = (-3/4) • (Γ I_cplx)`. -/
theorem two_chiral_spin_algebras_and_casimirs :
    let A1 := chiralSpinA spinJ1 boostK1
    let A2 := chiralSpinA spinJ2 boostK2
    let A3 := chiralSpinA spinJ3 boostK3
    let B1 := chiralSpinB spinJ1 boostK1
    let B2 := chiralSpinB spinJ2 boostK2
    let B3 := chiralSpinB spinJ3 boostK3
    (A1 = pMinus2 ⊗ₖ spinJ1) ∧
    (B1 = pPlus2 ⊗ₖ spinJ1) ∧
    (A1 * A2 - A2 * A1 = A3) ∧
    (B1 * B2 - B2 * B1 = B3) ∧
    (A1 * B2 - B2 * A1 = 0) ∧
    (bispinorMir * A1 * bispinorMir = B1) ∧
    (A1 * A1 + A2 * A2 + A3 * A3 = (-3 / 4 : ℝ) • (pMinus2 ⊗ₖ 1)) ∧
    (B1 * B1 + B2 * B2 + B3 * B3 = (-3 / 4 : ℝ) • (pPlus2 ⊗ₖ 1)) ∧
    ((2 : ℝ) • ((A1 * A1 + A2 * A2 + A3 * A3) + (B1 * B1 + B2 * B2 + B3 * B3)) =
      (-3 / 2 : ℝ) • (1 : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ)) ∧
    (bispinorJ spinJ1 * bispinorK boostK1 + bispinorJ spinJ2 * bispinorK boostK2 +
      bispinorJ spinJ3 * bispinorK boostK3 = (-3 / 4 : ℝ) • (bispinorCut * bispinorIcplx)) := by
  have hOK := diracOmega4_mul_boosts
  have hS1 := chiral_split_kron spinJ1 boostK1 hOK.1
  have hS2 := chiral_split_kron spinJ2 boostK2 hOK.2.1
  have hS3 := chiral_split_kron spinJ3 boostK3 hOK.2.2
  have hT := pauli2_mul_table
  have hAlg := lorentz_spin_algebra_and_two_casimirs
  have hSq := lorentz_spin_sq_rules
  have hCasJ : spinJ1 * spinJ1 + spinJ2 * spinJ2 + spinJ3 * spinJ3 =
      (-3 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    rw [hSq.1, hSq.2.1, hSq.2.2.1]
    module
  have hPadd : pMinus2 + pPlus2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pMinus2, pPlus2]
  dsimp
  rw [hS1.1, hS1.2, hS2.1, hS2.2, hS3.1, hS3.2]
  have hCA : (pMinus2 ⊗ₖ spinJ1) * (pMinus2 ⊗ₖ spinJ1) +
      (pMinus2 ⊗ₖ spinJ2) * (pMinus2 ⊗ₖ spinJ2) +
      (pMinus2 ⊗ₖ spinJ3) * (pMinus2 ⊗ₖ spinJ3) = (-3 / 4 : ℝ) • (pMinus2 ⊗ₖ 1) := by
    simp only [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.2.2.1, ← kron_add_right, hCasJ,
      kron_smul_right]
  have hCB : (pPlus2 ⊗ₖ spinJ1) * (pPlus2 ⊗ₖ spinJ1) +
      (pPlus2 ⊗ₖ spinJ2) * (pPlus2 ⊗ₖ spinJ2) +
      (pPlus2 ⊗ₖ spinJ3) * (pPlus2 ⊗ₖ spinJ3) = (-3 / 4 : ℝ) • (pPlus2 ⊗ₖ 1) := by
    simp only [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.2.1, ← kron_add_right, hCasJ,
      kron_smul_right]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hCA, hCB, ?_, ?_⟩
  · simp only [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.2.2.1, ← kron_sub_right, hAlg.1]
  · simp only [← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.2.1, ← kron_sub_right, hAlg.1]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hT.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.1, Matrix.zero_kronecker, Matrix.zero_kronecker, sub_zero]
  · dsimp [bispinorMir]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2]
  · rw [hCA, hCB, ← smul_add, ← kron_add_left, hPadd, one_kron_one_real8]
    module
  · unfold bispinorJ bispinorK bispinorCut bispinorIcplx
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, ← kron_add_right,
      hAlg.2.2.2.2.2.2.2, kron_smul_right]

/-! ### Part 4: Noncommutative Nambu 3-Brackets, Multiplication Modules, & Isotropic Collapse -/

/-- Alternating Nambu 3-bracket `[A, B, C]_Nambu = [A, B] C + [B, C] A + [C, A] B` in any
associative ring `B`. -/
def nambuBracket3 {B : Type*} [Ring B] (A B₁ C : B) : B :=
  (A * B₁ - B₁ * A) * C + (B₁ * C - C * B₁) * A + (C * A - A * C) * B₁

/-- Exact equivalence with `PeirceSpine.alternatingProduct3` from `AssociativeNambuOperators`. -/
theorem nambuBracket3_eq_alternatingProduct3 {B : Type*} [Ring B] (A B₁ C : B) :
    nambuBracket3 A B₁ C = alternatingProduct3 A B₁ C := by
  unfold nambuBracket3 alternatingProduct3
  noncomm_ring

/-- **Theorem 3A (Nambu 3-Bracket Equals Total Alternating `S₃` Product & Generates Spin Casimir)**:
1. `[A, B, C]_Nambu = (A B C + B C A + C A B) - (B A C + C B A + A C B)`.
2. Total skew-symmetry in the first two and last two slots.
3. **Spin-Nambu-Casimir Law**: Under `su(2)` cyclic commutator relations,
   `[A, B, C]_Nambu = A² + B² + C²`, instantiated directly on `spinJ1, spinJ2, spinJ3` (`= (-3/4) • I₄`). -/
theorem nambuBracket3_alt_skew_and_spin_casimir {B : Type*} [Ring B] (A B₁ C : B) :
    (nambuBracket3 A B₁ C =
      (A * B₁ * C + B₁ * C * A + C * A * B₁) -
      (B₁ * A * C + C * B₁ * A + A * C * B₁)) ∧
    (nambuBracket3 B₁ A C = -nambuBracket3 A B₁ C) ∧
    (nambuBracket3 A C B₁ = -nambuBracket3 A B₁ C) ∧
    (A * B₁ - B₁ * A = C → B₁ * C - C * B₁ = A → C * A - A * C = B₁ →
      nambuBracket3 A B₁ C = A * A + B₁ * B₁ + C * C) := by
  refine ⟨?_, ?_, ?_, fun h12 h23 h31 => ?_⟩
  · unfold nambuBracket3; noncomm_ring
  · unfold nambuBracket3; noncomm_ring
  · unfold nambuBracket3; noncomm_ring
  · rw [nambuBracket3_eq_alternatingProduct3]
    exact alternatingProduct3_eq_casimir A B₁ C h12 h23 h31

/-- Concrete Spin-Nambu-Casimir law on the real Majorana `su(2)` spin generators. -/
theorem spinJ_nambuBracket3_eq_casimir :
    nambuBracket3 spinJ1 spinJ2 spinJ3 =
      (-3 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  have hB := lorentz_spin_algebra_and_two_casimirs
  have hSq := lorentz_spin_sq_rules
  rw [(nambuBracket3_alt_skew_and_spin_casimir spinJ1 spinJ2 spinJ3).2.2.2 hB.1 hB.2.1 hB.2.2.1,
    hSq.1, hSq.2.1, hSq.2.2.1]
  module

/-- Left-multiplication Nambu operator `L_{A,B}(m) = [A, B] * m` on any associative ring `B`. -/
def nambuLeftMul {B : Type*} [Ring B] (A B₁ m : B) : B := (A * B₁ - B₁ * A) * m

/-- Inner-derivation Nambu operator `D_{A,B}(m) = [[A, B], m]` on any associative ring `B`. -/
def nambuDeriv {B : Type*} [Ring B] (A B₁ m : B) : B :=
  (A * B₁ - B₁ * A) * m - m * (A * B₁ - B₁ * A)

/-- **Theorem 3B (Noncommutative Nambu Multiplication Modules & Isotropic Collapse)**:
1. `nambuLeftMul A B₁` is a right-`B`-module endomorphism (`L(X * Y) = L(X) * Y`).
2. `nambuDeriv A B₁` satisfies the Leibniz law (`D(X * Y) = D(X) * Y + X * D(Y)`) and bridges to
   `AssociativeNambuOperators.ad_comm_mem_derivations`.
3. On any isotropic Peirce corner `P B (1 - P)`, pairwise products and Nambu 3-brackets vanish.
4. On any null-vector Dirac sandwich range `ι(v) M ι(v)` (`lorentzInner v v = 0`), pairwise
   products and `nambuBracket3` vanish identically. -/
theorem noncommutative_nambu_module_and_isotropic_collapse
    {B : Type*} [Ring B] (A B₁ C X Y : B) :
    (nambuLeftMul A B₁ (X * Y) = nambuLeftMul A B₁ X * Y) ∧
    (nambuDeriv A B₁ (X * Y) = nambuDeriv A B₁ X * Y + X * nambuDeriv A B₁ Y) ∧
    (∀ P : B, P * P = P →
      let I := fun Z => P * Z * (1 - P)
      I A * I B₁ = 0 ∧ nambuBracket3 (I A) (I B₁) (I C) = 0 ∧
        nambuLeftMul (I A) (I B₁) (I C) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold nambuLeftMul; noncomm_ring
  · unfold nambuDeriv; noncomm_ring
  · intro P hP
    dsimp
    have h1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    have hNull : ∀ U V : B, (P * U * (1 - P)) * (P * V * (1 - P)) = 0 := by
      intro U V
      calc (P * U * (1 - P)) * (P * V * (1 - P))
          = P * U * ((1 - P) * P) * V * (1 - P) := by noncomm_ring
        _ = 0 := by rw [h1P]; noncomm_ring
    refine ⟨hNull A B₁, ?_, ?_⟩
    · unfold nambuBracket3
      rw [hNull A B₁, hNull B₁ A, hNull B₁ C, hNull C B₁, hNull C A, hNull A C]
      noncomm_ring
    · unfold nambuLeftMul
      rw [hNull A B₁, hNull B₁ A]
      noncomm_ring

section LieDeriv

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Inner-derivation Nambu operator belongs to `NonAssocDerivation.derivations ℝ B`. -/
theorem nambuDeriv_mem_derivations {B : Type*} [Ring B] [Algebra ℝ B] (A B₁ : B) :
    ((fun m => nambuDeriv A B₁ m) = (fun m => LieAlgebra.ad ℝ B (PeirceSpine.comm A B₁) m)) ∧
    LieAlgebra.ad ℝ B (PeirceSpine.comm A B₁) ∈
      InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ B := by
  refine ⟨funext fun m => ?_, ad_comm_mem_derivations A B₁⟩
  unfold nambuDeriv PeirceSpine.comm
  simp [LieAlgebra.ad_apply, Ring.lie_def]
  noncomm_ring

end LieDeriv

/-- Null-vector Dirac sandwich isotropic collapse: if `lorentzInner v v = 0`, any operators in
`LinearMap.range (LinearMap.mulLeftRight ℝ (diracVectorLift v, diracVectorLift v))` have zero
product and zero `nambuBracket3`. -/
theorem diracNullVector_sandwich_isotropic_collapse {v : Fin 4 → ℝ}
    (hNull : lorentzInner v v = 0)
    {A B₁ C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ}
    (hA : A ∈ LinearMap.range (LinearMap.mulLeftRight ℝ (diracVectorLift v, diracVectorLift v)))
    (hB : B₁ ∈ LinearMap.range (LinearMap.mulLeftRight ℝ (diracVectorLift v, diracVectorLift v)))
    (hC : C ∈ LinearMap.range (LinearMap.mulLeftRight ℝ (diracVectorLift v, diracVectorLift v))) :
    A * B₁ = 0 ∧ nambuBracket3 A B₁ C = 0 := by
  have hN2 : diracVectorLift v * diracVectorLift v = 0 :=
    (diracVectorLift_null_trace_zero hNull).1
  refine ⟨mul_eq_zero_of_mem_sandwich_range (diracVectorLift v) hN2 hA hB, ?_⟩
  rw [nambuBracket3_eq_alternatingProduct3]
  exact alternatingProduct3_sandwich_range (diracVectorLift v) hN2 hA hB hC

end InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge