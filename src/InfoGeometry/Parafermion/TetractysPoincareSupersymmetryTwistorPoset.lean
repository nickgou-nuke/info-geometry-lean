/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.Canonical.TetractysCliffordLorentzAction

/-!
# The Real DeWitt Tetractys, 10D Poincaré Algebra $\mathfrak{iso}(3, 1)$, Peirce-Corner Lorentz Action, 4D Translation Module, and Majorana-Twistor Supersymmetry Poset ($\mathfrak{SP}_1 \prec \dots \prec \mathfrak{SP}_7$)

This module constructs the 4D $(-,+,+,+)$ Minkowski Clifford algebra, the 6 Lorentz generators,
the Peirce-corner Lorentz action, the 4-dimensional abelian translation module, the endogenous
Minkowski quadratic norm / correlator propagator pairing, and the real Majorana-twistor
supersymmetry / mass-shell identities **endogenously from the DeWitt Split Tetractys**
(`InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys`) without external coordinate Dirac matrices
or scalar complexification $i \in \mathbb{C}$.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- Purely algebraic ring identities (`6 + 4 = 10`, null light-cone polynomial identity, and
  2-twistor Lagrange-Sylvester Casimir identity over `ℤ` and `ℝ`).

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `tetractys_peirce_split_relations`: proves from `P * P = P` and `genPhi P W W * genPhi P W W = 1`
  that `S = invS P` and `Φ = genPhi P W W` satisfy `S² = 1`, `Φ² = 1`, and `Φ S = -(S Φ)`.
- `dewitt_tetractys_generates_4d_minkowski_clifford_algebra`: proves in any associative ring
  `[Ring B]` that two commuting DeWitt Tetractys splits `(S₁, Φ₁)` and `(S₂, Φ₂)` generate four
  Dirac operators `γ₀ = S₁ Φ₁, γ₁ = S₁, γ₂ = Φ₁ S₂, γ₃ = Φ₁ Φ₂` with Minkowski signature
  `(-, +, +, +)` and pairwise anticommutation `{γ_μ, γ_ν} = 0` (`μ ≠ ν`).
- `tetractys_lorentz_bivectors_and_4d_translation_module`: proves purely from the DeWitt Tetractys
  that:
  1. The 3 spatial rotation bivectors `L₁₂ = γ₁ γ₂`, `L₁₃ = γ₁ γ₃`, `L₂₃ = γ₂ γ₃` square to `-1`
     and the 3 Lorentz boost bivectors `K₀₁ = γ₀ γ₁`, `K₀₂ = γ₀ γ₂`, `K₀₃ = γ₀ γ₃` square to `+1`,
  2. The 4-dimensional Tetractys Dirac module element
     `tetractysSlash S₁ Φ₁ S₂ Φ₂ p₀ p₁ p₂ p₃ = p₀ • γ₀ + p₁ • γ₁ + p₂ • γ₂ + p₃ • γ₃`
     satisfies the endogenous Minkowski quadratic norm law
     `slash * slash = (-p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) • 1`
     and recovers all four coordinates via endogenous Tetractys anticommutators
     (`-anticomm γ₀ X = (2 * p₀) • 1`, `anticomm γᵢ X = (2 * pᵢ) • 1`),
  3. All 6 Tetractys Lorentz generators preserve `tetractysSlash` and act by the exact 4D Lorentz
     vector representation.
- `poincare_translations_commute_and_lorentz_covariance` &
  `peirce_corner_4d_translation_module_and_lorentz_action`: proves in any `[Ring B]` with Peirce
  idempotent `P * P = P` that the diagonal Lorentz stabilizer `LorentzL P M` preserves the upper
  Peirce corner `TransN P x = P x (1 - P)`, acts equivariantly when `P * M = M * P`, and that the
  4-dimensional translation module `tetractysPoincareTrans P W S₁ Φ₁ S₂ Φ₂ p₀ p₁ p₂ p₃` inside
  that corner is abelian, nilpotent, unipotent-group-forming, invariant under all 6 Tetractys
  Lorentz generators, and pairs with the lower Peirce corner to yield the Minkowski propagator norm.
- `super_peirce_odd_supercharge_anticommutator` &
  `real_twistor_susy_null_and_massive_momentum_factorization`: proves the odd Super-Peirce
  supercharge anticommutator closure into the even bosonic sector, the endogenous Tetractys
  decomposition of the rank-one twistor momentum operator
  `2 P_twistor(P, W; λ₁, λ₂) = (λ₁² + λ₂²) • 1 + (λ₁² - λ₂²) • invS P + (2 λ₁ λ₂) • genPhi P W W`,
  the 1-twistor null light-cone identity, the 2-twistor massive Casimir square
  `(λ₁² + μ₁²)(λ₂² + μ₂²) - (λ₁ λ₂ + μ₁ μ₂)² = (λ₁ μ₂ - λ₂ μ₁)²`, and Witten positive energy
  over `ℝ`.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 structure wrappers`).
-/

namespace InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine

universe u

/-!
## §1. Nodes $\mathfrak{SP}_1 \prec \mathfrak{SP}_2$: Endogenous 4D $(-,+,+,+)$ Minkowski Clifford Algebra & 6 Lorentz Generators from the Two-Bit Real DeWitt Tetractys
-/

section RealMinkowskiFromTetractys

variable {B : Type u} [Ring B]

/-- From any Peirce idempotent `P * P = P` and normalized bridge `genPhi P W W * genPhi P W W = 1`,
the Tetractys grading `invS P` and bridge `genPhi P W W` satisfy `(invS P)² = 1`,
`(genPhi P W W)² = 1`, and `genPhi P W W * invS P = -(invS P * genPhi P W W)`. -/
theorem tetractys_peirce_split_relations
    (P W : B) (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) :
    invS P * invS P = 1 ∧
    genPhi P W W * genPhi P W W = 1 ∧
    genPhi P W W * invS P = -(invS P * genPhi P W W) := by
  have hS_sq : invS P * invS P = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP P P).1
  have h_SJ : invS P * genPhi P W W = genJ P W W := by
    dsimp [invS, genPhi, genJ]
    simp only [sub_mul, mul_add, one_mul, P_mul_conePlus hP, P_mul_coneMinus hP]
    abel
  have h_JS : genPhi P W W * invS P = -genJ P W W := by
    dsimp [invS, genPhi, genJ]
    simp only [add_mul, mul_sub, mul_one, conePlus_mul_P hP, coneMinus_mul_P hP]
    abel
  refine ⟨hS_sq, hPhi, ?_⟩
  rw [h_JS, h_SJ]

/-- Anticommutator `{x, y} = x * y + y * x` in any ring `B`. -/
def anticomm (x y : B) : B := x * y + y * x

/-- Ring commutator `[x, y] = x * y - y * x` in any ring `B`. -/
def comm (x y : B) : B := x * y - y * x

/-- Endogenous timelike Tetractys Dirac operator $\gamma_0(S_1, \Phi_1) = S_1 \Phi_1 = J_1$. -/
def tetractysGamma0 (S1 Phi1 : B) : B := S1 * Phi1

/-- Endogenous first spacelike Tetractys Dirac operator $\gamma_1(S_1) = S_1$. -/
def tetractysGamma1 (S1 : B) : B := S1

/-- Endogenous second spacelike Tetractys Dirac operator $\gamma_2(\Phi_1, S_2) = \Phi_1 S_2$. -/
def tetractysGamma2 (Phi1 S2 : B) : B := Phi1 * S2

/-- Endogenous third spacelike Tetractys Dirac operator $\gamma_3(\Phi_1, \Phi_2) = \Phi_1 \Phi_2$. -/
def tetractysGamma3 (Phi1 Phi2 : B) : B := Phi1 * Phi2

/-- Endogenous Lorentz boost bivector $K_{01} = \gamma_0 \gamma_1$. -/
def tetractysK01 (S1 Phi1 : B) : B := tetractysGamma0 S1 Phi1 * tetractysGamma1 S1

/-- Endogenous Lorentz boost bivector $K_{02} = \gamma_0 \gamma_2$. -/
def tetractysK02 (S1 Phi1 S2 : B) : B := tetractysGamma0 S1 Phi1 * tetractysGamma2 Phi1 S2

/-- Endogenous Lorentz boost bivector $K_{03} = \gamma_0 \gamma_3$. -/
def tetractysK03 (S1 Phi1 Phi2 : B) : B := tetractysGamma0 S1 Phi1 * tetractysGamma3 Phi1 Phi2

/-- Endogenous spatial rotation bivector $L_{12} = \gamma_1 \gamma_2$. -/
def tetractysL12 (S1 Phi1 S2 : B) : B := tetractysGamma1 S1 * tetractysGamma2 Phi1 S2

/-- Endogenous spatial rotation bivector $L_{13} = \gamma_1 \gamma_3$. -/
def tetractysL13 (S1 Phi1 Phi2 : B) : B := tetractysGamma1 S1 * tetractysGamma3 Phi1 Phi2

/-- Endogenous spatial rotation bivector $L_{23} = \gamma_2 \gamma_3$. -/
def tetractysL23 (Phi1 S2 Phi2 : B) : B := tetractysGamma2 Phi1 S2 * tetractysGamma3 Phi1 Phi2

/-- The 4-dimensional Tetractys Dirac vector module element
$\not{p} = p_0 \gamma_0 + p_1 \gamma_1 + p_2 \gamma_2 + p_3 \gamma_3$ in `[Ring B]`. -/
def tetractysSlash (S1 Phi1 S2 Phi2 : B) (p0 p1 p2 p3 : ℤ) : B :=
  p0 • tetractysGamma0 S1 Phi1 +
  p1 • tetractysGamma1 S1 +
  p2 • tetractysGamma2 Phi1 S2 +
  p3 • tetractysGamma3 Phi1 Phi2

/--
**Theorem 1 ($\mathfrak{SP}_1 \prec \mathfrak{SP}_2$ — `dewitt_tetractys_generates_4d_minkowski_clifford_algebra`):**
Let `(S₁, Φ₁)` and `(S₂, Φ₂)` be two commuting DeWitt Tetractys splits in `[Ring B]`
(`S₁² = 1, Φ₁² = 1, Φ₁ S₁ = -(S₁ Φ₁)` and `S₂² = 1, Φ₂² = 1, Φ₂ S₂ = -(S₂ Φ₂)`).
Then the four endogenous Tetractys operators
`γ₀ = tetractysGamma0 S₁ Φ₁`, `γ₁ = tetractysGamma1 S₁`,
`γ₂ = tetractysGamma2 Φ₁ S₂`, `γ₃ = tetractysGamma3 Φ₁ Φ₂`
satisfy the 4D $(-,+,+,+)$ Minkowski Clifford algebra relations:
1. `γ₀ * γ₀ = -1` (timelike negative square from the endogenous bivector $J_1 = S_1 \Phi_1$),
2. `γ₁ * γ₁ = 1`, `γ₂ * γ₂ = 1`, `γ₃ * γ₃ = 1` (spacelike positive squares),
3. Pairwise Clifford anticommutation `anticomm γ_μ γ_ν = 0` for all `0 ≤ μ < ν ≤ 3`.
-/
theorem dewitt_tetractys_generates_4d_minkowski_clifford_algebra
    (S1 Phi1 S2 Phi2 : B)
    (hS1 : S1 * S1 = 1) (hPhi1 : Phi1 * Phi1 = 1) (hAnti1 : Phi1 * S1 = -(S1 * Phi1))
    (hS2 : S2 * S2 = 1) (hPhi2 : Phi2 * Phi2 = 1) (hAnti2 : Phi2 * S2 = -(S2 * Phi2))
    (hS1S2 : S1 * S2 = S2 * S1) (hS1Phi2 : S1 * Phi2 = Phi2 * S1)
    (hPhi1S2 : Phi1 * S2 = S2 * Phi1) (hPhi1Phi2 : Phi1 * Phi2 = Phi2 * Phi1) :
    let γ0 := tetractysGamma0 S1 Phi1
    let γ1 := tetractysGamma1 S1
    let γ2 := tetractysGamma2 Phi1 S2
    let γ3 := tetractysGamma3 Phi1 Phi2
    γ0 * γ0 = -1 ∧
    γ1 * γ1 = 1 ∧
    γ2 * γ2 = 1 ∧
    γ3 * γ3 = 1 ∧
    anticomm γ0 γ1 = 0 ∧
    anticomm γ0 γ2 = 0 ∧
    anticomm γ0 γ3 = 0 ∧
    anticomm γ1 γ2 = 0 ∧
    anticomm γ1 γ3 = 0 ∧
    anticomm γ2 γ3 = 0 := by
  dsimp only [tetractysGamma0, tetractysGamma1, tetractysGamma2, tetractysGamma3]
  have hJ1S1 : (S1 * Phi1) * S1 = -Phi1 := by
    calc
      (S1 * Phi1) * S1 = S1 * (Phi1 * S1) := by rw [mul_assoc]
      _ = S1 * (-(S1 * Phi1)) := by rw [hAnti1]
      _ = -((S1 * S1) * Phi1) := by rw [mul_neg, ← mul_assoc]
      _ = -Phi1 := by rw [hS1, one_mul]
  have hS1J1 : S1 * (S1 * Phi1) = Phi1 := by
    rw [← mul_assoc, hS1, one_mul]
  have hJ1Phi1 : (S1 * Phi1) * Phi1 = S1 := by
    rw [mul_assoc, hPhi1, mul_one]
  have hPhi1J1 : Phi1 * (S1 * Phi1) = -S1 := by
    calc
      Phi1 * (S1 * Phi1) = (Phi1 * S1) * Phi1 := by rw [← mul_assoc]
      _ = (-(S1 * Phi1)) * Phi1 := by rw [hAnti1]
      _ = -((S1 * Phi1) * Phi1) := by rw [neg_mul]
      _ = -S1 := by rw [hJ1Phi1]
  refine ⟨?_, hS1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (S1 * Phi1) * (S1 * Phi1) = ((S1 * Phi1) * S1) * Phi1 := by rw [← mul_assoc]
      _ = (-Phi1) * Phi1 := by rw [hJ1S1]
      _ = -(Phi1 * Phi1) := by rw [neg_mul]
      _ = -1 := by rw [hPhi1]
  · calc
      (Phi1 * S2) * (Phi1 * S2) = Phi1 * (S2 * Phi1) * S2 := by simp only [mul_assoc]
      _ = Phi1 * (Phi1 * S2) * S2 := by rw [← hPhi1S2]
      _ = (Phi1 * Phi1) * (S2 * S2) := by simp only [mul_assoc]
      _ = 1 := by rw [hPhi1, hS2, mul_one]
  · calc
      (Phi1 * Phi2) * (Phi1 * Phi2) = Phi1 * (Phi2 * Phi1) * Phi2 := by simp only [mul_assoc]
      _ = Phi1 * (Phi1 * Phi2) * Phi2 := by rw [← hPhi1Phi2]
      _ = (Phi1 * Phi1) * (Phi2 * Phi2) := by simp only [mul_assoc]
      _ = 1 := by rw [hPhi1, hPhi2, mul_one]
  · dsimp [anticomm]
    rw [hJ1S1, hS1J1, neg_add_cancel]
  · dsimp [anticomm]
    have h1 : (S1 * Phi1) * (Phi1 * S2) = S1 * S2 := by
      calc
        (S1 * Phi1) * (Phi1 * S2) = ((S1 * Phi1) * Phi1) * S2 := by simp only [mul_assoc]
        _ = S1 * S2 := by rw [hJ1Phi1]
    have h2 : (Phi1 * S2) * (S1 * Phi1) = -(S1 * S2) := by
      calc
        (Phi1 * S2) * (S1 * Phi1) = Phi1 * (S2 * S1) * Phi1 := by simp only [mul_assoc]
        _ = Phi1 * (S1 * S2) * Phi1 := by rw [← hS1S2]
        _ = (Phi1 * S1) * (S2 * Phi1) := by simp only [mul_assoc]
        _ = (Phi1 * S1) * (Phi1 * S2) := by rw [← hPhi1S2]
        _ = (Phi1 * (S1 * Phi1)) * S2 := by simp only [mul_assoc]
        _ = (-S1) * S2 := by rw [hPhi1J1]
        _ = -(S1 * S2) := by rw [neg_mul]
    rw [h1, h2, add_neg_cancel]
  · dsimp [anticomm]
    have h1 : (S1 * Phi1) * (Phi1 * Phi2) = S1 * Phi2 := by
      calc
        (S1 * Phi1) * (Phi1 * Phi2) = ((S1 * Phi1) * Phi1) * Phi2 := by simp only [mul_assoc]
        _ = S1 * Phi2 := by rw [hJ1Phi1]
    have h2 : (Phi1 * Phi2) * (S1 * Phi1) = -(S1 * Phi2) := by
      calc
        (Phi1 * Phi2) * (S1 * Phi1) = Phi1 * (Phi2 * S1) * Phi1 := by simp only [mul_assoc]
        _ = Phi1 * (S1 * Phi2) * Phi1 := by rw [← hS1Phi2]
        _ = (Phi1 * S1) * (Phi2 * Phi1) := by simp only [mul_assoc]
        _ = (Phi1 * S1) * (Phi1 * Phi2) := by rw [← hPhi1Phi2]
        _ = (Phi1 * (S1 * Phi1)) * Phi2 := by simp only [mul_assoc]
        _ = (-S1) * Phi2 := by rw [hPhi1J1]
        _ = -(S1 * Phi2) := by rw [neg_mul]
    rw [h1, h2, add_neg_cancel]
  · dsimp [anticomm]
    have h2 : (Phi1 * S2) * S1 = -(S1 * (Phi1 * S2)) := by
      calc
        (Phi1 * S2) * S1 = Phi1 * (S2 * S1) := by rw [mul_assoc]
        _ = Phi1 * (S1 * S2) := by rw [← hS1S2]
        _ = (Phi1 * S1) * S2 := by rw [← mul_assoc]
        _ = (-(S1 * Phi1)) * S2 := by rw [hAnti1]
        _ = -(S1 * (Phi1 * S2)) := by simp only [neg_mul, mul_assoc]
    rw [h2, add_neg_cancel]
  · dsimp [anticomm]
    have h2 : (Phi1 * Phi2) * S1 = -(S1 * (Phi1 * Phi2)) := by
      calc
        (Phi1 * Phi2) * S1 = Phi1 * (Phi2 * S1) := by rw [mul_assoc]
        _ = Phi1 * (S1 * Phi2) := by rw [← hS1Phi2]
        _ = (Phi1 * S1) * Phi2 := by rw [← mul_assoc]
        _ = (-(S1 * Phi1)) * Phi2 := by rw [hAnti1]
        _ = -(S1 * (Phi1 * Phi2)) := by simp only [neg_mul, mul_assoc]
    rw [h2, add_neg_cancel]
  · dsimp [anticomm]
    have h1 : (Phi1 * S2) * (Phi1 * Phi2) = S2 * Phi2 := by
      calc
        (Phi1 * S2) * (Phi1 * Phi2) = Phi1 * (S2 * Phi1) * Phi2 := by simp only [mul_assoc]
        _ = Phi1 * (Phi1 * S2) * Phi2 := by rw [← hPhi1S2]
        _ = (Phi1 * Phi1) * (S2 * Phi2) := by simp only [mul_assoc]
        _ = S2 * Phi2 := by rw [hPhi1, one_mul]
    have h2 : (Phi1 * Phi2) * (Phi1 * S2) = -(S2 * Phi2) := by
      calc
        (Phi1 * Phi2) * (Phi1 * S2) = Phi1 * (Phi2 * Phi1) * S2 := by simp only [mul_assoc]
        _ = Phi1 * (Phi1 * Phi2) * S2 := by rw [← hPhi1Phi2]
        _ = (Phi1 * Phi1) * (Phi2 * S2) := by simp only [mul_assoc]
        _ = Phi2 * S2 := by rw [hPhi1, one_mul]
        _ = -(S2 * Phi2) := hAnti2
    rw [h1, h2, add_neg_cancel]

/-- For any anticommuting elements `u * v + v * u = 0`, `(u * v) * (u * v) = -(u * u * (v * v))`. -/
lemma bivector_sq_of_anticomm {u v : B} (huv : anticomm u v = 0) :
    (u * v) * (u * v) = -(u * u * (v * v)) := by
  have h_vu : v * u = -(u * v) :=
    eq_neg_of_add_eq_zero_left (by dsimp [anticomm] at huv; rw [add_comm] at huv; exact huv)
  calc
    (u * v) * (u * v) = u * ((v * u) * v) := by simp only [mul_assoc]
    _ = u * ((-(u * v)) * v) := by rw [h_vu]
    _ = -(u * u * (v * v)) := by simp only [neg_mul, mul_neg, mul_assoc]

/-- For anticommuting `u, v`, `[u * v, u] = -((2 : ℤ) • (u * u * v))`. -/
lemma comm_bivector_left {u v : B} (huv : anticomm u v = 0) :
    comm (u * v) u = -((2 : ℤ) • (u * u * v)) := by
  have h_vu : v * u = -(u * v) :=
    eq_neg_of_add_eq_zero_left (by dsimp [anticomm] at huv; rw [add_comm] at huv; exact huv)
  have h1 : (u * v) * u = -(u * u * v) := by
    calc
      (u * v) * u = u * (v * u) := by rw [mul_assoc]
      _ = u * (-(u * v)) := by rw [h_vu]
      _ = -(u * u * v) := by simp only [mul_neg, mul_assoc]
  have h2 : (2 : ℤ) • (u * u * v) = u * u * v + u * u * v := two_zsmul (u * u * v)
  dsimp [comm]
  rw [h1, h2]
  simp only [mul_assoc]
  abel

/-- For anticommuting `u, v`, `[u * v, v] = (2 : ℤ) • (u * (v * v))`. -/
lemma comm_bivector_right {u v : B} (huv : anticomm u v = 0) :
    comm (u * v) v = (2 : ℤ) • (u * (v * v)) := by
  have h_vu : v * u = -(u * v) :=
    eq_neg_of_add_eq_zero_left (by dsimp [anticomm] at huv; rw [add_comm] at huv; exact huv)
  have h1 : v * (u * v) = -(u * (v * v)) := by
    calc
      v * (u * v) = (v * u) * v := by rw [← mul_assoc]
      _ = (-(u * v)) * v := by rw [h_vu]
      _ = -(u * (v * v)) := by simp only [neg_mul, mul_assoc]
  have h2 : (2 : ℤ) • (u * (v * v)) = u * (v * v) + u * (v * v) := two_zsmul (u * (v * v))
  dsimp [comm]
  rw [h1, h2]
  simp only [mul_assoc]
  abel

/-- If `w` anticommutes with both `u` and `v`, then `[u * v, w] = 0`. -/
lemma comm_bivector_orthog {u v w : B}
    (huw : anticomm u w = 0) (hvw : anticomm v w = 0) :
    comm (u * v) w = 0 := by
  have h_uw : u * w = -(w * u) := eq_neg_of_add_eq_zero_left huw
  have h_vw : v * w = -(w * v) := eq_neg_of_add_eq_zero_left hvw
  have h1 : (u * v) * w = w * (u * v) := by
    calc
      (u * v) * w = u * (v * w) := by rw [mul_assoc]
      _ = u * (-(w * v)) := by rw [h_vw]
      _ = -((u * w) * v) := by simp only [mul_neg, mul_assoc]
      _ = -((-(w * u)) * v) := by rw [h_uw]
      _ = w * (u * v) := by simp only [neg_mul, neg_neg, mul_assoc]
  dsimp [comm]
  rw [h1, sub_self]

/-- Symmetry of the anticommutator `{u, v} = {v, u}`. -/
lemma anticomm_symm (u v : B) : anticomm u v = anticomm v u := by
  dsimp [anticomm]
  abel

/-- Linearity of `comm M` across the 4-dimensional Tetractys Dirac module `tetractysSlash`. -/
lemma comm_tetractysSlash (M S1 Phi1 S2 Phi2 : B) (p0 p1 p2 p3 : ℤ) :
    comm M (tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3) =
      p0 • comm M (tetractysGamma0 S1 Phi1) +
      p1 • comm M (tetractysGamma1 S1) +
      p2 • comm M (tetractysGamma2 Phi1 S2) +
      p3 • comm M (tetractysGamma3 Phi1 Phi2) := by
  dsimp [comm, tetractysSlash]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, zsmul_sub]
  abel_nf

/-- Linearity of `anticomm M` across the 4-dimensional Tetractys Dirac module `tetractysSlash`. -/
lemma anticomm_tetractysSlash (M S1 Phi1 S2 Phi2 : B) (p0 p1 p2 p3 : ℤ) :
    anticomm M (tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3) =
      p0 • anticomm M (tetractysGamma0 S1 Phi1) +
      p1 • anticomm M (tetractysGamma1 S1) +
      p2 • anticomm M (tetractysGamma2 Phi1 S2) +
      p3 • anticomm M (tetractysGamma3 Phi1 Phi2) := by
  dsimp [anticomm, tetractysSlash]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, zsmul_add]
  abel_nf

/-- Square of an integer linear combination `(a • u + b • v)² = a² • u² + b² • v² + (a * b) • {u, v}`. -/
lemma sq_add_zsmul (a b : ℤ) (u v : B) :
    (a • u + b • v) * (a • u + b • v) =
      (a * a) • (u * u) + (b * b) • (v * v) + (a * b) • anticomm u v := by
  dsimp [anticomm]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, zsmul_add, ← mul_zsmul, mul_comm b a]
  abel

/-- Endogenous Minkowski quadratic norm of the 4-dimensional Tetractys Dirac module:
`tetractysSlash p0 p1 p2 p3 * tetractysSlash p0 p1 p2 p3 = (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • 1`. -/
theorem tetractysSlash_sq
    (S1 Phi1 S2 Phi2 : B)
    (hS1 : S1 * S1 = 1) (hPhi1 : Phi1 * Phi1 = 1) (hAnti1 : Phi1 * S1 = -(S1 * Phi1))
    (hS2 : S2 * S2 = 1) (hPhi2 : Phi2 * Phi2 = 1) (hAnti2 : Phi2 * S2 = -(S2 * Phi2))
    (hS1S2 : S1 * S2 = S2 * S1) (hS1Phi2 : S1 * Phi2 = Phi2 * S1)
    (hPhi1S2 : Phi1 * S2 = S2 * Phi1) (hPhi1Phi2 : Phi1 * Phi2 = Phi2 * Phi1)
    (p0 p1 p2 p3 : ℤ) :
    tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3 *
      tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B) := by
  have hCl := dewitt_tetractys_generates_4d_minkowski_clifford_algebra
    S1 Phi1 S2 Phi2 hS1 hPhi1 hAnti1 hS2 hPhi2 hAnti2 hS1S2 hS1Phi2 hPhi1S2 hPhi1Phi2
  rcases hCl with ⟨h00, h11, h22, h33, h01, h02, h03, h12, h13, h23⟩
  set γ0 := tetractysGamma0 S1 Phi1
  set γ1 := tetractysGamma1 S1
  set γ2 := tetractysGamma2 Phi1 S2
  set γ3 := tetractysGamma3 Phi1 Phi2
  have hSplit :
      tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3 =
        (p0 • γ0 + p1 • γ1) + (p2 • γ2 + p3 • γ3) := by
    dsimp [tetractysSlash, γ0, γ1, γ2, γ3]
    abel
  have hA : (p0 • γ0 + p1 • γ1) * (p0 • γ0 + p1 • γ1) = (-p0 ^ 2 + p1 ^ 2) • (1 : B) := by
    rw [sq_add_zsmul, h00, h11, h01, smul_neg, zsmul_zero, add_zero,
        ← neg_zsmul, ← add_zsmul, sq, sq]
  have hC : (p2 • γ2 + p3 • γ3) * (p2 • γ2 + p3 • γ3) = (p2 ^ 2 + p3 ^ 2) • (1 : B) := by
    rw [sq_add_zsmul, h22, h33, h23, zsmul_zero, add_zero, ← add_zsmul, sq, sq]
  have hAC : anticomm (p0 • γ0 + p1 • γ1) (p2 • γ2 + p3 • γ3) = 0 := by
    have hBi :
        anticomm (p0 • γ0 + p1 • γ1) (p2 • γ2 + p3 • γ3) =
          (p0 * p2) • anticomm γ0 γ2 + (p0 * p3) • anticomm γ0 γ3 +
          (p1 * p2) • anticomm γ1 γ2 + (p1 * p3) • anticomm γ1 γ3 := by
      dsimp [anticomm]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, zsmul_add,
                 ← mul_zsmul, mul_comm p2 p0, mul_comm p3 p0, mul_comm p2 p1, mul_comm p3 p1]
      abel_nf
    rw [hBi, h02, h03, h12, h13]
    simp only [zsmul_zero, add_zero]
  have hWhole := sq_add_zsmul 1 1 (p0 • γ0 + p1 • γ1) (p2 • γ2 + p3 • γ3)
  simp only [one_zsmul, mul_one] at hWhole
  rw [hSplit, hWhole, hA, hC, hAC, add_zero, ← add_zsmul]
  congr 1
  ring

/--
**Endogenous Tetractys Lorentz Bivectors & 4D Translation Module Action (`tetractys_lorentz_bivectors_and_4d_translation_module`):**
In any `[Ring B]` equipped with two commuting DeWitt Tetractys splits `(S₁, Φ₁)` and `(S₂, Φ₂)`:
1. **3 Spatial Rotations & 3 Lorentz Boosts from the Tetractys:**
   `tetractysL12² = tetractysL13² = tetractysL23² = -1` and
   `tetractysK01² = tetractysK02² = tetractysK03² = 1`.
2. **Endogenous Minkowski Quadratic Norm & 4-Coordinate Recovery (4D Module Faithfulness Without Coordinate Matrices):**
   For `X = tetractysSlash S₁ Φ₁ S₂ Φ₂ p₀ p₁ p₂ p₃`:
   `X * X = (-p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) • 1`,
   `-anticomm γ₀ X = (2 * p₀) • 1`, and `anticomm γᵢ X = (2 * pᵢ) • 1` (`i ∈ {1, 2, 3}`).
3. **6-Generator Lorentz Action Preserving the 4-Dimensional Module `tetractysSlash`:**
   - `[K₀₁, not_p(p₀, p₁, p₂, p₃)] = not_p(2 p₁, 2 p₀, 0, 0)`,
   - `[K₀₂, not_p(p₀, p₁, p₂, p₃)] = not_p(2 p₂, 0, 2 p₀, 0)`,
   - `[K₀₃, not_p(p₀, p₁, p₂, p₃)] = not_p(2 p₃, 0, 0, 2 p₀)`,
   - `[L₁₂, not_p(p₀, p₁, p₂, p₃)] = not_p(0, 2 p₂, -2 p₁, 0)`,
   - `[L₁₃, not_p(p₀, p₁, p₂, p₃)] = not_p(0, 2 p₃, 0, -2 p₁)`,
   - `[L₂₃, not_p(p₀, p₁, p₂, p₃)] = not_p(0, 0, 2 p₃, -2 p₂)`.
-/
theorem tetractys_lorentz_bivectors_and_4d_translation_module
    (S1 Phi1 S2 Phi2 : B)
    (hS1 : S1 * S1 = 1) (hPhi1 : Phi1 * Phi1 = 1) (hAnti1 : Phi1 * S1 = -(S1 * Phi1))
    (hS2 : S2 * S2 = 1) (hPhi2 : Phi2 * Phi2 = 1) (hAnti2 : Phi2 * S2 = -(S2 * Phi2))
    (hS1S2 : S1 * S2 = S2 * S1) (hS1Phi2 : S1 * Phi2 = Phi2 * S1)
    (hPhi1S2 : Phi1 * S2 = S2 * Phi1) (hPhi1Phi2 : Phi1 * Phi2 = Phi2 * Phi1)
    (p0 p1 p2 p3 : ℤ) :
    let γ0 := tetractysGamma0 S1 Phi1
    let γ1 := tetractysGamma1 S1
    let γ2 := tetractysGamma2 Phi1 S2
    let γ3 := tetractysGamma3 Phi1 Phi2
    let slash := tetractysSlash S1 Phi1 S2 Phi2
    (tetractysL12 S1 Phi1 S2 * tetractysL12 S1 Phi1 S2 = -1 ∧
     tetractysL13 S1 Phi1 Phi2 * tetractysL13 S1 Phi1 Phi2 = -1 ∧
     tetractysL23 Phi1 S2 Phi2 * tetractysL23 Phi1 S2 Phi2 = -1) ∧
    (tetractysK01 S1 Phi1 * tetractysK01 S1 Phi1 = 1 ∧
     tetractysK02 S1 Phi1 S2 * tetractysK02 S1 Phi1 S2 = 1 ∧
     tetractysK03 S1 Phi1 Phi2 * tetractysK03 S1 Phi1 Phi2 = 1) ∧
    (slash p0 p1 p2 p3 * slash p0 p1 p2 p3 =
       (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B) ∧
     -anticomm γ0 (slash p0 p1 p2 p3) = (2 * p0) • (1 : B) ∧
     anticomm γ1 (slash p0 p1 p2 p3) = (2 * p1) • (1 : B) ∧
     anticomm γ2 (slash p0 p1 p2 p3) = (2 * p2) • (1 : B) ∧
     anticomm γ3 (slash p0 p1 p2 p3) = (2 * p3) • (1 : B)) ∧
    (comm (tetractysK01 S1 Phi1) (slash p0 p1 p2 p3) = slash (2 * p1) (2 * p0) 0 0 ∧
     comm (tetractysK02 S1 Phi1 S2) (slash p0 p1 p2 p3) = slash (2 * p2) 0 (2 * p0) 0 ∧
     comm (tetractysK03 S1 Phi1 Phi2) (slash p0 p1 p2 p3) = slash (2 * p3) 0 0 (2 * p0) ∧
     comm (tetractysL12 S1 Phi1 S2) (slash p0 p1 p2 p3) = slash 0 (2 * p2) (-2 * p1) 0 ∧
     comm (tetractysL13 S1 Phi1 Phi2) (slash p0 p1 p2 p3) = slash 0 (2 * p3) 0 (-2 * p1) ∧
     comm (tetractysL23 Phi1 S2 Phi2) (slash p0 p1 p2 p3) = slash 0 0 (2 * p3) (-2 * p2)) := by
  have hCl := dewitt_tetractys_generates_4d_minkowski_clifford_algebra
    S1 Phi1 S2 Phi2 hS1 hPhi1 hAnti1 hS2 hPhi2 hAnti2 hS1S2 hS1Phi2 hPhi1S2 hPhi1Phi2
  rcases hCl with ⟨h00, h11, h22, h33, h01, h02, h03, h12, h13, h23⟩
  have hSq := tetractysSlash_sq
    S1 Phi1 S2 Phi2 hS1 hPhi1 hAnti1 hS2 hPhi2 hAnti2 hS1S2 hS1Phi2 hPhi1S2 hPhi1Phi2
    p0 p1 p2 p3
  have h10 : anticomm (tetractysGamma1 S1) (tetractysGamma0 S1 Phi1) = 0 := by
    rw [anticomm_symm]; exact h01
  have h20 : anticomm (tetractysGamma2 Phi1 S2) (tetractysGamma0 S1 Phi1) = 0 := by
    rw [anticomm_symm]; exact h02
  have h30 : anticomm (tetractysGamma3 Phi1 Phi2) (tetractysGamma0 S1 Phi1) = 0 := by
    rw [anticomm_symm]; exact h03
  have h21 : anticomm (tetractysGamma2 Phi1 S2) (tetractysGamma1 S1) = 0 := by
    rw [anticomm_symm]; exact h12
  have h31 : anticomm (tetractysGamma3 Phi1 Phi2) (tetractysGamma1 S1) = 0 := by
    rw [anticomm_symm]; exact h13
  have h32 : anticomm (tetractysGamma3 Phi1 Phi2) (tetractysGamma2 Phi1 S2) = 0 := by
    rw [anticomm_symm]; exact h23
  have ha00 : anticomm (tetractysGamma0 S1 Phi1) (tetractysGamma0 S1 Phi1) = -((2 : ℤ) • (1 : B)) := by
    dsimp [anticomm]; rw [h00, two_zsmul]; abel
  have ha11 : anticomm (tetractysGamma1 S1) (tetractysGamma1 S1) = (2 : ℤ) • (1 : B) := by
    dsimp [anticomm]; rw [h11, two_zsmul]
  have ha22 : anticomm (tetractysGamma2 Phi1 S2) (tetractysGamma2 Phi1 S2) = (2 : ℤ) • (1 : B) := by
    dsimp [anticomm]; rw [h22, two_zsmul]
  have ha33 : anticomm (tetractysGamma3 Phi1 Phi2) (tetractysGamma3 Phi1 Phi2) = (2 : ℤ) • (1 : B) := by
    dsimp [anticomm]; rw [h33, two_zsmul]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨hSq, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [tetractysL12]; rw [bivector_sq_of_anticomm h12, h11, h22, mul_one]
  · dsimp [tetractysL13]; rw [bivector_sq_of_anticomm h13, h11, h33, mul_one]
  · dsimp [tetractysL23]; rw [bivector_sq_of_anticomm h23, h22, h33, mul_one]
  · dsimp [tetractysK01]; rw [bivector_sq_of_anticomm h01, h00, h11, neg_one_mul, neg_neg]
  · dsimp [tetractysK02]; rw [bivector_sq_of_anticomm h02, h00, h22, neg_one_mul, neg_neg]
  · dsimp [tetractysK03]; rw [bivector_sq_of_anticomm h03, h00, h33, neg_one_mul, neg_neg]
  · rw [anticomm_tetractysSlash, ha00, h01, h02, h03]
    simp only [smul_neg, zsmul_zero, add_zero, neg_neg, ← mul_zsmul, mul_comm p0 2]
  · rw [anticomm_tetractysSlash, h10, ha11, h12, h13]
    simp only [zsmul_zero, zero_add, add_zero, ← mul_zsmul, mul_comm p1 2]
  · rw [anticomm_tetractysSlash, h20, h21, ha22, h23]
    simp only [zsmul_zero, zero_add, add_zero, ← mul_zsmul, mul_comm p2 2]
  · rw [anticomm_tetractysSlash, h30, h31, h32, ha33]
    simp only [zsmul_zero, zero_add, add_zero, ← mul_zsmul, mul_comm p3 2]
  · dsimp [tetractysK01]
    rw [comm_tetractysSlash, comm_bivector_left h01, comm_bivector_right h01,
        comm_bivector_orthog h02 h12, comm_bivector_orthog h03 h13, h00, h11]
    dsimp [tetractysSlash]
    simp only [neg_one_mul, mul_one, zsmul_neg, neg_neg, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p0 2, mul_comm p1 2]
    abel
  · dsimp [tetractysK02]
    rw [comm_tetractysSlash, comm_bivector_left h02, comm_bivector_orthog h01 h21,
        comm_bivector_right h02, comm_bivector_orthog h03 h23, h00, h22]
    dsimp [tetractysSlash]
    simp only [neg_one_mul, mul_one, zsmul_neg, neg_neg, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p0 2, mul_comm p2 2]
    abel
  · dsimp [tetractysK03]
    rw [comm_tetractysSlash, comm_bivector_left h03, comm_bivector_orthog h01 h31,
        comm_bivector_orthog h02 h32, comm_bivector_right h03, h00, h33]
    dsimp [tetractysSlash]
    simp only [neg_one_mul, mul_one, zsmul_neg, neg_neg, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p0 2, mul_comm p3 2]
    abel
  · dsimp [tetractysL12]
    rw [comm_tetractysSlash, comm_bivector_orthog h10 h20, comm_bivector_left h12,
        comm_bivector_right h12, comm_bivector_orthog h13 h23, h11, h22]
    dsimp [tetractysSlash]
    simp only [one_mul, mul_one, zsmul_neg, neg_mul, neg_zsmul, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p1 2, mul_comm p2 2]
    abel
  · dsimp [tetractysL13]
    rw [comm_tetractysSlash, comm_bivector_orthog h10 h30, comm_bivector_left h13,
        comm_bivector_orthog h12 h32, comm_bivector_right h13, h11, h33]
    dsimp [tetractysSlash]
    simp only [one_mul, mul_one, zsmul_neg, neg_mul, neg_zsmul, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p1 2, mul_comm p3 2]
    abel
  · dsimp [tetractysL23]
    rw [comm_tetractysSlash, comm_bivector_orthog h20 h30, comm_bivector_orthog h21 h31,
        comm_bivector_left h23, comm_bivector_right h23, h22, h33]
    dsimp [tetractysSlash]
    simp only [one_mul, mul_one, zsmul_neg, neg_mul, neg_zsmul, zsmul_zero, zero_zsmul,
               ← mul_zsmul, mul_comm p2 2, mul_comm p3 2]
    abel

end RealMinkowskiFromTetractys

/-!
## §2. Nodes $\mathfrak{SP}_3 \prec \mathfrak{SP}_4$: Peirce-Corner Lorentz Action, 4-Dimensional Translation Module, and Super-Jacobi Closure
-/

section PoincareLieAlgebraFromPeirce

variable {B : Type u} [Ring B]

/-- Primal nilpotent Peirce translation embedding $\mathcal{P}(p) = P_{\mathrm{tr}} p (1 - P_{\mathrm{tr}}) \in \mathfrak{n}_+$. -/
def TransN (P p : B) : B := P * p * (1 - P)

/-- Even stabilizer Lorentz embedding $\mathcal{L}(M) = P_{\mathrm{tr}} M P_{\mathrm{tr}} + (1 - P_{\mathrm{tr}}) M (1 - P_{\mathrm{tr}}) \in \mathfrak{k}$. -/
def LorentzL (P M : B) : B := P * M * P + (1 - P) * M * (1 - P)

/-- Odd Super-Peirce supercharge $Q(Z, \bar{Z}) = P Z (1 - P) + (1 - P) \bar{Z} P$. -/
def superQ (P Z Zbar : B) : B := P * Z * (1 - P) + (1 - P) * Zbar * P

/-- The 4-dimensional Poincaré translation module embedded in the upper Peirce corner
$\mathfrak{n}_+ = P B (1 - P)$ via a corner bridge seed $W \in B$ and the Tetractys Dirac module. -/
def tetractysPoincareTrans (P W S1 Phi1 S2 Phi2 : B) (p0 p1 p2 p3 : ℤ) : B :=
  TransN P (W * tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3)

/-- Right-associated idempotent collapse `P * (P * Z) = P * Z` for `P * P = P`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- When `M` commutes with `P` (`P * M = M * P`), the Peirce stabilizer projection `LorentzL P M` equals `M`. -/
lemma lorentzL_eq_self {P M : B} (hP : P * P = P) (hMP : P * M = M * P) :
    LorentzL P M = M := by
  have hPPM : P * (P * M) = P * M := by
    rw [← mul_assoc, hP]
  dsimp [LorentzL]
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, ← hMP, hPPM]
  abel

/-- When `M` commutes with `P`, the commutator action of `LorentzL P M` on the Peirce corner
`TransN P x` is equivariant: `[LorentzL P M, TransN P x] = TransN P [M, x]`. -/
lemma comm_lorentzL_transN {P M : B} (hP : P * P = P) (hMP : P * M = M * P) (x : B) :
    comm (LorentzL P M) (TransN P x) = TransN P (comm M x) := by
  rw [lorentzL_eq_self hP hMP]
  have h1 : M * (P * x * (1 - P)) = P * (M * x) * (1 - P) := by
    calc
      M * (P * x * (1 - P)) = (M * P) * x * (1 - P) := by simp only [mul_assoc]
      _ = (P * M) * x * (1 - P) := by rw [← hMP]
      _ = P * (M * x) * (1 - P) := by simp only [mul_assoc]
  have h2 : (P * x * (1 - P)) * M = P * (x * M) * (1 - P) := by
    have hQM : (1 - P) * M = M * (1 - P) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hMP]
    calc
      (P * x * (1 - P)) * M = P * x * ((1 - P) * M) := by simp only [mul_assoc]
      _ = P * x * (M * (1 - P)) := by rw [hQM]
      _ = P * (x * M) * (1 - P) := by simp only [mul_assoc]
  dsimp [comm, TransN]
  rw [h1, h2]
  simp only [mul_sub, sub_mul]
  abel

/-- Elements fixed by the Peirce corner projection, viewed as an additive `ℤ`-submodule.
This packages the corner itself; it does not assume that the corner has dimension four. -/
def upperPeirceCorner (P : B) : Submodule ℤ B where
  carrier := {x | P * x * (1 - P) = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    calc
      P * (x + y) * (1 - P) = P * x * (1 - P) + P * y * (1 - P) := by noncomm_ring
      _ = x + y := by rw [hx, hy]
  smul_mem' := by
    intro n x hx
    calc
      P * (n • x) * (1 - P) = n • (P * x * (1 - P)) := by
        simp only [mul_smul_comm, smul_mul_assoc]
      _ = n • x := by rw [hx]

/-- Every primal Peirce translation lies in the upper corner. -/
lemma transN_mem_upperPeirceCorner {P : B} (hP : P * P = P) (x : B) :
    P * TransN P x * (1 - P) = TransN P x := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; abel
  dsimp [TransN]
  calc
    P * (P * x * (1 - P)) * (1 - P) = P * P * x * ((1 - P) * (1 - P)) := by
      simp only [mul_assoc]
    _ = P * x * (1 - P) := by rw [hP, hQ]

/-- The stabilizer commutator induces a coordinate-free linear action on the upper Peirce
corner whenever its generator commutes with the Peirce idempotent. The carrier's dimension
is deliberately left unspecified; a four-dimensional representation requires a separate
dimension or faithful-coordinate theorem for the chosen algebra. -/
def upperPeirceLorentzAction (P M : B) (hP : P * P = P) (hMP : P * M = M * P) :
    upperPeirceCorner P →ₗ[ℤ] upperPeirceCorner P where
  toFun x := ⟨comm (LorentzL P M) x.1, by
    have hcorner : TransN P x.1 = x.1 := x.2
    rw [← hcorner, comm_lorentzL_transN hP hMP]
    exact transN_mem_upperPeirceCorner hP (comm M x.1)⟩
  map_add' x y := by
    apply Subtype.ext
    dsimp [comm]
    noncomm_ring
  map_smul' n x := by
    apply Subtype.ext
    dsimp [comm]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The induced corner actions satisfy the Lie representation identity
`ad M ∘ ad N - ad N ∘ ad M = ad [M,N]`. -/
theorem upperPeirceLorentzAction_commutator
    {P M N : B} (hP : P * P = P)
    (hMP : P * M = M * P) (hNP : P * N = N * P)
    (x : upperPeirceCorner P) :
    upperPeirceLorentzAction P M hP hMP
        (upperPeirceLorentzAction P N hP hNP x) -
      upperPeirceLorentzAction P N hP hNP
        (upperPeirceLorentzAction P M hP hMP x) =
      upperPeirceLorentzAction P (comm M N) hP (by
        dsimp [comm]
        calc
          P * (M * N - N * M) = (P * M) * N - (P * N) * M := by simp only [mul_assoc, mul_sub]
          _ = (M * P) * N - (N * P) * M := by rw [hMP, hNP]
          _ = M * (P * N) - N * (P * M) := by simp only [mul_assoc]
          _ = M * (N * P) - N * (M * P) := by rw [hNP, hMP]
          _ = (M * N) * P - (N * M) * P := by simp only [mul_assoc]
          _ = (M * N - N * M) * P := by rw [sub_mul]) x := by
  apply Subtype.ext
  change comm (LorentzL P M) (comm (LorentzL P N) x.1) -
      comm (LorentzL P N) (comm (LorentzL P M) x.1) =
    comm (LorentzL P (comm M N)) x.1
  rw [lorentzL_eq_self hP hMP, lorentzL_eq_self hP hNP]
  have hComm : P * comm M N = comm M N * P := by
    dsimp [comm]
    calc
      P * (M * N - N * M) = P * M * N - P * N * M := by simp only [mul_sub, mul_assoc]
      _ = M * P * N - N * P * M := by rw [hMP, hNP]
      _ = M * (P * N) - N * (P * M) := by simp only [mul_assoc]
      _ = M * (N * P) - N * (M * P) := by rw [hNP, hMP]
      _ = M * N * P - N * M * P := by simp only [mul_assoc]
      _ = (M * N - N * M) * P := by rw [sub_mul]
  rw [lorentzL_eq_self hP hComm]
  dsimp [comm]
  noncomm_ring

/-- The coordinate-free vector carrier maps additively into the upper Peirce corner through
the universal Clifford representation and a Peirce bridge `W`. No basis of `V` is selected. -/
def tetractysCliffordCornerMap
    {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) [Algebra R B]
    (ρ : CliffordAlgebra Q →ₐ[R] B) (P W : B) (hP : P * P = P) :
    V →+ upperPeirceCorner P where
  toFun v := ⟨P * W * ρ (CliffordAlgebra.ι Q v) * (1 - P), by
    have hQ : (1 - P) * (1 - P) = 1 - P := by
      calc
        (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP]; abel
    calc
      P * (P * W * ρ (CliffordAlgebra.ι Q v) * (1 - P)) * (1 - P) =
          P * P * W * ρ (CliffordAlgebra.ι Q v) * ((1 - P) * (1 - P)) := by
            simp only [mul_assoc]
      _ = P * W * ρ (CliffordAlgebra.ι Q v) * (1 - P) := by
        rw [hP, hQ]
        ⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' v w := by
    apply Subtype.ext
    change P * W * ρ (CliffordAlgebra.ι Q (v + w)) * (1 - P) =
      P * W * ρ (CliffordAlgebra.ι Q v) * (1 - P) +
        P * W * ρ (CliffordAlgebra.ι Q w) * (1 - P)
    rw [map_add, map_add]
    simp only [mul_add, add_mul]

/-- The Peirce-corner map intertwines the coordinate-free Clifford bivector action with the
commutator action on the corner. This is the bridge from the abstract quadratic module to the
operator-valued translation carrier; injectivity and the dimension of its image are separate. -/
theorem tetractysCliffordCornerMap_bivector_equivariant
    {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) [Algebra R B]
    (ρ : CliffordAlgebra Q →ₐ[R] B) (P W : B)
    (hP : P * P = P) (a b v : V)
    (hMP : P * ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) =
      ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * P)
    (hMW : ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * W =
      W * ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) :
    (upperPeirceLorentzAction P
      (ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) hP hMP
      (tetractysCliffordCornerMap Q ρ P W hP v)).1 =
    tetractysCliffordCornerMap Q ρ P W hP
      (InfoGeometry.Canonical.TetractysCliffordLorentzAction.bivectorAction Q a b v) := by
  let M := ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)
  let X := ρ (CliffordAlgebra.ι Q v)
  have hMQ : M * (1 - P) = (1 - P) * M := by
    calc
      M * (1 - P) = M - M * P := by simp only [mul_sub, mul_one]
      _ = M - P * M := by rw [hMP]
      _ = (1 - P) * M := by simp only [sub_mul, one_mul, mul_sub]
  have hLeft : M * (P * W * X * (1 - P)) = P * W * (M * X) * (1 - P) := by
    calc
      M * (P * W * X * (1 - P)) = (M * P) * W * X * (1 - P) := by simp only [mul_assoc]
      _ = (P * M) * W * X * (1 - P) := by rw [hMP]
      _ = P * (M * W) * X * (1 - P) := by simp only [mul_assoc]
      _ = P * (W * M) * X * (1 - P) := by rw [hMW]
      _ = P * W * (M * X) * (1 - P) := by simp only [mul_assoc]
  have hRight : (P * W * X * (1 - P)) * M = P * W * (X * M) * (1 - P) := by
    calc
      (P * W * X * (1 - P)) * M = P * W * X * ((1 - P) * M) := by simp only [mul_assoc]
      _ = P * W * X * (M * (1 - P)) := by rw [hMQ]
      _ = P * W * (X * M) * (1 - P) := by simp only [mul_assoc]
  have hRep : M * X - X * M =
      ρ (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
    dsimp [M, X]
    simp only [map_mul, map_sub, mul_assoc]
  have hBivector := InfoGeometry.Canonical.TetractysCliffordLorentzAction.bivector_commutator_preserves_vectors
    Q a b v
  change comm (LorentzL P M) (P * W * X * (1 - P)) =
    P * W * ρ (CliffordAlgebra.ι Q
      (InfoGeometry.Canonical.TetractysCliffordLorentzAction.bivectorAction Q a b v)) * (1 - P)
  rw [lorentzL_eq_self hP hMP]
  dsimp [comm]
  rw [hLeft, hRight]
  calc
    P * W * (M * X) * (1 - P) - P * W * (X * M) * (1 - P) =
        P * W * (M * X - X * M) * (1 - P) := by
          noncomm_ring
    _ = P * W * ρ (CliffordAlgebra.ι Q
        (InfoGeometry.Canonical.TetractysCliffordLorentzAction.bivectorAction Q a b v)) *
        (1 - P) := by rw [hRep, hBivector]

/-- When `M` commutes with `W`, `[M, W * y] = W * [M, y]`. -/
lemma comm_mul_right_of_comm {M W : B} (hMW : M * W = W * M) (y : B) :
    comm M (W * y) = W * comm M y := by
  have h1 : M * (W * y) = W * (M * y) := by
    calc
      M * (W * y) = (M * W) * y := by rw [← mul_assoc]
      _ = (W * M) * y := by rw [hMW]
      _ = W * (M * y) := by rw [mul_assoc]
  dsimp [comm]
  rw [h1, mul_sub, mul_assoc]

/--
**Theorem 2 ($\mathfrak{SP}_3 \prec \mathfrak{SP}_4$ — `poincare_translations_commute_and_lorentz_covariance`):**
1. **Tetractys Dimension Count:** `6 (Lorentz M_{μν}) + 4 (Translations P_μ) = 10`.
2. **Peirce Corner Membership & Abelian Spacetime Translations (`[P_μ, P_ν] = 0`):**
   For any `p, q ∈ B`, `P * TransN P p * (1 - P) = TransN P p`, `TransN P p * TransN P q = 0`,
   `comm (TransN P p) (TransN P q) = 0`,
   `(1 + TransN P p) * (1 + TransN P q) = 1 + TransN P (p + q)`, and
   `(1 + TransN P p) * (1 - TransN P p) = 1`.
3. **Lorentz Action Preserving the Peirce Corner & Equivariance:**
   For any `M, p ∈ B`, `LorentzL P M` commutes with `P` (`comm (LorentzL P M) P = 0`), its
   commutator action preserves the upper Peirce corner
   (`P * comm (LorentzL P M) (TransN P p) * (1 - P) = comm (LorentzL P M) (TransN P p)`),
   and when `P * M = M * P`, `comm (LorentzL P M) (TransN P p) = TransN P (comm M p)`.
4. **Super-Poincaré Odd Super-Jacobi Identities:**
   `comm Q (Q * Q + Q * Q) = 0` and
   `comm QA (anticomm QB QC) + comm QB (anticomm QC QA) + comm QC (anticomm QA QB) = 0`.
-/
theorem poincare_translations_commute_and_lorentz_covariance
    (P M p q Q QA QB QC : B) (hP : P * P = P) (hMP : P * M = M * P) :
    6 + 4 = 10 ∧
    P * TransN P p * (1 - P) = TransN P p ∧
    TransN P p * TransN P q = 0 ∧
    comm (TransN P p) (TransN P q) = 0 ∧
    (1 + TransN P p) * (1 + TransN P q) = 1 + TransN P (p + q) ∧
    (1 + TransN P p) * (1 - TransN P p) = 1 ∧
    comm (LorentzL P M) P = 0 ∧
    P * comm (LorentzL P M) (TransN P p) * (1 - P) = comm (LorentzL P M) (TransN P p) ∧
    comm (LorentzL P M) (TransN P p) = TransN P (comm M p) ∧
    comm Q (Q * Q + Q * Q) = 0 ∧
    comm QA (anticomm QB QC) + comm QB (anticomm QC QA) + comm QC (anticomm QA QB) = 0 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, comm_lorentzL_transN hP hMP p, ?_, ?_⟩ <;>
  · dsimp only [TransN, LorentzL, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, proj_idem hP]
    abel

/--
**Lorentz Action Preserving the Peirce Corner, 4-Dimensional Translation Module, and Correlator Propagator Pairing (`peirce_corner_4d_translation_module_and_lorentz_action`):**
Let `P * P = P` be a Peirce idempotent and `W : B` a corner bridge seed commuting with the
Two-Bit DeWitt Tetractys `(S₁, Φ₁, S₂, Φ₂)`. Then the 4-dimensional translation module
`T(p₀, p₁, p₂, p₃) = tetractysPoincareTrans P W S₁ Φ₁ S₂ Φ₂ p₀ p₁ p₂ p₃` satisfies:
1. **Peirce Corner Membership:** `P * T(p₀, p₁, p₂, p₃) * (1 - P) = T(p₀, p₁, p₂, p₃)`,
2. **4D Module Additivity & Abelian Nilpotency:**
   `T(p₀ + q₀, p₁ + q₁, p₂ + q₂, p₃ + q₃) = T(p₀, p₁, p₂, p₃) + T(q₀, q₁, q₂, q₃)`,
   `T(p₀, p₁, p₂, p₃) * T(q₀, q₁, q₂, q₃) = 0`, and
   `comm (T(p₀, p₁, p₂, p₃)) (T(q₀, q₁, q₂, q₃)) = 0`,
3. **Invariance Under All 6 Endogenous Tetractys Lorentz Generators:**
   - `comm (LorentzL P K₀₁) (T p₀ p₁ p₂ p₃) = T (2 * p₁) (2 * p₀) 0 0`,
   - `comm (LorentzL P K₀₂) (T p₀ p₁ p₂ p₃) = T (2 * p₂) 0 (2 * p₀) 0`,
   - `comm (LorentzL P K₀₃) (T p₀ p₁ p₂ p₃) = T (2 * p₃) 0 0 (2 * p₀)`,
   - `comm (LorentzL P L₁₂) (T p₀ p₁ p₂ p₃) = T 0 (2 * p₂) (-2 * p₁) 0`,
   - `comm (LorentzL P L₁₃) (T p₀ p₁ p₂ p₃) = T 0 (2 * p₃) 0 (-2 * p₁)`,
   - `comm (LorentzL P L₂₃) (T p₀ p₁ p₂ p₃) = T 0 0 (2 * p₃) (-2 * p₂)`,
4. **Endogenous Peirce-Corner Correlator Propagator Pairing:**
   `(conePlus P W * tetractysSlash p₀ p₁ p₂ p₃) * (tetractysSlash p₀ p₁ p₂ p₃ * coneMinus P W) = (-p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) • (conePlus P W * coneMinus P W)`.
-/
theorem peirce_corner_4d_translation_module_and_lorentz_action
    (P W S1 Phi1 S2 Phi2 : B)
    (hP : P * P = P)
    (hS1 : S1 * S1 = 1) (hPhi1 : Phi1 * Phi1 = 1) (hAnti1 : Phi1 * S1 = -(S1 * Phi1))
    (hS2 : S2 * S2 = 1) (hPhi2 : Phi2 * Phi2 = 1) (hAnti2 : Phi2 * S2 = -(S2 * Phi2))
    (hS1S2 : S1 * S2 = S2 * S1) (hS1Phi2 : S1 * Phi2 = Phi2 * S1)
    (hPhi1S2 : Phi1 * S2 = S2 * Phi1) (hPhi1Phi2 : Phi1 * Phi2 = Phi2 * Phi1)
    (hPK01 : P * tetractysK01 S1 Phi1 = tetractysK01 S1 Phi1 * P)
    (hPK02 : P * tetractysK02 S1 Phi1 S2 = tetractysK02 S1 Phi1 S2 * P)
    (hPK03 : P * tetractysK03 S1 Phi1 Phi2 = tetractysK03 S1 Phi1 Phi2 * P)
    (hPL12 : P * tetractysL12 S1 Phi1 S2 = tetractysL12 S1 Phi1 S2 * P)
    (hPL13 : P * tetractysL13 S1 Phi1 Phi2 = tetractysL13 S1 Phi1 Phi2 * P)
    (hPL23 : P * tetractysL23 Phi1 S2 Phi2 = tetractysL23 Phi1 S2 Phi2 * P)
    (hWK01 : tetractysK01 S1 Phi1 * W = W * tetractysK01 S1 Phi1)
    (hWK02 : tetractysK02 S1 Phi1 S2 * W = W * tetractysK02 S1 Phi1 S2)
    (hWK03 : tetractysK03 S1 Phi1 Phi2 * W = W * tetractysK03 S1 Phi1 Phi2)
    (hWL12 : tetractysL12 S1 Phi1 S2 * W = W * tetractysL12 S1 Phi1 S2)
    (hWL13 : tetractysL13 S1 Phi1 Phi2 * W = W * tetractysL13 S1 Phi1 Phi2)
    (hWL23 : tetractysL23 Phi1 S2 Phi2 * W = W * tetractysL23 Phi1 S2 Phi2)
    (p0 p1 p2 p3 q0 q1 q2 q3 : ℤ) :
    let T := tetractysPoincareTrans P W S1 Phi1 S2 Phi2
    let slash := tetractysSlash S1 Phi1 S2 Phi2
    P * T p0 p1 p2 p3 * (1 - P) = T p0 p1 p2 p3 ∧
    T (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) = T p0 p1 p2 p3 + T q0 q1 q2 q3 ∧
    T p0 p1 p2 p3 * T q0 q1 q2 q3 = 0 ∧
    comm (T p0 p1 p2 p3) (T q0 q1 q2 q3) = 0 ∧
    comm (LorentzL P (tetractysK01 S1 Phi1)) (T p0 p1 p2 p3) = T (2 * p1) (2 * p0) 0 0 ∧
    comm (LorentzL P (tetractysK02 S1 Phi1 S2)) (T p0 p1 p2 p3) = T (2 * p2) 0 (2 * p0) 0 ∧
    comm (LorentzL P (tetractysK03 S1 Phi1 Phi2)) (T p0 p1 p2 p3) = T (2 * p3) 0 0 (2 * p0) ∧
    comm (LorentzL P (tetractysL12 S1 Phi1 S2)) (T p0 p1 p2 p3) = T 0 (2 * p2) (-2 * p1) 0 ∧
    comm (LorentzL P (tetractysL13 S1 Phi1 Phi2)) (T p0 p1 p2 p3) = T 0 (2 * p3) 0 (-2 * p1) ∧
    comm (LorentzL P (tetractysL23 Phi1 S2 Phi2)) (T p0 p1 p2 p3) = T 0 0 (2 * p3) (-2 * p2) ∧
    (conePlus P W * slash p0 p1 p2 p3) * (slash p0 p1 p2 p3 * coneMinus P W) =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (conePlus P W * coneMinus P W) := by
  have hMod := tetractys_lorentz_bivectors_and_4d_translation_module
    S1 Phi1 S2 Phi2 hS1 hPhi1 hAnti1 hS2 hPhi2 hAnti2
    hS1S2 hS1Phi2 hPhi1S2 hPhi1Phi2 p0 p1 p2 p3
  have hSq := hMod.2.2.1.1
  rcases hMod.2.2.2 with ⟨hK01, hK02, hK03, hL12, hL13, hL23⟩
  have hBase := poincare_translations_commute_and_lorentz_covariance
    P (tetractysK01 S1 Phi1)
    (W * tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3)
    (W * tetractysSlash S1 Phi1 S2 Phi2 q0 q1 q2 q3)
    P P P P hP hPK01
  refine ⟨hBase.2.1, ?_, hBase.2.2.1, hBase.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [tetractysPoincareTrans, TransN, tetractysSlash]
    simp only [add_zsmul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    abel
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPK01, comm_mul_right_of_comm hWK01, hK01]
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPK02, comm_mul_right_of_comm hWK02, hK02]
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPK03, comm_mul_right_of_comm hWK03, hK03]
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPL12, comm_mul_right_of_comm hWL12, hL12]
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPL13, comm_mul_right_of_comm hWL13, hL13]
  · dsimp [tetractysPoincareTrans]
    rw [comm_lorentzL_transN hP hPL23, comm_mul_right_of_comm hWL23, hL23]
  · calc
      (conePlus P W * tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3) *
          (tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3 * coneMinus P W)
        = conePlus P W *
            (tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3 *
              tetractysSlash S1 Phi1 S2 Phi2 p0 p1 p2 p3) *
            coneMinus P W := by simp only [mul_assoc]
      _ = conePlus P W * ((-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B)) * coneMinus P W := by
        rw [hSq]
      _ = (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (conePlus P W * coneMinus P W) := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_one]

/--
**Super-Peirce Odd Supercharge Anticommutator (`super_peirce_odd_supercharge_anticommutator`):**
For any Bose–Fermi idempotent `P * P = P` and twistor seeds `Z₁, Z̄₁, Z₂, Z̄₂ : B`, the odd
supercharges `superQ P Z₁ Z̄₁` and `superQ P Z₂ Z̄₂` anticommute into the even diagonal sector,
and their bosonic projection `P * {Q₁, Q₂} * P` equals the symmetric twistor bilinear
`P * Z₁ * (1 - P) * Z̄₂ * P + P * Z₂ * (1 - P) * Z̄₁ * P`.
-/
theorem super_peirce_odd_supercharge_anticommutator
    (P Z1 Zbar1 Z2 Zbar2 : B) (hP : P * P = P) :
    P * anticomm (superQ P Z1 Zbar1) (superQ P Z2 Zbar2) * P =
      P * Z1 * (1 - P) * Zbar2 * P + P * Z2 * (1 - P) * Zbar1 * P ∧
    P * anticomm (superQ P Z1 Zbar1) (superQ P Z2 Zbar2) * (1 - P) = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · dsimp only [superQ, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, proj_idem hP]
    abel

end PoincareLieAlgebraFromPeirce

/-!
## §3. Nodes $\mathfrak{SP}_5 \prec \mathfrak{SP}_6 \prec \mathfrak{SP}_7$: Endogenous Tetractys Twistor Momentum Expansion, Null Light Cone, 2-Twistor Massive Casimir, & Positive Energy
-/

section RealTwistorSupersymmetry

variable {B : Type u} [Ring B]

/-- Endogenous DeWitt Tetractys rank-one chiral twistor momentum operator
$P_{\mathrm{twistor}}(P, W; \lambda_1, \lambda_2) = \lambda_1^2 P + \lambda_2^2 (1 - P) + (\lambda_1 \lambda_2)\,\mathrm{genPhi}(P, W, W)$
constructed purely from the Peirce idempotent `P` and bridge `genPhi P W W`. -/
def tetractysTwistorMom (P W : B) (lam1 lam2 : ℤ) : B :=
  (lam1 ^ 2) • P + (lam2 ^ 2) • (1 - P) + (lam1 * lam2) • genPhi P W W

/--
**Theorem 3 ($\mathfrak{SP}_5 \prec \mathfrak{SP}_6 \prec \mathfrak{SP}_7$ — `real_twistor_susy_null_and_massive_momentum_factorization`):**
For any Peirce idempotent `P : B`, bridge seed `W : B`, integer twistor components
`lam1, lam2, mu1, mu2 : ℤ`, and real twistor components `r1, r2, s1, s2 : ℝ`:
1. **Endogenous DeWitt Tetractys Basis Expansion of $2 P_{\mathrm{twistor}}(P, W; \lambda_1, \lambda_2)$:**
   `(2 : ℤ) • tetractysTwistorMom P W lam1 lam2 = (lam1 ^ 2 + lam2 ^ 2) • 1 + (lam1 ^ 2 - lam2 ^ 2) • invS P + (2 * lam1 * lam2) • genPhi P W W`.
2. **1-Twistor Massless Light-Cone Identity:**
   Setting `p₀_sc = lam1² + lam2²`, `p₁_sc = lam1² - lam2²`, and `p₂_sc = 2 * lam1 * lam2`,
   the Minkowski norm vanishes identically:
   `p₀_sc² - p₁_sc² - p₂_sc² = 0` and `(lam1²)(lam2²) - (lam1 * lam2)² = 0`.
3. **2-Twistor Massive Casimir Identity (`P = λ λᵀ + μ μᵀ`):**
   The determinant of the 2-twistor momentum equals the square of the symplectic twistor
   2-bracket `⟨λ μ⟩ = lam1 * mu2 - lam2 * mu1`:
   `(lam1² + mu1²)(lam2² + mu2²) - (lam1 * lam2 + mu1 * mu2)² = (lam1 * mu2 - lam2 * mu1)²`.
4. **Witten Positive Energy & Mass Positivity Over $\mathbb{R}$:**
   `0 ≤ r1 ^ 2 + r2 ^ 2` and `0 ≤ (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2`.
-/
theorem real_twistor_susy_null_and_massive_momentum_factorization
    (P W : B) (lam1 lam2 mu1 mu2 : ℤ) (r1 r2 s1 s2 : ℝ) :
    let p0_sc := lam1 ^ 2 + lam2 ^ 2
    let p1_sc := lam1 ^ 2 - lam2 ^ 2
    let p2_sc := 2 * lam1 * lam2
    (2 : ℤ) • tetractysTwistorMom P W lam1 lam2 =
      p0_sc • (1 : B) + p1_sc • invS P + p2_sc • genPhi P W W ∧
    p0_sc ^ 2 - p1_sc ^ 2 - p2_sc ^ 2 = 0 ∧
    (lam1 ^ 2) * (lam2 ^ 2) - (lam1 * lam2) ^ 2 = 0 ∧
    (lam1 ^ 2 + mu1 ^ 2) * (lam2 ^ 2 + mu2 ^ 2) - (lam1 * lam2 + mu1 * mu2) ^ 2 =
      (lam1 * mu2 - lam2 * mu1) ^ 2 ∧
    0 ≤ r1 ^ 2 + r2 ^ 2 ∧
    0 ≤ (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2 := by
  have hCasR :
      (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2 =
        (r1 * s2 - r2 * s1) ^ 2 := by ring
  refine ⟨?_, by ring, by ring, by ring, by positivity, ?_⟩
  · rw [two_zsmul]
    dsimp [tetractysTwistorMom, invS]
    simp only [two_mul, add_mul, zsmul_sub, add_zsmul, sub_zsmul, mul_zsmul]
    abel
  · rw [hCasR]
    positivity

end RealTwistorSupersymmetry

/-!
## §4. Endogenous Twistor Incidence Relation, 15D Conformal $\mathfrak{so}(4, 2)$ Grading, and Super-Grassmannian $\mathrm{Gr}(2|2, 4|4)$ Analytic Superspace
-/

section ConformalTwistorAndSuperGrassmannian

variable {B : Type u} [Ring B]

/-- Lower Peirce corner `(1 - P) * k * P` representing the 4 special conformal
generators $K_\mu \in \mathfrak{n}_- = (1 - P) B P$ of the 15-dimensional conformal
algebra $\mathfrak{so}(4, 2) \cong \mathfrak{su}(2, 2)$ (Dian, arXiv:2210.16671, §2.2 & §2.4.2). -/
def ConformalK (P k : B) : B := (1 - P) * k * P

/-- Bosonic spacetime block $P (E x E) (1 - P)$ of the $\mathrm{Gr}(2|2, 4|4)$ analytic superspace
upper Peirce corner (representing $x^{\dot{a} b}$ in Dian, arXiv:2210.16671, §2.2.1 Eq. (2.2.6)). -/
def superAnalyticX (P E x : B) : B := P * (E * x * E) * (1 - P)

/-- Internal $R$-symmetry bosonic block $P ((1 - E) y (1 - E)) (1 - P)$ of the $\mathrm{Gr}(2|2, 4|4)$
analytic superspace upper Peirce corner (representing $y^{A B'}$ in Dian, arXiv:2210.16671, §2.2.1 Eq. (2.2.6)). -/
def superAnalyticY (P E y : B) : B := P * ((1 - E) * y * (1 - E)) * (1 - P)

/-- Chiral odd Grassmann block $P (E \theta (1 - E)) (1 - P)$ of the $\mathrm{Gr}(2|2, 4|4)$
analytic superspace upper Peirce corner (representing $\theta^{\dot{a} B'}$ in Dian, arXiv:2210.16671, §2.2.1 Eq. (2.2.6)). -/
def superAnalyticTheta (P E theta : B) : B := P * (E * theta * (1 - E)) * (1 - P)

/-- Antichiral odd Grassmann block $P ((1 - E) \bar{\theta} E) (1 - P)$ of the $\mathrm{Gr}(2|2, 4|4)$
analytic superspace upper Peirce corner (representing $\bar{\theta}^{A b}$ in Dian, arXiv:2210.16671, §2.2.1 Eq. (2.2.6)). -/
def superAnalyticThetaBar (P E thetabar : B) : B := P * ((1 - E) * thetabar * E) * (1 - P)

/-- Full $\mathrm{Gr}(2|2, 4|4)$ analytic superspace super-translation in the upper Peirce corner
$\mathcal{X} = X_{\mathrm{bos}} + Y_{R} + \Theta + \bar{\Theta} \in P B (1 - P)$. -/
def superAnalyticCorner (P E x y theta thetabar : B) : B :=
  superAnalyticX P E x + superAnalyticY P E y +
  superAnalyticTheta P E theta + superAnalyticThetaBar P E thetabar

/--
**Theorem 4 (`tetractys_twistor_incidence_and_conformal_so42_grading`):**
For any Peirce idempotent `P * P = P` in a ring `B`, following Gabriele Dian
(*Geometrical aspects of Amplitudes and Correlators in $\mathcal{N}=4$ SYM*, arXiv:2210.16671, §2.2 & §2.4.2):
1. **15D Conformal Dimension Budget ($\mathfrak{so}(4, 2) \cong \mathfrak{su}(2, 2)$):**
   `4 + 4 + 6 + 1 = 15` (4 translations `TransN P x` + 4 special conformal generators `ConformalK P k`
   + 6 Lorentz generators `LorentzL P M` + 1 dilatation grading `invS P = 2P - 1`).
2. **Endogenous Twistor Incidence Relation ($\omega^a = x^{a \dot{b}} \pi_{\dot{b}}$):**
   - `(1 + TransN P x) * (P * lam + (1 - P) * mu) = P * (lam + x * (1 - P) * mu) + (1 - P) * mu`,
   - `P * ((1 + TransN P x) * ((1 - P) * mu)) = TransN P x * mu`.
3. **Abelian Nilpotent Special Conformal Subalgebra $\mathfrak{n}_- = (1 - P) B P$:**
   - `(1 - P) * ConformalK P k1 * P = ConformalK P k1`,
   - `ConformalK P k1 * ConformalK P k2 = 0`,
   - `comm (ConformalK P k1) (ConformalK P k2) = 0`,
   - `(1 + ConformalK P k1) * (1 + ConformalK P k2) = 1 + ConformalK P (k1 + k2)`.
4. **Conformal Dilatation Weight Grading under $D = S_P = \mathrm{invS}(P)$:**
   - `comm (invS P) (TransN P x) = (2 : ℤ) • TransN P x` (weight $+2$),
   - `comm (invS P) (ConformalK P k1) = -((2 : ℤ) • ConformalK P k1)` (weight $-2$),
   - `comm (invS P) (LorentzL P M) = 0` (weight $0$).
5. **Translation–Special Conformal Commutator Closure into the Block-Diagonal Stabilizer:**
   - `comm (TransN P x) (ConformalK P k1) = P * x * (1 - P) * k1 * P - (1 - P) * k1 * P * x * (1 - P)`,
   - `LorentzL P (comm (TransN P x) (ConformalK P k1)) = comm (TransN P x) (ConformalK P k1)`,
   - `comm (invS P) (comm (TransN P x) (ConformalK P k1)) = 0`.
-/
theorem tetractys_twistor_incidence_and_conformal_so42_grading
    (P x k1 k2 lam mu M : B) (hP : P * P = P) :
    4 + 4 + 6 + 1 = 15 ∧
    (1 + TransN P x) * (P * lam + (1 - P) * mu) =
      P * (lam + x * (1 - P) * mu) + (1 - P) * mu ∧
    P * ((1 + TransN P x) * ((1 - P) * mu)) = TransN P x * mu ∧
    (1 - P) * ConformalK P k1 * P = ConformalK P k1 ∧
    ConformalK P k1 * ConformalK P k2 = 0 ∧
    comm (ConformalK P k1) (ConformalK P k2) = 0 ∧
    (1 + ConformalK P k1) * (1 + ConformalK P k2) = 1 + ConformalK P (k1 + k2) ∧
    comm (invS P) (TransN P x) = (2 : ℤ) • TransN P x ∧
    comm (invS P) (ConformalK P k1) = -((2 : ℤ) • ConformalK P k1) ∧
    comm (invS P) (LorentzL P M) = 0 ∧
    comm (TransN P x) (ConformalK P k1) =
      P * x * (1 - P) * k1 * P - (1 - P) * k1 * P * x * (1 - P) ∧
    LorentzL P (comm (TransN P x) (ConformalK P k1)) =
      comm (TransN P x) (ConformalK P k1) ∧
    comm (invS P) (comm (TransN P x) (ConformalK P k1)) = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [TransN]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · dsimp only [TransN]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · dsimp only [ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp only [ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_assoc, proj_idem hP]
    abel
  · dsimp only [comm, ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_assoc, proj_idem hP]
    abel
  · dsimp only [ConformalK]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · rw [two_zsmul]
    dsimp only [comm, invS, TransN]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel
  · rw [two_zsmul]
    dsimp only [comm, invS, ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp only [comm, invS, LorentzL]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp only [comm, TransN, ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · dsimp only [LorentzL, comm, TransN, ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel
  · dsimp only [comm, invS, TransN, ConformalK]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, proj_idem hP]
    abel

/--
**Theorem 5 (`super_grassmannian_analytic_superspace_nilpotent_stratification`):**
For any spacetime Peirce idempotent `P * P = P` and internal $R$-symmetry / Bose–Fermi idempotent
`E * E = E` in `[Ring B]` (modeling the $\mathrm{Gr}(2|2, 4|4)$ analytic superspace Poincaré patch of
Gabriele Dian, arXiv:2210.16671, §2.2.1–§2.3):
1. **Four-Sector Resolution of the Upper Peirce Corner:**
   Every upper-corner element `TransN P Z = P * Z * (1 - P)` decomposes into the bosonic spacetime
   block `superAnalyticX P E Z`, the internal $R$-symmetry bosonic block `superAnalyticY P E Z`,
   and the chiral/antichiral odd Grassmann blocks `superAnalyticTheta P E Z` and `superAnalyticThetaBar P E Z`.
2. **Upper-Corner Membership, Mutual Nilpotency, and Unipotent Super-Translation Group Law:**
   - `P * superAnalyticCorner P E x1 y1 th1 thb1 * (1 - P) = superAnalyticCorner P E x1 y1 th1 thb1`,
   - `superAnalyticCorner P E x1 y1 th1 thb1 * superAnalyticCorner P E x2 y2 th2 thb2 = 0`,
   - `(1 + superAnalyticCorner P E x1 y1 th1 thb1) * (1 + superAnalyticCorner P E x2 y2 th2 thb2) = 1 + superAnalyticCorner P E (x1 + x2) (y1 + y2) (th1 + th2) (thb1 + thb2)`.
3. **Internal Chiral/Antichiral Grassmann Nilpotency & Bosonic Anticommutator Closure:**
   - `(E * th1 * (1 - E)) * (E * th2 * (1 - E)) = 0` (chiral Grassmann products truncate at order 1),
   - `((1 - E) * thb1 * E) * ((1 - E) * thb2 * E) = 0` (antichiral Grassmann products truncate at order 1),
   - `anticomm (E * th1 * (1 - E)) ((1 - E) * thb1 * E) = E * th1 * (1 - E) * thb1 * E + (1 - E) * thb1 * E * th1 * (1 - E)`.
-/
theorem super_grassmannian_analytic_superspace_nilpotent_stratification
    (P E Z x1 y1 th1 thb1 x2 y2 th2 thb2 : B)
    (hP : P * P = P) (hE : E * E = E) :
    TransN P Z = superAnalyticCorner P E Z Z Z Z ∧
    P * superAnalyticCorner P E x1 y1 th1 thb1 * (1 - P) =
      superAnalyticCorner P E x1 y1 th1 thb1 ∧
    superAnalyticCorner P E x1 y1 th1 thb1 *
      superAnalyticCorner P E x2 y2 th2 thb2 = 0 ∧
    (1 + superAnalyticCorner P E x1 y1 th1 thb1) *
      (1 + superAnalyticCorner P E x2 y2 th2 thb2) =
      1 + superAnalyticCorner P E (x1 + x2) (y1 + y2) (th1 + th2) (thb1 + thb2) ∧
    (E * th1 * (1 - E)) * (E * th2 * (1 - E)) = 0 ∧
    ((1 - E) * thb1 * E) * ((1 - E) * thb2 * E) = 0 ∧
    anticomm (E * th1 * (1 - E)) ((1 - E) * thb1 * E) =
      E * th1 * (1 - E) * thb1 * E + (1 - E) * thb1 * E * th1 * (1 - E) := by
  have hFold : ∀ x y th thb : B,
      superAnalyticCorner P E x y th thb =
        TransN P (E * x * E + (1 - E) * y * (1 - E) +
          E * th * (1 - E) + (1 - E) * thb * E) := by
    intro x y th thb
    dsimp only [superAnalyticCorner, superAnalyticX, superAnalyticY,
      superAnalyticTheta, superAnalyticThetaBar, TransN]
    simp only [add_mul, mul_add, mul_assoc]
  have hAdd :
      superAnalyticCorner P E (x1 + x2) (y1 + y2) (th1 + th2) (thb1 + thb2) =
        superAnalyticCorner P E x1 y1 th1 thb1 +
        superAnalyticCorner P E x2 y2 th2 thb2 := by
    dsimp only [superAnalyticCorner, superAnalyticX, superAnalyticY,
      superAnalyticTheta, superAnalyticThetaBar]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  have hPoinc1 :=
    poincare_translations_commute_and_lorentz_covariance P 0
      (E * x1 * E + (1 - E) * y1 * (1 - E) + E * th1 * (1 - E) + (1 - E) * thb1 * E)
      (E * x2 * E + (1 - E) * y2 * (1 - E) + E * th2 * (1 - E) + (1 - E) * thb2 * E)
      0 0 0 0 hP (by simp)
  have hMul :
      superAnalyticCorner P E x1 y1 th1 thb1 *
        superAnalyticCorner P E x2 y2 th2 thb2 = 0 := by
    rw [hFold x1 y1 th1 thb1, hFold x2 y2 th2 thb2]
    exact hPoinc1.2.2.1
  refine ⟨?_, ?_, hMul, ?_, ?_, ?_, ?_⟩
  · dsimp only [TransN, superAnalyticCorner, superAnalyticX, superAnalyticY,
      superAnalyticTheta, superAnalyticThetaBar]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
    abel
  · rw [hFold x1 y1 th1 thb1]
    exact hPoinc1.2.1
  · rw [hAdd]
    calc
      (1 + superAnalyticCorner P E x1 y1 th1 thb1) *
          (1 + superAnalyticCorner P E x2 y2 th2 thb2)
        = 1 + (superAnalyticCorner P E x1 y1 th1 thb1 +
            superAnalyticCorner P E x2 y2 th2 thb2) +
            superAnalyticCorner P E x1 y1 th1 thb1 *
              superAnalyticCorner P E x2 y2 th2 thb2 := by
          simp only [add_mul, mul_add, one_mul, mul_one]; abel
      _ = 1 + (superAnalyticCorner P E x1 y1 th1 thb1 +
            superAnalyticCorner P E x2 y2 th2 thb2) := by
          rw [hMul, add_zero]
  · simp only [sub_mul, mul_sub, mul_one, mul_assoc, proj_idem hE]
    abel
  · simp only [sub_mul, mul_sub, one_mul, mul_assoc, proj_idem hE]
    abel
  · dsimp only [anticomm]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hE]
    abel

end ConformalTwistorAndSuperGrassmannian

end InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset
