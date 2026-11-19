/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset

/-!
# Parabolic Jordan Trichotomy, Krein–Mannheim $V$-Metric & Noncommutative QGT Extensions

Extends `InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset` with five
division-free and non-commutative pillars grounded in the primary operator algebra:

1. **Krein–Mannheim $V$-Metric (`krein_reciprocalTotality_mannheim_V_metric`,
   `mat2Z_krein_ghost_to_mannheim_V_posdef_witness`)**: Over any `[Ring E] [StarRing E]` with
   `P^2 = P`, `Ω^2 = Ω`, `star η = η`, and `η * Ω = star Ω * η`, defining
   `V := η * reciprocalTotality Ω` gives `V = η * Σ₀ + η * B`, `star V = V`, `V * J_Ω = η`,
   `J_Ω^* η J_Ω = η`, `V * Ω = Ω^* * V`, and `J_Ω^* V J_Ω = V`. On `(P₀, Ω₀)` in `M₂(ℤ)`, the
   diagonal cut metric `η₀ = !![2, 0; 0, -1]` has negative ghost mode `e₂ᵀ η₀ e₂ = -1`, while
   `V₀ = η₀ * J_{Ω₀} = !![6, 4; 4, 3]` satisfies `xᵀ V₀ x = (2 x₀ + x₁)² + 2 (x₀ + x₁)² > 0`.
2. **Parabolic Jordan Null-Horizon & Three-Regime Trichotomy
   (`parabolic_jordan_null_horizon_witness`, `solve_et_coagula_three_regime_trichotomy`)**:
   On `Ω_par = !![1, 1; 0, 0]`, `X₀ = 0`, `A₀ = 0`, `M₀ = 0`, yet `B = !![0, 2; 0, 0] ≠ 0` and
   `[P₀, J_{Ω_par}] = !![0, 2; 0, 0] ≠ 0`. Paired over `ℚ` with elliptic (`Ω = !![1/2, 1/2;
   1/2, 1/2]`) and hyperbolic (`Ω = !![2, 1; -2, -1]`) witnesses, separates the three regimes.
3. **Krein Exceptional Point `EP2` (`krein_null_cone_jordan_exceptional_point_witness`)**:
   On `η = !![0, 1; 1, 0]` (`det = -1`), any Jordan block `!![lam, 1; 0, lam]` is
   `η`-self-adjoint while its eigenvector `![1, 0]` is `η`-null.
4. **Symmetrically Split Midpoint Frame Transport & Noncommutative QGT
   (`symSplitMidpoint_intertwining_and_norm`, `leibniz_idempotent_offDiagonal_and_noncommQGT`)**:
   For involutions `Γ₁² = Γ₂² = 1`, `(1 + Γ₂ Γ₁) Γ₁ = Γ₂ (1 + Γ₂ Γ₁)`; for Leibniz idempotent
   deformations, diagonal sectors vanish and the inner QGT reproduces `-socraticAporia P Ω`.
5. **Keldysh Glide-Reflection, Centered Strip $V_4$ & Apollonian Radical Bisector, & Poset
   Branching (`keldysh_klein_bottle_glide_law`, `centered_strip_V4_and_apollonian_radical_bisector`,
   `coagula_parallel_branching_and_chains`)**.

No `sorry`, `admit`, custom axioms, or `native_decide` are used.
-/

namespace InfoGeometry.OperatorAlgebra.ParabolicJordanTrichotomyAndMannheimVMetric

open Matrix
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset

/-! ### Section 1: Division-Free Krein–Mannheim $V$-Metric & $M_2(\mathbb{Z})$ Witness -/

section KreinMannheimVMetric

variable {E : Type*} [Ring E]

/-- Mannheim's intertwined inner-product metric `V := η * J_Ω = η * (2 Ω - 1)`. -/
def mannheimVMetric (η Ω : E) : E :=
  η * reciprocalTotality Ω

private lemma star_two_mul_sub_one [StarRing E] (Ω : E) :
    star ((2 : E) * Ω - 1) = (2 : E) * star Ω - 1 := by
  rw [two_mul, two_mul, star_sub, star_add, star_one]

/-- **Division-Free Krein–Mannheim $V$-Metric Theorem**:
Over any unital `[Ring E] [StarRing E]` with `P^2 = P`, `Ω^2 = Ω`, `star η = η`, and Krein
intertwining `η * Ω = star Ω * η`, the metric `V := η * reciprocalTotality Ω` decomposes across
`Σ₀ + B`, is `star`-Hermitian, makes `Ω` and `J_Ω` `V`-self-adjoint, and renders `J_Ω` both
`η`-pseudo-unitary and `V`-unitary. -/
theorem krein_reciprocalTotality_mannheim_V_metric [StarRing E]
    {P Ω η : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω)
    (hη : star η = η) (hηΩ : η * Ω = star Ω * η) :
    (mannheimVMetric η Ω = η * dogmaticTruncation P Ω + η * doubledBridge P Ω ∧
      η * (dogmaticTruncation P Ω * doubledBridge P Ω +
        doubledBridge P Ω * dogmaticTruncation P Ω) = 0) ∧
    star (mannheimVMetric η Ω) = mannheimVMetric η Ω ∧
    (mannheimVMetric η Ω * reciprocalTotality Ω = η ∧
      star (reciprocalTotality Ω) * mannheimVMetric η Ω = η) ∧
    star (reciprocalTotality Ω) * η * reciprocalTotality Ω = η ∧
    (mannheimVMetric η Ω * Ω = star Ω * mannheimVMetric η Ω ∧
      mannheimVMetric η Ω * reciprocalTotality Ω =
        star (reciprocalTotality Ω) * mannheimVMetric η Ω) ∧
    star (reciprocalTotality Ω) * mannheimVMetric η Ω * reciprocalTotality Ω =
      mannheimVMetric η Ω := by
  have h5 := prop5_incompleteness_of_dogmatic_truncation hP hΩ
  have hOm := thm_omega_indefinite_reciprocal_totality hP hΩ
  have hSplit :
      mannheimVMetric η Ω = η * dogmaticTruncation P Ω + η * doubledBridge P Ω := by
    rw [mannheimVMetric, ← hOm.1, mul_add]
  have hAntiZero :
      η * (dogmaticTruncation P Ω * doubledBridge P Ω +
        doubledBridge P Ω * dogmaticTruncation P Ω) = 0 := by
    rw [h5.1, mul_zero]
  have hηJ : η * reciprocalTotality Ω = star (reciprocalTotality Ω) * η := by
    unfold reciprocalTotality
    rw [star_two_mul_sub_one]
    calc
      η * ((2 : E) * Ω - 1) = (2 : E) * (η * Ω) - η := by noncomm_ring
      _ = (2 : E) * (star Ω * η) - η := by rw [hηΩ]
      _ = ((2 : E) * star Ω - 1) * η := by noncomm_ring
  have hVstar : star (mannheimVMetric η Ω) = mannheimVMetric η Ω := by
    calc
      star (mannheimVMetric η Ω)
          = star (reciprocalTotality Ω) * star η := by rw [mannheimVMetric, star_mul]
      _ = star (reciprocalTotality Ω) * η := by rw [hη]
      _ = η * reciprocalTotality Ω := hηJ.symm
      _ = mannheimVMetric η Ω := rfl
  have hVJ : mannheimVMetric η Ω * reciprocalTotality Ω = η := by
    calc
      mannheimVMetric η Ω * reciprocalTotality Ω
          = η * (reciprocalTotality Ω * reciprocalTotality Ω) := by rw [mannheimVMetric, mul_assoc]
      _ = η * 1 := by rw [hOm.2.1]
      _ = η := mul_one η
  have hJstarV : star (reciprocalTotality Ω) * mannheimVMetric η Ω = η := by
    calc
      star (reciprocalTotality Ω) * mannheimVMetric η Ω
          = (star (reciprocalTotality Ω) * η) * reciprocalTotality Ω := by
              rw [mannheimVMetric, ← mul_assoc]
      _ = (η * reciprocalTotality Ω) * reciprocalTotality Ω := by rw [← hηJ]
      _ = η := by rw [mul_assoc, hOm.2.1, mul_one]
  have hPseudoUnit : star (reciprocalTotality Ω) * η * reciprocalTotality Ω = η := by
    calc
      star (reciprocalTotality Ω) * η * reciprocalTotality Ω
          = (η * reciprocalTotality Ω) * reciprocalTotality Ω := by rw [← hηJ]
      _ = η := by rw [mul_assoc, hOm.2.1, mul_one]
  have hJΩ : reciprocalTotality Ω * Ω = Ω := by
    unfold reciprocalTotality
    calc
      ((2 : E) * Ω - 1) * Ω = (2 : E) * (Ω * Ω) - Ω := by noncomm_ring
      _ = (2 : E) * Ω - Ω := by rw [hΩ]
      _ = Ω := by rw [two_mul]; noncomm_ring
  have hVOmega : mannheimVMetric η Ω * Ω = star Ω * mannheimVMetric η Ω := by
    have hlhs : mannheimVMetric η Ω * Ω = η * Ω := by
      rw [mannheimVMetric, mul_assoc, hJΩ]
    have hrhs : star Ω * mannheimVMetric η Ω = η * Ω := by
      unfold mannheimVMetric reciprocalTotality
      calc
        star Ω * (η * ((2 : E) * Ω - 1))
            = (2 : E) * ((star Ω * η) * Ω) - star Ω * η := by noncomm_ring
        _ = (2 : E) * ((η * Ω) * Ω) - η * Ω := by rw [hηΩ]
        _ = (2 : E) * (η * (Ω * Ω)) - η * Ω := by noncomm_ring
        _ = (2 : E) * (η * Ω) - η * Ω := by rw [hΩ]
        _ = η * Ω := by rw [two_mul]; noncomm_ring
    exact hlhs.trans hrhs.symm
  have hVJ_selfAdj :
      mannheimVMetric η Ω * reciprocalTotality Ω =
        star (reciprocalTotality Ω) * mannheimVMetric η Ω :=
    hVJ.trans hJstarV.symm
  have hVUnit :
      star (reciprocalTotality Ω) * mannheimVMetric η Ω * reciprocalTotality Ω =
        mannheimVMetric η Ω := by
    rw [hJstarV, mannheimVMetric]
  exact ⟨⟨hSplit, hAntiZero⟩, hVstar, ⟨hVJ, hJstarV⟩, hPseudoUnit, ⟨hVOmega, hVJ_selfAdj⟩, hVUnit⟩

end KreinMannheimVMetric

section ConcreteMat2ZKreinWitness

/-- Explicit T16 non-commutativity guard on `Matrix (Fin 2) (Fin 2) ℤ`. -/
theorem trichotomy_mat2Z_noncomm_guard :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  mat2Z_noncomm_witness

/-- Explicit T16 non-commutativity guard on `Matrix (Fin 2) (Fin 2) ℚ`. -/
theorem trichotomy_mat2Q_noncomm_guard :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℚ, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![(1 : ℚ), 0; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℚ := !![(2 : ℚ), 1; -2, -1]
  refine ⟨A, B, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Indefinite `(1, 1)` Krein metric `η₀ = !![2, 0; 0, -1]` commuting with `cutP0`. -/
def kreinEta0 : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, -1]

/-- Mannheim's intertwined positive-definite metric `V₀ := η₀ * J_{Ω₀}` on `M₂(ℤ)`. -/
def mannheimV0 : Matrix (Fin 2) (Fin 2) ℤ :=
  mannheimVMetric kreinEta0 totalityOmega0

private lemma mat2Z_star_eq_transpose (M : Matrix (Fin 2) (Fin 2) ℤ) :
    star M = M.transpose := by
  ext i j
  rfl

/-- **Division-Free Ghost-to-Positive-$V$-Norm Witness in `M₂(ℤ)`**:
Shows that `η₀ = !![2, 0; 0, -1]` commutes with `P₀`, intertwines `Ω₀`, has indefinite
signature (`det η₀ = -2`, `e₂ᵀ η₀ e₂ = -1`), and lifts via `V₀ = η₀ J_{Ω₀} = !![6, 4; 4, 3]` to a
strictly positive-definite integer quadratic form `(2 x + y)² + 2 (x + y)²`. -/
theorem mat2Z_krein_ghost_to_mannheim_V_posdef_witness :
    (PeirceSpine.comm cutP0 kreinEta0 = 0 ∧
      kreinEta0.transpose = kreinEta0 ∧
      kreinEta0.det = -2 ∧
      dotProduct ![1, 0] (kreinEta0 *ᵥ ![1, 0]) = 2 ∧
      dotProduct ![0, 1] (kreinEta0 *ᵥ ![0, 1]) = -1 ∧
      socraticAporia cutP0 totalityOmega0 = !![-2, 0; 0, 0]) ∧
    (kreinEta0 * totalityOmega0 = totalityOmega0.transpose * kreinEta0 ∧
      kreinEta0 * totalityOmega0 = !![4, 2; 2, 1] ∧
      (reciprocalTotality totalityOmega0).transpose * kreinEta0 *
        reciprocalTotality totalityOmega0 = kreinEta0) ∧
    (mannheimV0 = !![6, 4; 4, 3] ∧
      mannheimV0.transpose = mannheimV0 ∧
      mannheimV0.det = 2) ∧
    (∀ x y : ℤ,
      dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y]) =
        (2 * x + y) ^ 2 + 2 * (x + y) ^ 2) ∧
    (∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) →
      0 < dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y])) := by
  have hcomm : PeirceSpine.comm cutP0 kreinEta0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PeirceSpine.comm, cutP0, kreinEta0, Matrix.mul_apply, Fin.sum_univ_two]
  have hetaT : kreinEta0.transpose = kreinEta0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [kreinEta0]
  have hetaDet : kreinEta0.det = -2 := by
    rw [Matrix.det_fin_two]
    norm_num [kreinEta0]
  have heta_pos : dotProduct ![1, 0] (kreinEta0 *ᵥ ![1, 0]) = 2 := by
    norm_num [kreinEta0, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  have heta_neg : dotProduct ![0, 1] (kreinEta0 *ᵥ ![0, 1]) = -1 := by
    norm_num [kreinEta0, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  have hap : socraticAporia cutP0 totalityOmega0 = !![-2, 0; 0, 0] :=
    concrete_mat2Z_indefinite_reciprocal_totality_witness.2.2.2.1
  have hηΩ_val : kreinEta0 * totalityOmega0 = !![4, 2; 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinEta0, totalityOmega0, Matrix.mul_apply, Fin.sum_univ_two]
  have hΩTη_val : totalityOmega0.transpose * kreinEta0 = !![4, 2; 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinEta0, totalityOmega0, Matrix.mul_apply, Fin.sum_univ_two]
  have hηΩ_transp : kreinEta0 * totalityOmega0 = totalityOmega0.transpose * kreinEta0 :=
    hηΩ_val.trans hΩTη_val.symm
  have hηStar : star kreinEta0 = kreinEta0 := by
    rw [mat2Z_star_eq_transpose]
    exact hetaT
  have hηΩ_star : kreinEta0 * totalityOmega0 = star totalityOmega0 * kreinEta0 := by
    rw [mat2Z_star_eq_transpose]
    exact hηΩ_transp
  have hAbs := krein_reciprocalTotality_mannheim_V_metric (E := Matrix (Fin 2) (Fin 2) ℤ)
    cutP0_idem totalityOmega0_idem hηStar hηΩ_star
  have hPseudo :
      (reciprocalTotality totalityOmega0).transpose * kreinEta0 *
        reciprocalTotality totalityOmega0 = kreinEta0 := by
    rw [← mat2Z_star_eq_transpose]
    exact hAbs.2.2.2.1
  have hJval : reciprocalTotality totalityOmega0 = !![3, 2; -4, -3] :=
    concrete_mat2Z_indefinite_reciprocal_totality_witness.2.2.2.2.2.2.2.1
  have hVval : mannheimV0 = !![6, 4; 4, 3] := by
    unfold mannheimV0 mannheimVMetric
    rw [hJval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinEta0, Matrix.mul_apply, Fin.sum_univ_two]
  have hVT : mannheimV0.transpose = mannheimV0 := by
    rw [hVval]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hVdet : mannheimV0.det = 2 := by
    rw [hVval, Matrix.det_fin_two]
    norm_num
  have hSOS : ∀ x y : ℤ,
      dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y]) =
        (2 * x + y) ^ 2 + 2 * (x + y) ^ 2 := by
    intro x y
    rw [hVval]
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hPos : ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) →
      0 < dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y]) := by
    intro x y hne
    rw [hSOS x y]
    have hsq1 : 0 ≤ (2 * x + y) ^ 2 := sq_nonneg (2 * x + y)
    have hsq2 : 0 ≤ (x + y) ^ 2 := sq_nonneg (x + y)
    rcases lt_or_eq_of_le hsq1 with h1pos | h1zero
    · linarith
    · rcases lt_or_eq_of_le hsq2 with h2pos | h2zero
      · linarith
      · exfalso
        have hz1 : 2 * x + y = 0 := sq_eq_zero_iff.mp h1zero.symm
        have hz2 : x + y = 0 := sq_eq_zero_iff.mp h2zero.symm
        have hx0 : x = 0 := by linarith
        have hy0 : y = 0 := by linarith
        rcases hne with hnx | hny
        · exact hnx hx0
        · exact hny hy0
  exact ⟨⟨hcomm, hetaT, hetaDet, heta_pos, heta_neg, hap⟩,
    ⟨hηΩ_transp, hηΩ_val, hPseudo⟩,
    ⟨hVval, hVT, hVdet⟩,
    hSOS, hPos⟩

end ConcreteMat2ZKreinWitness

/-! ### Section 2: Parabolic Jordan Null Horizon, Trichotomy & Krein Exceptional Point -/

section ParabolicAndTrichotomy

/-- Parabolic one-way null-horizon idempotent `Ω_par = !![1, 1; 0, 0]`. -/
def parabolicOmega0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 0]

/-- **Parabolic Jordan Null-Horizon Witness (`M₂(ℤ)`)**:
Demonstrates that `Ω_par = !![1, 1; 0, 0]` has vanishing `X₀ = 0`, stealth-zero aporia
`A₀ = 0 = M₀ = 1 - Σ₀²`, and nilpotent shear `B = !![0, 2; 0, 0] ≠ 0`, `B² = 0`, yet
`[P₀, J_{Ω_par}] = !![0, 2; 0, 0] ≠ 0` and `J_{Ω_par} ≠ Γ₀`. -/
theorem parabolic_jordan_null_horizon_witness :
    parabolicOmega0 * parabolicOmega0 = parabolicOmega0 ∧
    PeirceSpine.comm cutP0 parabolicOmega0 = !![0, 1; 0, 0] ∧
    PeirceSpine.comm cutP0 parabolicOmega0 ≠ 0 ∧
    outwardProj cutP0 parabolicOmega0 = 0 ∧
    inwardIntrusion cutP0 parabolicOmega0 = !![0, 1; 0, 0] ∧
    inwardIntrusion cutP0 parabolicOmega0 ≠ 0 ∧
    socraticAporia cutP0 parabolicOmega0 = 0 ∧
    shadowAporia cutP0 parabolicOmega0 = 0 ∧
    substantiveGravity cutP0 parabolicOmega0 = 0 ∧
    1 - dogmaticTruncation cutP0 parabolicOmega0 *
      dogmaticTruncation cutP0 parabolicOmega0 = 0 ∧
    doubledBridge cutP0 parabolicOmega0 = !![0, 2; 0, 0] ∧
    doubledBridge cutP0 parabolicOmega0 ≠ 0 ∧
    doubledBridge cutP0 parabolicOmega0 * doubledBridge cutP0 parabolicOmega0 = 0 ∧
    reciprocalTotality parabolicOmega0 = !![1, 2; 0, -1] ∧
    reciprocalTotality parabolicOmega0 * reciprocalTotality parabolicOmega0 = 1 ∧
    PeirceSpine.comm cutP0 (reciprocalTotality parabolicOmega0) = !![0, 2; 0, 0] ∧
    PeirceSpine.comm cutP0 (reciprocalTotality parabolicOmega0) ≠ 0 ∧
    reciprocalTotality parabolicOmega0 ≠ polarityGamma cutP0 := by
  have hP0 : cutP0 * cutP0 = cutP0 := cutP0_idem
  have hO : parabolicOmega0 * parabolicOmega0 = parabolicOmega0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [parabolicOmega0, Matrix.mul_apply, Fin.sum_univ_two]
  have hOm := thm_omega_indefinite_reciprocal_totality hP0 hO
  have h5 := prop5_incompleteness_of_dogmatic_truncation hP0 hO
  have h4 := prop4_exact_socratic_aporia hP0 hO
  have hComm : PeirceSpine.comm cutP0 parabolicOmega0 = !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PeirceSpine.comm, cutP0, parabolicOmega0, Matrix.mul_apply, Fin.sum_univ_two]
  have hCommNe : PeirceSpine.comm cutP0 parabolicOmega0 ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [hComm] at h01
    norm_num at h01
  have hX0 : outwardProj cutP0 parabolicOmega0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [outwardProj, shadowQ, cutP0, parabolicOmega0, Matrix.mul_apply, Fin.sum_univ_two]
  have hY0 : inwardIntrusion cutP0 parabolicOmega0 = !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inwardIntrusion, shadowQ, cutP0, parabolicOmega0,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hYNe : inwardIntrusion cutP0 parabolicOmega0 ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [hY0] at h01
    norm_num at h01
  have hA0 : socraticAporia cutP0 parabolicOmega0 = 0 := by
    rw [h4.1, hX0, mul_zero]
  have hG0 : shadowAporia cutP0 parabolicOmega0 = 0 := by
    rw [h4.2.1, hX0, zero_mul]
  have hM0 : substantiveGravity cutP0 parabolicOmega0 = 0 := by
    rw [← h4.2.2.1, hA0, hG0, add_zero]
  have hDef :
      1 - dogmaticTruncation cutP0 parabolicOmega0 *
        dogmaticTruncation cutP0 parabolicOmega0 = 0 := by
    rw [h5.2.2.2, hM0, mul_zero]
  have hBval : doubledBridge cutP0 parabolicOmega0 = !![0, 2; 0, 0] := by
    unfold doubledBridge integrativeBridge
    rw [hX0, hY0, zero_add, two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hBne : doubledBridge cutP0 parabolicOmega0 ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [hBval] at h01
    norm_num at h01
  have hB2 : doubledBridge cutP0 parabolicOmega0 * doubledBridge cutP0 parabolicOmega0 = 0 := by
    rw [h5.2.1, hM0, mul_zero]
  have hJval : reciprocalTotality parabolicOmega0 = !![1, 2; 0, -1] := by
    unfold reciprocalTotality
    rw [two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [parabolicOmega0]
  have hCommJ : PeirceSpine.comm cutP0 (reciprocalTotality parabolicOmega0) = !![0, 2; 0, 0] := by
    rw [hOm.2.2.1, hComm, two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hTors : ∀ Z : Matrix (Fin 2) (Fin 2) ℤ, 2 * Z = 0 → Z = 0 := by
    intro Z h2
    ext i j
    change Z i j = 0
    rw [two_mul] at h2
    have hij : Z i j + Z i j = 0 := by
      have h := congrFun (congrFun h2 i) j
      simpa using h
    omega
  have hIrred := hOm.2.2.2.1 hTors hCommNe
  exact ⟨hO, hComm, hCommNe, hX0, hY0, hYNe, hA0, hG0, hM0, hDef,
    hBval, hBne, hB2, hJval, hOm.2.1, hCommJ, hIrred.1, hIrred.2⟩

/-- Rational conscious cut `P₀ ∈ M₂(ℚ)`. -/
def cutPQ : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]

/-- Elliptic maximal-superposition totality `Ω_ell ∈ M₂(ℚ)`. -/
def ellipticOmegaQ : Matrix (Fin 2) (Fin 2) ℚ := !![(1 / 2 : ℚ), 1 / 2; 1 / 2, 1 / 2]

/-- Parabolic Jordan null-horizon totality `Ω_par ∈ M₂(ℚ)`. -/
def parabolicOmegaQ : Matrix (Fin 2) (Fin 2) ℚ := !![(1 : ℚ), 1; 0, 0]

/-- Hyperbolic Krein squeezed totality `Ω_hyp ∈ M₂(ℚ)`. -/
def hyperbolicOmegaQ : Matrix (Fin 2) (Fin 2) ℚ := !![(2 : ℚ), 1; -2, -1]

/-- **Three-Regime `SOLVE ET COAGULA` Trichotomy Over `M₂(ℚ)`**:
Separates all three algebraic/spectral regimes sharing `P₀ = diag(1, 0)`:
1. **Elliptic (`M > 0`)**: `A₀(0,0) = 1/4 > 0`, `B² = I₂`, `Σ₀ = 0`;
2. **Parabolic (`M = 0 ∧ B ≠ 0`)**: `A₀ = 0`, `B² = 0`, `B ≠ 0`, `J_{Ω_par} ≠ Γ₀`;
3. **Hyperbolic (`M < 0`)**: `A₀(0,0) = -2 < 0`, `B² = -8 • I₂`, `J_{Ω_hyp} ≠ Γ₀`. -/
theorem solve_et_coagula_three_regime_trichotomy :
    (cutPQ * cutPQ = cutPQ ∧
      ellipticOmegaQ * ellipticOmegaQ = ellipticOmegaQ ∧
      socraticAporia cutPQ ellipticOmegaQ 0 0 = (1 / 4 : ℚ) ∧
      0 < socraticAporia cutPQ ellipticOmegaQ 0 0 ∧
      doubledBridge cutPQ ellipticOmegaQ * doubledBridge cutPQ ellipticOmegaQ = 1 ∧
      dogmaticTruncation cutPQ ellipticOmegaQ = 0 ∧
      reciprocalTotality ellipticOmegaQ = !![(0 : ℚ), 1; 1, 0]) ∧
    (parabolicOmegaQ * parabolicOmegaQ = parabolicOmegaQ ∧
      socraticAporia cutPQ parabolicOmegaQ = 0 ∧
      doubledBridge cutPQ parabolicOmegaQ * doubledBridge cutPQ parabolicOmegaQ = 0 ∧
      doubledBridge cutPQ parabolicOmegaQ ≠ 0 ∧
      reciprocalTotality parabolicOmegaQ ≠ polarityGamma cutPQ) ∧
    (hyperbolicOmegaQ * hyperbolicOmegaQ = hyperbolicOmegaQ ∧
      socraticAporia cutPQ hyperbolicOmegaQ 0 0 = (-2 : ℚ) ∧
      socraticAporia cutPQ hyperbolicOmegaQ 0 0 < 0 ∧
      doubledBridge cutPQ hyperbolicOmegaQ * doubledBridge cutPQ hyperbolicOmegaQ =
        (-8 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) ∧
      reciprocalTotality hyperbolicOmegaQ ≠ polarityGamma cutPQ) := by
  have hPQ : cutPQ * cutPQ = cutPQ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cutPQ, Matrix.mul_apply, Fin.sum_univ_two]
  have hEll : ellipticOmegaQ * ellipticOmegaQ = ellipticOmegaQ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ellipticOmegaQ, Matrix.mul_apply, Fin.sum_univ_two]
  have hPar : parabolicOmegaQ * parabolicOmegaQ = parabolicOmegaQ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [parabolicOmegaQ, Matrix.mul_apply, Fin.sum_univ_two]
  have hHyp : hyperbolicOmegaQ * hyperbolicOmegaQ = hyperbolicOmegaQ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hyperbolicOmegaQ, Matrix.mul_apply, Fin.sum_univ_two]
  have hEllA : socraticAporia cutPQ ellipticOmegaQ 0 0 = (1 / 4 : ℚ) := by
    norm_num [socraticAporia, consciousThesis, cutPQ, ellipticOmegaQ,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hQQ : shadowQ cutPQ = !![(0 : ℚ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [shadowQ, cutPQ]
  have hEllB : doubledBridge cutPQ ellipticOmegaQ = !![(0 : ℚ), 1; 1, 0] := by
    unfold doubledBridge integrativeBridge outwardProj inwardIntrusion
    rw [hQQ, two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cutPQ, ellipticOmegaQ, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hEllB2 : doubledBridge cutPQ ellipticOmegaQ * doubledBridge cutPQ ellipticOmegaQ = 1 := by
    rw [hEllB]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hEllSig : dogmaticTruncation cutPQ ellipticOmegaQ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dogmaticTruncation, consciousThesis, autonomousGround, shadowQ,
        cutPQ, ellipticOmegaQ, two_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hEllJ : reciprocalTotality ellipticOmegaQ = !![(0 : ℚ), 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [reciprocalTotality, ellipticOmegaQ, two_mul]
  have hParA : socraticAporia cutPQ parabolicOmegaQ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [socraticAporia, consciousThesis, cutPQ, parabolicOmegaQ,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hParB : doubledBridge cutPQ parabolicOmegaQ = !![(0 : ℚ), 2; 0, 0] := by
    unfold doubledBridge integrativeBridge outwardProj inwardIntrusion
    rw [hQQ, two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cutPQ, parabolicOmegaQ, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hParB2 : doubledBridge cutPQ parabolicOmegaQ * doubledBridge cutPQ parabolicOmegaQ = 0 := by
    rw [hParB]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hParBne : doubledBridge cutPQ parabolicOmegaQ ≠ 0 := by
    intro h
    rw [hParB] at h
    have h01 : (!![(0 : ℚ), 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) 0 1 =
        (0 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by rw [h]
    norm_num at h01
  have hParJne : reciprocalTotality parabolicOmegaQ ≠ polarityGamma cutPQ := by
    intro h
    have h01 : (reciprocalTotality parabolicOmegaQ) 0 1 = (polarityGamma cutPQ) 0 1 := by rw [h]
    norm_num [reciprocalTotality, polarityGamma, shadowQ, cutPQ, parabolicOmegaQ, two_mul] at h01
  have hHypA : socraticAporia cutPQ hyperbolicOmegaQ 0 0 = (-2 : ℚ) := by
    norm_num [socraticAporia, consciousThesis, cutPQ, hyperbolicOmegaQ,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hHypB : doubledBridge cutPQ hyperbolicOmegaQ = !![(0 : ℚ), 2; -4, 0] := by
    unfold doubledBridge integrativeBridge outwardProj inwardIntrusion
    rw [hQQ, two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cutPQ, hyperbolicOmegaQ, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hHypB2 :
      doubledBridge cutPQ hyperbolicOmegaQ * doubledBridge cutPQ hyperbolicOmegaQ =
        (-8 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [hHypB]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hHypJne : reciprocalTotality hyperbolicOmegaQ ≠ polarityGamma cutPQ := by
    intro h
    have h01 : (reciprocalTotality hyperbolicOmegaQ) 0 1 = (polarityGamma cutPQ) 0 1 := by rw [h]
    norm_num [reciprocalTotality, polarityGamma, shadowQ, cutPQ, hyperbolicOmegaQ, two_mul] at h01
  exact ⟨⟨hPQ, hEll, hEllA, by linarith, hEllB2, hEllSig, hEllJ⟩,
    ⟨hPar, hParA, hParB2, hParBne, hParJne⟩,
    ⟨hHyp, hHypA, by linarith, hHypB2, hHypJne⟩⟩

/-- Off-diagonal hyperbolic Krein metric `η_null = !![0, 1; 1, 0]` (`det = -1`). -/
def kreinNullEta : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- Non-diagonalizable upper-triangular `2 × 2` Jordan block `!![lam, 1; 0, lam]`. -/
def jordanBlock2Z (lam : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![lam, 1; 0, lam]

/-- **Krein Exceptional Point (`EP2`) Null-Cone Self-Adjointness Witness**:
With `η_null = !![0, 1; 1, 0]`, every Jordan block `J_lam = !![lam, 1; 0, lam]` is
`η_null`-self-adjoint (`η_null * J_lam = J_lamᵀ * η_null`), while its unique eigenvector
`v₀ = ![1, 0]` lies strictly on the `η_null`-null lightcone (`v₀ᵀ η_null v₀ = 0`). -/
theorem krein_null_cone_jordan_exceptional_point_witness (lam : ℤ) :
    kreinNullEta.transpose = kreinNullEta ∧
    kreinNullEta.det = -1 ∧
    kreinNullEta * kreinNullEta = 1 ∧
    kreinNullEta * jordanBlock2Z lam = (jordanBlock2Z lam).transpose * kreinNullEta ∧
    jordanBlock2Z lam *ᵥ ![1, 0] = ![lam, 0] ∧
    dotProduct ![1, 0] (kreinNullEta *ᵥ ![1, 0]) = 0 := by
  have hT : kreinNullEta.transpose = kreinNullEta := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [kreinNullEta]
  have hDet : kreinNullEta.det = -1 := by
    rw [Matrix.det_fin_two]
    norm_num [kreinNullEta]
  have hSq : kreinNullEta * kreinNullEta = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinNullEta, Matrix.mul_apply, Fin.sum_univ_two]
  have hSA : kreinNullEta * jordanBlock2Z lam = (jordanBlock2Z lam).transpose * kreinNullEta := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinNullEta, jordanBlock2Z, Matrix.mul_apply, Fin.sum_univ_two]
  have hEig : jordanBlock2Z lam *ᵥ ![1, 0] = ![lam, 0] := by
    ext i
    fin_cases i <;> norm_num [jordanBlock2Z, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hNull : dotProduct ![1, 0] (kreinNullEta *ᵥ ![1, 0]) = 0 := by
    norm_num [kreinNullEta, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  exact ⟨hT, hDet, hSq, hSA, hEig, hNull⟩

end ParabolicAndTrichotomy

/-! ### Section 3: Symmetrically Split Frame Transport & Noncommutative Covariant QGT -/

section FrameTransportAndNoncommQGT

variable {E : Type*} [Ring E]

/-- Unnormalized algebraic midpoint frame intertwiner `1 + Γ₂ * Γ₁` between two involutions. -/
def symSplitMidpointIntertwiner (Γ₁ Γ₂ : E) : E :=
  1 + Γ₂ * Γ₁

/-- **Symmetrically Split Midpoint Transport Intertwining & Normalization Identity**:
In any associative ring, two involutions `Γ₁² = 1` and `Γ₂² = 1` satisfy the exact two-sided
perspective-symmetric intertwining `(1 + Γ₂ Γ₁) Γ₁ = Γ₁ + Γ₂ = Γ₂ (1 + Γ₂ Γ₁)` and
normalization factor `(1 + Γ₂ Γ₁) (1 + Γ₁ Γ₂) = 2 + (Γ₁ Γ₂ + Γ₂ Γ₁)`. -/
theorem symSplitMidpoint_intertwining_and_norm {Γ₁ Γ₂ : E}
    (h1 : Γ₁ * Γ₁ = 1) (h2 : Γ₂ * Γ₂ = 1) :
    symSplitMidpointIntertwiner Γ₁ Γ₂ * Γ₁ = Γ₁ + Γ₂ ∧
    Γ₂ * symSplitMidpointIntertwiner Γ₁ Γ₂ = Γ₁ + Γ₂ ∧
    symSplitMidpointIntertwiner Γ₁ Γ₂ * Γ₁ = Γ₂ * symSplitMidpointIntertwiner Γ₁ Γ₂ ∧
    symSplitMidpointIntertwiner Γ₁ Γ₂ * symSplitMidpointIntertwiner Γ₂ Γ₁ =
      2 + (Γ₁ * Γ₂ + Γ₂ * Γ₁) := by
  have hlhs : symSplitMidpointIntertwiner Γ₁ Γ₂ * Γ₁ = Γ₁ + Γ₂ := by
    unfold symSplitMidpointIntertwiner
    calc
      (1 + Γ₂ * Γ₁) * Γ₁ = Γ₁ + Γ₂ * (Γ₁ * Γ₁) := by noncomm_ring
      _ = Γ₁ + Γ₂ * 1 := by rw [h1]
      _ = Γ₁ + Γ₂ := by rw [mul_one]
  have hrhs : Γ₂ * symSplitMidpointIntertwiner Γ₁ Γ₂ = Γ₁ + Γ₂ := by
    unfold symSplitMidpointIntertwiner
    calc
      Γ₂ * (1 + Γ₂ * Γ₁) = Γ₂ + (Γ₂ * Γ₂) * Γ₁ := by noncomm_ring
      _ = Γ₂ + 1 * Γ₁ := by rw [h2]
      _ = Γ₁ + Γ₂ := by rw [one_mul, add_comm]
  have hnorm :
      symSplitMidpointIntertwiner Γ₁ Γ₂ * symSplitMidpointIntertwiner Γ₂ Γ₁ =
        2 + (Γ₁ * Γ₂ + Γ₂ * Γ₁) := by
    unfold symSplitMidpointIntertwiner
    calc
      (1 + Γ₂ * Γ₁) * (1 + Γ₁ * Γ₂)
          = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + Γ₂ * (Γ₁ * Γ₁) * Γ₂ := by noncomm_ring
      _ = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + Γ₂ * 1 * Γ₂ := by rw [h1]
      _ = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + Γ₂ * Γ₂ := by noncomm_ring
      _ = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + 1 := by rw [h2]
      _ = 2 + (Γ₁ * Γ₂ + Γ₂ * Γ₁) := by
            rw [← one_add_one_eq_two]
            abel
  exact ⟨hlhs, hrhs, hlhs.trans hrhs.symm, hnorm⟩

/-- Noncommutative operator-valued Quantum Geometric Tensor (QGT) pairing
`Q_hat(DP₁, DP₂) := P DP₁ (1 - P) DP₂ P`. -/
def noncommQGTPairing (P DP₁ DP₂ : E) : E :=
  P * DP₁ * shadowQ P * DP₂ * P

/-- **Leibniz Off-Diagonal Criterion & Noncommutative Covariant QGT Theorem**:
1. For any idempotent `P² = P`, `Q_hat(DP₁, DP₂) = (P DP₁ Q) * (Q DP₂ P)`.
2. Any derivation deformation `DP₁` satisfying `DP₁ = DP₁ P + P DP₁` has strictly vanishing
   diagonal blocks `P DP₁ P = 0` and `Q DP₁ Q = 0`.
3. Every inner commutator derivation `DP = [P, Ω]` automatically satisfies `DP = DP P + P DP`,
   has vanishing diagonal blocks, and reproduces negative Socratic aporia
   `Q_hat([P, Ω], [P, Ω]) = -A₀ = -(Y X)` when `Ω² = Ω`. -/
theorem leibniz_idempotent_offDiagonal_and_noncommQGT
    {P DP₁ DP₂ Ω : E} (hP : P * P = P)
    (hLeib : DP₁ = DP₁ * P + P * DP₁) (hΩ : Ω * Ω = Ω) :
    noncommQGTPairing P DP₁ DP₂ = inwardIntrusion P DP₁ * outwardProj P DP₂ ∧
    P * DP₁ * P = 0 ∧
    shadowQ P * DP₁ * shadowQ P = 0 ∧
    (PeirceSpine.comm P Ω = PeirceSpine.comm P Ω * P + P * PeirceSpine.comm P Ω ∧
      P * PeirceSpine.comm P Ω * P = 0 ∧
      shadowQ P * PeirceSpine.comm P Ω * shadowQ P = 0 ∧
      noncommQGTPairing P (PeirceSpine.comm P Ω) (PeirceSpine.comm P Ω) =
        -socraticAporia P Ω) := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have h4 := prop4_exact_socratic_aporia hP hΩ
  have hQ := h1.1
  have hPQ := h1.2.1
  have hQP := h1.2.2.1
  have hFact : noncommQGTPairing P DP₁ DP₂ = inwardIntrusion P DP₁ * outwardProj P DP₂ := by
    unfold noncommQGTPairing inwardIntrusion outwardProj
    calc
      P * DP₁ * shadowQ P * DP₂ * P
          = P * DP₁ * (shadowQ P * shadowQ P) * DP₂ * P := by rw [hQ]
      _ = (P * DP₁ * shadowQ P) * (shadowQ P * DP₂ * P) := by noncomm_ring
  have hDiagP : P * DP₁ * P = 0 := by
    have hEq : P * DP₁ * P = P * DP₁ * P + P * DP₁ * P := by
      calc
        P * DP₁ * P = P * (DP₁ * P + P * DP₁) * P := by nth_rw 1 [hLeib]
        _ = P * DP₁ * (P * P) + (P * P) * DP₁ * P := by noncomm_ring
        _ = P * DP₁ * P + P * DP₁ * P := by rw [hP]
    calc
      P * DP₁ * P = (P * DP₁ * P + P * DP₁ * P) - P * DP₁ * P := by abel
      _ = P * DP₁ * P - P * DP₁ * P := by rw [← hEq]
      _ = 0 := sub_self _
  have hDiagQ : shadowQ P * DP₁ * shadowQ P = 0 := by
    calc
      shadowQ P * DP₁ * shadowQ P
          = shadowQ P * (DP₁ * P + P * DP₁) * shadowQ P := by nth_rw 1 [hLeib]
      _ = shadowQ P * DP₁ * (P * shadowQ P) + (shadowQ P * P) * DP₁ * shadowQ P := by noncomm_ring
      _ = 0 := by rw [hPQ, hQP]; noncomm_ring
  have hInnerLeib :
      PeirceSpine.comm P Ω = PeirceSpine.comm P Ω * P + P * PeirceSpine.comm P Ω := by
    unfold PeirceSpine.comm
    calc
      P * Ω - Ω * P = P * Ω - Ω * (P * P) + (P * P) * Ω - P * Ω := by
        rw [hP]
        noncomm_ring
      _ = (P * Ω - Ω * P) * P + P * (P * Ω - Ω * P) := by noncomm_ring
  have hInnerDiagP : P * PeirceSpine.comm P Ω * P = 0 := by
    unfold PeirceSpine.comm
    calc
      P * (P * Ω - Ω * P) * P = (P * P) * Ω * P - P * Ω * (P * P) := by noncomm_ring
      _ = P * Ω * P - P * Ω * P := by rw [hP]
      _ = 0 := sub_self _
  have hInnerDiagQ : shadowQ P * PeirceSpine.comm P Ω * shadowQ P = 0 := by
    unfold PeirceSpine.comm
    calc
      shadowQ P * (P * Ω - Ω * P) * shadowQ P
          = (shadowQ P * P) * Ω * shadowQ P - shadowQ P * Ω * (P * shadowQ P) := by noncomm_ring
      _ = 0 := by rw [hQP, hPQ]; noncomm_ring
  have hInComm : inwardIntrusion P (PeirceSpine.comm P Ω) = inwardIntrusion P Ω := by
    unfold inwardIntrusion PeirceSpine.comm
    calc
      P * (P * Ω - Ω * P) * shadowQ P
          = (P * P) * Ω * shadowQ P - P * Ω * (P * shadowQ P) := by noncomm_ring
      _ = P * Ω * shadowQ P := by rw [hP, hPQ]; noncomm_ring
  have hOutComm : outwardProj P (PeirceSpine.comm P Ω) = -outwardProj P Ω := by
    unfold outwardProj PeirceSpine.comm
    calc
      shadowQ P * (P * Ω - Ω * P) * P
          = (shadowQ P * P) * Ω * P - shadowQ P * Ω * (P * P) := by noncomm_ring
      _ = -(shadowQ P * Ω * P) := by rw [hQP, hP]; noncomm_ring
  have hQGTInner :
      noncommQGTPairing P (PeirceSpine.comm P Ω) (PeirceSpine.comm P Ω) =
        -socraticAporia P Ω := by
    unfold noncommQGTPairing
    calc
      P * PeirceSpine.comm P Ω * shadowQ P * PeirceSpine.comm P Ω * P
          = P * PeirceSpine.comm P Ω * (shadowQ P * shadowQ P) * PeirceSpine.comm P Ω * P := by
              rw [hQ]
      _ = inwardIntrusion P (PeirceSpine.comm P Ω) * outwardProj P (PeirceSpine.comm P Ω) := by
              unfold inwardIntrusion outwardProj
              noncomm_ring
      _ = inwardIntrusion P Ω * (-outwardProj P Ω) := by rw [hInComm, hOutComm]
      _ = -(inwardIntrusion P Ω * outwardProj P Ω) := mul_neg _ _
      _ = -socraticAporia P Ω := by rw [← h4.1]
  exact ⟨hFact, hDiagP, hDiagQ, ⟨hInnerLeib, hInnerDiagP, hInnerDiagQ, hQGTInner⟩⟩

end FrameTransportAndNoncommQGT

/-! ### Section 4: Keldysh Klein-Bottle Glide, Apollonian Radical Bisector & Poset Branching -/

section KeldyshApollonianAndPoset

/-- Schwinger–Keldysh / KMS Klein-bottle glide-reflection `σ(t, τ) = (-t, τ + β/2)`. -/
def keldyshKleinGlide (β : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (-p.1, p.2 + β / 2)

/-- **Klein-Bottle Glide-Reflection & Fixed-Point-Freeness Theorem**:
Doubling the glide shifts modular time by a full KMS period `β`, while any nonzero inverse
temperature `β ≠ 0` forbids fixed points (`σ p ≠ p`). -/
theorem keldysh_klein_bottle_glide_law (β : ℚ) (p : ℚ × ℚ) :
    keldyshKleinGlide β (keldyshKleinGlide β p) = (p.1, p.2 + β) ∧
    (β ≠ 0 → keldyshKleinGlide β p ≠ p) := by
  refine ⟨?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · simp [keldyshKleinGlide]
    · simp [keldyshKleinGlide]
      ring
  · intro hβ hfix
    have h2 : p.2 + β / 2 = p.2 := congrArg Prod.snd hfix
    apply hβ
    linarith

/-- Centered strip frequency / time-reversal involution `T(u, t) = (u, -t)`. -/
def stripTimeRev (w : ℚ × ℚ) : ℚ × ℚ := (w.1, -w.2)

/-- Centered strip horizon reflection `P(u, t) = (-u, t)`. -/
def stripHorizonRefl (w : ℚ × ℚ) : ℚ × ℚ := (-w.1, w.2)

/-- Centered strip functional-equation inversion `PT(u, t) = (-u, -t)`. -/
def stripFunctionalEq (w : ℚ × ℚ) : ℚ × ℚ := (-w.1, -w.2)

/-- Right Apollonian dipole pole `P_+ = (1/2, 0)` corresponding to `s = 1`. -/
def apollonianPolePlus : ℚ × ℚ := (1 / 2, 0)

/-- Left Apollonian dipole pole `P_- = (-1/2, 0)` corresponding to `s = 0`. -/
def apollonianPoleMinus : ℚ × ℚ := (-1 / 2, 0)

/-- Planar Euclidean squared distance on `ℚ × ℚ`. -/
def planarDistSq (a b : ℚ × ℚ) : ℚ :=
  (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- **Centered Strip $V_4$ Symmetry & Apollonian Radical Bisector Theorem**:
Verifies the Klein four-group relations on `(T, P, PT)`, antipodal pole swapping, the exact
squared-distance identity `‖w - P_-‖² - ‖w - P_+‖² = 2 u`, and the characterization of the
horizon axis `u = 0` (`Re(s) = 1/2`) as the Apollonian radical bisector
`‖w - P_+‖² = ‖w - P_-‖²`. -/
theorem centered_strip_V4_and_apollonian_radical_bisector (w : ℚ × ℚ) :
    (stripTimeRev (stripTimeRev w) = w ∧
      stripHorizonRefl (stripHorizonRefl w) = w ∧
      stripFunctionalEq (stripFunctionalEq w) = w ∧
      stripHorizonRefl (stripTimeRev w) = stripFunctionalEq w ∧
      stripTimeRev (stripHorizonRefl w) = stripFunctionalEq w) ∧
    (stripHorizonRefl apollonianPolePlus = apollonianPoleMinus ∧
      stripFunctionalEq apollonianPolePlus = apollonianPoleMinus) ∧
    planarDistSq w apollonianPoleMinus - planarDistSq w apollonianPolePlus = 2 * w.1 ∧
    (planarDistSq w apollonianPolePlus = planarDistSq w apollonianPoleMinus ↔ w.1 = 0) ∧
    (stripHorizonRefl w = w ↔ w.1 = 0) := by
  have hTT : stripTimeRev (stripTimeRev w) = w := by ext <;> simp [stripTimeRev]
  have hPP : stripHorizonRefl (stripHorizonRefl w) = w := by ext <;> simp [stripHorizonRefl]
  have hPTPT : stripFunctionalEq (stripFunctionalEq w) = w := by
    ext <;> simp [stripFunctionalEq]
  have hPT : stripHorizonRefl (stripTimeRev w) = stripFunctionalEq w := by
    ext <;> simp [stripHorizonRefl, stripTimeRev, stripFunctionalEq]
  have hTP : stripTimeRev (stripHorizonRefl w) = stripFunctionalEq w := by
    ext <;> simp [stripTimeRev, stripHorizonRefl, stripFunctionalEq]
  have hPole1 : stripHorizonRefl apollonianPolePlus = apollonianPoleMinus := by
    refine Prod.ext ?_ ?_
    · norm_num [stripHorizonRefl, apollonianPolePlus, apollonianPoleMinus]
    · norm_num [stripHorizonRefl, apollonianPolePlus, apollonianPoleMinus]
  have hPole2 : stripFunctionalEq apollonianPolePlus = apollonianPoleMinus := by
    refine Prod.ext ?_ ?_
    · norm_num [stripFunctionalEq, apollonianPolePlus, apollonianPoleMinus]
    · norm_num [stripFunctionalEq, apollonianPolePlus, apollonianPoleMinus]
  have hDist :
      planarDistSq w apollonianPoleMinus - planarDistSq w apollonianPolePlus = 2 * w.1 := by
    unfold planarDistSq apollonianPoleMinus apollonianPolePlus
    ring
  have hBisect :
      planarDistSq w apollonianPolePlus = planarDistSq w apollonianPoleMinus ↔ w.1 = 0 := by
    constructor
    · intro heq
      have hzero : planarDistSq w apollonianPoleMinus - planarDistSq w apollonianPolePlus = 0 :=
        sub_eq_zero.mpr heq.symm
      rw [hDist] at hzero
      linarith
    · intro hw0
      have hzero : planarDistSq w apollonianPoleMinus - planarDistSq w apollonianPolePlus = 0 := by
        rw [hDist, hw0, mul_zero]
      exact (sub_eq_zero.mp hzero).symm
  have hFixed : stripHorizonRefl w = w ↔ w.1 = 0 := by
    constructor
    · intro hfix
      have h1 : -w.1 = w.1 := congrArg Prod.fst hfix
      linarith
    · intro hw0
      ext
      · simp [stripHorizonRefl, hw0]
      · simp [stripHorizonRefl]
  exact ⟨⟨hTT, hPP, hPTPT, hPT, hTP⟩, ⟨hPole1, hPole2⟩, hDist, hBisect, hFixed⟩

/-- **Parallel Branching & Multi-Stratum Chains on `CoagulaNode`**:
Confirms genuine branching incomparability (`N2b_OutwardX ∥ N2c_InwardY` and
`N4a_AporiaA0 ∥ N4b_TruncationSigma0`) alongside multi-step causal reachability paths. -/
theorem coagula_parallel_branching_and_chains :
    (¬ Relation.TransGen CoagulaCovers .N2b_OutwardX .N2c_InwardY ∧
      ¬ Relation.TransGen CoagulaCovers .N2c_InwardY .N2b_OutwardX) ∧
    (¬ Relation.TransGen CoagulaCovers .N4a_AporiaA0 .N4b_TruncationSigma0 ∧
      ¬ Relation.TransGen CoagulaCovers .N4b_TruncationSigma0 .N4a_AporiaA0) ∧
    Relation.TransGen CoagulaCovers .N0_Omega .N6_ReciprocalJOmega ∧
    Relation.TransGen CoagulaCovers .N1a_ThesisP .N4a_AporiaA0 ∧
    Relation.TransGen CoagulaCovers .N2b_OutwardX .N5_MetaTower := by
  have hXY : ¬ Relation.TransGen CoagulaCovers .N2b_OutwardX .N2c_InwardY := fun h => by
    have hlt := coagulaCovers_transGen_topoRank_strictMono h
    simp [topoRank] at hlt
  have hYX : ¬ Relation.TransGen CoagulaCovers .N2c_InwardY .N2b_OutwardX := fun h => by
    have hlt := coagulaCovers_transGen_topoRank_strictMono h
    simp [topoRank] at hlt
  have hASig : ¬ Relation.TransGen CoagulaCovers .N4a_AporiaA0 .N4b_TruncationSigma0 := fun h => by
    have hlt := coagulaCovers_transGen_topoRank_strictMono h
    simp [topoRank] at hlt
  have hSigA : ¬ Relation.TransGen CoagulaCovers .N4b_TruncationSigma0 .N4a_AporiaA0 := fun h => by
    have hlt := coagulaCovers_transGen_topoRank_strictMono h
    simp [topoRank] at hlt
  have hPtoA0 : Relation.TransGen CoagulaCovers .N1a_ThesisP .N4a_AporiaA0 :=
    Relation.TransGen.tail
      (Relation.TransGen.single CoagulaCovers.P_to_T)
      CoagulaCovers.T_to_A0
  have hXtoTower : Relation.TransGen CoagulaCovers .N2b_OutwardX .N5_MetaTower :=
    Relation.TransGen.tail
      (Relation.TransGen.single CoagulaCovers.X_to_F)
      CoagulaCovers.F_to_tower
  exact ⟨⟨hXY, hYX⟩, ⟨hASig, hSigA⟩,
    coagula_root_reaches_synthesis, hPtoA0, hXtoTower⟩

end KeldyshApollonianAndPoset

end InfoGeometry.OperatorAlgebra.ParabolicJordanTrichotomyAndMannheimVMetric
