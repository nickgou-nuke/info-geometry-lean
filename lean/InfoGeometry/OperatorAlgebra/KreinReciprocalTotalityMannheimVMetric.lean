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
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset

/-!
# Krein–Reciprocal-Totality–Mannheim $V$-Metric Bridge

Unifies the algebraic `SOLVE -> COAGULA` reciprocal totality operator
`J_Ω = 2 Ω - 1 = Σ₀ + B` (`IndefiniteReciprocalTotalityPoset` and
`IndefiniteReciprocalTotalityAporiaPoset`) with Krein fundamental-symmetry
intertwining (`η * Ω = Ω* * η`) and Philip Mannheim's ghost-resolving
$V$-norm metric `V := η * J_Ω`:

1. **Cross-Poset Alignment (`reciprocalTotality_eq_reciprocityInvolution`)**:
   Identifies `(J_Ω, Σ₀, B)` between `IndefiniteReciprocalTotalityPoset` and
   `IndefiniteReciprocalTotalityAporiaPoset` identically over any unital `[Ring E]`.
2. **Division-Free `[Ring E] [StarRing E]` Theorem
   (`krein_reciprocalTotality_mannheim_V_metric`)**:
   Whenever `P^2 = P`, `Ω^2 = Ω`, `star η = η`, and `η * Ω = star Ω * η`:
   - `V = η * Σ₀ + η * B`, while the cross-anticommutator `Σ₀ B + B Σ₀ = 0`;
   - `star V = V` ($V$ is Hermitian without assuming `[P, η] = 0`);
   - `V * J_Ω = η = star J_Ω * V` and `star J_Ω * η * J_Ω = η`;
   - `V * Ω = star Ω * V` ($V$-self-adjointness of `Ω`) and
     `star J_Ω * V * J_Ω = V` ($V$-unitarity of `J_Ω`).
3. **Constructive Division-Free $M_2(\mathbb{Z})$ Ghost-to-Positive-$V$-Norm Witness
   (`mat2Z_krein_ghost_and_mannheim_V_posdef_witness`)**:
   For the concrete witness `(P₀, Ω₀)` (`P₀ = diag(1, 0)`, `Ω₀ = !![2, 1; -2, -1]`):
   - Any diagonal `P₀`-commuting `Ω₀`-intertwiner is forced into the
     indefinite `(1,1)` Krein metric `η₀ = !![2, 0; 0, -1]` (`det = -2 < 0`),
     producing negative aporia `A₀ = !![-2, 0; 0, 0]` and the indefinite
     ghost mode `e₂ᵀ η₀ e₂ = -1`;
   - Multiplying by `J_{Ω₀} = !![3, 2; -4, -3]` produces Mannheim's symmetric
     positive-definite metric `V₀ = η₀ * J_{Ω₀} = !![6, 4; 4, 3]` (`det = 2 > 0`),
     satisfying the exact integer sum-of-squares identity
     `xᵀ V₀ x = (2 x₀ + x₁)² + 2 (x₀ + x₁)² > 0` for all `(x₀, x₁) ≠ (0, 0)`.

No `sorry`, `admit`, custom axioms, or `native_decide` are used.
-/

namespace InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric

open Matrix
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset

section AlignmentAndAbstractVMetric

variable {E : Type*} [Ring E]

/-- Alignment of `Σ₀`, `B`, and `J_Ω` between `IndefiniteReciprocalTotalityPoset` and
`IndefiniteReciprocalTotalityAporiaPoset` over any unital `[Ring E]`. -/
theorem reciprocalTotality_eq_reciprocityInvolution (P Ω : E) :
    IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω =
      IndefiniteReciprocalTotalityAporiaPoset.reciprocityInvolution Ω ∧
    IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω =
      IndefiniteReciprocalTotalityAporiaPoset.severedDogma P Ω ∧
    IndefiniteReciprocalTotalityPoset.doubledBridge P Ω =
      IndefiniteReciprocalTotalityAporiaPoset.scaledBridge P Ω := by
  refine ⟨rfl, ?_, rfl⟩
  unfold IndefiniteReciprocalTotalityPoset.dogmaticTruncation
    IndefiniteReciprocalTotalityAporiaPoset.severedDogma
    IndefiniteReciprocalTotalityPoset.consciousThesis
    IndefiniteReciprocalTotalityAporiaPoset.consciousThesis
    IndefiniteReciprocalTotalityPoset.autonomousGround
    IndefiniteReciprocalTotalityAporiaPoset.autonomousGround
    IndefiniteReciprocalTotalityPoset.shadowQ
    IndefiniteReciprocalTotalityAporiaPoset.shadowComp
    PeirceSpine.peirce11 PeirceSpine.peirce00
  noncomm_ring

/-- Mannheim's intertwined metric `V := η * J_Ω = η * (2 Ω - 1)` in an associative ring. -/
def mannheimVMetric (η Ω : E) : E :=
  η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω

private lemma star_two_mul_sub_one [StarRing E] (Ω : E) :
    star ((2 : E) * Ω - 1) = (2 : E) * star Ω - 1 := by
  rw [two_mul, two_mul, star_sub, star_add, star_one]

/-- **Division-Free Mannheim $V$-Metric & Reciprocal-Totality Theorem**:
Over any unital `[Ring E] [StarRing E]`, for any Peirce cut `P^2 = P`, totality `Ω^2 = Ω`,
symmetric metric `star η = η`, and Krein pseudo-Hermiticity intertwiner `η * Ω = star Ω * η`,
`V := η * J_Ω` splits via `Σ₀ + B`, is `star`-Hermitian, renders both `Ω` and `J_Ω`
`V`-self-adjoint, and renders `J_Ω` simultaneously `η`-pseudo-unitary and `V`-unitary. -/
theorem krein_reciprocalTotality_mannheim_V_metric [StarRing E]
    {P Ω η : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω)
    (hη : star η = η) (hηΩ : η * Ω = star Ω * η) :
    (mannheimVMetric η Ω =
        η * IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω +
          η * IndefiniteReciprocalTotalityPoset.doubledBridge P Ω ∧
      η * (IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω *
            IndefiniteReciprocalTotalityPoset.doubledBridge P Ω +
          IndefiniteReciprocalTotalityPoset.doubledBridge P Ω *
            IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω) = 0) ∧
    star (mannheimVMetric η Ω) = mannheimVMetric η Ω ∧
    (mannheimVMetric η Ω * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = η ∧
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω = η) ∧
    star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * η *
      IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = η ∧
    (mannheimVMetric η Ω * Ω = star Ω * mannheimVMetric η Ω ∧
      mannheimVMetric η Ω * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω =
        star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω) ∧
    star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω *
      IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = mannheimVMetric η Ω := by
  have h5 := IndefiniteReciprocalTotalityPoset.prop5_incompleteness_of_dogmatic_truncation hP hΩ
  have hOm := IndefiniteReciprocalTotalityPoset.thm_omega_indefinite_reciprocal_totality hP hΩ
  have hSum : IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω +
      IndefiniteReciprocalTotalityPoset.doubledBridge P Ω =
      IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω := hOm.1
  have hJsq : IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω *
      IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = 1 := hOm.2.1
  have hSplit :
      mannheimVMetric η Ω =
        η * IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω +
          η * IndefiniteReciprocalTotalityPoset.doubledBridge P Ω := by
    rw [mannheimVMetric, ← hSum, mul_add]
  have hAntiZero :
      η * (IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω *
            IndefiniteReciprocalTotalityPoset.doubledBridge P Ω +
          IndefiniteReciprocalTotalityPoset.doubledBridge P Ω *
            IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω) = 0 := by
    rw [h5.1, mul_zero]
  have hηJ :
      η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω =
        star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * η := by
    dsimp [IndefiniteReciprocalTotalityPoset.reciprocalTotality]
    rw [star_two_mul_sub_one]
    calc
      η * ((2 : E) * Ω - 1) = (2 : E) * (η * Ω) - η := by noncomm_ring
      _ = (2 : E) * (star Ω * η) - η := by rw [hηΩ]
      _ = ((2 : E) * star Ω - 1) * η := by noncomm_ring
  have hVstar : star (mannheimVMetric η Ω) = mannheimVMetric η Ω := by
    calc
      star (mannheimVMetric η Ω)
          = star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * star η := by
              rw [mannheimVMetric, star_mul]
      _ = star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * η := by rw [hη]
      _ = η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω := hηJ.symm
      _ = mannheimVMetric η Ω := rfl
  have hVJ : mannheimVMetric η Ω * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = η := by
    calc
      mannheimVMetric η Ω * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω
          = η * (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω *
              IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) := by
              rw [mannheimVMetric, mul_assoc]
      _ = η * 1 := by rw [hJsq]
      _ = η := mul_one η
  have hJstarV :
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω = η := by
    calc
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω
          = star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) *
              (η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) := rfl
      _ = (η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) *
              IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω := by
              rw [← mul_assoc, ← hηJ, mul_assoc]
      _ = η := by
            rw [mul_assoc, hJsq, mul_one]
  have hPseudoUnit :
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * η *
          IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = η := by
    calc
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * η *
          IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω
          = (η * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) *
              IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω := by rw [← hηJ]
      _ = η := hVJ
  have hJΩ : IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω * Ω = Ω := by
    dsimp [IndefiniteReciprocalTotalityPoset.reciprocalTotality]
    calc
      ((2 : E) * Ω - 1) * Ω = (2 : E) * (Ω * Ω) - Ω := by noncomm_ring
      _ = (2 : E) * Ω - Ω := by rw [hΩ]
      _ = Ω := by
            rw [two_mul]
            noncomm_ring
  have hVOmega : mannheimVMetric η Ω * Ω = star Ω * mannheimVMetric η Ω := by
    have hlhs : mannheimVMetric η Ω * Ω = η * Ω := by
      rw [mannheimVMetric, mul_assoc, hJΩ]
    have hrhs : star Ω * mannheimVMetric η Ω = η * Ω := by
      dsimp [mannheimVMetric, IndefiniteReciprocalTotalityPoset.reciprocalTotality]
      calc
        star Ω * (η * ((2 : E) * Ω - 1))
            = (2 : E) * ((star Ω * η) * Ω) - star Ω * η := by noncomm_ring
        _ = (2 : E) * ((η * Ω) * Ω) - η * Ω := by rw [hηΩ]
        _ = (2 : E) * (η * (Ω * Ω)) - η * Ω := by noncomm_ring
        _ = (2 : E) * (η * Ω) - η * Ω := by rw [hΩ]
        _ = η * Ω := by
              rw [two_mul]
              noncomm_ring
    exact hlhs.trans hrhs.symm
  have hVJ_selfAdj :
      mannheimVMetric η Ω * IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω =
        star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω :=
    hVJ.trans hJstarV.symm
  have hVUnit :
      star (IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω) * mannheimVMetric η Ω *
          IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω = mannheimVMetric η Ω := by
    rw [hJstarV, mannheimVMetric]
  exact ⟨⟨hSplit, hAntiZero⟩, hVstar, ⟨hVJ, hJstarV⟩, hPseudoUnit, ⟨hVOmega, hVJ_selfAdj⟩, hVUnit⟩

end AlignmentAndAbstractVMetric

section ConcreteMat2ZWitness

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℤ`. -/
theorem mannheim_mat2Z_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  IndefiniteReciprocalTotalityPoset.mat2Z_noncomm_witness

/-- Indefinite `(1, 1)` Krein metric `η₀ = !![2, 0; 0, -1]` commuting with `cutP0`. -/
def kreinEta0 : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, -1]

/-- Mannheim's intertwined metric `V₀ := η₀ * J_{Ω₀}` on `M₂(ℤ)`. -/
def mannheimV0 : Matrix (Fin 2) (Fin 2) ℤ :=
  mannheimVMetric kreinEta0 IndefiniteReciprocalTotalityPoset.totalityOmega0

/-- **Division-Free Ghost-to-Positive-$V$-Norm Witness Over `ℤ`**:
1. The diagonal Krein metric `η₀` commutes with the conscious cut `P₀`, is symmetric,
   has indefinite determinant `det η₀ = -2 < 0` (`e₂ᵀ η₀ e₂ = -1` ghost mode),
   while `socraticAporia P₀ Ω₀ = !![-2, 0; 0, 0]`;
2. `η₀` intertwines `Ω₀` (`η₀ Ω₀ = Ω₀ᵀ η₀ = !![4, 2; 2, 1]`) and makes `J_{Ω₀}`
   pseudo-unitary (`J_{Ω₀}ᵀ η₀ J_{Ω₀} = η₀`);
3. Passing to `V₀ := η₀ * J_{Ω₀}` clears the negative metric mode without division:
   `V₀ = !![6, 4; 4, 3]`, `V₀ᵀ = V₀`, `det V₀ = 2 > 0`, and
   `xᵀ V₀ x = (2 x₀ + x₁)² + 2 (x₀ + x₁)² > 0` for every nonzero `(x₀, x₁) : ℤ × ℤ`. -/
theorem mat2Z_krein_ghost_and_mannheim_V_posdef_witness :
    (PeirceSpine.comm IndefiniteReciprocalTotalityPoset.cutP0 kreinEta0 = 0 ∧
      kreinEta0.transpose = kreinEta0 ∧
      kreinEta0.det = -2 ∧
      dotProduct ![1, 0] (kreinEta0 *ᵥ ![1, 0]) = 2 ∧
      dotProduct ![0, 1] (kreinEta0 *ᵥ ![0, 1]) = -1 ∧
      IndefiniteReciprocalTotalityAporiaPoset.socraticAporia
        IndefiniteReciprocalTotalityPoset.cutP0
        IndefiniteReciprocalTotalityPoset.totalityOmega0 = !![-2, 0; 0, 0]) ∧
    (kreinEta0 * IndefiniteReciprocalTotalityPoset.totalityOmega0 =
        IndefiniteReciprocalTotalityPoset.totalityOmega0.transpose * kreinEta0 ∧
      kreinEta0 * IndefiniteReciprocalTotalityPoset.totalityOmega0 = !![4, 2; 2, 1] ∧
      (IndefiniteReciprocalTotalityPoset.reciprocalTotality
          IndefiniteReciprocalTotalityPoset.totalityOmega0).transpose *
        kreinEta0 *
        IndefiniteReciprocalTotalityPoset.reciprocalTotality
          IndefiniteReciprocalTotalityPoset.totalityOmega0 = kreinEta0) ∧
    (mannheimV0 = !![6, 4; 4, 3] ∧
      mannheimV0.transpose = mannheimV0 ∧
      mannheimV0.det = 2) ∧
    (∀ x y : ℤ,
      dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y]) =
        (2 * x + y) ^ 2 + 2 * (x + y) ^ 2) ∧
    (∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) →
      0 < dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y])) := by
  have hcomm : PeirceSpine.comm IndefiniteReciprocalTotalityPoset.cutP0 kreinEta0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PeirceSpine.comm, IndefiniteReciprocalTotalityPoset.cutP0, kreinEta0]
  have hetaT : kreinEta0.transpose = kreinEta0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kreinEta0]
  have hetaDet : kreinEta0.det = -2 := by
    rw [Matrix.det_fin_two]
    norm_num [kreinEta0]
  have heta_pos : dotProduct ![1, 0] (kreinEta0 *ᵥ ![1, 0]) = 2 := by
    decide
  have heta_neg : dotProduct ![0, 1] (kreinEta0 *ᵥ ![0, 1]) = -1 := by
    decide
  have hap :
      IndefiniteReciprocalTotalityAporiaPoset.socraticAporia
        IndefiniteReciprocalTotalityPoset.cutP0
        IndefiniteReciprocalTotalityPoset.totalityOmega0 = !![-2, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hηΩ_val : kreinEta0 * IndefiniteReciprocalTotalityPoset.totalityOmega0 = !![4, 2; 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kreinEta0, IndefiniteReciprocalTotalityPoset.totalityOmega0,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hΩTη_val :
      IndefiniteReciprocalTotalityPoset.totalityOmega0.transpose * kreinEta0 = !![4, 2; 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kreinEta0, IndefiniteReciprocalTotalityPoset.totalityOmega0,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hηΩ := hηΩ_val.trans hΩTη_val.symm
  have hAbs := krein_reciprocalTotality_mannheim_V_metric (E := Matrix (Fin 2) (Fin 2) ℤ)
    IndefiniteReciprocalTotalityPoset.cutP0_idem
    IndefiniteReciprocalTotalityPoset.totalityOmega0_idem
    hetaT hηΩ
  have hPseudo :
      (IndefiniteReciprocalTotalityPoset.reciprocalTotality
          IndefiniteReciprocalTotalityPoset.totalityOmega0).transpose *
        kreinEta0 *
        IndefiniteReciprocalTotalityPoset.reciprocalTotality
          IndefiniteReciprocalTotalityPoset.totalityOmega0 = kreinEta0 :=
    hAbs.2.2.2.1
  have hVval : mannheimV0 = !![6, 4; 4, 3] := by
    dsimp [mannheimV0, mannheimVMetric]
    rw [IndefiniteReciprocalTotalityPoset.concrete_mat2Z_indefinite_reciprocal_totality_witness.2.2.2.2.2.2.2.1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kreinEta0]
  have hVT : mannheimV0.transpose = mannheimV0 := by
    rw [hVval]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hVdet : mannheimV0.det = 2 := by
    rw [hVval, Matrix.det_fin_two]
    norm_num
  have hSOS : ∀ x y : ℤ,
      dotProduct ![x, y] (mannheimV0 *ᵥ ![x, y]) =
        (2 * x + y) ^ 2 + 2 * (x + y) ^ 2 := by
    intro x y
    rw [hVval]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
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
    ⟨hηΩ, hηΩ_val, hPseudo⟩,
    ⟨hVval, hVT, hVdet⟩,
    hSOS, hPos⟩

end ConcreteMat2ZWitness

end InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric
