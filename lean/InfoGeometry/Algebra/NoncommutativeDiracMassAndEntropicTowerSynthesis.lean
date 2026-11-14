/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

/-!
# Noncommutative Dirac Mass & Entropic Tower Synthesis ($\mathcal{D}\mathcal{M}_1$–$\mathcal{D}\mathcal{M}_4$)

Formalization of inter-sheet mass mixing, operator-valued Dirac equations,
and all-scales mass/entropy summability over arbitrary noncommutative rings
`[Ring A]` and $\star$-rings `[Ring A] [StarRing A]`:

1. **$\mathcal{D}\mathcal{M}_1$** (`sheet_mixing_mass_and_chiral_supertrace_anomaly`):
   Inter-sheet Witt transition operators `isotropicSheetPlus`, `isotropicSheetMinus`,
   the DeWitt-odd sheet-mixing mass operator `sheetMassOp μ_plus μ_minus`, its
   diagonalized square, and the chiral supertrace commutator anomaly
   `superTrace2 ((sheetMassOp μ_plus μ_minus)^2) = ⁅μ_plus, μ_minus⁆`.
2. **$\mathcal{D}\mathcal{M}_2$** (`operator_dirac_sheet_coupling_and_klein_gordon_weitzenbock`):
   Peirce sheet-coupling equivalence for the operator-valued Dirac equation
   `(D_ev - M_mix) * Ψ = 0` on `M₂(A)` and the noncommutative
   Klein–Gordon–Weitzenböck identity with off-diagonal commutator obstruction `⁅D_ev, M_mix⁆`.
3. **$\mathcal{D}\mathcal{M}_3$** (`gradedOperatorMassTower_square`):
   For arbitrary stagewise operator masses, the square has an exact
   off-diagonal Lie-commutator obstruction; no commutativity is assumed.
4. **$\mathcal{D}\mathcal{M}_4$** (`entropicMassTower`):
   An operator-valued defect tower annihilates the source corner, accumulates
   on the sink corner through its projected operator sum, and is stable under
   the Bott corner embedding.

The dependency order is `DM₁ → DM₂`; `DM₃` and `DM₄` are separate tower
constructions over the inductive matrix algebra. No implication between the
two tower constructions is asserted.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

namespace InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis

section Matrix2Simp

variable {A : Type*} [Ring A]

/-- Upper-triangular isotropic Witt sheet transition operator. -/
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
/-- Lower-triangular isotropic Witt sheet transition operator. -/
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
/-- Diagonal fiber embedding of `A` into `M₂(A)`. -/
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
/-- $\mathbb{Z}_2$-graded supertrace on `M₂(A)`. -/
def superTrace2 (M : Matrix (Fin 2) (Fin 2) A) : A := M 0 0 - M 1 1

/-- Explicit non-commutativity witness for the Witt sheet transition operators over `ℤ`. -/
lemma isotropicSheetPlus_mul_isotropicSheetMinus_ne :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) ℤ) * isotropicSheetMinus ≠
      isotropicSheetMinus * isotropicSheetPlus := by
  intro h
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  simp [isotropicSheetPlus, isotropicSheetMinus, Matrix.mul_apply, Fin.sum_univ_two, mat2] at h00

end Matrix2Simp

/-!
## Archetype $\mathcal{D}\mathcal{M}_1$: Mass as Inter-Sheet Witt Mixing & Chiral Supertrace Commutator Anomaly
-/

section ArchetypeDM1_SheetMixingMass

variable {A : Type*} [Ring A]

/-- Noncommutative sheet-mixing mass operator
$\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-) = \iota(\mu_+)\mathcal{I}_+ + \iota(\mu_-)\mathcal{I}_- = \bigl(\begin{smallmatrix} 0 & \mu_+ \\ \mu_- & 0 \end{smallmatrix}\bigr)$. -/
def sheetMassOp (μ_plus μ_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 0 μ_plus μ_minus 0

/-- **Sheet-Mixing Mass Square & Chiral Supertrace Anomaly Theorem ($\mathcal{D}\mathcal{M}_1$)**:
1. $\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-) = \iota(\mu_+)\mathcal{I}_+ + \iota(\mu_-)\mathcal{I}_-$,
2. $\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-)^2 = \mathrm{diag}(\mu_+ \mu_-, \mu_- \mu_+)$,
3. $\mathrm{Str}(\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-)^2) = \⁅\mu_+, \mu_-⁆$,
4. Over `[StarRing A]`, $\mathcal{M}_{\mathrm{mix}}(\mu, \mu^\star)$ is self-adjoint with square $\mathrm{diag}(\mu\mu^\star, \mu^\star\mu)$. -/
theorem sheet_mixing_mass_and_chiral_supertrace_anomaly [StarRing A]
    (μ_plus μ_minus μ : A) :
    sheetMassOp μ_plus μ_minus =
      fiberEmbed μ_plus * isotropicSheetPlus +
      fiberEmbed μ_minus * isotropicSheetMinus ∧
    sheetMassOp μ_plus μ_minus * sheetMassOp μ_plus μ_minus =
      mat2 (μ_plus * μ_minus) 0 0 (μ_minus * μ_plus) ∧
    superTrace2 (sheetMassOp μ_plus μ_minus * sheetMassOp μ_plus μ_minus) =
      ⁅μ_plus, μ_minus⁆ ∧
    (sheetMassOp μ (star μ))ᴴ = sheetMassOp μ (star μ) ∧
    sheetMassOp μ (star μ) * sheetMassOp μ (star μ) =
      mat2 (μ * star μ) 0 0 (star μ * μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [sheetMassOp, fiberEmbed, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> simp [sheetMassOp]
  · dsimp [superTrace2, sheetMassOp]; rw [Ring.lie_def]; simp
  · apply ext_fin2 <;> simp [sheetMassOp]
  · apply ext_fin2 <;> simp [sheetMassOp]

end ArchetypeDM1_SheetMixingMass

/-!
## Archetype $\mathcal{D}\mathcal{M}_2$: Operator-Valued Dirac Equation on $M_2(A)$ & Noncommutative Klein–Gordon–Weitzenböck Identity
-/

section ArchetypeDM2_OperatorDiracEquation

variable {A : Type*} [Ring A]

/-- Intra-sheet kinetic / covariant propagation operator $D_{\mathrm{even}}(\nabla_+, \nabla_-) = \mathrm{diag}(\nabla_+, \nabla_-)$. -/
def evenKinOp (d_plus d_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 d_plus 0 0 d_minus

/-- DeWitt even (diagonal intra-sheet) projection of an operator state $\Psi \in M_2(A)$. -/
def dewittEven (Ψ : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 (Ψ 0 0) 0 0 (Ψ 1 1)

/-- DeWitt odd (off-diagonal inter-sheet) projection of an operator state $\Psi \in M_2(A)$. -/
def dewittOdd (Ψ : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 0 (Ψ 0 1) (Ψ 1 0) 0

/-- **Operator-Valued Dirac Sheet-Coupling & Klein–Gordon–Weitzenböck Theorem ($\mathcal{D}\mathcal{M}_2$)**:
For any operator state $\Psi \in M_2(A)$, intra-sheet operators $\nabla_+, \nabla_- \in A$, and
inter-sheet mass couplings $\mu_+, \mu_- \in A$:
1. $(D_{\mathrm{even}} - \mathcal{M}_{\mathrm{mix}})\Psi = 0 \iff
    (D_{\mathrm{even}}\Psi_{\mathrm{even}} = \mathcal{M}_{\mathrm{mix}}\Psi_{\mathrm{odd}} \;\wedge\;
     D_{\mathrm{even}}\Psi_{\mathrm{odd}} = \mathcal{M}_{\mathrm{mix}}\Psi_{\mathrm{even}})$,
2. *Klein–Gordon–Weitzenböck Identity*:
   $(D_{\mathrm{even}} + \mathcal{M}_{\mathrm{mix}})(D_{\mathrm{even}} - \mathcal{M}_{\mathrm{mix}}) =
    \mathrm{diag}(\nabla_+^2 - \mu_+\mu_-, \nabla_-^2 - \mu_-\mu_+) - \⁅D_{\mathrm{even}}, \mathcal{M}_{\mathrm{mix}}⁆$. -/
theorem operator_dirac_sheet_coupling_and_klein_gordon_weitzenbock
    (d_plus d_minus μ_plus μ_minus : A) (Ψ : Matrix (Fin 2) (Fin 2) A) :
    let D_ev  := evenKinOp d_plus d_minus
    let M_mix := sheetMassOp μ_plus μ_minus
    ((D_ev - M_mix) * Ψ = 0 ↔
      (D_ev * dewittEven Ψ = M_mix * dewittOdd Ψ ∧
       D_ev * dewittOdd Ψ = M_mix * dewittEven Ψ)) ∧
    (D_ev + M_mix) * (D_ev - M_mix) =
      mat2 (d_plus * d_plus - μ_plus * μ_minus) 0 0 (d_minus * d_minus - μ_minus * μ_plus) -
      ⁅D_ev, M_mix⁆ := by
  intro D_ev M_mix
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have h00 : ((D_ev - M_mix) * Ψ) 0 0 = 0 := by rw [h]; rfl
      have h01 : ((D_ev - M_mix) * Ψ) 0 1 = 0 := by rw [h]; rfl
      have h10 : ((D_ev - M_mix) * Ψ) 1 0 = 0 := by rw [h]; rfl
      have h11 : ((D_ev - M_mix) * Ψ) 1 1 = 0 := by rw [h]; rfl
      dsimp [D_ev, M_mix, evenKinOp, sheetMassOp] at h00 h01 h10 h11
      simp only [Matrix.sub_apply, mul2_00, mul2_01, mul2_10, mul2_11,
        mat2_00, mat2_01, mat2_10, mat2_11, sub_zero, zero_sub,
        neg_mul, add_neg_eq_zero, neg_add_eq_zero] at h00 h01 h10 h11
      constructor
      · apply ext_fin2 <;>
          simp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd, h00, h11]
      · apply ext_fin2 <;>
          simp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd, h01, h10]
    · rintro ⟨h_ev, h_odd⟩
      have h00 : (D_ev * dewittEven Ψ) 0 0 = (M_mix * dewittOdd Ψ) 0 0 := by rw [h_ev]
      have h11 : (D_ev * dewittEven Ψ) 1 1 = (M_mix * dewittOdd Ψ) 1 1 := by rw [h_ev]
      have h01 : (D_ev * dewittOdd Ψ) 0 1 = (M_mix * dewittEven Ψ) 0 1 := by rw [h_odd]
      have h10 : (D_ev * dewittOdd Ψ) 1 0 = (M_mix * dewittEven Ψ) 1 0 := by rw [h_odd]
      dsimp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd] at h00 h11 h01 h10
      simp only [mul2_00, mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        mul_zero, add_zero, zero_add] at h00 h11 h01 h10
      apply ext_fin2 <;>
        simp [D_ev, M_mix, evenKinOp, sheetMassOp, h00, h01, h10, h11]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [D_ev, M_mix, evenKinOp, sheetMassOp] <;> noncomm_ring

end ArchetypeDM2_OperatorDiracEquation

/-!
## Archetypes $\mathcal{D}\mathcal{M}_3$ and $\mathcal{D}\mathcal{M}_4$: Operator-valued towers
-/

section ArchetypeDM3_DM4_InductiveMassAndEntropyTowers

universe u

/-- Inductive $2^n \times 2^n$ matrix tower $\mathcal{C}\ell_n(A)$. -/
@[reducible] def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

/-- Non-unital Bott corner embedding $\iota_{\mathrm{Bott}}(X) = \mathrm{diag}(X, 0)$. -/
def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

/-- Cantor corner projection used by the local operator tower. -/
def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0 => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

/-- Opposite sink corner projection. -/
def sinkProj : ∀ (n : ℕ), ClTower A n
  | 0 => (1 : A)
  | n + 1 => mat2 0 0 0 (sinkProj n)

/-- Recursive matrix trace with values in the coefficient ring. -/
def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0, x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0, _ => rfl
  | _ + 1, X => by
      simp only [towerTrace, Matrix.neg_apply]
      rw [towerTrace_neg (X 0 0), towerTrace_neg (X 1 1)]
      abel

/-- Graded operator mass tower: `M₀ = μ₀` and
`Mₙ₊₁ = [[Mₙ, μₙ], [μₙ, -Mₙ]]`, for arbitrary stagewise operator masses. -/
def gradedOperatorMassTower (μ : ∀ n, ClTower A n) : ∀ n, ClTower A n
  | 0 => μ 0
  | n + 1 => mat2 (gradedOperatorMassTower μ n) (μ n)
      (μ n) (-gradedOperatorMassTower μ n)

/-- The square records the exact noncommutative commutator defect. -/
theorem gradedOperatorMassTower_square (μ : ∀ n, ClTower A n) (n : ℕ) :
    let M := gradedOperatorMassTower μ n
    let C := μ n
    mat2 M C C (-M) * mat2 M C C (-M) =
      mat2 (M * M + C * C) ⁅M, C⁆ ⁅C, M⁆ (M * M + C * C) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp
  all_goals first | noncomm_ring | abel

/-- The recursive matrix trace of each positive-level graded operator mass is zero. -/
theorem gradedOperatorMassTower_trace_succ (μ : ∀ n, ClTower A n) (n : ℕ) :
    towerTrace (gradedOperatorMassTower μ (n + 1)) = 0 := by
  simp [gradedOperatorMassTower, towerTrace, towerTrace_neg]

/-- Entropic defect tower with arbitrary operator-valued coefficients. -/
def entropicMassTower (μ : ∀ n, ClTower A n) : ∀ n, ClTower A n
  | 0 => 0
  | n + 1 => mat2 (entropicMassTower μ n) 0 0
      (entropicMassTower μ n + μ n)

/-- Cumulative operator mass supported on the sink corner. -/
def sinkMassSum (μ : ∀ n, ClTower A n) : ∀ n, ClTower A n
  | 0 => 0
  | n + 1 => mat2 0 0 0 (sinkMassSum μ n + μ n * sinkProj n)

theorem entropicMassTower_vacuum_annihilation (μ : ∀ n, ClTower A n) :
    ∀ n, entropicMassTower μ n * cantorProj n = 0
  | 0 => by simp [entropicMassTower, cantorProj]
  | n + 1 => by
      apply ext_fin2 <;>
        simp [entropicMassTower, cantorProj, bottEmbed,
          entropicMassTower_vacuum_annihilation μ n]

theorem entropicMassTower_sink_sum (μ : ∀ n, ClTower A n) :
    ∀ n, entropicMassTower μ n * sinkProj n = sinkMassSum μ n
  | 0 => by simp [entropicMassTower, sinkProj, sinkMassSum]
  | n + 1 => by
      apply ext_fin2
      · simp [entropicMassTower, sinkProj, sinkMassSum]
      · simp [entropicMassTower, sinkProj, sinkMassSum]
      · simp [entropicMassTower, sinkProj, sinkMassSum]
      · simp only [entropicMassTower, sinkProj, sinkMassSum,
          mul2_11, mat2_01, mat2_10, mat2_11,
          mul_zero, zero_mul, zero_add]
        rw [add_mul, entropicMassTower_sink_sum μ n]

theorem entropicMassTower_bott_stable (μ : ∀ n, ClTower A n)
    (n : ℕ) (X : ClTower A n) :
    entropicMassTower μ (n + 1) * bottEmbed X =
      bottEmbed (entropicMassTower μ n * X) := by
  apply ext_fin2 <;> simp [entropicMassTower, bottEmbed]

/-- Operator-valued all-scales mass and defect laws. The square is stated with
its commutator terms, so it is valid over arbitrary noncommutative rings. -/
theorem all_scales_operator_mass_and_defect_laws
    (μ ν : ∀ n, ClTower A n) (n : ℕ) (X : ClTower A n) :
    (let M := gradedOperatorMassTower μ n
     let C := μ n
     mat2 M C C (-M) * mat2 M C C (-M) =
       mat2 (M * M + C * C) ⁅M, C⁆ ⁅C, M⁆ (M * M + C * C)) ∧
    towerTrace (gradedOperatorMassTower μ (n + 1)) = 0 ∧
    entropicMassTower ν n * cantorProj n = 0 ∧
    entropicMassTower ν n * sinkProj n = sinkMassSum ν n ∧
    entropicMassTower ν (n + 1) * bottEmbed X =
      bottEmbed (entropicMassTower ν n * X) := by
  exact ⟨gradedOperatorMassTower_square μ n,
    gradedOperatorMassTower_trace_succ μ n,
    entropicMassTower_vacuum_annihilation ν n,
    entropicMassTower_sink_sum ν n,
    entropicMassTower_bott_stable ν n X⟩

end ArchetypeDM3_DM4_InductiveMassAndEntropyTowers

end InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis
