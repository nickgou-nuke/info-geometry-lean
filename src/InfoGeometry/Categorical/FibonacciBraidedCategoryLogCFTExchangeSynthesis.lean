/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.FibonacciBraiding
import InfoGeometry.Categorical.BraidPermutationQuotient
import InfoGeometry.Clifford.ExchangeSMatrixBridge
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

/-!
# Three-Strand Artin Braid Group Representation `B₃ →* GL₂(ℂ)`, Colimit Hadjiivanov Monodromy, and LogCFT–Krein–Yangian Exchange Unification

Closes **Rank 2** of the repository's highest-ROI formalization gaps (`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` §7 & §10):

1. **Invertible `GL₂(ℂ)` Units for Fibonacci Fusion & Braiding (`fibonacciFusionUnit`, `fibonacciRUnit`, `fibonacciBUnit`):**
   Lifts `fibonacciFusionMatrix τ s`, `fibonacciRMatrix q`, and `fibonacciBMatrix q τ s = F R F`
   into `Units (Matrix (Fin 2) (Fin 2) ℂ)`.
2. **Canonical 3-Strand Artin Braid Group Homomorphism `B₃ →* GL₂(ℂ)` & Pure-Braid Restriction:**
   Constructs `fibonacciThreeStrandArtinSystem : ArtinBraidSystem (Units (Matrix (Fin 2) (Fin 2) ℂ)) 2`,
   inducing the canonical group homomorphism
   `fibonacciThreeStrandBraidRep : Braid.braid_group 3 →* Units (Matrix (Fin 2) (Fin 2) ℂ)`
   and its restriction `fibonacciThreeStrandPureBraidRep` to the canonical pure-braid kernel
   `pureBraidSubgroup 2`, proving exact generator and pure generator-square evaluations.
3. **Colimit Hadjiivanov Monodromy & Exchange S-Matrix Winding Transport (`TensorTowerColimit`):**
   Transports the Hadjiivanov logarithmic monodromy `lowerHadjiivanovMonodromy h ^ k` and
   multi-block exchange S-matrix `lowerExchangeSMatrix blocks` across any `TensorTowerColimit`
   system `(A, iota, A_inf, psi, psi_comm)`, proving that colimit projection commutes with
   the additive logarithmic shear winding law.
4. **LogCFT Virasoro Rank-2 Jordan Partner ↔ `4 × 4` Krein–Hamiltonian–Hopf Double-Pole Resolvent:**
   Proves the universal rank-2 Jordan double-pole resolvent identity
   `(z • 1 - (h • 1 + N)) * ((z - h) • 1 + N) = (z - h) ^ 2 • 1` for any square-zero `N * N = 0`,
   instantiating it simultaneously on the `2 × 2` Virasoro `L₀` Jordan cell `virasoroL0Cell h`,
   its `4 × 4` Kronecker lift `kronIdLeft4 (virasoroL0Cell h)`, and the `4 × 4` Krein–Hopf
   exceptional generator `kreinHopfGen wBar dw dw`.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciBraidedCategoryLogCFTExchangeSynthesis

open Matrix
open Braid
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciBraiding
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.Categorical.BraidPermutationQuotient
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.ExchangeSMatrixBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset

/-! ===========================================================================
    Section 1: Invertible `GL₂(ℂ)` Units for Fibonacci Fusion & Braiding
    =========================================================================== -/

section FibonacciMatrixUnits

/-- Inverse of `fibonacciRMatrix q`, with diagonal entries `q⁴` and `q⁻³`. -/
def fibonacciRMatrixInv (q : Units ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q ^ (4 : ℤ) : Units ℂ), 0; 0, (q ^ (-3 : ℤ) : Units ℂ)]

theorem fibonacciRMatrix_mul_inv (q : Units ℂ) :
    fibonacciRMatrix q * fibonacciRMatrixInv q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciRMatrix, fibonacciRMatrixInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem fibonacciRMatrixInv_mul (q : Units ℂ) :
    fibonacciRMatrixInv q * fibonacciRMatrix q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciRMatrix, fibonacciRMatrixInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- `fibonacciRMatrix q` packaged as a unit in `GL₂(ℂ)`. -/
def fibonacciRUnit (q : Units ℂ) : Units (Matrix (Fin 2) (Fin 2) ℂ) where
  val := fibonacciRMatrix q
  inv := fibonacciRMatrixInv q
  val_inv := fibonacciRMatrix_mul_inv q
  inv_val := fibonacciRMatrixInv_mul q

/-- `fibonacciFusionMatrix τ s` packaged as an involutive unit in `GL₂(ℂ)` when `s² = τ` and `τ² + τ = 1`. -/
def fibonacciFusionUnit (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Units (Matrix (Fin 2) (Fin 2) ℂ) where
  val := fibonacciFusionMatrix τ s
  inv := fibonacciFusionMatrix τ s
  val_inv := fibonacciFusionMatrix_sq hs hτ
  inv_val := fibonacciFusionMatrix_sq hs hτ

/-- `fibonacciBMatrix q τ s = F R F` packaged as a unit in `GL₂(ℂ)`. -/
def fibonacciBUnit (q : Units ℂ) (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Units (Matrix (Fin 2) (Fin 2) ℂ) :=
  fibonacciFusionUnit τ s hs hτ * fibonacciRUnit q * fibonacciFusionUnit τ s hs hτ

@[simp] theorem fibonacciBUnit_val (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fibonacciBUnit q τ s hs hτ : Matrix (Fin 2) (Fin 2) ℂ) = fibonacciBMatrix q τ s :=
  rfl

end FibonacciMatrixUnits

/-! ===========================================================================
    Section 2: Canonical 3-Strand Artin Braid Group Homomorphism `B₃ →* GL₂(ℂ)`
    and Pure-Braid Restriction
    =========================================================================== -/

section FibonacciArtinBraidRepresentation

/-- The 2-generator (`3`-strand) Artin braid system in `Units (Matrix (Fin 2) (Fin 2) ℂ)`
sending generator `0` to `R = fibonacciRUnit q` and generator `1` to `B = F R F = fibonacciBUnit q τ s`. -/
def fibonacciThreeStrandArtinSystem
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ArtinBraidSystem (Units (Matrix (Fin 2) (Fin 2) ℂ)) 2 where
  gen i := if i.val = 0 then fibonacciRUnit q else fibonacciBUnit q τ s hs hτ_quad
  adjacent i j hij := by
    fin_cases i <;> fin_cases j
    · simp at hij
    · apply Units.ext
      change fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s
      exact fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs
    · simp at hij
    · simp at hij
  farCommute i j hfar := by
    fin_cases i <;> fin_cases j <;> simp at hfar

/-- Canonical group homomorphism `B₃ →* GL₂(ℂ)` induced by the Fibonacci `R` and `B = F R F` matrices. -/
def fibonacciThreeStrandBraidRep
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    braid_group 3 →* Units (Matrix (Fin 2) (Fin 2) ℂ) :=
  (fibonacciThreeStrandArtinSystem q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ).toGroupHom

/-- Restriction of the 3-strand Fibonacci braid representation to the canonical pure-braid
subgroup `pureBraidSubgroup 2 = (braidToPerm 2).ker ≤ braid_group 3`. -/
def fibonacciThreeStrandPureBraidRep
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    pureBraidSubgroup 2 →* Units (Matrix (Fin 2) (Fin 2) ℂ) :=
  (fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ).comp
    (Subgroup.subtype (pureBraidSubgroup 2))

/-- Standard Artin generator `σ₀ ∈ B₃` maps to `fibonacciRMatrix q` under `fibonacciThreeStrandBraidRep`. -/
@[simp] theorem fibonacciThreeStrandBraidRep_gen0
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ((fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
        (σ' 2 ⟨0, by decide⟩) : Units (Matrix (Fin 2) (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = fibonacciRMatrix q := by
  unfold fibonacciThreeStrandBraidRep
  rw [ArtinBraidSystem.toGroupHom_generator]
  rfl

/-- Standard Artin generator `σ₁ ∈ B₃` maps to `fibonacciBMatrix q τ s` under `fibonacciThreeStrandBraidRep`. -/
@[simp] theorem fibonacciThreeStrandBraidRep_gen1
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ((fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
        (σ' 2 ⟨1, by decide⟩) : Units (Matrix (Fin 2) (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = fibonacciBMatrix q τ s := by
  unfold fibonacciThreeStrandBraidRep
  rw [ArtinBraidSystem.toGroupHom_generator]
  rfl

/-- Pure generator square `σ₀² ∈ PB₃` maps to `R²` under `fibonacciThreeStrandPureBraidRep`. -/
theorem fibonacciThreeStrandPureBraidRep_gen0_sq
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ((fibonacciThreeStrandPureBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
        ⟨(σ' 2 ⟨0, by decide⟩) ^ 2, generatorSquare_mem_pureBraidSubgroup 2 ⟨0, by decide⟩⟩ :
      Units (Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      fibonacciRMatrix q * fibonacciRMatrix q := by
  unfold fibonacciThreeStrandPureBraidRep
  change ((fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
      ((σ' 2 ⟨0, by decide⟩) ^ 2) : Units (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix (Fin 2) (Fin 2) ℂ) = fibonacciRMatrix q * fibonacciRMatrix q
  rw [pow_two, map_mul, Units.val_mul,
    fibonacciThreeStrandBraidRep_gen0 q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ]

/-- Pure generator square `σ₁² ∈ PB₃` maps to `F R² F` under `fibonacciThreeStrandPureBraidRep`. -/
theorem fibonacciThreeStrandPureBraidRep_gen1_sq
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    ((fibonacciThreeStrandPureBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
        ⟨(σ' 2 ⟨1, by decide⟩) ^ 2, generatorSquare_mem_pureBraidSubgroup 2 ⟨1, by decide⟩⟩ :
      Units (Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      fibonacciFusionMatrix τ s * (fibonacciRMatrix q * fibonacciRMatrix q) *
        fibonacciFusionMatrix τ s := by
  unfold fibonacciThreeStrandPureBraidRep
  change ((fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
      ((σ' 2 ⟨1, by decide⟩) ^ 2) : Units (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix (Fin 2) (Fin 2) ℂ) =
    fibonacciFusionMatrix τ s * (fibonacciRMatrix q * fibonacciRMatrix q) *
      fibonacciFusionMatrix τ s
  rw [pow_two, map_mul, Units.val_mul,
    fibonacciThreeStrandBraidRep_gen1 q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ]
  unfold fibonacciBMatrix
  calc
    (fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s) *
        (fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s) =
      fibonacciFusionMatrix τ s * fibonacciRMatrix q *
        (fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s) *
        fibonacciRMatrix q * fibonacciFusionMatrix τ s := by
      noncomm_ring
    _ = fibonacciFusionMatrix τ s * (fibonacciRMatrix q * fibonacciRMatrix q) *
          fibonacciFusionMatrix τ s := by
      rw [fibonacciFusionMatrix_sq hs hτ_quad]
      noncomm_ring

/-- **Theorem 2.1 (`fibonacci_three_strand_braid_and_pure_braid_representation`):**
Verifies that `fibonacciThreeStrandBraidRep` maps the standard Artin generators `σ₀, σ₁ ∈ B₃` to
`fibonacciRMatrix q` and `fibonacciBMatrix q τ s`, while `fibonacciThreeStrandPureBraidRep` maps
the pure generator squares `σ₀², σ₁² ∈ PB₃` to `R²` and `B² = F R² F`. -/
theorem fibonacci_three_strand_braid_and_pure_braid_representation
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ_quad : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = -(q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    let ρ := fibonacciThreeStrandBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
    let ρ_pure := fibonacciThreeStrandPureBraidRep q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ
    ((ρ (σ' 2 ⟨0, by decide⟩) : Matrix (Fin 2) (Fin 2) ℂ) = fibonacciRMatrix q) ∧
    ((ρ (σ' 2 ⟨1, by decide⟩) : Matrix (Fin 2) (Fin 2) ℂ) = fibonacciBMatrix q τ s) ∧
    ((ρ_pure ⟨(σ' 2 ⟨0, by decide⟩) ^ 2, generatorSquare_mem_pureBraidSubgroup 2 ⟨0, by decide⟩⟩ :
        Matrix (Fin 2) (Fin 2) ℂ) =
      fibonacciRMatrix q * fibonacciRMatrix q) ∧
    ((ρ_pure ⟨(σ' 2 ⟨1, by decide⟩) ^ 2, generatorSquare_mem_pureBraidSubgroup 2 ⟨1, by decide⟩⟩ :
        Matrix (Fin 2) (Fin 2) ℂ) =
      fibonacciFusionMatrix τ s * (fibonacciRMatrix q * fibonacciRMatrix q) *
        fibonacciFusionMatrix τ s) :=
  ⟨fibonacciThreeStrandBraidRep_gen0 q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ,
   fibonacciThreeStrandBraidRep_gen1 q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ,
   fibonacciThreeStrandPureBraidRep_gen0_sq q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ,
   fibonacciThreeStrandPureBraidRep_gen1_sq q τ s hs hτ_quad hq_inv hq_pow3 hq5 h_poly hτ⟩

end FibonacciArtinBraidRepresentation

/-! ===========================================================================
    Section 3: Colimit Hadjiivanov Monodromy & Exchange S-Matrix Winding Transport
    =========================================================================== -/

section ColimitHadjiivanovMonodromy

/-- **Theorem 3.1 (`colimit_hadjiivanov_monodromy_and_exchange_smatrix_winding`):**
For any `TensorTowerColimit` system `(A, iota, A_inf, psi, psi_comm)` over `ℂ` and any stagewise
embedding `embedSBlock : ∀ n, SBlock →ₗ[ℂ] A n` commuting with `iota`
(`∀ n M, iota n (embedSBlock n M) = embedSBlock (n + 1) M`):
1. The `m`-step tensor-tower transport `iota_seq A iota n m` preserves every `k`-wrap
   Hadjiivanov monodromy `lowerHadjiivanovMonodromy h ^ k` and multi-block exchange S-matrix
   `lowerExchangeSMatrix blocks`;
2. The colimit evaluation `psi (n + m) (iota_seq A iota n m (embedSBlock n (lowerHadjiivanovMonodromy h ^ k)))`
   equals the stage-`n` evaluation `psi n (embedSBlock n (lowerParabolicSBlock (lcftPhase h ^ k) (k * logShearBase)))`;
3. For any multi-block exchange list `blocks : List (ℂ × ℂ)`, the colimit evaluation
   `psi n (embedSBlock n (lowerExchangeSMatrix blocks))` equals
   `psi n (embedSBlock n (lowerParabolicSBlock (lowerExchangePhase blocks) (lowerExchangeShear blocks)))`
   with zero upper-right leakage (`lowerExchangeSMatrix blocks 0 1 = 0`). -/
theorem colimit_hadjiivanov_monodromy_and_exchange_smatrix_winding
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)]
    (iota : ∀ n, A n →ₗ[ℂ] A (n + 1))
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, A n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (embedSBlock : ∀ n, SBlock →ₗ[ℂ] A n)
    (n m k : ℕ) (h : ℂ) (blocks : List (ℂ × ℂ)) :
    psi (n + m) (iota_seq A iota n m (embedSBlock n (lowerHadjiivanovMonodromy h ^ k))) =
      psi n (embedSBlock n (lowerParabolicSBlock (lcftPhase h ^ k) ((k : ℂ) * logShearBase))) ∧
    psi (n + m) (iota_seq A iota n m (embedSBlock n (lowerExchangeSMatrix blocks))) =
      psi n (embedSBlock n
        (lowerParabolicSBlock (lowerExchangePhase blocks) (lowerExchangeShear blocks))) ∧
    lowerExchangeSMatrix blocks 0 1 = 0 := by
  have hPsiSeq := congr_arg
    (fun (f : A n →ₗ[ℂ] A_inf) =>
      f (embedSBlock n (lowerHadjiivanovMonodromy h ^ k)))
    (psi_comp_iota_seq A iota A_inf psi psi_comm n m)
  have hPsiBlocks := congr_arg
    (fun (f : A n →ₗ[ℂ] A_inf) =>
      f (embedSBlock n (lowerExchangeSMatrix blocks)))
    (psi_comp_iota_seq A iota A_inf psi psi_comm n m)
  have hWinding :
      lowerHadjiivanovMonodromy h ^ k =
        lowerParabolicSBlock (lcftPhase h ^ k) ((k : ℂ) * logShearBase) :=
    lowerHadjiivanov_winding_exchange_constraint h k
  refine ⟨?_, ?_, lowerExchangeSMatrix_upper_right_zero blocks⟩
  · dsimp at hPsiSeq
    rw [hPsiSeq, hWinding]
  · dsimp at hPsiBlocks
    rw [hPsiBlocks, lowerExchangeSMatrix_eq_lowerParabolicSBlock]

end ColimitHadjiivanovMonodromy

/-! ===========================================================================
    Section 4: LogCFT Virasoro Rank-2 Jordan Cell ↔ `4 × 4` Krein–Hopf
    Double-Pole Resolvent Unification
    =========================================================================== -/

section LogCFTKreinHopfResolventUnification

/-- Universal rank-2 Jordan double-pole resolvent identity in any `R`-algebra `[Ring B] [Algebra R B]`:
for any square-zero operator `N * N = 0`,
`(algebraMap R B z - (algebraMap R B h + N)) * (algebraMap R B (z - h) + N) = algebraMap R B ((z - h) ^ 2)`. -/
theorem rank2_jordan_double_pole_resolvent
    {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]
    {N : B} (hN : N * N = 0) (z h : R) :
    (algebraMap R B z - (algebraMap R B h + N)) * (algebraMap R B (z - h) + N) =
      algebraMap R B ((z - h) ^ 2) ∧
    (algebraMap R B (z - h) + N) * (algebraMap R B z - (algebraMap R B h + N)) =
      algebraMap R B ((z - h) ^ 2) := by
  have hSub : algebraMap R B z - (algebraMap R B h + N) = algebraMap R B (z - h) - N := by
    rw [map_sub]
    abel
  have hComm : algebraMap R B (z - h) * N = N * algebraMap R B (z - h) :=
    Algebra.commutes (z - h) N
  refine ⟨?_, ?_⟩
  · rw [hSub]
    calc
      (algebraMap R B (z - h) - N) * (algebraMap R B (z - h) + N) =
        algebraMap R B (z - h) * algebraMap R B (z - h) +
          (algebraMap R B (z - h) * N - N * algebraMap R B (z - h)) - N * N := by
        noncomm_ring
      _ = algebraMap R B ((z - h) ^ 2) := by
        rw [hComm, sub_self, add_zero, hN, sub_zero, ← map_mul, sq]
  · rw [hSub]
    calc
      (algebraMap R B (z - h) + N) * (algebraMap R B (z - h) - N) =
        algebraMap R B (z - h) * algebraMap R B (z - h) -
          (algebraMap R B (z - h) * N - N * algebraMap R B (z - h)) - N * N := by
        noncomm_ring
      _ = algebraMap R B ((z - h) ^ 2) := by
        rw [hComm, sub_self, sub_zero, hN, sub_zero, ← map_mul, sq]

/-- Exact double-pole resolvent identity for the `2 × 2` Virasoro `L₀` Jordan cell `virasoroL0Cell h`. -/
theorem virasoroL0Cell_double_pole_resolvent {R : Type*} [CommRing R] (z h : R) :
    (z • (1 : Matrix (Fin 2) (Fin 2) R) - virasoroL0Cell h) *
      ((z - h) • (1 : Matrix (Fin 2) (Fin 2) R) + jordanNilpotent) =
      (z - h) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [virasoroL0Cell, upperJordan, jordanNilpotent] <;> ring

/-- Decomposition of the `4 × 4` Kronecker lift `kronIdLeft4 (virasoroL0Cell h)` into `h • 1 + kronIdLeft4 jordanNilpotent`. -/
theorem kronIdLeft4_virasoroL0Cell_decomp {R : Type*} [CommRing R] (h : R) :
    kronIdLeft4 (virasoroL0Cell h) =
      h • (1 : Matrix (Fin 4) (Fin 4) R) + kronIdLeft4 (jordanNilpotent (K := R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronIdLeft4, virasoroL0Cell, upperJordan, jordanNilpotent]

/-- Square-zero law for the `4 × 4` Kronecker lift `kronIdLeft4 jordanNilpotent`. -/
theorem kronIdLeft4_jordanNilpotent_sq_zero {R : Type*} [CommRing R] :
    kronIdLeft4 (jordanNilpotent (K := R)) * kronIdLeft4 (jordanNilpotent (K := R)) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, jordanNilpotent]

/-- Exact double-pole resolvent identity for the `4 × 4` Krein–Hamiltonian–Hopf generator at the crash point. -/
theorem kreinHopf_double_pole_resolvent {R : Type*} [CommRing R] (z wBar dw : R) :
    (z • (1 : Matrix (Fin 4) (Fin 4) R) -
      (wBar • (1 : Matrix (Fin 4) (Fin 4) R) + kreinCrashNilpotent dw)) *
      ((z - wBar) • (1 : Matrix (Fin 4) (Fin 4) R) + kreinCrashNilpotent dw) =
      (z - wBar) ^ 2 • (1 : Matrix (Fin 4) (Fin 4) R) := by
  have hKreinNil : kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0 :=
    (kreinHamiltonianHopf_bifurcation (0 : R) dw dw).2.2.2
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (rank2_jordan_double_pole_resolvent hKreinNil z wBar).1

/-- **Theorem 4.1 (`universal_rank2_jordan_double_pole_resolvent_and_virasoro_krein_bridge`):**
1. **Universal Non-Commutative Rank-2 Jordan Double-Pole Resolvent:**
   In any associative ring `[Ring B]` with `[Algebra R B]` (`[CommRing R]`), for any square-zero
   operator `N : B` (`N * N = 0`) and scalars `z h : R`, the shifted rank-2 Jordan operator
   `L := algebraMap R B h + N` and unnormalized resolvent numerator
   `R_num := algebraMap R B (z - h) + N` satisfy the exact double-pole identity:
   `(algebraMap R B z - L) * R_num = algebraMap R B ((z - h) ^ 2)` and
   `R_num * (algebraMap R B z - L) = algebraMap R B ((z - h) ^ 2)`.
2. **`2 × 2` Virasoro `L₀` Jordan Cell Realization (`LogCftMonodromy.virasoroL0Cell`):**
   On `Matrix (Fin 2) (Fin 2) R`,
   `(z • 1 - virasoroL0Cell h) * ((z - h) • 1 + jordanNilpotent) = (z - h) ^ 2 • 1`.
3. **`4 × 4` Kronecker Lift & Krein–Hamiltonian–Hopf Exceptional Point Realization:**
   On `Matrix (Fin 4) (Fin 4) R`:
   - `kronIdLeft4 (virasoroL0Cell h) = h • 1 + kronIdLeft4 jordanNilpotent` with
     `kronIdLeft4 jordanNilpotent * kronIdLeft4 jordanNilpotent = 0`,
   - `kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0` and
     `(z • 1 - (wBar • 1 + kreinCrashNilpotent dw)) * ((z - wBar) • 1 + kreinCrashNilpotent dw) = (z - wBar) ^ 2 • 1`. -/
theorem universal_rank2_jordan_double_pole_resolvent_and_virasoro_krein_bridge
    {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]
    {N : B} (hN : N * N = 0) (z h wBar dw : R) :
    let L : B := algebraMap R B h + N
    let R_num : B := algebraMap R B (z - h) + N
    ((algebraMap R B z - L) * R_num = algebraMap R B ((z - h) ^ 2) ∧
     R_num * (algebraMap R B z - L) = algebraMap R B ((z - h) ^ 2)) ∧
    (((z • (1 : Matrix (Fin 2) (Fin 2) R) - virasoroL0Cell h) *
        ((z - h) • (1 : Matrix (Fin 2) (Fin 2) R) + jordanNilpotent) =
        (z - h) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) R)) ∧
     kronIdLeft4 (virasoroL0Cell h) =
       h • (1 : Matrix (Fin 4) (Fin 4) R) + kronIdLeft4 (jordanNilpotent (K := R)) ∧
     kronIdLeft4 (jordanNilpotent (K := R)) * kronIdLeft4 (jordanNilpotent (K := R)) = 0 ∧
     kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0 ∧
     (z • (1 : Matrix (Fin 4) (Fin 4) R) -
        (wBar • (1 : Matrix (Fin 4) (Fin 4) R) + kreinCrashNilpotent dw)) *
       ((z - wBar) • (1 : Matrix (Fin 4) (Fin 4) R) + kreinCrashNilpotent dw) =
       (z - wBar) ^ 2 • (1 : Matrix (Fin 4) (Fin 4) R)) :=
  ⟨rank2_jordan_double_pole_resolvent hN z h,
   virasoroL0Cell_double_pole_resolvent z h,
   kronIdLeft4_virasoroL0Cell_decomp h,
   kronIdLeft4_jordanNilpotent_sq_zero,
   (kreinHamiltonianHopf_bifurcation (0 : R) dw dw).2.2.2,
   kreinHopf_double_pole_resolvent z wBar dw⟩

/-- Elementary Peirce projector `E₀₀` on `Matrix (Fin 2) (Fin 2) R`. -/
def peirce00Mat2 {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![(1 : R), 0; 0, 0]

/-- Elementary Virasoro nilpotent Jordan partner `E₀₁` on `Matrix (Fin 2) (Fin 2) R`. -/
def virasoroNilpotentMat2 {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![(0 : R), 1; 0, 0]

/-- Exact non-commutativity of `peirce00Mat2` and `virasoroNilpotentMat2` on `Matrix (Fin 2) (Fin 2) R`
for any nontrivial ring `R`. -/
theorem peirce00Mat2_mul_virasoroNilpotentMat2_ne {R : Type*} [CommRing R] [Nontrivial R] :
    (peirce00Mat2 : Matrix (Fin 2) (Fin 2) R) * (virasoroNilpotentMat2 : Matrix (Fin 2) (Fin 2) R) ≠
      (virasoroNilpotentMat2 : Matrix (Fin 2) (Fin 2) R) * (peirce00Mat2 : Matrix (Fin 2) (Fin 2) R) := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [peirce00Mat2, virasoroNilpotentMat2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Elementary `4 × 4` projector `E₀₀` on `Matrix (Fin 4) (Fin 4) R`. -/
def peirce00Mat4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Elementary `4 × 4` Jordan partner `E₀₁` on `Matrix (Fin 4) (Fin 4) R`. -/
def jordanNilpotentMat4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Exact non-commutativity of `peirce00Mat4` and `jordanNilpotentMat4` on `Matrix (Fin 4) (Fin 4) R`
for any nontrivial ring `R`. -/
theorem peirce00Mat4_mul_jordanNilpotentMat4_ne {R : Type*} [CommRing R] [Nontrivial R] :
    (peirce00Mat4 : Matrix (Fin 4) (Fin 4) R) * (jordanNilpotentMat4 : Matrix (Fin 4) (Fin 4) R) ≠
      (jordanNilpotentMat4 : Matrix (Fin 4) (Fin 4) R) * (peirce00Mat4 : Matrix (Fin 4) (Fin 4) R) := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [peirce00Mat4, jordanNilpotentMat4, Matrix.mul_apply] at h01

end LogCFTKreinHopfResolventUnification

end InfoGeometry.Categorical.FibonacciBraidedCategoryLogCFTExchangeSynthesis
