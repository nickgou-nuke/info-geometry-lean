/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.Physics.BraidIdealDescent
import InfoGeometry.Physics.ChiralTLDescent
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Algebra.IdempotentCornerCommutant

/-!
# Color and tensor-product occupation readouts

This module proves finite identities for a triple tensor product of two-state
matrix algebras and for separate imported Clifford-CAR and braid carriers.
The local tensor-factor operators below are not claimed to satisfy graded
cross-mode CAR relations.  Furey/Standard-Model terminology is naming
motivation only: no theorem here identifies the tensor span with a Clifford
minimal left ideal or identifies its states with physical fermions.
-/

noncomputable section

namespace InfoGeometry.Physics.ColorCARStandardModel

open Matrix
open TensorProduct
open ChiralCausalCone
open ChiralTensorRecoupling
open BraidIdealDescent
open ChiralTLDescent

/-! ## CAR submodule — τ-ideal stability

The CAR submodule `R_CAR` is the span of the 4 basis tensors that generate
the TL projector `e`. Because `tauL (qCrossMap Complex.I)` acts as
`Complex.I • flip` on any tensor in `SpinPair` (`tauL_qCrossMap_on_any`), any
submodule of `SpinPair`—and in particular `R_CAR`—is a left `τ`-ideal. -/

/-- The chiral CAR submodule: span of the 4 basis tensors that generate the
TL projector `e = σ⁺⊗σ⁻ + σ⁻⊗σ⁺ + ½(I⊗I - σ₃⊗σ₃)`. -/
def R_CAR : Submodule ℂ SpinPair :=
  Submodule.span ℂ {σPlus ⊗ₜ[ℂ] σMinus, σMinus ⊗ₜ[ℂ] σPlus,
    (1 : M2C) ⊗ₜ[ℂ] (1 : M2C), σ3c ⊗ₜ[ℂ] σ3c}

/-- The TL generator `e` is in `R_CAR`. Each of X, Y, Z is a basis element
or linear combination thereof. -/
theorem e_mem_R_CAR : e ∈ R_CAR := by
  dsimp [R_CAR, ChiralTensorRecoupling.e, ChiralTensorRecoupling.X,
    ChiralTensorRecoupling.Y, ChiralTensorRecoupling.Z]
  -- X = σ⁺⊗σ⁻ is the 1st basis element
  have hX : σPlus ⊗ₜ[ℂ] σMinus ∈ Submodule.span ℂ
      {σPlus ⊗ₜ[ℂ] σMinus, σMinus ⊗ₜ[ℂ] σPlus, (1 : M2C) ⊗ₜ[ℂ] (1 : M2C), σ3c ⊗ₜ[ℂ] σ3c} := by
    apply Submodule.subset_span; simp
  -- Y = σ⁻⊗σ⁺ is the 2nd basis element
  have hY : σMinus ⊗ₜ[ℂ] σPlus ∈ Submodule.span ℂ
      {σPlus ⊗ₜ[ℂ] σMinus, σMinus ⊗ₜ[ℂ] σPlus, (1 : M2C) ⊗ₜ[ℂ] (1 : M2C), σ3c ⊗ₜ[ℂ] σ3c} := by
    apply Submodule.subset_span; simp
  -- Z = ½(I⊗I - σ₃⊗σ₃) is a linear combination of the 3rd and 4th basis elements
  have hZ : ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) ∈ Submodule.span ℂ
      {σPlus ⊗ₜ[ℂ] σMinus, σMinus ⊗ₜ[ℂ] σPlus, (1 : M2C) ⊗ₜ[ℂ] (1 : M2C), σ3c ⊗ₜ[ℂ] σ3c} := by
    refine Submodule.smul_mem _ (1/2 : ℂ) (Submodule.sub_mem _ ?_ ?_)
    · apply Submodule.subset_span; simp
    · apply Submodule.subset_span; simp
  -- e = X + Y + Z ∈ R_CAR
  exact Submodule.add_mem _ (Submodule.add_mem _ hX hY) hZ

/-- The CAR submodule is a left τ-ideal for `qCrossMap Complex.I`.
Since `tauL (qCrossMap Complex.I) (η ⊗ v) = Complex.I • (v ⊗ η)` for any
`v ∈ SpinPair` (by `tauL_qCrossMap_on_any`), any submodule of `SpinPair` (and in
particular `R_CAR`) satisfies `IsLeftTauIdeal` because `v ⊗ η ∈ leftTarget R_CAR`
whenever `v ∈ R_CAR`. -/
theorem car_submodule_is_left_tau_ideal :
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C)
    R_CAR (qCrossMap (K := ℂ) Complex.I) := by
  intro eta r
  -- r : R_CAR, so r.val ∈ R_CAR
  have h_r : r.val ∈ R_CAR := r.property
  -- The key identity: tauL (qCrossMap i) (η ⊗ v) = i·(v ⊗ η)
  rw [tauL_qCrossMap_on_any eta r.val]
  -- Now we need: i·(r.val ⊗ η) ∈ leftTarget R_CAR
  -- Since r.val ∈ R_CAR, the tensor r.val ⊗ η is in the range of map (R_CAR.subtype) id
  have h_base : r.val ⊗ₜ[ℂ] eta ∈ leftTarget (H := M2C) (H_dual := M2C) R_CAR := by
    unfold leftTarget
    apply LinearMap.mem_range.mpr
    refine ⟨⟨r.val, h_r⟩ ⊗ₜ[ℂ] eta, ?_⟩
    simp
  -- leftTarget is a Submodule, closed under scalar multiplication
  exact Submodule.smul_mem _ Complex.I h_base

/-! ## Triple tensor product — finite eight-generator span

Each tensor factor has a local pair `(σ⁺, σ⁻)`.  The raw tensor product here
does not insert the parity strings needed for cross-mode fermionic CAR
relations; the eight displayed expressions define only a finite subspace. -/

/-- Three copies of the CAR algebra: triple tensor product of M2C. -/
abbrev CAR3 : Type := M2C ⊗[ℂ] M2C ⊗[ℂ] M2C

/- Bind the native Mathlib tensor-algebra instances explicitly at each layer. -/
instance spinPairSemiring : Semiring SpinPair :=
  Algebra.TensorProduct.instSemiring
instance spinPairRing : Ring SpinPair :=
  Algebra.TensorProduct.instRing
instance spinPairNonAssocSemiring : NonAssocSemiring SpinPair :=
  spinPairSemiring.toNonAssocSemiring
instance spinPairNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring SpinPair :=
  spinPairSemiring.toNonUnitalNonAssocSemiring
instance spinPairNonAssocRing : NonAssocRing SpinPair :=
  spinPairRing.toNonAssocRing
instance spinPairNonUnitalNonAssocRing : NonUnitalNonAssocRing SpinPair :=
  spinPairRing.toNonAssocRing.toNonUnitalNonAssocRing
instance spinPairAlgebra : Algebra ℂ SpinPair :=
  Algebra.TensorProduct.instAlgebra
instance car3Semiring : Semiring CAR3 :=
  Algebra.TensorProduct.instSemiring
instance car3Ring : Ring CAR3 :=
  Algebra.TensorProduct.instRing
instance car3NonAssocSemiring : NonAssocSemiring CAR3 :=
  car3Semiring.toNonAssocSemiring
instance car3NonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring CAR3 :=
  car3Semiring.toNonUnitalNonAssocSemiring
instance car3NonAssocRing : NonAssocRing CAR3 :=
  car3Ring.toNonAssocRing
instance car3NonUnitalNonAssocRing : NonUnitalNonAssocRing CAR3 :=
  car3Ring.toNonAssocRing.toNonUnitalNonAssocRing
instance car3Algebra : Algebra ℂ CAR3 :=
  Algebra.TensorProduct.instAlgebra

/-- CAR annihilation operator σ⁺ on factor i ∈ {0,1,2}. -/
def carAnn0 : CAR3 := σPlus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
def carAnn1 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] σPlus ⊗ₜ[ℂ] (1 : M2C)
def carAnn2 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] σPlus

/-- CAR creation operator σ⁻ on factor i ∈ {0,1,2}. -/
def carCre0 : CAR3 := σMinus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
def carCre1 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] σMinus ⊗ₜ[ℂ] (1 : M2C)
def carCre2 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] σMinus

/-- The identity tensor `1 ⊗ 1 ⊗ 1` in `CAR3`. -/
def vacuum : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)

/-- The finite span of the eight displayed CAR triple-product generators.

The particle labels from the Furey literature are not asserted as Lean theorems
in this file. -/
def fureyGeneration : Submodule ℂ CAR3 :=
  Submodule.span ℂ {
    vacuum,
    carCre0, carCre1, carCre2,
    carCre0 * carCre1, carCre1 * carCre2, carCre0 * carCre2,
    carCre0 * carCre1 * carCre2
  }

/-! The exterior/Clifford bridges use the native `Cl(5,5)` positive-chiral
channels.  Keep that carrier separate from the tensor-product CAR span above.
-/

/-- The real span of the three native positive-chiral `Cl(5,5)` generators.
This is the conjugate landing carrier for the exterior restriction bridges. -/
def fureyConjugateGeneration :
    Submodule ℝ InfoGeometry.Clifford.Clifford55.Cl55 :=
  Submodule.span ℝ (Set.range InfoGeometry.Clifford.Clifford55.chiralPlus55)

/-- Each native positive-chiral channel belongs to the conjugate landing span. -/
theorem carAnn_mem_fureyConjugateGeneration (i : Fin 3) :
    InfoGeometry.Clifford.Clifford55.chiralPlus55 i ∈ fureyConjugateGeneration := by
  apply Submodule.subset_span
  exact ⟨i, rfl⟩

/-! ## Factor projectors `numberOp` ($a_k a_k^\dagger$) and `excitationOp` ($a_k^\dagger a_k$)

With `carAnn_k` built from `σPlus` ($a_k$) and `carCre_k` built from `σMinus`
($a_k^\dagger$):
* `numberOp0/1/2 := carAnn_k * carCre_k` are the positive-chiral factor
  projectors $a_k a_k^\dagger = \sigma^+_k \sigma^-_k = N_+$ (which project onto
  the factor annihilated by $a_k = \sigma^+$).
* `excitationOp0/1/2 := carCre_k * carAnn_k` are the complementary
  negative-chiral factor projectors $a_k^\dagger a_k = \sigma^-_k \sigma^+_k = N_-$
  (which project onto the factor created by $a_k^\dagger = \sigma^-$). -/

/-- Positive-chiral factor projector on ladder k: `numberOp_k = carAnn_k * carCre_k`
($a_k a_k^\dagger = \sigma^+_k \sigma^-_k$). -/
def numberOp0 : CAR3 := carAnn0 * carCre0
def numberOp1 : CAR3 := carAnn1 * carCre1
def numberOp2 : CAR3 := carAnn2 * carCre2

/-- Negative-chiral excitation projector on ladder k:
`excitationOp_k = carCre_k * carAnn_k` ($a_k^\dagger a_k = \sigma^-_k \sigma^+_k$). -/
def excitationOp0 : CAR3 := carCre0 * carAnn0
def excitationOp1 : CAR3 := carCre1 * carAnn1
def excitationOp2 : CAR3 := carCre2 * carAnn2

/-- The key matrix lemma is the existing positive-chirality projector theorem. -/
private lemma σPlus_mul_σMinus_sq : (σPlus * σMinus) * (σPlus * σMinus) = σPlus * σMinus := by
  simpa [PPlus] using PPlus_idempotent

/-- Complementary matrix lemma from the negative-chirality projector theorem. -/
private lemma σMinus_mul_σPlus_sq : (σMinus * σPlus) * (σMinus * σPlus) = σMinus * σPlus := by
  simpa [PMinus] using PMinus_idempotent

/-! ## Chiral projectors `N₊ = σ⁺σ⁻`, `N₋ = σ⁻σ⁺`

The chiral projectors are the fundamental idempotent building blocks of the
single-mode CAR algebra. Their sum is the identity and their difference is the
chirality grading `σ₃`. -/

/-- `N₊ = σ⁺σ⁻` — positive-chiral vacancy projector annihilated on the left by `σ⁺`. -/
def N_plus : M2C := σPlus * σMinus

/-- `N₋ = σ⁻σ⁺` — negative-chiral excitation projector created on the left by `σ⁻`. -/
def N_minus : M2C := σMinus * σPlus

/-- Sum is identity: `N₊ + N₋ = I`. The chiral projectors partition unity. -/
theorem N_plus_add_N_minus : N_plus + N_minus = (1 : M2C) := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_add_PMinus

/-- Difference is the CPT compass: `N₊ - N₋ = σ₃`. The Cartan grading
operator is the difference of the chiral projectors. -/
theorem N_plus_sub_N_minus : N_plus - N_minus = σ3c := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_sub_PMinus

/-- Orthogonality: `N₊ * N₋ = 0`. -/
theorem N_plus_mul_N_minus : N_plus * N_minus = (0 : M2C) := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_PMinus_orthogonal

/-- Orthogonality: `N₋ * N₊ = 0`. Symmetric. -/
theorem N_minus_mul_N_plus : N_minus * N_plus = (0 : M2C) := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PMinus_PPlus_orthogonal

/-- The positive-chiral projector `N₊` is idempotent. -/
theorem N_plus_idempotent : N_plus * N_plus = N_plus := by
  simpa [N_plus, PPlus] using PPlus_idempotent

/-- The negative-chiral projector `N₋` is idempotent. -/
theorem N_minus_idempotent : N_minus * N_minus = N_minus := by
  simpa [N_minus, PMinus] using PMinus_idempotent

/-- `σ⁺` annihilates `N₊` from the left: `σ⁺ N₊ = (σ⁺)² σ⁻ = 0`. -/
@[simp]
theorem σPlus_mul_N_plus : σPlus * N_plus = (0 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, N_plus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ⁻` acts as creation on `N₊` from the left: `σ⁻ N₊ = σ⁻ σ⁺ σ⁻ = σ⁻`. -/
@[simp]
theorem σMinus_mul_N_plus : σMinus * N_plus = σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, N_plus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ₃` fixes `N₊` from the left: `σ₃ N₊ = N₊`. -/
@[simp]
theorem σ3c_mul_N_plus : σ3c * N_plus = N_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σPlus, N_plus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Number operator idempotence: `N₀² = N₀`.
Lifts the 2×2 projector identity to the triple tensor product. -/
theorem numberOp0_idem : numberOp0 * numberOp0 = numberOp0 := by
  dsimp [numberOp0, carAnn0, carCre0]
  simp [σPlus_mul_σMinus_sq]

/-- Number operator idempotence: `N₁² = N₁`. -/
theorem numberOp1_idem : numberOp1 * numberOp1 = numberOp1 := by
  dsimp [numberOp1, carAnn1, carCre1]
  simp [σPlus_mul_σMinus_sq]

/-- Number operator idempotence: `N₂² = N₂`. -/
theorem numberOp2_idem : numberOp2 * numberOp2 = numberOp2 := by
  dsimp [numberOp2, carAnn2, carCre2]
  simp [σPlus_mul_σMinus_sq]

/-- Excitation operator idempotence: `excitationOp0² = excitationOp0`. -/
theorem excitationOp0_idem : excitationOp0 * excitationOp0 = excitationOp0 := by
  dsimp [excitationOp0, carCre0, carAnn0]
  simp [σMinus_mul_σPlus_sq]

/-- Excitation operator idempotence: `excitationOp1² = excitationOp1`. -/
theorem excitationOp1_idem : excitationOp1 * excitationOp1 = excitationOp1 := by
  dsimp [excitationOp1, carCre1, carAnn1]
  simp [σMinus_mul_σPlus_sq]

/-- Excitation operator idempotence: `excitationOp2² = excitationOp2`. -/
theorem excitationOp2_idem : excitationOp2 * excitationOp2 = excitationOp2 := by
  dsimp [excitationOp2, carCre2, carAnn2]
  simp [σMinus_mul_σPlus_sq]

/-- The tensor product of the three positive-chiral vacancy projectors `N₊` is the
vacuum idempotent in the finite three-mode CAR carrier: it is annihilated on the
left by `carAnn0`, `carAnn1`, `carAnn2` (built from `σ⁺`) and supports non-zero
creation states under left multiplication by `carCre0`, `carCre1`, `carCre2`
(built from `σ⁻`). -/
def fureyVacuumIdempotent : CAR3 :=
  N_plus ⊗ₜ[ℂ] N_plus ⊗ₜ[ℂ] N_plus

/-- The submodule model of the principal left ideal generated by the finite
three-mode vacuum idempotent. -/
def fureyVacuumLeftIdeal : Submodule ℂ CAR3 :=
  InfoGeometry.Algebra.IdempotentCornerCommutant.principalLeftIdealSubmodule
    (R := ℂ) fureyVacuumIdempotent

/-- The finite three-mode vacuum generator is idempotent. -/
theorem fureyVacuumIdempotent_sq :
    fureyVacuumIdempotent * fureyVacuumIdempotent = fureyVacuumIdempotent := by
  dsimp [fureyVacuumIdempotent]
  simp [N_plus_idempotent]

/-- Mode-0 annihilation operator annihilates the vacuum idempotent. -/
theorem carAnn0_mul_fureyVacuumIdempotent :
    carAnn0 * fureyVacuumIdempotent = 0 := by
  dsimp [carAnn0, fureyVacuumIdempotent]
  simp [σPlus_mul_N_plus]

/-- Mode-1 annihilation operator annihilates the vacuum idempotent. -/
theorem carAnn1_mul_fureyVacuumIdempotent :
    carAnn1 * fureyVacuumIdempotent = 0 := by
  dsimp [carAnn1, fureyVacuumIdempotent]
  simp [σPlus_mul_N_plus]

/-- Mode-2 annihilation operator annihilates the vacuum idempotent. -/
theorem carAnn2_mul_fureyVacuumIdempotent :
    carAnn2 * fureyVacuumIdempotent = 0 := by
  dsimp [carAnn2, fureyVacuumIdempotent]
  simp [σPlus_mul_N_plus]

/-- The top three-mode creation state on the vacuum idempotent evaluates to
`σ⁻ ⊗ σ⁻ ⊗ σ⁻`. -/
theorem furey_top_creation_state_eq :
    ((carCre0 * carCre1) * carCre2) * fureyVacuumIdempotent =
      σMinus ⊗ₜ[ℂ] σMinus ⊗ₜ[ℂ] σMinus := by
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent]
  simp [σMinus_mul_N_plus]

/-- Linear readout `(a ⊗ b) ⊗ c ↦ a₁₀ · b₁₀ · c₁₀` detecting `σ⁻ ⊗ σ⁻ ⊗ σ⁻`. -/
def readoutMinus3 : CAR3 →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun (x : M2C ⊗[ℂ] M2C) (c : M2C) =>
        TensorProduct.lift
          (LinearMap.mk₂ ℂ (fun (a b : M2C) => a 1 0 * b 1 0)
            (fun a₁ a₂ b => by simp [add_mul])
            (fun r a b => by simp [mul_assoc])
            (fun a b₁ b₂ => by simp [mul_add])
            (fun r a b => by simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_left_comm _ _ _)) x * c 1 0)
      (fun x₁ x₂ c => by simp [add_mul])
      (fun r x c => by simp [mul_assoc])
      (fun x c₁ c₂ => by simp [mul_add])
      (fun r x c => by simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_left_comm _ _ _))

@[simp]
theorem readoutMinus3_tmul (a b c : M2C) :
    readoutMinus3 (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] c) = a 1 0 * b 1 0 * c 1 0 := by
  simp [readoutMinus3]

/-- The pure tensor `σ⁻ ⊗ σ⁻ ⊗ σ⁻` is non-zero in `CAR3`. -/
theorem σMinus_tmul_three_ne_zero :
    (σMinus ⊗ₜ[ℂ] σMinus ⊗ₜ[ℂ] σMinus : CAR3) ≠ 0 := by
  intro h
  have h1 := congrArg readoutMinus3 h
  simp [readoutMinus3_tmul, σMinus] at h1

/-- The top three-mode creation state on the vacuum idempotent is non-zero. -/
theorem furey_top_creation_state_ne_zero :
    ((carCre0 * carCre1) * carCre2) * fureyVacuumIdempotent ≠ 0 := by
  rw [furey_top_creation_state_eq]
  exact σMinus_tmul_three_ne_zero

/-- The vacuum idempotent itself is non-zero. -/
theorem fureyVacuumIdempotent_ne_zero :
    fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : ((carCre0 * carCre1) * carCre2) * fureyVacuumIdempotent = 0 := by
    rw [h, mul_zero]
  exact furey_top_creation_state_ne_zero h1

/-- Mode-0 one-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre0_mul_fureyVacuumIdempotent_ne_zero :
    carCre0 * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : (carCre1 * carCre2) * (carCre0 * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Mode-1 one-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre1_mul_fureyVacuumIdempotent_ne_zero :
    carCre1 * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : (carCre0 * carCre2) * (carCre1 * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Mode-2 one-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre2_mul_fureyVacuumIdempotent_ne_zero :
    carCre2 * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : (carCre0 * carCre1) * (carCre2 * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Modes 0 and 1 two-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre0_carCre1_mul_fureyVacuumIdempotent_ne_zero :
    (carCre0 * carCre1) * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : carCre2 * ((carCre0 * carCre1) * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Modes 1 and 2 two-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre1_carCre2_mul_fureyVacuumIdempotent_ne_zero :
    (carCre1 * carCre2) * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : carCre0 * ((carCre1 * carCre2) * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Modes 0 and 2 two-particle creation state on the vacuum idempotent is non-zero. -/
theorem carCre0_carCre2_mul_fureyVacuumIdempotent_ne_zero :
    (carCre0 * carCre2) * fureyVacuumIdempotent ≠ 0 := by
  intro h
  have h1 : carCre1 * ((carCre0 * carCre2) * fureyVacuumIdempotent) = 0 := by
    rw [h, mul_zero]
  dsimp [carCre0, carCre1, carCre2, fureyVacuumIdempotent] at h1
  simp [σMinus_mul_N_plus] at h1
  exact σMinus_tmul_three_ne_zero h1

/-- Every element generated as `x * e` belongs to the principal left ideal
`Ae` when `e` is the idempotent vacuum generator. -/
theorem mul_fureyVacuumIdempotent_mem (x : CAR3) :
    x * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal := by
  let _ : Semigroup CAR3 := car3Semiring.toSemigroup
  change (x * fureyVacuumIdempotent) * fureyVacuumIdempotent =
    x * fureyVacuumIdempotent
  rw [mul_assoc, fureyVacuumIdempotent_sq]

/-- The generated finite vacuum left ideal is stable under left
multiplication by the CAR algebra. -/
theorem fureyVacuumLeftIdeal_left_mul_closed (a x : CAR3)
    (hx : x ∈ fureyVacuumLeftIdeal) :
    a * x ∈ fureyVacuumLeftIdeal := by
  let _ : Semigroup CAR3 := car3Semiring.toSemigroup
  change (a * x) * fureyVacuumIdempotent = a * x
  change x * fureyVacuumIdempotent = x at hx
  simp [mul_assoc, hx]

/-- Each displayed finite creation monomial belongs to the principal left
ideal generated by the vacuum idempotent. This is an algebraic membership
statement; it does not assert a particle-physics interpretation. -/
theorem furey_creation_states_mem_fureyVacuumLeftIdeal :
    carCre0 * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      carCre1 * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      carCre2 * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      (carCre0 * carCre1) * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      (carCre1 * carCre2) * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      (carCre0 * carCre2) * fureyVacuumIdempotent ∈ fureyVacuumLeftIdeal ∧
      ((carCre0 * carCre1) * carCre2) * fureyVacuumIdempotent ∈
        fureyVacuumLeftIdeal := by
  exact ⟨mul_fureyVacuumIdempotent_mem carCre0,
    mul_fureyVacuumIdempotent_mem carCre1,
    mul_fureyVacuumIdempotent_mem carCre2,
    mul_fureyVacuumIdempotent_mem (carCre0 * carCre1),
    mul_fureyVacuumIdempotent_mem (carCre1 * carCre2),
    mul_fureyVacuumIdempotent_mem (carCre0 * carCre2),
    mul_fureyVacuumIdempotent_mem ((carCre0 * carCre1) * carCre2)⟩


/-- Synthesis of the CAR generation structure:
The CAR submodule is a left τ-ideal. The chiral projectors N₊, N₋ partition unity,
their difference is the CPT compass σ₃, and they are orthogonal.
The ladder projectors are idempotent. -/
theorem color_car_standard_model_synthesis :
    e ∈ R_CAR ∧
    IsLeftTauIdeal (K := ℂ) (H := M2C) (H_dual := M2C) R_CAR (qCrossMap (K := ℂ) Complex.I) ∧
    N_plus + N_minus = 1 ∧
    N_plus - N_minus = σ3c ∧
    N_plus * N_minus = 0 ∧
    N_minus * N_plus = 0 ∧
    numberOp0 * numberOp0 = numberOp0 ∧
    numberOp1 * numberOp1 = numberOp1 ∧
    numberOp2 * numberOp2 = numberOp2 := by
  exact ⟨e_mem_R_CAR,
    car_submodule_is_left_tau_ideal,
    N_plus_add_N_minus,
    N_plus_sub_N_minus,
    N_plus_mul_N_minus,
    N_minus_mul_N_plus,
    numberOp0_idem,
    numberOp1_idem,
    numberOp2_idem⟩

end InfoGeometry.Physics.ColorCARStandardModel
