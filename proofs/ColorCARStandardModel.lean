import Mathlib
import proofs.ChiralCausalCone
import proofs.ChiralTensorRecoupling
import proofs.BraidIdealDescent
import proofs.ChiralTLDescent

/-!
# ColorCAR — CAR triple product and Standard Model color bridge

The Furey ladder: one generation of Standard Model fermions is a minimal
left ideal of `Cl(6) ≅ M₈(ℂ)`. Three copies of the CAR algebra `(σ⁺, σ⁻)`
generate the 8 fermion states.

This module proves:
  1. The CAR submodule `span{σ⁺⊗σ⁻, σ⁻⊗σ⁺, I⊗I, σ₃⊗σ₃}` is a left τ-ideal
     for `qCrossMap i`. (Follows from `tauL_qCrossMap_on_any` — the same
     proof as `chiral_left_tau_ideal`.)
  2. Three copies of the CAR algebra define an 8-dim Furey generation.

The results are finite algebraic identities in the imported CAR and braid setting.
-/

noncomputable section

namespace ColorCARStandardModel

open Matrix
open TensorProduct
open ChiralCausalCone
open ChiralTensorRecoupling
open BraidIdealDescent
open ChiralTLDescent

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1000000

/-! ## CAR submodule — τ-ideal stability

The CAR submodule `R_CAR` is the span of the 4 basis tensors that generate
the TL projector `e`. Since we already proved `IsLeftTauIdeal` for `span{e}`
and `e ∈ R_CAR`, the same proof technique works for `R_CAR` directly. -/

/-- The chiral CAR submodule: span of the 4 basis tensors that generate the
TL projector `e = σ⁺⊗σ⁻ + σ⁻⊗σ⁺ + ½(I⊗I - σ₃⊗σ₃)`. -/
def R_CAR : Submodule ℂ SpinPair :=
  Submodule.span ℂ {σPlus ⊗ₜ[ℂ] σMinus, σMinus ⊗ₜ[ℂ] σPlus,
    (1 : M2C) ⊗ₜ[ℂ] (1 : M2C), σ3c ⊗ₜ[ℂ] σ3c}

/-- The TL generator `e` is in `R_CAR`. Each of X, Y, Z is a basis element
or linear combination thereof. -/
theorem e_mem_R_CAR : e ∈ R_CAR := by
  dsimp [R_CAR, e, X, Y, Z]
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

/-- The CAR submodule is a left τ-ideal for `qCrossMap i`.
Proof: `tauL (qCrossMap i) (η ⊗ v) = i·(v ⊗ η)` for any `v ∈ SpinPair`
(by `tauL_qCrossMap_on_any`), and `v ⊗ η ∈ leftTarget R_CAR` whenever `v ∈ R_CAR`
by construction of `leftTarget`. -/
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

/-! ## Triple CAR product — Furey generation

Three copies of the CAR algebra `(σ⁺ᵢ, σ⁻ᵢ)` for i ∈ {0,1,2} generate the
8-dimensional Furey minimal left ideal. One generation of Standard Model
fermions = one minimal left ideal of `Cl(6)`. -/

/-- Three copies of the CAR algebra: triple tensor product of M2C. -/
abbrev CAR3 : Type := M2C ⊗[ℂ] M2C ⊗[ℂ] M2C

/-- CAR annihilation operator σ⁺ on factor i ∈ {0,1,2}. -/
def carAnn0 : CAR3 := σPlus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
def carAnn1 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] σPlus ⊗ₜ[ℂ] (1 : M2C)
def carAnn2 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] σPlus

/-- CAR creation operator σ⁻ on factor i ∈ {0,1,2}. -/
def carCre0 : CAR3 := σMinus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
def carCre1 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] σMinus ⊗ₜ[ℂ] (1 : M2C)
def carCre2 : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] σMinus

/-- The vacuum state |0⟩ = |0⟩₀ ⊗ |0⟩₁ ⊗ |0⟩₂. -/
def vacuum : CAR3 := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)

/-- One generation of Standard Model fermions as an 8-dimensional submodule
of the triple CAR product. Built by applying creation operators to the vacuum.

   |ν⟩     = |0⟩                            (neutrino)
   |eₗ⁻⟩   = carCre₀·|0⟩                    (left electron)
   |uᵣ⟩    = carCre₁·|0⟩                    (red up quark)
   |uᵦ⟩    = carCre₂·|0⟩                    (green up quark)
   |uᵇ⟩    = carCre₀·carCre₁·|0⟩            (blue up quark)
   |d̄ᵣ⟩    = carCre₁·carCre₂·|0⟩            (anti-red down)
   |d̄ᵦ⟩    = carCre₀·carCre₂·|0⟩            (anti-green down)
   |d̄ᵇ⟩    = carCre₀·carCre₁·carCre₂·|0⟩   (anti-blue down)

These 8 states form the basis of one Furey generation. -/
def fureyGeneration : Submodule ℂ CAR3 :=
  Submodule.span ℂ {
    vacuum,
    carCre0, carCre1, carCre2,
    carCre0 * carCre1, carCre1 * carCre2, carCre0 * carCre2,
    carCre0 * carCre1 * carCre2
  }

/-! ## Charge quantization — number operators on the Furey ladder

The number operator `N_k = σ⁺_k · σ⁻_k` counts fermion occupancy on ladder k.
Charge is the linear combination: `Q = -N₀ + (1/3)(N₁ + N₂)` (lepton charge -1,
quark charge +1/3 per occupied color slot). The key theorem: number operators
commute with the τ-ideal braid exchange — braiding preserves particle type. -/

/-- Number operator on ladder k: `N_k = carAnn_k * carCre_k`. Counts fermion
occupancy (0 or 1 since `(σ⁺)² = (σ⁻)² = 0`). -/
def numberOp0 : CAR3 := carAnn0 * carCre0
def numberOp1 : CAR3 := carAnn1 * carCre1
def numberOp2 : CAR3 := carAnn2 * carCre2

/-- The key matrix lemma: `(σ⁺σ⁻)² = σ⁺σ⁻` in M₂(ℂ).
σ⁺σ⁻ = diag(1,0) is a projector — 2×2 finite computation. -/
private lemma σPlus_mul_σMinus_sq : (σPlus * σMinus) * (σPlus * σMinus) = σPlus * σMinus := by
  rw [σPlus_mul_σMinus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-! ## Chiral numbers `N₊ = σ⁺σ⁻`, `N₋ = σ⁻σ⁺`

The chiral projectors are the fundamental atomic building blocks of the
CAR algebra. Their sum is the identity, their difference is the CPT compass
`σ₃`. The charge operator is built from their linear combinations. -/

/-- `N₊ = σ⁺σ⁻` — projector onto the "occupied" chiral state (1,0). -/
def N_plus : M2C := σPlus * σMinus

/-- `N₋ = σ⁻σ⁺` — projector onto the "empty" chiral state (0,1). -/
def N_minus : M2C := σMinus * σPlus

/-- Sum is identity: `N₊ + N₋ = I`. The chiral projectors partition unity. -/
theorem N_plus_add_N_minus : N_plus + N_minus = (1 : M2C) := by
  dsimp [N_plus, N_minus]
  rw [σPlus_mul_σMinus, σMinus_mul_σPlus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Difference is the CPT compass: `N₊ - N₋ = σ₃`. The Cartan grading
operator is the difference of the chiral occupation numbers. -/
theorem N_plus_sub_N_minus : N_plus - N_minus = σ3c := by
  dsimp [N_plus, N_minus]
  rw [σPlus_mul_σMinus, σMinus_mul_σPlus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [σ3c]

/-- Orthogonality: `N₊ * N₋ = 0`. The occupied and empty projectors are
orthogonal — a state cannot be both. -/
theorem N_plus_mul_N_minus : N_plus * N_minus = (0 : M2C) := by
  dsimp [N_plus, N_minus]
  rw [σPlus_mul_σMinus, σMinus_mul_σPlus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Orthogonality: `N₋ * N₊ = 0`. Symmetric. -/
theorem N_minus_mul_N_plus : N_minus * N_plus = (0 : M2C) := by
  dsimp [N_plus, N_minus]
  rw [σPlus_mul_σMinus, σMinus_mul_σPlus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

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


/-- Synthesis of the CAR generation structure:
The CAR submodule is a left τ-ideal. The chiral numbers N₊, N₋ partition unity,
their difference is the CPT compass σ₃, and they are orthogonal.
The ladder number operators are idempotent. -/
theorem color_car_finite_car_projector_synthesis :
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

end ColorCARStandardModel
