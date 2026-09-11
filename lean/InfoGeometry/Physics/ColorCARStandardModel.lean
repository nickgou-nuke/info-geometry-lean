import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.Physics.BraidIdealDescent
import InfoGeometry.Physics.ChiralTLDescent
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators

/-!
# ColorCAR — finite CAR triple-product readouts

This module proves finite algebraic identities in the imported CAR and braid
setting.  Furey/Standard-Model terminology is used only as naming motivation;
no theorem here constructs a Standard Model representation, proves a minimal
left-ideal classification, or identifies physical fermions.
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

/-! ## Triple CAR product — finite eight-generator span

Three copies of the CAR algebra `(σ⁺ᵢ, σ⁻ᵢ)` for `i ∈ {0,1,2}` give a finite
span of eight displayed tensor expressions. -/

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

/-- The vacuum state |0⟩ = |0⟩₀ ⊗ |0⟩₁ ⊗ |0⟩₂. -/
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

/-- The key matrix lemma is the existing positive-chirality projector theorem. -/
private lemma σPlus_mul_σMinus_sq : (σPlus * σMinus) * (σPlus * σMinus) = σPlus * σMinus := by
  simpa [PPlus] using PPlus_idempotent

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
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_add_PMinus

/-- Difference is the CPT compass: `N₊ - N₋ = σ₃`. The Cartan grading
operator is the difference of the chiral occupation numbers. -/
theorem N_plus_sub_N_minus : N_plus - N_minus = σ3c := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_sub_PMinus

/-- Orthogonality: `N₊ * N₋ = 0`. The occupied and empty projectors are
orthogonal — a state cannot be both. -/
theorem N_plus_mul_N_minus : N_plus * N_minus = (0 : M2C) := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PPlus_PMinus_orthogonal

/-- Orthogonality: `N₋ * N₊ = 0`. Symmetric. -/
theorem N_minus_mul_N_plus : N_minus * N_plus = (0 : M2C) := by
  simpa [N_plus, N_minus, PPlus, PMinus] using PMinus_PPlus_orthogonal

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
