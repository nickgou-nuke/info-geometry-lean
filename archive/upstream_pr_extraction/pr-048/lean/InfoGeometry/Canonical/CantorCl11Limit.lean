import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Clifford.Cl11TensorTowerLimit

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.CantorCl11Limit

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# InfoGeometry.Canonical.CantorCl11Limit

Finite-prefix/algebraic-direct-limit bridge for the repo's Cantor boundary and
`Cl(1,1)` tensor tower.

Safe content only:
- Cantor boundary prefixes are read from the existing owner file;
- stagewise `Cl(1,1)` data are transported by the existing one-step embedding;
- the direct-limit image is constant along a prefix-indexed compatible family.

This file does not construct an analytic infinite tensor product, a categorical
completion, a Virasoro/SUSY identification, or any global representation
surjectivity theorem.
-/

/-- The repo-owned finite prefix of a Cantor boundary word at depth `n`. -/
def prefixAt (n : ℕ)
    (ξ : (ℕ → Bool)) : List Bool :=
  boundaryPrefix n ξ

@[simp] theorem prefixAt_zero (ξ : (ℕ → Bool)) :
    prefixAt 0 ξ = [] := by
  rfl

@[simp] theorem prefixAt_succ (n : ℕ) (ξ : (ℕ → Bool)) :
    prefixAt (n + 1) ξ = boundaryHead ξ :: prefixAt n (boundaryTail ξ) := by
  rfl

@[simp] theorem prefixAt_length (n : ℕ) (ξ : (ℕ → Bool)) :
    (prefixAt n ξ).length = n := by
  exact boundaryPrefix_length n ξ

/-- A prefix-indexed stage family specialized along one boundary code. -/
def prefixStageSequence
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool)) :
    ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.MatStage n :=
  fun n => F n (prefixAt n ξ)

@[simp] theorem prefixStageSequence_zero
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool)) :
    prefixStageSequence F ξ 0 = F 0 [] := by
  rfl

theorem prefixStageSequence_succ
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (n : ℕ) :
    stageEmbed n (prefixStageSequence F ξ n) = prefixStageSequence F ξ (n + 1) := by
  simpa [prefixStageSequence] using hF n

/- #### BUCKET 1: CLOSED FINITE THEOREMS -/

/-- A prefix-compatible stage family has constant image in the algebraic direct limit. -/
theorem prefix_family_constant_in_limit
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ)) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0 (F 0 []) := by
  intro n
  simpa [prefixStageSequence] using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit
      (F := prefixStageSequence F ξ)
      (hF := prefixStageSequence_succ F ξ hF) n

/-- InfoGeometry.Clifford.Cl11TensorTower.MatStage-zero square-zero data remain square-zero along a prefix-compatible family. -/
theorem prefix_family_square_zero_in_limit
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (h0 : F 0 [] * F 0 [] = 0) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) *
          InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) = 0 := by
  have h0' :
      prefixStageSequence F ξ 0 * prefixStageSequence F ξ 0 = 0 := by
    simpa [prefixStageSequence] using h0
  intro n
  simpa [prefixStageSequence] using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_square_zero_in_limit
      (F := prefixStageSequence F ξ)
      (hF := prefixStageSequence_succ F ξ hF)
      (h0 := h0') n

/-- InfoGeometry.Clifford.Cl11TensorTower.MatStage-zero idempotent data remain idempotent along a prefix-compatible family. -/
theorem prefix_family_idempotent_in_limit
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (h0 : F 0 [] * F 0 [] = F 0 []) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) *
          InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) := by
  have h0' :
      prefixStageSequence F ξ 0 * prefixStageSequence F ξ 0 = prefixStageSequence F ξ 0 := by
    simpa [prefixStageSequence] using h0
  intro n
  simpa [prefixStageSequence] using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_idempotent_in_limit
      (F := prefixStageSequence F ξ)
      (hF := prefixStageSequence_succ F ξ hF)
      (h0 := h0') n

/-- InfoGeometry.Clifford.Cl11TensorTower.MatStage-zero involutive data remain involutive along a prefix-compatible family. -/
theorem prefix_family_involution_in_limit
    (F : ∀ n : ℕ, List Bool → InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (h0 : F 0 [] * F 0 [] = 1) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) *
          InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (F n (prefixAt n ξ)) = 1 := by
  have h0' :
      prefixStageSequence F ξ 0 * prefixStageSequence F ξ 0 = 1 := by
    simpa [prefixStageSequence] using h0
  intro n
  simpa [prefixStageSequence] using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_involution_in_limit
      (F := prefixStageSequence F ξ)
      (hF := prefixStageSequence_succ F ξ hF)
      (h0 := h0') n

theorem prefix_families_product_constant_in_limit
    (F G : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (hG : ∀ n : ℕ,
      stageEmbed n (G n (prefixAt n ξ)) = G (n + 1) (prefixAt (n + 1) ξ)) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (F n (prefixAt n ξ) * G n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0
          (F 0 [] * G 0 []) := by
  let H : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n :=
    fun n w => F n w * G n w
  have hH : ∀ n : ℕ,
      stageEmbed n (H n (prefixAt n ξ)) =
        H (n + 1) (prefixAt (n + 1) ξ) := by
    intro n
    change stageEmbed n
        (F n (prefixAt n ξ) * G n (prefixAt n ξ)) = _
    rw [map_mul, hF n, hG n]
  intro n
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
      (H n (prefixAt n ξ)) =
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0 (H 0 [])
  simpa using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit
      (F := fun m => H m (prefixAt m ξ))
      (hF := hH) n

theorem prefix_families_add_constant_in_limit
    (F G : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (hG : ∀ n : ℕ,
      stageEmbed n (G n (prefixAt n ξ)) = G (n + 1) (prefixAt (n + 1) ξ)) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (F n (prefixAt n ξ) + G n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0
          (F 0 [] + G 0 []) := by
  let H : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n :=
    fun n w => F n w + G n w
  have hH : ∀ n : ℕ,
      stageEmbed n (H n (prefixAt n ξ)) =
        H (n + 1) (prefixAt (n + 1) ξ) := by
    intro n
    change stageEmbed n
        (F n (prefixAt n ξ) + G n (prefixAt n ξ)) = _
    rw [map_add, hF n, hG n]
  intro n
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
      (H n (prefixAt n ξ)) =
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0 (H 0 [])
  simpa using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit
      (F := fun m => H m (prefixAt m ξ))
      (hF := hH) n

theorem prefix_families_sub_constant_in_limit
    (F G : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ))
    (hG : ∀ n : ℕ,
      stageEmbed n (G n (prefixAt n ξ)) = G (n + 1) (prefixAt (n + 1) ξ)) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (F n (prefixAt n ξ) - G n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0
          (F 0 [] - G 0 []) := by
  let H : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n :=
    fun n w => F n w - G n w
  have hH : ∀ n : ℕ,
      stageEmbed n (H n (prefixAt n ξ)) =
        H (n + 1) (prefixAt (n + 1) ξ) := by
    intro n
    change stageEmbed n
        (F n (prefixAt n ξ) - G n (prefixAt n ξ)) = _
    rw [map_sub, hF n, hG n]
  intro n
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
      (H n (prefixAt n ξ)) =
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0 (H 0 [])
  simpa using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit
      (F := fun m => H m (prefixAt m ξ))
      (hF := hH) n

theorem prefix_family_smul_constant_in_limit
    (r : ℝ)
    (F : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (ξ : (ℕ → Bool))
    (hF : ∀ n : ℕ,
      stageEmbed n (F n (prefixAt n ξ)) = F (n + 1) (prefixAt (n + 1) ξ)) :
    ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (r • F n (prefixAt n ξ)) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0
          (r • F 0 []) := by
  let H : ∀ n : ℕ, List Bool →
      InfoGeometry.Clifford.Cl11TensorTower.MatStage n :=
    fun n w => r • F n w
  have hH : ∀ n : ℕ,
      stageEmbed n (H n (prefixAt n ξ)) =
        H (n + 1) (prefixAt (n + 1) ξ) := by
    intro n
    change stageEmbed n (r • F n (prefixAt n ξ)) = _
    rw [map_smul, hF n]
  intro n
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
      (H n (prefixAt n ξ)) =
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 0 (H 0 [])
  simpa using
    InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit
      (F := fun m => H m (prefixAt m ξ))
      (hF := hH) n

/- #### BUCKET 2: CONDITIONAL THEOREMS -/
-- [Empty.]

/- #### BUCKET 3: OPEN CLOSURE DEBT -/
-- No theorem in this module identifies the prefix-indexed `Cl(1,1)` tower with
-- Virasoro, SUSY, categorical completion, or analytic infinite tensor-product
-- structure. Those require separate owner-side constructions.

end InfoGeometry.Canonical.CantorCl11Limit
