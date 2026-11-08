/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.FiveGradedDecomposition
import InfoGeometry.External.Virasoro.Sugawara
import InfoGeometry.Canonical.AffineKacMoodyColimitIsomorphism

/-!
# Sugawara Adjoint Current Action & Finite-Window Casimir Sum on the Kac--Moody Colimit

This file establishes the constructive connection between the categorical
`ModuleCat 𝕜` colimit `affineFiniteModeColimit Φ hΦ hΦs` of an affine
Kac--Moody algebra and the Sugawara adjoint current mode-shift and Casimir sum.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.External.Virasoro.AffineKacMoody`: `AffineKacMoody`,
    `affineCurrentGen`, `affineCentralGen`, `affineCurrentGen_bracket`.
  * `InfoGeometry.Canonical.AffineKacMoodyColimitIsomorphism`:
    `affineFiniteModeColimit`, `affineCurrentColimitMode`,
    `affineCentralColimitMode`, `affineCurrentColimitMode_lie_eq`,
    `affineCurrentColimitMode_lie_central`.
- BUCKET 2 (Deconfabulation):
  * Replaced the unimplemented comment stub and file-level `injected-hypothesis-surface`
    variables with constructive definitions and theorems for the Sugawara
    adjoint current action and finite-window Casimir sum directly on
    `affineFiniteModeColimit Φ hΦ hΦs`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `sugawaraColimitAdjointTerm`: adjoint current commutator
    `⁅affineCurrentColimitMode Φ hΦ hΦs k x, affineCurrentColimitMode Φ hΦ hΦs m y⁆`
    in `affineFiniteModeColimit Φ hΦ hΦs`.
  * `sugawaraColimitAdjointTerm_eq`: proves the mode-shift + central-cocycle
    expansion of `sugawaraColimitAdjointTerm`.
  * `sugawaraColimitAdjointTerm_lie_central`: proves that
    `sugawaraColimitAdjointTerm` commutes with `affineCentralColimitMode`.
  * `sugawaraColimitCasimirWindow`, `sugawaraColimitCasimirWindow_eq`:
    finite-window Casimir current action $\sum_{a \in \iota} [J_k(e_a), J_m(y)]$
    and its mode-shifted expansion in `affineFiniteModeColimit Φ hΦ hΦs`.
-/

noncomputable section

namespace VirasoroProject

open InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]

/-- Single-mode Sugawara adjoint action of the categorical colimit current
`J_k(x)` on `J_m(y)` inside `affineFiniteModeColimit Φ hΦ hΦs`. -/
def sugawaraColimitAdjointTerm
    (Φ : LinearMap.BilinForm 𝕜 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (k m : ℤ) (x y : 𝓰) :
    (affineFiniteModeColimit Φ hΦ hΦs : Type _) :=
  ⁅affineCurrentColimitMode Φ hΦ hΦs k x,
    affineCurrentColimitMode Φ hΦ hΦs m y⁆

/-- **Sugawara Colimit Adjoint Mode-Shift & Central Cocycle Expansion**:
Evaluating `sugawaraColimitAdjointTerm Φ hΦ hΦs k m x y` shifts the mode from
`m` to `k + m` with Lie bracket `⁅x, y⁆` and adds the central residue cocycle
`((k : 𝕜) * Φ x y) • affineCentralColimitMode Φ hΦ hΦs` when `k + m = 0`. -/
theorem sugawaraColimitAdjointTerm_eq
    (Φ : LinearMap.BilinForm 𝕜 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (k m : ℤ) (x y : 𝓰) :
    sugawaraColimitAdjointTerm Φ hΦ hΦs k m x y =
      affineCurrentColimitMode Φ hΦ hΦs (k + m) (⁅x, y⁆ : 𝓰) +
        if k + m = 0 then
          ((k : 𝕜) * Φ x y) • affineCentralColimitMode Φ hΦ hΦs
        else 0 := by
  unfold sugawaraColimitAdjointTerm
  exact affineCurrentColimitMode_lie_eq Φ hΦ hΦs k m x y

/-- Every Sugawara adjoint current term commutes with the central colimit
generator `affineCentralColimitMode Φ hΦ hΦs`. -/
theorem sugawaraColimitAdjointTerm_lie_central
    (Φ : LinearMap.BilinForm 𝕜 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (k m : ℤ) (x y : 𝓰) :
    ⁅sugawaraColimitAdjointTerm Φ hΦ hΦs k m x y,
      affineCentralColimitMode Φ hΦ hΦs⁆ = 0 := by
  rw [sugawaraColimitAdjointTerm_eq Φ hΦ hΦs k m x y, add_lie,
    affineCurrentColimitMode_lie_central Φ hΦ hΦs (k + m) ⁅x, y⁆, zero_add]
  by_cases hkm : k + m = 0
  · simp only [hkm, ↓reduceIte, smul_lie, lie_self, smul_zero]
  · simp only [hkm, ↓reduceIte, zero_lie]

/-- Finite-basis Sugawara Casimir current action $\sum_{a \in \iota} [J_k(e_a), J_m(y)]$
inside the categorical `ModuleCat 𝕜` colimit `affineFiniteModeColimit Φ hΦ hΦs`. -/
def sugawaraColimitCasimirWindow
    {ι : Type*} [Fintype ι]
    (Φ : LinearMap.BilinForm 𝕜 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (e : ι → 𝓰) (k m : ℤ) (y : 𝓰) :
    (affineFiniteModeColimit Φ hΦ hΦs : Type _) :=
  ∑ a : ι, sugawaraColimitAdjointTerm Φ hΦ hΦs k m (e a) y

/-- Expansion of `sugawaraColimitCasimirWindow` into the sum of mode-shifted
currents `J_{k+m}([e_a, y])` and central residue contributions. -/
theorem sugawaraColimitCasimirWindow_eq
    {ι : Type*} [Fintype ι]
    (Φ : LinearMap.BilinForm 𝕜 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (e : ι → 𝓰) (k m : ℤ) (y : 𝓰) :
    sugawaraColimitCasimirWindow Φ hΦ hΦs e k m y =
      ∑ a : ι,
        (affineCurrentColimitMode Φ hΦ hΦs (k + m) (⁅e a, y⁆ : 𝓰) +
          if k + m = 0 then
            ((k : 𝕜) * Φ (e a) y) • affineCentralColimitMode Φ hΦ hΦs
          else 0) := by
  unfold sugawaraColimitCasimirWindow
  refine Finset.sum_congr rfl ?_
  intro a _
  exact sugawaraColimitAdjointTerm_eq Φ hΦ hΦs k m (e a) y

end VirasoroProject

end noncomputable section
