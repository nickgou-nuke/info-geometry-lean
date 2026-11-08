/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
import InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge

/-!
# $\mathrm{Cl}(5,5)$ Twistor & Lepton–Quark `LinearEquiv` Promotions, Exact Minimal Period 4 of Andreev Reflections, and Transported Bilinear Sedenion Product on `Twistor55 ℝ`

This module closes the remaining twistor-lane and Andreev order-four gaps identified in §6 and §8
of `docs/SPLIT_SEDENION_CL44_GROUND_TRUTH_CONTRACT.md` on top of
`InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis`,
`InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge`, and
`InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge`:

1. **Section 1 — $\mathbb{R}$-Linear Equivalence Promotions `Twistor55 ℝ ≃ₗ[ℝ] SplitSedenion ℝ` and `LeftIdeal primIdem ≃ₗ[ℝ] Twistor55 ℝ`**:
   - Proves `twistor55ToSplitSedenion_smul` and promotes `twistor55SplitSedenionEquiv` and
     `cl44MatrixLeftIdealTwistor55Equiv` to genuine $\mathbb{R}$-linear equivalences
     `twistor55SplitSedenionLinearEquiv : Twistor55 ℝ ≃ₗ[ℝ] SplitSedenion ℝ` and
     `cl44MatrixLeftIdealTwistor55LinearEquiv : LeftIdeal primIdem ≃ₗ[ℝ] Twistor55 ℝ`.

2. **Section 2 — Peircian Lepton–Quark `LinearEquiv` Promotion `ZornSplitOctonion ℝ ≃ₗ[ℝ] GunaydinGurseyMultiplet ℝ`**:
   - Proves `zornToLeptonQuarkMultiplet_smul` and promotes `zornLeptonQuarkEquiv` to the genuine
     $\mathbb{R}$-linear equivalence
     `zornLeptonQuarkLinearEquiv : ZornSplitOctonion ℝ ≃ₗ[ℝ] GunaydinGurseyMultiplet ℝ`.
   - These are coordinate-carrier linear equivalences; no gauge-group representation is asserted.

3. **Section 3 — Exact Minimal Period 4 of `sedenionAndreevSheetSwap` and `superAndreevReflect`**:
   - Certifies explicit non-fixed witnesses (`sedenionOne : SplitSedenion ℝ` and
     `canonicalSuperTwistor55 : SuperTwistor55 ℝ`) showing that the first, second, and third
     iterates of `sedenionAndreevSheetSwap` and `superAndreevReflect` are strictly non-identity,
     while the fourth iterate is the identity (`sedenionAndreevSheetSwap_exact_minimal_period_four`
     and `superAndreevReflect_exact_minimal_period_four`).

4. **Section 4 — Transported $\mathbb{R}$-Bilinear Non-Associative Sedenion Product `twistor55SedenionMul` on `Twistor55 ℝ`**:
   - Defines `twistor55SedenionMul` on `Twistor55 ℝ` and proves its $\mathbb{R}$-bilinearity
     (`twistor55SedenionMul_add_left`, `twistor55SedenionMul_add_right`,
     `twistor55SedenionMul_smul_left`, `twistor55SedenionMul_smul_right`), existence of non-zero
     zero divisors (`exists_twistor55Sedenion_zero_divisors`), and non-associativity
     (`exists_twistor55Sedenion_nonzero_associator`).
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge

open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
open InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge

/-!
## Section 1: $\mathbb{R}$-Linear Equivalence Promotions `Twistor55 ℝ ≃ₗ[ℝ] SplitSedenion ℝ` and `LeftIdeal primIdem ≃ₗ[ℝ] Twistor55 ℝ`
-/

/-- `twistor55ToSplitSedenion` is homogeneous with respect to scalar multiplication. -/
theorem twistor55ToSplitSedenion_smul (c : ℝ) (ψ : Twistor55 ℝ) :
    twistor55ToSplitSedenion (c • ψ) = c • twistor55ToSplitSedenion ψ := by
  apply Prod.ext
  · exact fin8ToZorn_smul c ψ.1
  · exact fin8ToZorn_smul c ψ.2

/-- Genuine $\mathbb{R}$-linear equivalence `Twistor55 ℝ ≃ₗ[ℝ] SplitSedenion ℝ` promoting
`twistor55SplitSedenionEquiv`. -/
def twistor55SplitSedenionLinearEquiv : Twistor55 ℝ ≃ₗ[ℝ] SplitSedenion ℝ where
  toEquiv := twistor55SplitSedenionEquiv
  map_add' Z W := twistor55ToSplitSedenion_add Z W
  map_smul' c Z := twistor55ToSplitSedenion_smul c Z

@[simp] theorem twistor55SplitSedenionLinearEquiv_apply (Z : Twistor55 ℝ) :
    twistor55SplitSedenionLinearEquiv Z = twistor55ToSplitSedenion Z :=
  rfl

@[simp] theorem twistor55SplitSedenionLinearEquiv_symm_apply (X : SplitSedenion ℝ) :
    twistor55SplitSedenionLinearEquiv.symm X = splitSedenionToTwistor55 X :=
  rfl

/-- Composite $\mathbb{R}$-linear equivalence `LeftIdeal primIdem ≃ₗ[ℝ] Twistor55 ℝ` promoting
`cl44MatrixLeftIdealTwistor55Equiv`. -/
def cl44MatrixLeftIdealTwistor55LinearEquiv : LeftIdeal primIdem ≃ₗ[ℝ] Twistor55 ℝ :=
  cl44MatrixLeftIdealSplitSedenionLinearEquiv.trans twistor55SplitSedenionLinearEquiv.symm

@[simp] theorem cl44MatrixLeftIdealTwistor55LinearEquiv_apply (A : LeftIdeal primIdem) :
    cl44MatrixLeftIdealTwistor55LinearEquiv A = cl44MatrixLeftIdealTwistor55Equiv A :=
  rfl

@[simp] theorem cl44MatrixLeftIdealTwistor55LinearEquiv_symm_apply (Z : Twistor55 ℝ) :
    cl44MatrixLeftIdealTwistor55LinearEquiv.symm Z =
      cl44MatrixLeftIdealTwistor55Equiv.symm Z :=
  rfl

/-!
## Section 2: Peircian Lepton–Quark `LinearEquiv` Promotion `ZornSplitOctonion ℝ ≃ₗ[ℝ] GunaydinGurseyMultiplet ℝ`
-/

/-- `zornToLeptonQuarkMultiplet` is homogeneous with respect to scalar multiplication. -/
theorem zornToLeptonQuarkMultiplet_smul (c : ℝ) (z : ZornSplitOctonion ℝ) :
    zornToLeptonQuarkMultiplet (c • z) = c • zornToLeptonQuarkMultiplet z := by
  change gunaydinGurseySplit (zornToFin8 (zornSmul c z)) =
    c • gunaydinGurseySplit (zornToFin8 z)
  rw [zornToFin8_zornSmul]
  exact (gunaydinGurseyEquiv ℝ).map_smul c (zornToFin8 z)

/-- Genuine $\mathbb{R}$-linear equivalence `ZornSplitOctonion ℝ ≃ₗ[ℝ] GunaydinGurseyMultiplet ℝ`
promoting `zornLeptonQuarkEquiv`. -/
def zornLeptonQuarkLinearEquiv : ZornSplitOctonion ℝ ≃ₗ[ℝ] GunaydinGurseyMultiplet ℝ where
  toEquiv := zornLeptonQuarkEquiv
  map_add' x y := zornToLeptonQuarkMultiplet_add x y
  map_smul' c z := zornToLeptonQuarkMultiplet_smul c z

@[simp] theorem zornLeptonQuarkLinearEquiv_apply (z : ZornSplitOctonion ℝ) :
    zornLeptonQuarkLinearEquiv z = zornToLeptonQuarkMultiplet z :=
  rfl

@[simp] theorem zornLeptonQuarkLinearEquiv_symm_apply (m : GunaydinGurseyMultiplet ℝ) :
    zornLeptonQuarkLinearEquiv.symm m = leptonQuarkMultipletToZorn m :=
  rfl

/-!
## Section 3: Exact Minimal Period 4 of `sedenionAndreevSheetSwap` and `superAndreevReflect`
-/

/-- `sedenionAndreevSheetSwap` does not fix `sedenionOne : SplitSedenion ℝ`. -/
theorem sedenionAndreevSheetSwap_sedenionOne_ne :
    sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ) ≠ sedenionOne := by
  intro h
  have ha : (sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ)).1.a =
      (sedenionOne : SplitSedenion ℝ).1.a :=
    congrArg (fun X : SplitSedenion ℝ => X.1.a) h
  norm_num [sedenionAndreevSheetSwap, sedenionOne, zornSmul, zornOne, zornZero] at ha

/-- The second iterate of `sedenionAndreevSheetSwap` does not fix `sedenionOne : SplitSedenion ℝ`. -/
theorem sedenionAndreevSheetSwap_sq_sedenionOne_ne :
    sedenionAndreevSheetSwap (sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ)) ≠
      sedenionOne := by
  intro h
  have ha : (sedenionAndreevSheetSwap
      (sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ))).1.a =
      (sedenionOne : SplitSedenion ℝ).1.a :=
    congrArg (fun X : SplitSedenion ℝ => X.1.a) h
  norm_num [sedenionAndreevSheetSwap, sedenionOne, zornSmul, zornOne, zornZero] at ha

/-- The third iterate of `sedenionAndreevSheetSwap` does not fix `sedenionOne : SplitSedenion ℝ`. -/
theorem sedenionAndreevSheetSwap_cube_sedenionOne_ne :
    sedenionAndreevSheetSwap
      (sedenionAndreevSheetSwap
        (sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ))) ≠
      sedenionOne := by
  intro h
  have ha : (sedenionAndreevSheetSwap
      (sedenionAndreevSheetSwap
        (sedenionAndreevSheetSwap (sedenionOne : SplitSedenion ℝ)))).1.a =
      (sedenionOne : SplitSedenion ℝ).1.a :=
    congrArg (fun X : SplitSedenion ℝ => X.1.a) h
  norm_num [sedenionAndreevSheetSwap, sedenionOne, zornSmul, zornOne, zornZero] at ha

/-- **Exact Minimal Period 4 of `sedenionAndreevSheetSwap`**:
The fourth iterate of `sedenionAndreevSheetSwap` is the identity on `SplitSedenion ℝ`, whereas
its first, second, and third iterates are strictly distinct from `id`. -/
theorem sedenionAndreevSheetSwap_exact_minimal_period_four :
    (∀ X : SplitSedenion ℝ,
      sedenionAndreevSheetSwap
        (sedenionAndreevSheetSwap
          (sedenionAndreevSheetSwap (sedenionAndreevSheetSwap X))) = X) ∧
    (sedenionAndreevSheetSwap ≠ id) ∧
    ((sedenionAndreevSheetSwap ∘ sedenionAndreevSheetSwap) ≠ id) ∧
    ((sedenionAndreevSheetSwap ∘ sedenionAndreevSheetSwap ∘ sedenionAndreevSheetSwap) ≠ id) := by
  refine ⟨sedenionAndreevSheetSwap_order_four, ?_, ?_, ?_⟩
  · intro h
    exact sedenionAndreevSheetSwap_sedenionOne_ne (congrFun h sedenionOne)
  · intro h
    exact sedenionAndreevSheetSwap_sq_sedenionOne_ne (congrFun h sedenionOne)
  · intro h
    exact sedenionAndreevSheetSwap_cube_sedenionOne_ne (congrFun h sedenionOne)

/-- Canonical non-zero supertwistor witness in `SuperTwistor55 ℝ` for certifying exact minimal
period 4 of `superAndreevReflect`. -/
def canonicalSuperTwistor55 : SuperTwistor55 ℝ :=
  ((fun _ => 1, fun _ => 0), fun _ => 0, fun _ => 0, fun _ => 0)

/-- `superAndreevReflect` does not fix `canonicalSuperTwistor55`. -/
theorem superAndreevReflect_canonical_ne :
    superAndreevReflect canonicalSuperTwistor55 ≠ canonicalSuperTwistor55 := by
  intro h
  have h0 : (superAndreevReflect canonicalSuperTwistor55).1.1 0 =
      canonicalSuperTwistor55.1.1 0 :=
    congrFun (congrArg (fun 𝒮 : SuperTwistor55 ℝ => 𝒮.1.1) h) 0
  norm_num [superAndreevReflect, canonicalSuperTwistor55] at h0

/-- The second iterate of `superAndreevReflect` does not fix `canonicalSuperTwistor55`. -/
theorem superAndreevReflect_sq_canonical_ne :
    superAndreevReflect (superAndreevReflect canonicalSuperTwistor55) ≠
      canonicalSuperTwistor55 := by
  intro h
  have h0 : (superAndreevReflect (superAndreevReflect canonicalSuperTwistor55)).1.1 0 =
      canonicalSuperTwistor55.1.1 0 :=
    congrFun (congrArg (fun 𝒮 : SuperTwistor55 ℝ => 𝒮.1.1) h) 0
  norm_num [superAndreevReflect, canonicalSuperTwistor55] at h0

/-- The third iterate of `superAndreevReflect` does not fix `canonicalSuperTwistor55`. -/
theorem superAndreevReflect_cube_canonical_ne :
    superAndreevReflect
      (superAndreevReflect (superAndreevReflect canonicalSuperTwistor55)) ≠
      canonicalSuperTwistor55 := by
  intro h
  have h0 : (superAndreevReflect
      (superAndreevReflect (superAndreevReflect canonicalSuperTwistor55))).1.1 0 =
      canonicalSuperTwistor55.1.1 0 :=
    congrFun (congrArg (fun 𝒮 : SuperTwistor55 ℝ => 𝒮.1.1) h) 0
  norm_num [superAndreevReflect, canonicalSuperTwistor55] at h0

/-- **Exact Minimal Period 4 of `superAndreevReflect` on `SuperTwistor55 ℝ`**:
The fourth iterate of `superAndreevReflect` is the identity on `SuperTwistor55 ℝ`, whereas its
first, second, and third iterates are strictly distinct from `id`. -/
theorem superAndreevReflect_exact_minimal_period_four :
    (∀ 𝒮 : SuperTwistor55 ℝ,
      superAndreevReflect
        (superAndreevReflect (superAndreevReflect (superAndreevReflect 𝒮))) = 𝒮) ∧
    ((superAndreevReflect : SuperTwistor55 ℝ → SuperTwistor55 ℝ) ≠ id) ∧
    (((superAndreevReflect : SuperTwistor55 ℝ → SuperTwistor55 ℝ) ∘ superAndreevReflect) ≠ id) ∧
    (((superAndreevReflect : SuperTwistor55 ℝ → SuperTwistor55 ℝ) ∘
        superAndreevReflect ∘ superAndreevReflect) ≠ id) := by
  refine ⟨fun 𝒮 => (superAndreevReflect_order_four_and_symplectic_invariance 𝒮 𝒮).2.1,
    ?_, ?_, ?_⟩
  · intro h
    exact superAndreevReflect_canonical_ne (congrFun h canonicalSuperTwistor55)
  · intro h
    exact superAndreevReflect_sq_canonical_ne (congrFun h canonicalSuperTwistor55)
  · intro h
    exact superAndreevReflect_cube_canonical_ne (congrFun h canonicalSuperTwistor55)

/-!
## Section 4: Transported Non-Associative Sedenion Product `twistor55SedenionMul` on `Twistor55 ℝ`
-/

/-- Transported split-sedenion multiplication on `Twistor55 ℝ` induced by
`twistor55SplitSedenionEquiv`. -/
def twistor55SedenionMul (ψ₁ ψ₂ : Twistor55 ℝ) : Twistor55 ℝ :=
  splitSedenionToTwistor55
    (sedenionMul (twistor55ToSplitSedenion ψ₁) (twistor55ToSplitSedenion ψ₂))

/-- Left additivity of the transported product `twistor55SedenionMul` on `Twistor55 ℝ`. -/
theorem twistor55SedenionMul_add_left (ψ₁ ψ₂ φ : Twistor55 ℝ) :
    twistor55SedenionMul (ψ₁ + ψ₂) φ =
      twistor55SedenionMul ψ₁ φ + twistor55SedenionMul ψ₂ φ := by
  change twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv (ψ₁ + ψ₂))
        (twistor55SplitSedenionLinearEquiv φ)) =
    twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ₁)
        (twistor55SplitSedenionLinearEquiv φ)) +
    twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ₂)
        (twistor55SplitSedenionLinearEquiv φ))
  rw [twistor55SplitSedenionLinearEquiv.map_add,
      sedenionMul_add_left,
      twistor55SplitSedenionLinearEquiv.symm.map_add]

/-- Right additivity of the transported product `twistor55SedenionMul` on `Twistor55 ℝ`. -/
theorem twistor55SedenionMul_add_right (ψ φ₁ φ₂ : Twistor55 ℝ) :
    twistor55SedenionMul ψ (φ₁ + φ₂) =
      twistor55SedenionMul ψ φ₁ + twistor55SedenionMul ψ φ₂ := by
  change twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv (φ₁ + φ₂))) =
    twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv φ₁)) +
    twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv φ₂))
  rw [twistor55SplitSedenionLinearEquiv.map_add,
      sedenionMul_add_right,
      twistor55SplitSedenionLinearEquiv.symm.map_add]

/-- Left $\mathbb{R}$-homogeneity of the transported product `twistor55SedenionMul` on `Twistor55 ℝ`. -/
theorem twistor55SedenionMul_smul_left (c : ℝ) (ψ φ : Twistor55 ℝ) :
    twistor55SedenionMul (c • ψ) φ = c • twistor55SedenionMul ψ φ := by
  change twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv (c • ψ))
        (twistor55SplitSedenionLinearEquiv φ)) =
    c • twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv φ))
  rw [twistor55SplitSedenionLinearEquiv.map_smul,
      sedenionMul_smul_left,
      twistor55SplitSedenionLinearEquiv.symm.map_smul]

/-- Right $\mathbb{R}$-homogeneity of the transported product `twistor55SedenionMul` on `Twistor55 ℝ`. -/
theorem twistor55SedenionMul_smul_right (c : ℝ) (ψ φ : Twistor55 ℝ) :
    twistor55SedenionMul ψ (c • φ) = c • twistor55SedenionMul ψ φ := by
  change twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv (c • φ))) =
    c • twistor55SplitSedenionLinearEquiv.symm
      (sedenionMul (twistor55SplitSedenionLinearEquiv ψ)
        (twistor55SplitSedenionLinearEquiv φ))
  rw [twistor55SplitSedenionLinearEquiv.map_smul,
      sedenionMul_smul_right,
      twistor55SplitSedenionLinearEquiv.symm.map_smul]

/-- The existing non-zero split-sedenion zero-divisor pair transfers to `twistor55SedenionMul`
on `Twistor55 ℝ`. -/
theorem exists_twistor55Sedenion_zero_divisors :
    ∃ ψ φ : Twistor55 ℝ,
      ψ ≠ 0 ∧ φ ≠ 0 ∧ twistor55SedenionMul ψ φ = 0 := by
  obtain ⟨hXY, hX, hY, _hNull⟩ := splitSedenion_explicit_zero_divisors_and_null_norm
  let X : SplitSedenion ℝ := (zornE0, zornZero)
  let Y : SplitSedenion ℝ := (zornE1, zornZero)
  refine ⟨twistor55SplitSedenionLinearEquiv.symm X,
    twistor55SplitSedenionLinearEquiv.symm Y, ?_, ?_, ?_⟩
  · intro h
    apply hX
    have hm := congrArg twistor55SplitSedenionLinearEquiv h
    rw [twistor55SplitSedenionLinearEquiv.map_zero,
        twistor55SplitSedenionLinearEquiv.apply_symm_apply] at hm
    exact hm
  · intro h
    apply hY
    have hm := congrArg twistor55SplitSedenionLinearEquiv h
    rw [twistor55SplitSedenionLinearEquiv.map_zero,
        twistor55SplitSedenionLinearEquiv.apply_symm_apply] at hm
    exact hm
  · apply twistor55SplitSedenionLinearEquiv.injective
    rw [twistor55SplitSedenionLinearEquiv.map_zero]
    change twistor55ToSplitSedenion
      (splitSedenionToTwistor55
        (sedenionMul
          (twistor55ToSplitSedenion (splitSedenionToTwistor55 X))
          (twistor55ToSplitSedenion (splitSedenionToTwistor55 Y)))) = sedenionZero
    rw [twistor55ToSplitSedenion_splitSedenionToTwistor55,
        twistor55ToSplitSedenion_splitSedenionToTwistor55,
        twistor55ToSplitSedenion_splitSedenionToTwistor55]
    exact hXY

/-- The split-sedenion non-associativity witness transfers to `twistor55SedenionMul` on
`Twistor55 ℝ`. -/
theorem exists_twistor55Sedenion_nonzero_associator :
    ∃ ψ₁ ψ₂ ψ₃ : Twistor55 ℝ,
      twistor55SedenionMul (twistor55SedenionMul ψ₁ ψ₂) ψ₃ ≠
        twistor55SedenionMul ψ₁ (twistor55SedenionMul ψ₂ ψ₃) := by
  obtain ⟨_hAssocCl, hPair⟩ := cl44_associative_vs_splitSedenion_nonAssociative
  obtain ⟨X, Y, Z, hXYZ⟩ := hPair
  refine ⟨splitSedenionToTwistor55 X,
    splitSedenionToTwistor55 Y,
    splitSedenionToTwistor55 Z, ?_⟩
  intro h
  apply hXYZ
  have hm := congrArg twistor55ToSplitSedenion h
  unfold twistor55SedenionMul at hm
  repeat rw [twistor55ToSplitSedenion_splitSedenionToTwistor55] at hm
  exact hm

end InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge
