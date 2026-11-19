/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.SuperMetriplectic.Blocks
import InfoGeometry.SuperMetriplectic.CartanBridge
import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Thermo.OnsagerOperatorClosure
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# SuperMetriplectic Cartan–Onsager–Parity Bridge

Connects the conservative `SuperMetriplectic` packets (`CartanOnsagerSplit`,
`DrazinCartanOnsagerBridge`, `OnsagerMetricData`, `ScalarSchurDrazinBlock`,
`DrazinPenroseSchurTriad`, `TKKOnsagerMatrix`, `ConformalOnsagerBlock`, and
`ConformalPKMetriplecticSplit`) to `OnsagerCasimirSystem`, `TimeReversal`, and
`ParityOnsagerSystem` in `InfoGeometry.Thermo.OnsagerClosure`.

The Cartan involution `θ` on a `CartanOnsagerSplit L` lifts unconditionally to
`TimeReversal L` via `-θ` (making `𝔭` = `+1` T-even dissipative and `𝔨` = `-1`
T-odd reversible) as well as `+θ` (`𝔨` = `+1`, `𝔭` = `-1`).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge

open InfoGeometry.Core
open InfoGeometry.SuperMetriplectic
open InfoGeometry.SuperMetriplectic.CartanBridge
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem

/-! ## Part 1: Unconditional `TimeReversal L` lifts from `CartanOnsagerSplit L` -/

section CartanSplitTimeReversal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Realize the Cartan split as a `TimeReversal L` with `𝔭` (`-1` eigenspace of `θ`)
as the `T`-even (`+1`) sector and `𝔨` (`+1` eigenspace of `θ`) as the `T`-odd (`-1`)
sector: `T = -θ`. -/
def cartanTimeReversal (C : CartanOnsagerSplit L) : TimeReversal L where
  op := -(C.S.toLieAut.toLinearEquiv.toLinearMap)
  involutive x := by
    change -C.S.θ (-C.S.θ x) = x
    rw [C.S.θ.map_neg, neg_neg, C.S.involutive x]

@[simp] theorem cartanTimeReversal_apply (C : CartanOnsagerSplit L) (x : L) :
    (cartanTimeReversal C).op x = -C.S.θ x := rfl

/-- Realize the Cartan involution directly as `TimeReversal L` (`T = +θ`),
fixing `𝔨` (`+1`) and reversing `𝔭` (`-1`). -/
def cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) : TimeReversal L where
  op := C.S.toLieAut.toLinearEquiv.toLinearMap
  involutive x := C.S.involutive x

@[simp] theorem cartanInvolutionTimeReversal_apply (C : CartanOnsagerSplit L) (x : L) :
    (cartanInvolutionTimeReversal C).op x = C.S.θ x := rfl

theorem cartanTimeReversal_op_eq_neg (C : CartanOnsagerSplit L) (x : L) :
    (cartanTimeReversal C).op x = -(cartanInvolutionTimeReversal C).op x := rfl

theorem cartanTimeReversal_eq_self_of_mem_dissipativeRange
    (C : CartanOnsagerSplit L) {x : L} (hx : x ∈ C.dissipativeRange) :
    (cartanTimeReversal C).op x = x := by
  rw [C.dissipativeRange_eq_p] at hx
  have hθ : C.S.θ x = -x := (C.S.mem_oddSubmodule_iff).1 hx
  simp [cartanTimeReversal_apply, hθ]

theorem cartanTimeReversal_eq_neg_of_mem_drazinCore
    (C : CartanOnsagerSplit L) {x : L} (hx : x ∈ C.drazinCore) :
    (cartanTimeReversal C).op x = -x := by
  rw [C.drazinCore_eq_k] at hx
  have hθ : C.S.θ x = x := (C.S.mem_evenSubmodule_iff).1 hx
  simp [cartanTimeReversal_apply, hθ]

theorem mem_dissipativeRange_iff_cartanTimeReversal_eq_self
    (C : CartanOnsagerSplit L) (x : L) :
    x ∈ C.dissipativeRange ↔ (cartanTimeReversal C).op x = x := by
  rw [C.dissipativeRange_eq_p]
  dsimp only [SymmetricLieAlgebra.𝔭]
  rw [C.S.mem_oddSubmodule_iff, cartanTimeReversal_apply]
  constructor
  · intro hθ
    rw [hθ, neg_neg]
  · intro hop
    exact neg_eq_iff_eq_neg.mp hop

theorem mem_drazinCore_iff_cartanTimeReversal_eq_neg
    (C : CartanOnsagerSplit L) (x : L) :
    x ∈ C.drazinCore ↔ (cartanTimeReversal C).op x = -x := by
  rw [C.drazinCore_eq_k]
  dsimp only [SymmetricLieAlgebra.𝔨]
  rw [C.S.mem_evenSubmodule_iff, cartanTimeReversal_apply]
  exact neg_inj.symm

theorem cartanInvolutionTimeReversal_eq_self_of_mem_drazinCore
    (C : CartanOnsagerSplit L) {x : L} (hx : x ∈ C.drazinCore) :
    (cartanInvolutionTimeReversal C).op x = x := by
  rw [C.drazinCore_eq_k] at hx
  exact (C.S.mem_evenSubmodule_iff).1 hx

theorem cartanInvolutionTimeReversal_eq_neg_of_mem_dissipativeRange
    (C : CartanOnsagerSplit L) {x : L} (hx : x ∈ C.dissipativeRange) :
    (cartanInvolutionTimeReversal C).op x = -x := by
  rw [C.dissipativeRange_eq_p] at hx
  exact (C.S.mem_oddSubmodule_iff).1 hx

theorem mem_drazinCore_iff_cartanInvolutionTimeReversal_eq_self
    (C : CartanOnsagerSplit L) (x : L) :
    x ∈ C.drazinCore ↔ (cartanInvolutionTimeReversal C).op x = x := by
  rw [C.drazinCore_eq_k]
  dsimp only [SymmetricLieAlgebra.𝔨]
  rw [C.S.mem_evenSubmodule_iff, cartanInvolutionTimeReversal_apply]

theorem mem_dissipativeRange_iff_cartanInvolutionTimeReversal_eq_neg
    (C : CartanOnsagerSplit L) (x : L) :
    x ∈ C.dissipativeRange ↔ (cartanInvolutionTimeReversal C).op x = -x := by
  rw [C.dissipativeRange_eq_p]
  dsimp only [SymmetricLieAlgebra.𝔭]
  rw [C.S.mem_oddSubmodule_iff, cartanInvolutionTimeReversal_apply]

@[simp] theorem cartanTimeReversal_P_plus (C : CartanOnsagerSplit L) (x : L) :
    (cartanTimeReversal C).op (C.S.P_plus x) = -C.S.P_plus x := by
  have hmem : C.S.P_plus x ∈ C.S.evenLieSubalgebra := by
    rw [C.S.P_plus_eq_plusPart]
    exact C.S.plusPart_mem_even x
  have hθ : C.S.θ (C.S.P_plus x) = C.S.P_plus x := (C.S.mem_even_iff).1 hmem
  rw [cartanTimeReversal_apply, hθ]

@[simp] theorem cartanTimeReversal_P_minus (C : CartanOnsagerSplit L) (x : L) :
    (cartanTimeReversal C).op (C.S.P_minus x) = C.S.P_minus x := by
  have hmem : C.S.P_minus x ∈ C.S.oddSubmodule := by
    rw [C.S.P_minus_eq_minusPart]
    exact C.S.minusPart_mem_odd x
  have hθ : C.S.θ (C.S.P_minus x) = -C.S.P_minus x := (C.S.mem_oddSubmodule_iff).1 hmem
  rw [cartanTimeReversal_apply, hθ, neg_neg]

@[simp] theorem P_plus_cartanTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_plus ((cartanTimeReversal C).op x) = -C.S.P_plus x := by
  change ((2 : ℝ)⁻¹) • (-C.S.θ x + C.S.θ (-C.S.θ x)) = -(((2 : ℝ)⁻¹) • (x + C.S.θ x))
  rw [C.S.θ.map_neg, C.S.involutive x, add_comm, ← neg_add, smul_neg]

@[simp] theorem P_minus_cartanTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_minus ((cartanTimeReversal C).op x) = C.S.P_minus x := by
  change ((2 : ℝ)⁻¹) • (-C.S.θ x - C.S.θ (-C.S.θ x)) = ((2 : ℝ)⁻¹) • (x - C.S.θ x)
  rw [C.S.θ.map_neg, C.S.involutive x, sub_neg_eq_add, add_comm, sub_eq_add_neg]

theorem P_plus_comm_cartanTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_plus ((cartanTimeReversal C).op x) = (cartanTimeReversal C).op (C.S.P_plus x) := by
  rw [P_plus_cartanTimeReversal, cartanTimeReversal_P_plus]

theorem P_minus_comm_cartanTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_minus ((cartanTimeReversal C).op x) = (cartanTimeReversal C).op (C.S.P_minus x) := by
  rw [P_minus_cartanTimeReversal, cartanTimeReversal_P_minus]

theorem P_plus_comp_cartanTimeReversal (C : CartanOnsagerSplit L) :
    C.S.P_plus.comp (cartanTimeReversal C).op = (cartanTimeReversal C).op.comp C.S.P_plus := by
  ext x
  exact P_plus_comm_cartanTimeReversal C x

theorem P_minus_comp_cartanTimeReversal (C : CartanOnsagerSplit L) :
    C.S.P_minus.comp (cartanTimeReversal C).op = (cartanTimeReversal C).op.comp C.S.P_minus := by
  ext x
  exact P_minus_comm_cartanTimeReversal C x

@[simp] theorem cartanInvolutionTimeReversal_P_plus (C : CartanOnsagerSplit L) (x : L) :
    (cartanInvolutionTimeReversal C).op (C.S.P_plus x) = C.S.P_plus x := by
  have hmem : C.S.P_plus x ∈ C.S.evenLieSubalgebra := by
    rw [C.S.P_plus_eq_plusPart]
    exact C.S.plusPart_mem_even x
  exact (C.S.mem_even_iff).1 hmem

@[simp] theorem cartanInvolutionTimeReversal_P_minus (C : CartanOnsagerSplit L) (x : L) :
    (cartanInvolutionTimeReversal C).op (C.S.P_minus x) = -C.S.P_minus x := by
  have hmem : C.S.P_minus x ∈ C.S.oddSubmodule := by
    rw [C.S.P_minus_eq_minusPart]
    exact C.S.minusPart_mem_odd x
  exact (C.S.mem_oddSubmodule_iff).1 hmem

@[simp] theorem P_plus_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_plus ((cartanInvolutionTimeReversal C).op x) = C.S.P_plus x := by
  change ((2 : ℝ)⁻¹) • (C.S.θ x + C.S.θ (C.S.θ x)) = ((2 : ℝ)⁻¹) • (x + C.S.θ x)
  rw [C.S.involutive x, add_comm]

@[simp] theorem P_minus_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_minus ((cartanInvolutionTimeReversal C).op x) = -C.S.P_minus x := by
  change ((2 : ℝ)⁻¹) • (C.S.θ x - C.S.θ (C.S.θ x)) = -(((2 : ℝ)⁻¹) • (x - C.S.θ x))
  rw [C.S.involutive x, ← smul_neg, neg_sub]

theorem P_plus_comm_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_plus ((cartanInvolutionTimeReversal C).op x) =
      (cartanInvolutionTimeReversal C).op (C.S.P_plus x) := by
  rw [P_plus_cartanInvolutionTimeReversal, cartanInvolutionTimeReversal_P_plus]

theorem P_minus_comm_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) (x : L) :
    C.S.P_minus ((cartanInvolutionTimeReversal C).op x) =
      (cartanInvolutionTimeReversal C).op (C.S.P_minus x) := by
  rw [P_minus_cartanInvolutionTimeReversal, cartanInvolutionTimeReversal_P_minus]

theorem P_plus_comp_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) :
    C.S.P_plus.comp (cartanInvolutionTimeReversal C).op =
      (cartanInvolutionTimeReversal C).op.comp C.S.P_plus := by
  ext x
  exact P_plus_comm_cartanInvolutionTimeReversal C x

theorem P_minus_comp_cartanInvolutionTimeReversal (C : CartanOnsagerSplit L) :
    C.S.P_minus.comp (cartanInvolutionTimeReversal C).op =
      (cartanInvolutionTimeReversal C).op.comp C.S.P_minus := by
  ext x
  exact P_minus_comm_cartanInvolutionTimeReversal C x

theorem bilinForm_cartanTimeReversal_eq_involution
    (C : CartanOnsagerSplit L) (B : LinearMap.BilinForm ℝ L) (x y : L) :
    B ((cartanTimeReversal C).op x) ((cartanTimeReversal C).op y) =
      B ((cartanInvolutionTimeReversal C).op x) ((cartanInvolutionTimeReversal C).op y) := by
  simp [cartanTimeReversal_apply, cartanInvolutionTimeReversal_apply]

/-! ## Part 2: `CartanOnsagerSplit L` → `OnsagerCasimirSystem L` & `ParityOnsagerSystem L` -/

/-- Dissipative bilinear form projected onto the `𝔭` (`T`-even) sector via `P_minus`. -/
def cartanProjectedDissipative (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L) : LinearMap.BilinForm ℝ L :=
  g.compl₁₂ C.S.P_minus C.S.P_minus

/-- Skew-symmetric reversible coupling between `𝔨` (`P_plus`) and `𝔭` (`P_minus`). -/
def cartanSkewCoupling (C : CartanOnsagerSplit L)
    (η : LinearMap.BilinForm ℝ L) : LinearMap.BilinForm ℝ L :=
  η.compl₁₂ C.S.P_plus C.S.P_minus - (η.compl₁₂ C.S.P_plus C.S.P_minus).flip

@[simp] theorem cartanProjectedDissipative_apply (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L) (x y : L) :
    cartanProjectedDissipative C g x y = g (C.S.P_minus x) (C.S.P_minus y) :=
  LinearMap.compl₁₂_apply g C.S.P_minus C.S.P_minus x y

@[simp] theorem cartanSkewCoupling_apply (C : CartanOnsagerSplit L)
    (η : LinearMap.BilinForm ℝ L) (x y : L) :
    cartanSkewCoupling C η x y =
      η (C.S.P_plus x) (C.S.P_minus y) - η (C.S.P_plus y) (C.S.P_minus x) := by
  simp [cartanSkewCoupling, LinearMap.compl₁₂_apply]

theorem cartanProjectedDissipative_symm (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L) (hg_symm : ∀ x y, g x y = g y x) (x y : L) :
    cartanProjectedDissipative C g x y = cartanProjectedDissipative C g y x := by
  simpa [cartanProjectedDissipative_apply] using hg_symm (C.S.P_minus x) (C.S.P_minus y)

theorem cartanProjectedDissipative_nonneg (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L) (hg_nonneg : ∀ x, 0 ≤ g x x) (x : L) :
    0 ≤ cartanProjectedDissipative C g x x := by
  simpa [cartanProjectedDissipative_apply] using hg_nonneg (C.S.P_minus x)

theorem cartanProjectedDissipative_T_even (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L) (x y : L) :
    cartanProjectedDissipative C g ((cartanTimeReversal C).op x) ((cartanTimeReversal C).op y) =
      cartanProjectedDissipative C g x y := by
  rw [cartanProjectedDissipative_apply, cartanProjectedDissipative_apply,
    P_minus_cartanTimeReversal, P_minus_cartanTimeReversal]

theorem cartanProjectedDissipative_eq_zero_left_of_mem_drazinCore
    (C : CartanOnsagerSplit L) (g : LinearMap.BilinForm ℝ L)
    {x : L} (hx : x ∈ C.drazinCore) (y : L) :
    cartanProjectedDissipative C g x y = 0 := by
  rw [C.drazinCore_eq_k] at hx
  have hP : C.S.P_minus x = 0 := by
    rw [C.S.P_minus_eq_minusPart]
    exact C.S.minusPart_of_mem_even hx
  simp [cartanProjectedDissipative_apply, hP]

theorem cartanSkewCoupling_skew (C : CartanOnsagerSplit L)
    (η : LinearMap.BilinForm ℝ L) (x y : L) :
    cartanSkewCoupling C η x y = -cartanSkewCoupling C η y x := by
  simp only [cartanSkewCoupling_apply]
  exact (neg_sub _ _).symm

theorem cartanSkewCoupling_T_odd (C : CartanOnsagerSplit L)
    (η : LinearMap.BilinForm ℝ L) (x y : L) :
    cartanSkewCoupling C η ((cartanTimeReversal C).op x) ((cartanTimeReversal C).op y) =
      -cartanSkewCoupling C η x y := by
  simp only [cartanSkewCoupling_apply, P_plus_cartanTimeReversal, P_minus_cartanTimeReversal,
    map_neg, LinearMap.neg_apply]
  rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, ← neg_sub]

theorem cartanSkewCoupling_eq_zero_of_mem_drazinCore
    (C : CartanOnsagerSplit L) (η : LinearMap.BilinForm ℝ L)
    {x y : L} (hx : x ∈ C.drazinCore) (hy : y ∈ C.drazinCore) :
    cartanSkewCoupling C η x y = 0 := by
  rw [C.drazinCore_eq_k] at hx hy
  have hx0 : C.S.P_minus x = 0 := by
    rw [C.S.P_minus_eq_minusPart]
    exact C.S.minusPart_of_mem_even hx
  have hy0 : C.S.P_minus y = 0 := by
    rw [C.S.P_minus_eq_minusPart]
    exact C.S.minusPart_of_mem_even hy
  simp [cartanSkewCoupling_apply, hx0, hy0]

theorem cartanSkewCoupling_eq_zero_of_mem_dissipativeRange
    (C : CartanOnsagerSplit L) (η : LinearMap.BilinForm ℝ L)
    {x y : L} (hx : x ∈ C.dissipativeRange) (hy : y ∈ C.dissipativeRange) :
    cartanSkewCoupling C η x y = 0 := by
  rw [C.dissipativeRange_eq_p] at hx hy
  have hx0 : C.S.P_plus x = 0 := by
    rw [C.S.P_plus_eq_plusPart]
    exact C.S.plusPart_of_mem_odd hx
  have hy0 : C.S.P_plus y = 0 := by
    rw [C.S.P_plus_eq_plusPart]
    exact C.S.plusPart_of_mem_odd hy
  simp [cartanSkewCoupling_apply, hx0, hy0]

/-- `OnsagerCasimirSystem L` constructed from a `CartanOnsagerSplit L` and arbitrary
symmetric PSD dissipative form `g` and coupling form `η`. -/
def cartanOnsagerSystemOfForms
    (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L)
    (hg_symm : ∀ x y, g x y = g y x)
    (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ L) :
    OnsagerCasimirSystem L where
  dissipative := cartanProjectedDissipative C g
  reversible := cartanSkewCoupling C η
  dissipative_symm x y := hg_symm (C.S.P_minus x) (C.S.P_minus y)
  reversible_skew x y := cartanSkewCoupling_skew C η x y
  dissipative_nonneg x := hg_nonneg (C.S.P_minus x)

/-- `ParityOnsagerSystem L` constructed from `CartanOnsagerSplit L` with `T = -θ`
(`cartanTimeReversal C`). -/
def cartanParityOnsagerSystemOfForms
    (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L)
    (hg_symm : ∀ x y, g x y = g y x)
    (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ L) :
    ParityOnsagerSystem L where
  toOnsagerCasimirSystem := cartanOnsagerSystemOfForms C g hg_symm hg_nonneg η
  T := cartanTimeReversal C
  dissipative_T_even := cartanProjectedDissipative_T_even C g
  reversible_T_odd := cartanSkewCoupling_T_odd C η

/-- `ParityOnsagerSystem L` constructed from `CartanOnsagerSplit L` with `T = +θ`
(`cartanInvolutionTimeReversal C`). -/
def cartanParityOnsagerSystemOfInvolution
    (C : CartanOnsagerSplit L)
    (g : LinearMap.BilinForm ℝ L)
    (hg_symm : ∀ x y, g x y = g y x)
    (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ L) :
    ParityOnsagerSystem L where
  toOnsagerCasimirSystem := cartanOnsagerSystemOfForms C g hg_symm hg_nonneg η
  T := cartanInvolutionTimeReversal C
  dissipative_T_even x y := by
    rw [← bilinForm_cartanTimeReversal_eq_involution]
    exact cartanProjectedDissipative_T_even C g x y
  reversible_T_odd x y := by
    rw [← bilinForm_cartanTimeReversal_eq_involution]
    exact cartanSkewCoupling_T_odd C η x y

/-- Direct `ParityOnsagerSystem L` from pre-existing `θ`-compatible dissipative and
reversible bilinear forms on `L`. -/
def cartanParityOnsagerSystemOfCompatibleForms
    (C : CartanOnsagerSplit L)
    (dissipative reversible : LinearMap.BilinForm ℝ L)
    (hdiss_symm : ∀ x y, dissipative x y = dissipative y x)
    (hdiss_nonneg : ∀ x, 0 ≤ dissipative x x)
    (hrev_skew : ∀ x y, reversible x y = -reversible y x)
    (hdiss_even : ∀ x y, dissipative (C.S.θ x) (C.S.θ y) = dissipative x y)
    (hrev_odd : ∀ x y, reversible (C.S.θ x) (C.S.θ y) = -reversible x y) :
    ParityOnsagerSystem L where
  dissipative := dissipative
  reversible := reversible
  dissipative_symm := hdiss_symm
  reversible_skew := hrev_skew
  dissipative_nonneg := hdiss_nonneg
  T := cartanTimeReversal C
  dissipative_T_even x y := by
    simp only [cartanTimeReversal_apply, map_neg, LinearMap.neg_apply, neg_neg]
    exact hdiss_even x y
  reversible_T_odd x y := by
    simp only [cartanTimeReversal_apply, map_neg, LinearMap.neg_apply, neg_neg]
    exact hrev_odd x y

/-- Any `θ`-even bilinear form vanishes between `C.drazinCore` (`𝔨`) and
`C.dissipativeRange` (`𝔭`). -/
theorem cartan_T_even_imp_orthogonal_core_range
    (C : CartanOnsagerSplit L) (B : LinearMap.BilinForm ℝ L)
    (hEven : ∀ x y, B (C.S.θ x) (C.S.θ y) = B x y)
    {k p : L} (hk : k ∈ C.drazinCore) (hp : p ∈ C.dissipativeRange) :
    B k p = 0 := by
  rw [C.drazinCore_eq_k] at hk
  rw [C.dissipativeRange_eq_p] at hp
  have hθk : C.S.θ k = k := (C.S.mem_evenSubmodule_iff).1 hk
  have hθp : C.S.θ p = -p := (C.S.mem_oddSubmodule_iff).1 hp
  have hEq : B k p = -B k p := by
    calc
      B k p = B (C.S.θ k) (C.S.θ p) := (hEven k p).symm
      _ = B k (-p) := by rw [hθk, hθp]
      _ = -B k p := by simp
  exact self_eq_neg.mp hEq

/-- Any `θ`-odd bilinear form vanishes on the diagonal sectors `𝔨 × 𝔨` and `𝔭 × 𝔭`. -/
theorem cartan_T_odd_imp_diag_sectors_zero
    (C : CartanOnsagerSplit L) (Ω : LinearMap.BilinForm ℝ L)
    (hOdd : ∀ x y, Ω (C.S.θ x) (C.S.θ y) = -Ω x y) :
    (∀ k₁ ∈ C.drazinCore, ∀ k₂ ∈ C.drazinCore, Ω k₁ k₂ = 0) ∧
      (∀ p₁ ∈ C.dissipativeRange, ∀ p₂ ∈ C.dissipativeRange, Ω p₁ p₂ = 0) := by
  constructor
  · intro k₁ hk₁ k₂ hk₂
    rw [C.drazinCore_eq_k] at hk₁ hk₂
    have h1 : C.S.θ k₁ = k₁ := (C.S.mem_evenSubmodule_iff).1 hk₁
    have h2 : C.S.θ k₂ = k₂ := (C.S.mem_evenSubmodule_iff).1 hk₂
    have hEq : Ω k₁ k₂ = -Ω k₁ k₂ := by
      calc
        Ω k₁ k₂ = -(Ω (C.S.θ k₁) (C.S.θ k₂)) := by rw [hOdd k₁ k₂, neg_neg]
        _ = -Ω k₁ k₂ := by rw [h1, h2]
    exact self_eq_neg.mp hEq
  · intro p₁ hp₁ p₂ hp₂
    rw [C.dissipativeRange_eq_p] at hp₁ hp₂
    have h1 : C.S.θ p₁ = -p₁ := (C.S.mem_oddSubmodule_iff).1 hp₁
    have h2 : C.S.θ p₂ = -p₂ := (C.S.mem_oddSubmodule_iff).1 hp₂
    have hEq : Ω p₁ p₂ = -Ω p₁ p₂ := by
      calc
        Ω p₁ p₂ = -(Ω (C.S.θ p₁) (C.S.θ p₂)) := by rw [hOdd p₁ p₂, neg_neg]
        _ = -(Ω (-p₁) (-p₂)) := by rw [h1, h2]
        _ = -Ω p₁ p₂ := by simp
    exact self_eq_neg.mp hEq

end CartanSplitTimeReversal

section OnsagerMetricBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Lift `OnsagerMetricData V` (`Flow.lean`) into `OnsagerCasimirSystem V` when the
pairing is represented by a bilinear form `B`. -/
def onsagerCasimirSystemOfMetricData
    (M : OnsagerMetricData V)
    (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, M.pairing x y = B x y) :
    OnsagerCasimirSystem V where
  dissipative := B.compl₁₂ LinearMap.id M.onsager
  reversible := 0
  dissipative_symm x y := by
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
    rw [← hB x (M.onsager y), ← hB y (M.onsager x)]
    exact M.metric_symmetric x y
  reversible_skew x y := by simp
  dissipative_nonneg x := by
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
    rw [← hB x (M.onsager x)]
    exact M.metric_nonnegative x

@[simp] theorem onsagerCasimirSystemOfMetricData_dissipative_diag
    (M : OnsagerMetricData V) (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, M.pairing x y = B x y) (x : V) :
    (onsagerCasimirSystemOfMetricData M B hB).dissipative x x = M.quadratic x := by
  simp only [onsagerCasimirSystemOfMetricData, LinearMap.compl₁₂_apply, LinearMap.id_apply]
  rw [← hB x (M.onsager x)]
  rfl

end OnsagerMetricBridge

/-! ## Part 2b: Specialization to `DrazinCartanOnsagerBridge` (`CartanBridge.lean`) -/

section DrazinCartanBridgeSection

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Unconditional `TimeReversal (E →L[ℝ] E)` associated to a `DrazinCartanOnsagerBridge`
(`-θ_S`, so noncompact sector is `T`-even and compact sector is `T`-odd). -/
def drazinCartanTimeReversal
    (B : DrazinCartanOnsagerBridge (E := E)) : TimeReversal (E →L[ℝ] E) :=
  cartanTimeReversal B.toCartanOnsagerSplit

/-- Unconditional involution `TimeReversal (E →L[ℝ] E)` (`+θ_S`) associated to a
`DrazinCartanOnsagerBridge`. -/
def drazinCartanInvolutionTimeReversal
    (B : DrazinCartanOnsagerBridge (E := E)) : TimeReversal (E →L[ℝ] E) :=
  cartanInvolutionTimeReversal B.toCartanOnsagerSplit

theorem drazinCartanTimeReversal_eq_neg_of_isSpectralCompact
    (B : DrazinCartanOnsagerBridge (E := E)) {X : E →L[ℝ] E}
    (hX : B.CIK.IsSpectralCompact X) :
    (drazinCartanTimeReversal B).op X = -X := by
  have hcomm : X * B.CIK.GammaS = B.CIK.GammaS * X :=
    B.CIK.isSpectralCompact_iff_commute_GammaS.mp hX
  change -(B.CIK.GammaS * X * B.CIK.GammaS) = -X
  calc
    -(B.CIK.GammaS * X * B.CIK.GammaS) = -(B.CIK.GammaS * (X * B.CIK.GammaS)) := by
      rw [mul_assoc]
    _ = -(B.CIK.GammaS * (B.CIK.GammaS * X)) := by rw [hcomm]
    _ = -((B.CIK.GammaS * B.CIK.GammaS) * X) := by rw [← mul_assoc]
    _ = -(1 * X) := by rw [B.CIK.GammaS_sq_eq_one]
    _ = -X := by rw [one_mul]

theorem drazinCartanTimeReversal_eq_self_of_isSpectralNonCompact
    (B : DrazinCartanOnsagerBridge (E := E)) {X : E →L[ℝ] E}
    (hX : B.CIK.IsSpectralNonCompact X) :
    (drazinCartanTimeReversal B).op X = X := by
  have hanti : X * B.CIK.GammaS = -(B.CIK.GammaS * X) :=
    B.CIK.isSpectralNonCompact_iff_anticommute_GammaS.mp hX
  change -(B.CIK.GammaS * X * B.CIK.GammaS) = X
  calc
    -(B.CIK.GammaS * X * B.CIK.GammaS) = -(B.CIK.GammaS * (X * B.CIK.GammaS)) := by
      rw [mul_assoc]
    _ = -(B.CIK.GammaS * -(B.CIK.GammaS * X)) := by rw [hanti]
    _ = (B.CIK.GammaS * B.CIK.GammaS) * X := by
      rw [mul_neg, neg_neg, ← mul_assoc]
    _ = 1 * X := by rw [B.CIK.GammaS_sq_eq_one]
    _ = X := by rw [one_mul]

theorem drazinCartanTimeReversal_spectralProjector
    (B : DrazinCartanOnsagerBridge (E := E)) :
    (drazinCartanTimeReversal B).op B.CIK.spectralProjector = -B.CIK.spectralProjector :=
  drazinCartanTimeReversal_eq_neg_of_isSpectralCompact B B.CIK.spectralProjector_isSpectralCompact

theorem drazinCartanTimeReversal_spectralComplementaryProjector
    (B : DrazinCartanOnsagerBridge (E := E)) :
    (drazinCartanTimeReversal B).op B.CIK.spectralComplementaryProjector =
      -B.CIK.spectralComplementaryProjector :=
  drazinCartanTimeReversal_eq_neg_of_isSpectralCompact B
    B.CIK.spectralComplementaryProjector_isSpectralCompact

theorem drazinCartanTimeReversal_GammaS
    (B : DrazinCartanOnsagerBridge (E := E)) :
    (drazinCartanTimeReversal B).op B.CIK.GammaS = -B.CIK.GammaS := by
  change -B.CIK.thetaS B.CIK.GammaS = -B.CIK.GammaS
  have hθ : B.CIK.thetaS B.CIK.GammaS = B.CIK.GammaS := by
    change B.CIK.GammaS.comp (B.CIK.GammaS.comp B.CIK.GammaS) = B.CIK.GammaS
    rw [← ContinuousLinearMap.comp_assoc, GammaS_comp_GammaS B.CIK, ContinuousLinearMap.id_comp]
  rw [hθ]

/-- General `ParityOnsagerSystem (E →L[ℝ] E)` induced by `DrazinCartanOnsagerBridge` and
any symmetric PSD form `g` plus skew-coupling form `η`. -/
def drazinCartanParityOnsagerSystem
    (B : DrazinCartanOnsagerBridge (E := E))
    (g : LinearMap.BilinForm ℝ (E →L[ℝ] E))
    (hg_symm : ∀ x y, g x y = g y x)
    (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ (E →L[ℝ] E)) :
    ParityOnsagerSystem (E →L[ℝ] E) :=
  cartanParityOnsagerSystemOfForms B.toCartanOnsagerSplit g hg_symm hg_nonneg η

/-- Concrete `InnerProductSpace ℝ E` probe bilinear form `(X, Y) ↦ ⟪X u, Y u⟫_ℝ`. -/
def operatorProbeBilin (u : E) : LinearMap.BilinForm ℝ (E →L[ℝ] E) :=
  LinearMap.mk₂ ℝ
    (fun X Y : E →L[ℝ] E => @inner ℝ E _ (X u) (Y u))
    (fun X₁ X₂ Y => by simp [inner_add_left])
    (fun r X Y => by simp [inner_smul_left])
    (fun X Y₁ Y₂ => by simp [inner_add_right])
    (fun r X Y => by simp [inner_smul_right])

omit [CompleteSpace E] in
@[simp] theorem operatorProbeBilin_apply (u : E) (X Y : E →L[ℝ] E) :
    operatorProbeBilin u X Y = @inner ℝ E _ (X u) (Y u) := rfl

omit [CompleteSpace E] in
theorem operatorProbeBilin_symm (u : E) (X Y : E →L[ℝ] E) :
    operatorProbeBilin u X Y = operatorProbeBilin u Y X :=
  real_inner_comm (Y u) (X u)

omit [CompleteSpace E] in
theorem operatorProbeBilin_nonneg (u : E) (X : E →L[ℝ] E) :
    0 ≤ operatorProbeBilin u X X :=
  real_inner_self_nonneg

/-- Concrete `ParityOnsagerSystem (E →L[ℝ] E)` instantiated from `DrazinCartanOnsagerBridge`
using the `InnerProductSpace` probe form `operatorProbeBilin u`. -/
def drazinCartanParityOnsagerSystemOfProbe
    (B : DrazinCartanOnsagerBridge (E := E)) (u : E)
    (η : LinearMap.BilinForm ℝ (E →L[ℝ] E)) :
    ParityOnsagerSystem (E →L[ℝ] E) :=
  drazinCartanParityOnsagerSystem B (operatorProbeBilin u)
    (operatorProbeBilin_symm u) (operatorProbeBilin_nonneg u) η

end DrazinCartanBridgeSection

/-! ## Part 3: `ScalarSchurDrazinBlock` & `DrazinPenroseSchurTriad` (`Axioms.lean`) -/

section ScalarSchurDrazinSection

/-- When the body force in `DrazinPenroseSchurTriad` is nonzero, body entropy
nonnegativity implies nonnegativity of the Schur-complement coefficient
`T.block.effectiveEvenOnsager`. -/
theorem effectiveEvenOnsager_nonneg_of_triad
    (T : DrazinPenroseSchurTriad)
    (hForce : T.entropy.bodyForce ≠ 0) :
    0 ≤ T.block.effectiveEvenOnsager := by
  have hprod : 0 ≤ T.entropy.bodyForce * T.block.effectiveEvenOnsager * T.entropy.bodyForce := by
    simpa [T.entropy.production_eq, T.entropy_uses_effective_block] using T.entropy.production_nonneg
  have hsq : 0 < T.entropy.bodyForce * T.entropy.bodyForce := mul_self_pos.mpr hForce
  by_contra hlt
  push Not at hlt
  have hneg : T.entropy.bodyForce * T.block.effectiveEvenOnsager * T.entropy.bodyForce < 0 := by
    nlinarith
  linarith

/-- Scalar bilinear form `(x, y) ↦ a * x * y` on `ℝ`. -/
def scalarEffectiveDissipative (a : ℝ) : LinearMap.BilinForm ℝ ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => a * x * y)
    (fun x₁ x₂ y => by rw [mul_add, add_mul])
    (fun r x y => by simp only [smul_eq_mul]; rw [mul_left_comm, mul_assoc])
    (fun x y₁ y₂ => by rw [mul_add])
    (fun r x y => by simp only [smul_eq_mul]; rw [mul_left_comm, mul_assoc])

@[simp] theorem scalarEffectiveDissipative_apply (a x y : ℝ) :
    scalarEffectiveDissipative a x y = a * x * y := rfl

/-- `TimeReversal ℝ` acting as `+1` (`T`-even Schur-reduced sector). -/
def scalarIdTimeReversal : TimeReversal ℝ where
  op := LinearMap.id
  involutive _ := rfl

/-- `TimeReversal ℝ` acting as `-1` (`T`-odd sector). -/
def scalarNegTimeReversal : TimeReversal ℝ where
  op := -LinearMap.id
  involutive x := by simp

/-- 1D `OnsagerCasimirSystem ℝ` driven by `B.effectiveEvenOnsager`. -/
def scalarEffectiveOnsagerSystem
    (B : ScalarSchurDrazinBlock)
    (hEff : 0 ≤ B.effectiveEvenOnsager) :
    OnsagerCasimirSystem ℝ where
  dissipative := scalarEffectiveDissipative B.effectiveEvenOnsager
  reversible := 0
  dissipative_symm x y := by simp only [scalarEffectiveDissipative_apply]; ring
  reversible_skew x y := by simp
  dissipative_nonneg x := by
    simp only [scalarEffectiveDissipative_apply]
    nlinarith [sq_nonneg x]

/-- 1D `ParityOnsagerSystem ℝ` driven by `B.effectiveEvenOnsager` with `T = id`. -/
def scalarEffectiveParityOnsagerSystem
    (B : ScalarSchurDrazinBlock)
    (hEff : 0 ≤ B.effectiveEvenOnsager) :
    ParityOnsagerSystem ℝ where
  toOnsagerCasimirSystem := scalarEffectiveOnsagerSystem B hEff
  T := scalarIdTimeReversal
  dissipative_T_even _ _ := rfl
  reversible_T_odd _ _ := by simp [scalarEffectiveOnsagerSystem]

/-- 1D `OnsagerCasimirSystem ℝ` derived directly from a `DrazinPenroseSchurTriad`
when `T.entropy.bodyForce ≠ 0`. -/
def triadEffectiveOnsagerSystem
    (T : DrazinPenroseSchurTriad)
    (hForce : T.entropy.bodyForce ≠ 0) :
    OnsagerCasimirSystem ℝ :=
  scalarEffectiveOnsagerSystem T.block (effectiveEvenOnsager_nonneg_of_triad T hForce)

/-- 1D `ParityOnsagerSystem ℝ` derived directly from a `DrazinPenroseSchurTriad`
when `T.entropy.bodyForce ≠ 0`. -/
def triadEffectiveParityOnsagerSystem
    (T : DrazinPenroseSchurTriad)
    (hForce : T.entropy.bodyForce ≠ 0) :
    ParityOnsagerSystem ℝ :=
  scalarEffectiveParityOnsagerSystem T.block (effectiveEvenOnsager_nonneg_of_triad T hForce)

private theorem twoBlockSym_add_left (a b c : ℝ) (x₁ x₂ y : Fin 2 → ℝ) :
    a * (x₁ + x₂) 0 * y 0 + b * ((x₁ + x₂) 0 * y 1 + (x₁ + x₂) 1 * y 0) + c * (x₁ + x₂) 1 * y 1 =
      (a * x₁ 0 * y 0 + b * (x₁ 0 * y 1 + x₁ 1 * y 0) + c * x₁ 1 * y 1) +
        (a * x₂ 0 * y 0 + b * (x₂ 0 * y 1 + x₂ 1 * y 0) + c * x₂ 1 * y 1) := by
  simp only [Pi.add_apply]; ring

private theorem twoBlockSym_smul_left (a b c r : ℝ) (x y : Fin 2 → ℝ) :
    a * (r • x) 0 * y 0 + b * ((r • x) 0 * y 1 + (r • x) 1 * y 0) + c * (r • x) 1 * y 1 =
      r • (a * x 0 * y 0 + b * (x 0 * y 1 + x 1 * y 0) + c * x 1 * y 1) := by
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem twoBlockSym_add_right (a b c : ℝ) (x y₁ y₂ : Fin 2 → ℝ) :
    a * x 0 * (y₁ + y₂) 0 + b * (x 0 * (y₁ + y₂) 1 + x 1 * (y₁ + y₂) 0) + c * x 1 * (y₁ + y₂) 1 =
      (a * x 0 * y₁ 0 + b * (x 0 * y₁ 1 + x 1 * y₁ 0) + c * x 1 * y₁ 1) +
        (a * x 0 * y₂ 0 + b * (x 0 * y₂ 1 + x 1 * y₂ 0) + c * x 1 * y₂ 1) := by
  simp only [Pi.add_apply]; ring

private theorem twoBlockSym_smul_right (a b c r : ℝ) (x y : Fin 2 → ℝ) :
    a * x 0 * (r • y) 0 + b * (x 0 * (r • y) 1 + x 1 * (r • y) 0) + c * x 1 * (r • y) 1 =
      r • (a * x 0 * y 0 + b * (x 0 * y 1 + x 1 * y 0) + c * x 1 * y 1) := by
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem twoBlockSkew_add_left (c : ℝ) (x₁ x₂ y : Fin 2 → ℝ) :
    c * ((x₁ + x₂) 0 * y 1 - (x₁ + x₂) 1 * y 0) =
      c * (x₁ 0 * y 1 - x₁ 1 * y 0) + c * (x₂ 0 * y 1 - x₂ 1 * y 0) := by
  simp only [Pi.add_apply]; ring

private theorem twoBlockSkew_smul_left (c r : ℝ) (x y : Fin 2 → ℝ) :
    c * ((r • x) 0 * y 1 - (r • x) 1 * y 0) = r • (c * (x 0 * y 1 - x 1 * y 0)) := by
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem twoBlockSkew_add_right (c : ℝ) (x y₁ y₂ : Fin 2 → ℝ) :
    c * (x 0 * (y₁ + y₂) 1 - x 1 * (y₁ + y₂) 0) =
      c * (x 0 * y₁ 1 - x 1 * y₁ 0) + c * (x 0 * y₂ 1 - x 1 * y₂ 0) := by
  simp only [Pi.add_apply]; ring

private theorem twoBlockSkew_smul_right (c r : ℝ) (x y : Fin 2 → ℝ) :
    c * (x 0 * (r • y) 1 - x 1 * (r • y) 0) = r • (c * (x 0 * y 1 - x 1 * y 0)) := by
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Symmetric part of the 2×2 block `[[LPP, LPΘ], [LΘP, LΘΘ]]` on `Fin 2 → ℝ`. -/
def scalarTwoBlockDissipative (B : ScalarSchurDrazinBlock) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => B.LPP * x 0 * y 0
      + ((B.LPΘ + B.LΘP) / 2) * (x 0 * y 1 + x 1 * y 0)
      + B.LΘΘ * x 1 * y 1)
    (twoBlockSym_add_left B.LPP ((B.LPΘ + B.LΘP) / 2) B.LΘΘ)
    (fun r x y => twoBlockSym_smul_left B.LPP ((B.LPΘ + B.LΘP) / 2) B.LΘΘ r x y)
    (twoBlockSym_add_right B.LPP ((B.LPΘ + B.LΘP) / 2) B.LΘΘ)
    (fun r x y => twoBlockSym_smul_right B.LPP ((B.LPΘ + B.LΘP) / 2) B.LΘΘ r x y)

/-- Skew-symmetric part of the 2×2 block `[[LPP, LPΘ], [LΘP, LΘΘ]]` on `Fin 2 → ℝ`. -/
def scalarTwoBlockReversible (B : ScalarSchurDrazinBlock) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => ((B.LPΘ - B.LΘP) / 2) * (x 0 * y 1 - x 1 * y 0))
    (twoBlockSkew_add_left ((B.LPΘ - B.LΘP) / 2))
    (fun r x y => twoBlockSkew_smul_left ((B.LPΘ - B.LΘP) / 2) r x y)
    (twoBlockSkew_add_right ((B.LPΘ - B.LΘP) / 2))
    (fun r x y => twoBlockSkew_smul_right ((B.LPΘ - B.LΘP) / 2) r x y)

@[simp] theorem scalarTwoBlockDissipative_apply (B : ScalarSchurDrazinBlock)
    (x y : Fin 2 → ℝ) :
    scalarTwoBlockDissipative B x y =
      B.LPP * x 0 * y 0 + ((B.LPΘ + B.LΘP) / 2) * (x 0 * y 1 + x 1 * y 0) + B.LΘΘ * x 1 * y 1 :=
  rfl

@[simp] theorem scalarTwoBlockReversible_apply (B : ScalarSchurDrazinBlock)
    (x y : Fin 2 → ℝ) :
    scalarTwoBlockReversible B x y =
      ((B.LPΘ - B.LΘP) / 2) * (x 0 * y 1 - x 1 * y 0) :=
  rfl

theorem scalarTwoBlock_sum_eq (B : ScalarSchurDrazinBlock) (x y : Fin 2 → ℝ) :
    scalarTwoBlockDissipative B x y + scalarTwoBlockReversible B x y =
      B.LPP * x 0 * y 0 + B.LPΘ * x 0 * y 1 + B.LΘP * x 1 * y 0 + B.LΘΘ * x 1 * y 1 := by
  simp only [scalarTwoBlockDissipative_apply, scalarTwoBlockReversible_apply]
  ring

/-- `P`-even / `Θ`-odd time reversal `(x₀, x₁) ↦ (x₀, -x₁)` on `Fin 2 → ℝ`. -/
def scalarTwoBlockTimeReversal : TimeReversal (Fin 2 → ℝ) where
  op :=
    { toFun := fun x i => if i = 0 then x 0 else -x 1
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp }
  involutive := fun x => by
    ext i
    fin_cases i <;> simp

@[simp] theorem scalarTwoBlockTimeReversal_apply_zero (x : Fin 2 → ℝ) :
    scalarTwoBlockTimeReversal.op x 0 = x 0 := rfl

@[simp] theorem scalarTwoBlockTimeReversal_apply_one (x : Fin 2 → ℝ) :
    scalarTwoBlockTimeReversal.op x 1 = -x 1 := rfl

theorem scalarTwoBlock_psd_of_det_nonneg (B : ScalarSchurDrazinBlock)
    (hLPP : 0 ≤ B.LPP) (hLΘΘ : 0 ≤ B.LΘΘ)
    (hdet : (B.LPΘ + B.LΘP) ^ 2 ≤ 4 * B.LPP * B.LΘΘ)
    (x : Fin 2 → ℝ) :
    0 ≤ B.LPP * x 0 * x 0 + (B.LPΘ + B.LΘP) * x 0 * x 1 + B.LΘΘ * x 1 * x 1 := by
  by_cases h0 : B.LPP = 0
  · have hcross : B.LPΘ + B.LΘP = 0 := by
      have hsq : (B.LPΘ + B.LΘP) ^ 2 ≤ 0 := by simpa [h0] using hdet
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    rw [h0, hcross]
    nlinarith [sq_nonneg (x 1)]
  · have hpos : 0 < B.LPP := lt_of_le_of_ne hLPP (Ne.symm h0)
    have hmul : 0 ≤ B.LPP * (B.LPP * x 0 * x 0 + (B.LPΘ + B.LΘP) * x 0 * x 1 + B.LΘΘ * x 1 * x 1) := by
      have hsq : (B.LPP * x 0 + ((B.LPΘ + B.LΘP) / 2) * x 1) ^ 2 ≥ 0 := sq_nonneg _
      have hdisc : (B.LPP * B.LΘΘ - ((B.LPΘ + B.LΘP) / 2) ^ 2) * x 1 ^ 2 ≥ 0 := by
        apply mul_nonneg _ (sq_nonneg (x 1))
        linarith
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul hpos

/-- General 2-block `(P, Θ)` `OnsagerCasimirSystem (Fin 2 → ℝ)` (no Casimir assumption). -/
def scalarTwoBlockOnsagerSystem
    (B : ScalarSchurDrazinBlock)
    (hPSD : ∀ x : Fin 2 → ℝ,
      0 ≤ B.LPP * x 0 * x 0 + (B.LPΘ + B.LΘP) * x 0 * x 1 + B.LΘΘ * x 1 * x 1) :
    OnsagerCasimirSystem (Fin 2 → ℝ) where
  dissipative := scalarTwoBlockDissipative B
  reversible := scalarTwoBlockReversible B
  dissipative_symm x y := by simp only [scalarTwoBlockDissipative_apply]; ring
  reversible_skew x y := by simp only [scalarTwoBlockReversible_apply]; ring
  dissipative_nonneg x := by
    have h := hPSD x
    have heq : scalarTwoBlockDissipative B x x =
        B.LPP * x 0 * x 0 + (B.LPΘ + B.LΘP) * x 0 * x 1 + B.LΘΘ * x 1 * x 1 := by
      simp only [scalarTwoBlockDissipative_apply]
      ring
    rw [heq]
    exact h

/-- Minimal Casimir-parity 2-block `(P, Θ)` `ParityOnsagerSystem (Fin 2 → ℝ)` under
`(x₀, x₁) ↦ (x₀, -x₁)`, requiring only `0 ≤ LPP`, `0 ≤ LΘΘ`, and `LPΘ + LΘP = 0`. -/
def scalarTwoBlockParityOnsagerSystem
    (B : ScalarSchurDrazinBlock)
    (hLPP : 0 ≤ B.LPP) (hLΘΘ : 0 ≤ B.LΘΘ)
    (hCasimir : B.LPΘ + B.LΘP = 0) :
    ParityOnsagerSystem (Fin 2 → ℝ) where
  dissipative := scalarTwoBlockDissipative B
  reversible := scalarTwoBlockReversible B
  dissipative_symm x y := by simp only [scalarTwoBlockDissipative_apply]; ring
  reversible_skew x y := by simp only [scalarTwoBlockReversible_apply]; ring
  dissipative_nonneg x := by
    simp only [scalarTwoBlockDissipative_apply, hCasimir]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  T := scalarTwoBlockTimeReversal
  dissipative_T_even x y := by
    simp only [scalarTwoBlockDissipative_apply, scalarTwoBlockTimeReversal_apply_zero,
      scalarTwoBlockTimeReversal_apply_one, hCasimir]
    ring
  reversible_T_odd x y := by
    simp only [scalarTwoBlockReversible_apply, scalarTwoBlockTimeReversal_apply_zero,
      scalarTwoBlockTimeReversal_apply_one]
    ring

/-- Schur-reduced 2-block `(P, Θ)` `ParityOnsagerSystem (Fin 2 → ℝ)` placing
`B.effectiveEvenOnsager` on the `P`-channel and `B.LΘΘ` on the `Θ`-channel. -/
def scalarSchurReducedTwoBlockDissipative (B : ScalarSchurDrazinBlock) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => B.effectiveEvenOnsager * x 0 * y 0 + B.LΘΘ * x 1 * y 1)
    (fun x₁ x₂ y => by
      simpa using twoBlockSym_add_left B.effectiveEvenOnsager 0 B.LΘΘ x₁ x₂ y)
    (fun r x y => by
      simpa using twoBlockSym_smul_left B.effectiveEvenOnsager 0 B.LΘΘ r x y)
    (fun x y₁ y₂ => by
      simpa using twoBlockSym_add_right B.effectiveEvenOnsager 0 B.LΘΘ x y₁ y₂)
    (fun r x y => by
      simpa using twoBlockSym_smul_right B.effectiveEvenOnsager 0 B.LΘΘ r x y)

@[simp] theorem scalarSchurReducedTwoBlockDissipative_apply
    (B : ScalarSchurDrazinBlock) (x y : Fin 2 → ℝ) :
    scalarSchurReducedTwoBlockDissipative B x y =
      B.effectiveEvenOnsager * x 0 * y 0 + B.LΘΘ * x 1 * y 1 := rfl

def scalarSchurReducedTwoBlockParityOnsagerSystem
    (B : ScalarSchurDrazinBlock)
    (hEff : 0 ≤ B.effectiveEvenOnsager)
    (hLΘΘ : 0 ≤ B.LΘΘ) :
    ParityOnsagerSystem (Fin 2 → ℝ) where
  dissipative := scalarSchurReducedTwoBlockDissipative B
  reversible := scalarTwoBlockReversible B
  dissipative_symm x y := by simp only [scalarSchurReducedTwoBlockDissipative_apply]; ring
  reversible_skew x y := by simp only [scalarTwoBlockReversible_apply]; ring
  dissipative_nonneg x := by
    simp only [scalarSchurReducedTwoBlockDissipative_apply]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  T := scalarTwoBlockTimeReversal
  dissipative_T_even x y := by
    simp only [scalarSchurReducedTwoBlockDissipative_apply,
      scalarTwoBlockTimeReversal_apply_zero, scalarTwoBlockTimeReversal_apply_one]
    ring
  reversible_T_odd x y := by
    simp only [scalarTwoBlockReversible_apply,
      scalarTwoBlockTimeReversal_apply_zero, scalarTwoBlockTimeReversal_apply_one]
    ring

theorem scalarSchurReducedTwoBlock_restrict_zero
    (B : ScalarSchurDrazinBlock) (hEff : 0 ≤ B.effectiveEvenOnsager)
    (hLΘΘ : 0 ≤ B.LΘΘ) (u v : ℝ) :
    (scalarSchurReducedTwoBlockParityOnsagerSystem B hEff hLΘΘ).totalGenerator ![u, 0] ![v, 0] =
      (scalarEffectiveOnsagerSystem B hEff).totalGenerator u v := by
  simp [totalGenerator, scalarSchurReducedTwoBlockParityOnsagerSystem,
    scalarEffectiveOnsagerSystem, scalarSchurReducedTwoBlockDissipative_apply,
    scalarTwoBlockReversible_apply, scalarEffectiveDissipative_apply]

end ScalarSchurDrazinSection

/-! ## Part 4: `TKKOnsagerMatrix` (`Blocks.lean`) → `OnsagerCasimirSystem` & `ParityOnsagerSystem` -/

section TKKSection

/-- Explicit 3-term sum over `TKKGrade` without introducing an orphan `Fintype TKKGrade`. -/
def tkkSum (f : TKKGrade → ℝ) : ℝ :=
  f .minus + f .zero + f .plus

theorem tkkSum_add (f g : TKKGrade → ℝ) :
    tkkSum (fun i => f i + g i) = tkkSum f + tkkSum g := by
  simp only [tkkSum]
  ring

theorem tkkSum_smul (r : ℝ) (f : TKKGrade → ℝ) :
    tkkSum (fun i => r * f i) = r * tkkSum f := by
  simp only [tkkSum]
  ring

private theorem tkkBilin_add_left (E : TKKGrade → TKKGrade → ℝ) (x₁ x₂ y : TKKGrade → ℝ) :
    tkkSum (fun i => tkkSum (fun j => (x₁ + x₂) i * E i j * y j)) =
      tkkSum (fun i => tkkSum (fun j => x₁ i * E i j * y j)) +
        tkkSum (fun i => tkkSum (fun j => x₂ i * E i j * y j)) := by
  simp only [Pi.add_apply, tkkSum]
  ring

private theorem tkkBilin_smul_left (E : TKKGrade → TKKGrade → ℝ) (r : ℝ) (x y : TKKGrade → ℝ) :
    tkkSum (fun i => tkkSum (fun j => (r • x) i * E i j * y j)) =
      r • tkkSum (fun i => tkkSum (fun j => x i * E i j * y j)) := by
  simp only [Pi.smul_apply, smul_eq_mul, tkkSum]
  ring

private theorem tkkBilin_add_right (E : TKKGrade → TKKGrade → ℝ) (x y₁ y₂ : TKKGrade → ℝ) :
    tkkSum (fun i => tkkSum (fun j => x i * E i j * (y₁ + y₂) j)) =
      tkkSum (fun i => tkkSum (fun j => x i * E i j * y₁ j)) +
        tkkSum (fun i => tkkSum (fun j => x i * E i j * y₂ j)) := by
  simp only [Pi.add_apply, tkkSum]
  ring

private theorem tkkBilin_smul_right (E : TKKGrade → TKKGrade → ℝ) (r : ℝ) (x y : TKKGrade → ℝ) :
    tkkSum (fun i => tkkSum (fun j => x i * E i j * (r • y) j)) =
      r • tkkSum (fun i => tkkSum (fun j => x i * E i j * y j)) := by
  simp only [Pi.smul_apply, smul_eq_mul, tkkSum]
  ring

/-- Symmetric bilinear form on `TKKGrade → ℝ` determined by `M : TKKOnsagerMatrix`. -/
def tkkDissipativeForm (M : TKKOnsagerMatrix) :
    LinearMap.BilinForm ℝ (TKKGrade → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => tkkSum (fun i => tkkSum (fun j => x i * M.entry i j * y j)))
    (tkkBilin_add_left M.entry)
    (fun r x y => tkkBilin_smul_left M.entry r x y)
    (tkkBilin_add_right M.entry)
    (fun r x y => tkkBilin_smul_right M.entry r x y)

@[simp] theorem tkkDissipativeForm_apply (M : TKKOnsagerMatrix)
    (x y : TKKGrade → ℝ) :
    tkkDissipativeForm M x y =
      tkkSum (fun i => tkkSum (fun j => x i * M.entry i j * y j)) := rfl

theorem tkkDissipativeForm_symm (M : TKKOnsagerMatrix) (x y : TKKGrade → ℝ) :
    tkkDissipativeForm M x y = tkkDissipativeForm M y x := by
  simp only [tkkDissipativeForm_apply, tkkSum]
  rw [M.reciprocal .minus .zero, M.reciprocal .minus .plus, M.reciprocal .zero .plus]
  ring

/-- Skew bilinear form on `TKKGrade → ℝ` determined by a skew matrix `Ω`. -/
def tkkSkewForm (Ω : TKKGrade → TKKGrade → ℝ) :
    LinearMap.BilinForm ℝ (TKKGrade → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => tkkSum (fun i => tkkSum (fun j => x i * Ω i j * y j)))
    (tkkBilin_add_left Ω)
    (fun r x y => tkkBilin_smul_left Ω r x y)
    (tkkBilin_add_right Ω)
    (fun r x y => tkkBilin_smul_right Ω r x y)

@[simp] theorem tkkSkewForm_apply (Ω : TKKGrade → TKKGrade → ℝ) (x y : TKKGrade → ℝ) :
    tkkSkewForm Ω x y =
      tkkSum (fun i => tkkSum (fun j => x i * Ω i j * y j)) := rfl

theorem tkkSkewForm_skew (Ω : TKKGrade → TKKGrade → ℝ)
    (hΩ_skew : ∀ i j, Ω i j = -Ω j i) (x y : TKKGrade → ℝ) :
    tkkSkewForm Ω x y = -tkkSkewForm Ω y x := by
  simp only [tkkSkewForm_apply, tkkSum]
  have hmm : Ω .minus .minus = 0 := by have h := hΩ_skew .minus .minus; linarith
  have hzz : Ω .zero .zero = 0 := by have h := hΩ_skew .zero .zero; linarith
  have hpp : Ω .plus .plus = 0 := by have h := hΩ_skew .plus .plus; linarith
  rw [hmm, hzz, hpp, hΩ_skew .minus .zero, hΩ_skew .minus .plus, hΩ_skew .zero .plus]
  ring

/-- Grade-reversing `TimeReversal (TKKGrade → ℝ)` induced by `TKKGrade.dual`. -/
def tkkDualTimeReversal : TimeReversal (TKKGrade → ℝ) where
  op :=
    { toFun := fun v g => v g.dual
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  involutive v := by
    funext g
    simp [TKKGrade.dual_dual]

@[simp] theorem tkkDualTimeReversal_apply (v : TKKGrade → ℝ) (g : TKKGrade) :
    tkkDualTimeReversal.op v g = v g.dual := rfl

/-- `OnsagerCasimirSystem (TKKGrade → ℝ)` from `TKKOnsagerMatrix` and a PSD witness. -/
def tkkOnsagerSystem
    (M : TKKOnsagerMatrix)
    (hPSD : ∀ v : TKKGrade → ℝ, 0 ≤ tkkSum (fun i => tkkSum (fun j => v i * M.entry i j * v j))) :
    OnsagerCasimirSystem (TKKGrade → ℝ) where
  dissipative := tkkDissipativeForm M
  reversible := 0
  dissipative_symm := tkkDissipativeForm_symm M
  reversible_skew _ _ := by simp
  dissipative_nonneg := hPSD

/-- `ParityOnsagerSystem (TKKGrade → ℝ)` from `TKKOnsagerMatrix`, PSD witness, and
`TKKGrade.dual`-invariance of `M.entry`. -/
def tkkParityOnsagerSystem
    (M : TKKOnsagerMatrix)
    (hPSD : ∀ v : TKKGrade → ℝ, 0 ≤ tkkSum (fun i => tkkSum (fun j => v i * M.entry i j * v j)))
    (hDual : ∀ i j : TKKGrade, M.entry i.dual j.dual = M.entry i j) :
    ParityOnsagerSystem (TKKGrade → ℝ) where
  toOnsagerCasimirSystem := tkkOnsagerSystem M hPSD
  T := tkkDualTimeReversal
  dissipative_T_even x y := by
    simp only [tkkOnsagerSystem, tkkDissipativeForm_apply, tkkDualTimeReversal_apply, tkkSum,
      TKKGrade.dual]
    have hmm : M.entry .plus .plus = M.entry .minus .minus := hDual .minus .minus
    have hmp : M.entry .plus .minus = M.entry .minus .plus := hDual .minus .plus
    have hmz : M.entry .plus .zero = M.entry .minus .zero := hDual .minus .zero
    have hpm : M.entry .minus .plus = M.entry .plus .minus := hDual .plus .minus
    have hpp : M.entry .minus .minus = M.entry .plus .plus := hDual .plus .plus
    have hpz : M.entry .minus .zero = M.entry .plus .zero := hDual .plus .zero
    have hzm : M.entry .zero .plus = M.entry .zero .minus := hDual .zero .minus
    have hzp : M.entry .zero .minus = M.entry .zero .plus := hDual .zero .plus
    rw [hmm, hmp, hmz, hpz, hzm, hzp]
    ring
  reversible_T_odd _ _ := by simp [tkkOnsagerSystem]

/-- Generalized `ParityOnsagerSystem (TKKGrade → ℝ)` with nonzero `T`-odd skew coupling `Ω`. -/
def tkkParityOnsagerSystemWithSkew
    (M : TKKOnsagerMatrix)
    (hPSD : ∀ v : TKKGrade → ℝ, 0 ≤ tkkSum (fun i => tkkSum (fun j => v i * M.entry i j * v j)))
    (hDual : ∀ i j : TKKGrade, M.entry i.dual j.dual = M.entry i j)
    (Ω : TKKGrade → TKKGrade → ℝ)
    (hΩ_skew : ∀ i j, Ω i j = -Ω j i)
    (hΩ_odd : ∀ i j, Ω i.dual j.dual = -Ω i j) :
    ParityOnsagerSystem (TKKGrade → ℝ) where
  dissipative := tkkDissipativeForm M
  reversible := tkkSkewForm Ω
  dissipative_symm := tkkDissipativeForm_symm M
  reversible_skew := tkkSkewForm_skew Ω hΩ_skew
  dissipative_nonneg := hPSD
  T := tkkDualTimeReversal
  dissipative_T_even := (tkkParityOnsagerSystem M hPSD hDual).dissipative_T_even
  reversible_T_odd x y := by
    simp only [tkkSkewForm_apply, tkkDualTimeReversal_apply, tkkSum, TKKGrade.dual]
    have hmm : Ω .plus .plus = -Ω .minus .minus := hΩ_odd .minus .minus
    have hmp : Ω .plus .minus = -Ω .minus .plus := hΩ_odd .minus .plus
    have hmz : Ω .plus .zero = -Ω .minus .zero := hΩ_odd .minus .zero
    have hpz : Ω .minus .zero = -Ω .plus .zero := hΩ_odd .plus .zero
    have hzm : Ω .zero .plus = -Ω .zero .minus := hΩ_odd .zero .minus
    have hzp : Ω .zero .minus = -Ω .zero .plus := hΩ_odd .zero .plus
    have hzz : Ω .zero .zero = 0 := by have h := hΩ_skew .zero .zero; linarith
    rw [hmm, hmp, hmz, hpz, hzm, hzp, hzz]
    ring

end TKKSection

/-! ## Part 5: `ConformalOnsagerBlock` & `ConformalPKMetriplecticSplit` (`Blocks.lean`) -/

section ConformalPKSection

/-- Project a `ConformalOnsagerBlock A` onto its `ConformalPKMetriplecticSplit`. -/
def conformalBlockToPKSplit {A : Type*} [Ring A] [Algebra ℝ A]
    (C : ConformalOnsagerBlock A) : ConformalPKMetriplecticSplit where
  reversiblePK := C.reversiblePK
  covariancePK := C.covariancePK
  souriauCocyclePK := C.souriauCocyclePK
  dissipativePK := C.covariancePK + C.souriauCocyclePK
  totalPK := C.totalPK
  dissipativePK_eq_covariance_plus_cocycle := rfl
  totalPK_eq_reversible_plus_dissipative := by
    rw [C.totalPK_eq_reversible_plus_covariance_plus_cocycle, add_assoc]

/-- Symmetric `(P, K)` dissipative bilinear form on `Fin 2 → ℝ` with diagonal
stiffness weights `dP`, `dK` and off-diagonal dissipative coupling `S.dissipativePK`. -/
def pkDissipativeForm (S : ConformalPKMetriplecticSplit) (dP dK : ℝ) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => dP * x 0 * y 0 + S.dissipativePK * (x 0 * y 1 + x 1 * y 0) + dK * x 1 * y 1)
    (twoBlockSym_add_left dP S.dissipativePK dK)
    (fun r x y => twoBlockSym_smul_left dP S.dissipativePK dK r x y)
    (twoBlockSym_add_right dP S.dissipativePK dK)
    (fun r x y => twoBlockSym_smul_right dP S.dissipativePK dK r x y)

/-- Skew-symmetric `(P, K)` reversible bilinear form on `Fin 2 → ℝ` with coupling
`S.reversiblePK`. -/
def pkReversibleForm (S : ConformalPKMetriplecticSplit) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => S.reversiblePK * (x 0 * y 1 - x 1 * y 0))
    (twoBlockSkew_add_left S.reversiblePK)
    (fun r x y => twoBlockSkew_smul_left S.reversiblePK r x y)
    (twoBlockSkew_add_right S.reversiblePK)
    (fun r x y => twoBlockSkew_smul_right S.reversiblePK r x y)

@[simp] theorem pkDissipativeForm_apply (S : ConformalPKMetriplecticSplit) (dP dK : ℝ)
    (x y : Fin 2 → ℝ) :
    pkDissipativeForm S dP dK x y =
      dP * x 0 * y 0 + S.dissipativePK * (x 0 * y 1 + x 1 * y 0) + dK * x 1 * y 1 := rfl

@[simp] theorem pkReversibleForm_apply (S : ConformalPKMetriplecticSplit)
    (x y : Fin 2 → ℝ) :
    pkReversibleForm S x y = S.reversiblePK * (x 0 * y 1 - x 1 * y 0) := rfl

theorem pkDissipative_nonneg_of_det
    (S : ConformalPKMetriplecticSplit) (dP dK : ℝ)
    (hdP : 0 ≤ dP) (hdK : 0 ≤ dK) (hdet : S.dissipativePK ^ 2 ≤ dP * dK)
    (x : Fin 2 → ℝ) :
    0 ≤ pkDissipativeForm S dP dK x x := by
  simp only [pkDissipativeForm_apply]
  by_cases h0 : dP = 0
  · have hS0 : S.dissipativePK = 0 := by
      have hsq : S.dissipativePK ^ 2 ≤ 0 := by simpa [h0] using hdet
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    rw [h0, hS0]
    nlinarith [hdK, sq_nonneg (x 1)]
  · have hpos : 0 < dP := lt_of_le_of_ne hdP (Ne.symm h0)
    have hmul : 0 ≤ dP * (dP * x 0 * x 0 + S.dissipativePK * (x 0 * x 1 + x 1 * x 0) + dK * x 1 * x 1) := by
      have hsq : (dP * x 0 + S.dissipativePK * x 1) ^ 2 ≥ 0 := sq_nonneg _
      have hdisc : (dP * dK - S.dissipativePK ^ 2) * x 1 ^ 2 ≥ 0 :=
        mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg (x 1))
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul hpos

theorem pkDissipative_nonneg_of_abs_le
    (S : ConformalPKMetriplecticSplit) (d : ℝ) (hd : |S.dissipativePK| ≤ d)
    (x : Fin 2 → ℝ) :
    0 ≤ pkDissipativeForm S d d x x := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have hdet : S.dissipativePK ^ 2 ≤ d * d := by
    have hsq : |S.dissipativePK| ^ 2 ≤ d ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_abs, abs_of_nonneg hd0] using hd)
    simpa [sq_abs, pow_two] using hsq
  exact pkDissipative_nonneg_of_det S d d hd0 hd0 hdet x

/-- `OnsagerCasimirSystem (Fin 2 → ℝ)` for a `ConformalPKMetriplecticSplit`. -/
def conformalPKSplitOnsagerSystem
    (S : ConformalPKMetriplecticSplit) (dP dK : ℝ)
    (hdP : 0 ≤ dP) (hdK : 0 ≤ dK) (hdet : S.dissipativePK ^ 2 ≤ dP * dK) :
    OnsagerCasimirSystem (Fin 2 → ℝ) where
  dissipative := pkDissipativeForm S dP dK
  reversible := pkReversibleForm S
  dissipative_symm x y := by simp only [pkDissipativeForm_apply]; ring
  reversible_skew x y := by simp only [pkReversibleForm_apply]; ring
  dissipative_nonneg := pkDissipative_nonneg_of_det S dP dK hdP hdK hdet

theorem conformalPKSplitOnsagerSystem_totalGenerator_basis
    (S : ConformalPKMetriplecticSplit) (dP dK : ℝ)
    (hdP : 0 ≤ dP) (hdK : 0 ≤ dK) (hdet : S.dissipativePK ^ 2 ≤ dP * dK) :
    (conformalPKSplitOnsagerSystem S dP dK hdP hdK hdet).totalGenerator ![1, 0] ![0, 1] =
      S.totalPK := by
  simp only [conformalPKSplitOnsagerSystem, totalGenerator, LinearMap.BilinForm.add_apply,
    pkDissipativeForm_apply, pkReversibleForm_apply, S.totalPK_eq_reversible_plus_dissipative]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Conformal `P ↔ K` swap time reversal `(x₀, x₁) ↦ (x₁, x₀)` on `Fin 2 → ℝ`. -/
def pkSwapTimeReversal : TimeReversal (Fin 2 → ℝ) where
  op :=
    { toFun := fun x i => if i = 0 then x 1 else x 0
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp }
  involutive := fun x => by
    ext i
    fin_cases i <;> simp

@[simp] theorem pkSwapTimeReversal_apply_zero (x : Fin 2 → ℝ) :
    pkSwapTimeReversal.op x 0 = x 1 := rfl

@[simp] theorem pkSwapTimeReversal_apply_one (x : Fin 2 → ℝ) :
    pkSwapTimeReversal.op x 1 = x 0 := rfl

/-- `P`-even / `K`-odd time reversal `(x₀, x₁) ↦ (x₀, -x₁)` on `Fin 2 → ℝ`. -/
def pkFlipTimeReversal : TimeReversal (Fin 2 → ℝ) :=
  scalarTwoBlockTimeReversal

/-- `ParityOnsagerSystem (Fin 2 → ℝ)` for a `ConformalPKMetriplecticSplit` with
`P ↔ K` swap `TimeReversal` and uniform diagonal weight `d ≥ |S.dissipativePK|`. -/
def conformalPKSplitParityOnsagerSystem
    (S : ConformalPKMetriplecticSplit) (d : ℝ) (hd : |S.dissipativePK| ≤ d) :
    ParityOnsagerSystem (Fin 2 → ℝ) where
  dissipative := pkDissipativeForm S d d
  reversible := pkReversibleForm S
  dissipative_symm x y := by simp only [pkDissipativeForm_apply]; ring
  reversible_skew x y := by simp only [pkReversibleForm_apply]; ring
  dissipative_nonneg := pkDissipative_nonneg_of_abs_le S d hd
  T := pkSwapTimeReversal
  dissipative_T_even x y := by
    simp only [pkDissipativeForm_apply, pkSwapTimeReversal_apply_zero,
      pkSwapTimeReversal_apply_one]
    ring
  reversible_T_odd x y := by
    simp only [pkReversibleForm_apply, pkSwapTimeReversal_apply_zero,
      pkSwapTimeReversal_apply_one]
    ring

/-- Unconditional canonical `ParityOnsagerSystem (Fin 2 → ℝ)` for any
`ConformalPKMetriplecticSplit` using `d := |S.dissipativePK|`. -/
def conformalPKSplitCanonicalParityOnsagerSystem
    (S : ConformalPKMetriplecticSplit) :
    ParityOnsagerSystem (Fin 2 → ℝ) :=
  conformalPKSplitParityOnsagerSystem S |S.dissipativePK| (le_refl _)

theorem conformalPKSplitCanonicalParityOnsagerSystem_totalGenerator_basis
    (S : ConformalPKMetriplecticSplit) :
    (conformalPKSplitCanonicalParityOnsagerSystem S).totalGenerator ![1, 0] ![0, 1] =
      S.totalPK := by
  simp only [conformalPKSplitCanonicalParityOnsagerSystem, conformalPKSplitParityOnsagerSystem,
    totalGenerator, LinearMap.BilinForm.add_apply, pkDissipativeForm_apply,
    pkReversibleForm_apply, S.totalPK_eq_reversible_plus_dissipative]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `ParityOnsagerSystem (Fin 2 → ℝ)` under `pkFlipTimeReversal` when `S.dissipativePK = 0`
(perfect conformal / zero-covariance-zero-cocycle regime). -/
def conformalPKSplitFlipParityOnsagerSystem
    (S : ConformalPKMetriplecticSplit) (dP dK : ℝ)
    (hdP : 0 ≤ dP) (hdK : 0 ≤ dK) (hDissZero : S.dissipativePK = 0) :
    ParityOnsagerSystem (Fin 2 → ℝ) where
  toOnsagerCasimirSystem :=
    conformalPKSplitOnsagerSystem S dP dK hdP hdK
      (by rw [hDissZero]; norm_num; exact mul_nonneg hdP hdK)
  T := pkFlipTimeReversal
  dissipative_T_even x y := by
    simp only [conformalPKSplitOnsagerSystem, pkDissipativeForm_apply, pkFlipTimeReversal,
      scalarTwoBlockTimeReversal_apply_zero, scalarTwoBlockTimeReversal_apply_one, hDissZero]
    ring
  reversible_T_odd x y := by
    simp only [conformalPKSplitOnsagerSystem, pkReversibleForm_apply, pkFlipTimeReversal,
      scalarTwoBlockTimeReversal_apply_zero, scalarTwoBlockTimeReversal_apply_one]
    ring

/-- `ParityOnsagerSystem (Fin 2 → ℝ)` for a `ConformalOnsagerBlock A` via
`conformalBlockToPKSplit` and weight `d ≥ |C.covariancePK + C.souriauCocyclePK|`. -/
def conformalBlockParityOnsagerSystem {A : Type*} [Ring A] [Algebra ℝ A]
    (C : ConformalOnsagerBlock A) (d : ℝ)
    (hd : |C.covariancePK + C.souriauCocyclePK| ≤ d) :
    ParityOnsagerSystem (Fin 2 → ℝ) :=
  conformalPKSplitParityOnsagerSystem (conformalBlockToPKSplit C) d hd

/-- Unconditional canonical `ParityOnsagerSystem (Fin 2 → ℝ)` for any
`ConformalOnsagerBlock A`. -/
def conformalBlockCanonicalParityOnsagerSystem {A : Type*} [Ring A] [Algebra ℝ A]
    (C : ConformalOnsagerBlock A) :
    ParityOnsagerSystem (Fin 2 → ℝ) :=
  conformalPKSplitCanonicalParityOnsagerSystem (conformalBlockToPKSplit C)

theorem conformalBlockCanonicalParityOnsagerSystem_totalGenerator_basis
    {A : Type*} [Ring A] [Algebra ℝ A] (C : ConformalOnsagerBlock A) :
    (conformalBlockCanonicalParityOnsagerSystem C).totalGenerator ![1, 0] ![0, 1] =
      C.totalPK :=
  conformalPKSplitCanonicalParityOnsagerSystem_totalGenerator_basis (conformalBlockToPKSplit C)

end ConformalPKSection

end InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge
