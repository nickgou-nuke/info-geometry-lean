/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornPeirce0SO55

/-! The native null extension boundary for the Peirce-0 quadratic carrier.

The carrier and bilinear form are formalized here.  The conformal generator
maps are kept as ordinary functions until their linearity and skewness
hypotheses are supplied in a dedicated owner.
-/
noncomputable section
namespace InfoGeometry.Canonical.H3ZornPeirce0TKK66

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety
open InfoGeometry.Canonical.H3ZornPeirce0SO55

abbrev V10 := Minkowski10
abbrev V12 := ℝ × V10 × ℝ

def B66 (x y : V12) : ℝ :=
  x.1 * y.2.2 + x.2.2 * y.1 + BQ10 x.2.1 y.2.1

@[simp] theorem B66_comm (x y : V12) : B66 x y = B66 y x := by
  rw [B66, B66, BQ10_comm]
  ring

def translation (u : V10) (x : V12) : V12 :=
  ⟨-BQ10 u x.2.1, ⟨x.2.2 • u, 0⟩⟩

def specialConformal (v : V10) (x : V12) : V12 :=
  ⟨0, ⟨x.1 • v, -BQ10 v x.2.1⟩⟩

def dilation (scale : ℝ) (x : V12) : V12 :=
  ⟨scale * x.1, ⟨0, -scale * x.2.2⟩⟩

def middleAction (M : V10 → V10) (x : V12) : V12 :=
  ⟨0, ⟨M x.2.1, 0⟩⟩

theorem translation_is_skew (u : V10) (x y : V12) :
    B66 (translation u x) y + B66 x (translation u y) = 0 := by
  rw [B66, B66, translation, translation]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 u]
  ring

theorem specialConformal_is_skew (v : V10) (x y : V12) :
    B66 (specialConformal v x) y + B66 x (specialConformal v y) = 0 := by
  rw [B66, B66, specialConformal, specialConformal]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 v]
  ring

theorem dilation_is_skew (scale : ℝ) (x y : V12) :
    B66 (dilation scale x) y + B66 x (dilation scale y) = 0 := by
  have hz (u : V10) : BQ10 u 0 = 0 := by
    simpa using BQ10_smul_right (0 : ℝ) u (0 : V10)
  have hzL (u : V10) : BQ10 0 u = 0 := by
    rw [BQ10_comm]
    exact hz u
  rw [B66, B66, dilation]
  simp [dilation, hz, hzL]
  ring

theorem so66_dimension_numeral : 12 * (12 - 1) / 2 = 66 := by
  norm_num


abbrev End10 := V10 →ₗ[ℝ] V10
abbrev End12 := V12 →ₗ[ℝ] V12

def InSO66 (T : End12) : Prop := ∀ x y : V12, B66 (T x) y + B66 x (T y) = 0

noncomputable def P (u : V10) : End12 where
  toFun x := ⟨-BQ10 u x.2.1, ⟨x.2.2 • u, 0⟩⟩
  map_add' x y := by ext <;> simp [BQ10_add_right] <;> ring
  map_smul' r x := by ext <;> simp [BQ10_smul_right, smul_smul]

noncomputable def K (v : V10) : End12 where
  toFun x := ⟨0, ⟨x.1 • v, -BQ10 v x.2.1⟩⟩
  map_add' x y := by ext <;> simp [BQ10_add_right] <;> ring
  map_smul' r x := by ext <;> simp [BQ10_smul_right, smul_smul]

noncomputable def D (lam : ℝ) : End12 where
  toFun x := ⟨lam * x.1, ⟨0, -lam * x.2.2⟩⟩
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

noncomputable def Mrot (M : End10) : End12 where
  toFun x := ⟨0, ⟨M x.2.1, 0⟩⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

theorem Mrot_in_so66 (M : End10) (hM : InSO55BQ M) : InSO66 (Mrot M) := by
  intro x y
  simp only [B66, Mrot, LinearMap.coe_mk, AddHom.coe_mk,
    zero_mul, mul_zero, zero_add, add_zero]
  exact hM x.2.1 y.2.1

def bracket (A B : End12) : End12 := A.comp B - B.comp A

def crossRotation (u v : V10) : End10 := (-1 / 2 : ℝ) • bivectorGen u v

theorem crossRotation_apply (u v z : V10) :
    crossRotation u v z = BQ10 u z • v - BQ10 v z • u := by
  ext i
  simp [crossRotation, bivectorGen]
  ring

theorem finrank_V12 : Module.finrank ℝ V12 = 12 := by
  simp [V12]

private theorem BQ10_zero_right (u : V10) : BQ10 u (0 : V10) = 0 := by
  simpa using BQ10_smul_right (0 : ℝ) u (0 : V10)

private theorem BQ10_zero_left (v : V10) : BQ10 (0 : V10) v = 0 := by
  simpa using BQ10_smul_left (0 : ℝ) (0 : V10) v

/-- Translations are infinitesimally orthogonal for `B66`. -/
theorem P_in_so66 (u : V10) : InSO66 (P u) := by
  intro x y
  simp only [B66, P, LinearMap.coe_mk, AddHom.coe_mk]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 u]
  ring

/-- Special conformal generators are infinitesimally orthogonal for `B66`. -/
theorem K_in_so66 (v : V10) : InSO66 (K v) := by
  intro x y
  simp only [B66, K, LinearMap.coe_mk, AddHom.coe_mk]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 v]
  ring

/-- Dilatations preserve the split null-pairing infinitesimally. -/
theorem D_in_so66 (lam : ℝ) : InSO66 (D lam) := by
  intro x y
  simp [B66, D, BQ10_zero_left, BQ10_zero_right]
  ring

/-- Degree `-1` is abelian. -/
theorem bracket_P_P (u v : V10) : bracket (P u) (P v) = 0 := by
  apply LinearMap.ext; intro x
  apply Prod.ext
  · simp [bracket, P, BQ10_smul_right, BQ10_comm u v]
  · apply Prod.ext
    · simp [bracket, P]
    · simp [bracket, P]

/-- Degree `+1` is abelian. -/
theorem bracket_K_K (u v : V10) : bracket (K u) (K v) = 0 := by
  apply LinearMap.ext; intro x
  apply Prod.ext
  · simp [bracket, K]
  · apply Prod.ext
    · simp [bracket, K]
    · simp [bracket, K, BQ10_smul_right, BQ10_comm u v]

/-- Dilatation grading on translations. -/
theorem bracket_D_P (lam : ℝ) (u : V10) :
    bracket (D lam) (P u) = P (lam • u) := by
  apply LinearMap.ext; intro x
  apply Prod.ext
  · simp [bracket, D, P, BQ10_smul_left, BQ10_zero_right]
  · apply Prod.ext
    · simp [bracket, D, P, smul_smul]; ring_nf
    · simp [bracket, D, P]

/-- Dilatation grading on special conformal generators. -/
theorem bracket_D_K (lam : ℝ) (v : V10) :
    bracket (D lam) (K v) = -K (lam • v) := by
  apply LinearMap.ext; intro x
  apply Prod.ext
  · simp [bracket, D, K]
  · apply Prod.ext
    · simp [bracket, D, K, smul_smul]; ring_nf
    · simp [bracket, D, K, BQ10_smul_left, BQ10_zero_right]

/-- The cross-bracket rotation is `BQ10`-skew. -/
theorem crossRotation_in_so55 (u v : V10) :
    InSO55BQ (crossRotation u v) := by
  intro x y
  simp [crossRotation, BQ10_smul_left, BQ10_smul_right]
  have h := bivectorGen_in_so55 u v x y
  linarith

/-- TKK cross bracket: degree `-1` against degree `+1` lands in degree zero as
one dilatation plus one metric rotation. -/
theorem bracket_P_K (u v : V10) :
    bracket (P u) (K v) =
      D (-BQ10 u v) + Mrot (crossRotation u v) := by
  apply LinearMap.ext; intro x
  apply Prod.ext
  · simp [bracket, P, K, D, Mrot, BQ10_smul_right]; ring
  · apply Prod.ext
    · simp [bracket, P, K, D, Mrot, crossRotation_apply]
      module
    · simp [bracket, P, K, D, Mrot, BQ10_smul_right, BQ10_comm]; ring

/-- Closure of the displayed cross-bracket inside the 12D metric-skew class. -/
theorem bracket_P_K_in_so66 (u v : V10) :
    InSO66 (bracket (P u) (K v)) := by
  rw [bracket_P_K]
  intro x y
  simp only [LinearMap.add_apply]
  have hD := D_in_so66 (-BQ10 u v) x y
  have hM := Mrot_in_so66 (crossRotation u v)
    (crossRotation_in_so55 u v) x y
  unfold B66 at hD hM ⊢
  simp only [Prod.fst_add, Prod.snd_add, add_mul, mul_add,
    BQ10_add_left, BQ10_add_right]
  linarith

/-- The `BQ10`-skew middle maps form a real vector subspace of `End10`. -/
def so55BQSubmodule : Submodule ℝ End10 where
  carrier := { A | InSO55BQ A }
  zero_mem' := by
    intro x y
    have hzL : BQ10 (0 : V10) y = 0 := by
      simpa using BQ10_smul_left (0 : ℝ) (0 : V10) y
    have hzR : BQ10 x (0 : V10) = 0 := by
      simpa using BQ10_smul_right (0 : ℝ) x (0 : V10)
    simp [hzL, hzR]
  add_mem' := by
    intro A B hA hB x y
    simp only [LinearMap.add_apply, BQ10_add_left, BQ10_add_right]
    have h1 := hA x y
    have h2 := hB x y
    linarith
  smul_mem' := by
    intro r A hA x y
    simp only [LinearMap.smul_apply, BQ10_smul_left, BQ10_smul_right]
    have h := hA x y
    linear_combination r * h

/-- The full TKK parameter module `g₋₁ ⊕ (ℝD ⊕ so(BQ10)) ⊕ g₊₁`. -/
abbrev TKKParams := V10 × ℝ × so55BQSubmodule × V10

/-- Linear parameterization by translation, dilation, middle rotation, and
special-conformal blocks. -/
noncomputable def tkkParamMap : TKKParams →ₗ[ℝ] End12 where
  toFun p := P p.1 + D p.2.1 + Mrot p.2.2.1.1 + K p.2.2.2
  map_add' p q := by
    apply LinearMap.ext; intro x
    apply Prod.ext
    · simp [P, D, Mrot, K, BQ10_add_left]; ring
    · apply Prod.ext
      · simp [P, D, Mrot, K, smul_add]; module
      · simp [P, D, Mrot, K, BQ10_add_left]; ring
  map_smul' r p := by
    apply LinearMap.ext; intro x
    apply Prod.ext
    · simp [P, D, Mrot, K, BQ10_smul_left]; ring
    · apply Prod.ext
      · simp [P, D, Mrot, K, smul_add, smul_smul]; module
      · simp [P, D, Mrot, K, BQ10_smul_left]; ring

/-- Test-vector uniqueness: if the sum of the four graded components vanishes,
then every parameter vanishes. -/
theorem tkk_param_zero
    (u : V10) (lam : ℝ) (A : End10) (v : V10)
    (h_zero : P u + D lam + Mrot A + K v = 0) :
    u = 0 ∧ lam = 0 ∧ A = 0 ∧ v = 0 := by
  have hzL (w : V10) : BQ10 w (0 : V10) = 0 := by
    simpa using BQ10_smul_right (0 : ℝ) w (0 : V10)
  have h1 := LinearMap.congr_fun h_zero ((1 : ℝ), (0 : V10), (0 : ℝ))
  have h2 := LinearMap.congr_fun h_zero ((0 : ℝ), (0 : V10), (1 : ℝ))
  have hlam : lam = 0 := by
    have hs := congrArg (fun w : V12 => w.1) h1
    simpa [P, D, Mrot, K, hzL] using hs
  have hv : v = 0 := by
    have hz := congrArg (fun w : V12 => w.2.1) h1
    simpa [P, D, Mrot, K] using hz
  have hu : u = 0 := by
    have hz := congrArg (fun w : V12 => w.2.1) h2
    simpa [P, D, Mrot, K] using hz
  have hA : A = 0 := by
    apply LinearMap.ext; intro z
    have hz := LinearMap.congr_fun h_zero ((0 : ℝ), z, (0 : ℝ))
    have hm := congrArg (fun w : V12 => w.2.1) hz
    simpa [P, D, Mrot, K, hu, hv, hlam] using hm
  exact ⟨hu, hlam, hA, hv⟩

/-- The 3-graded TKK parameterization is injective. -/
theorem tkkParamMap_injective : Function.Injective tkkParamMap := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rcases p with ⟨u, lam, A, v⟩
  change P u + D lam + Mrot A.1 + K v = 0 at hp
  have h := tkk_param_zero u lam A.1 v hp
  rcases h with ⟨hu, hlam, hA, hv⟩
  apply Prod.ext
  · exact hu
  · apply Prod.ext
    · exact hlam
    · apply Prod.ext
      · exact Subtype.ext hA
      · exact hv

/-- Compact 3-grading generator packet. -/
theorem tkk66_generator_packet :
    Module.finrank ℝ V12 = 12 ∧
    Function.Injective tkkParamMap ∧
    (∀ u, InSO66 (P u)) ∧
    (∀ v, InSO66 (K v)) ∧
    (∀ lam, InSO66 (D lam)) ∧
    (∀ u v, bracket (P u) (P v) = 0) ∧
    (∀ u v, bracket (K u) (K v) = 0) :=
  ⟨finrank_V12, tkkParamMap_injective, P_in_so66, K_in_so66,
    D_in_so66, bracket_P_P, bracket_K_K⟩

end InfoGeometry.Canonical.H3ZornPeirce0TKK66
