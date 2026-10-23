/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierAddGroup
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierModule
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketScalarBilinearity
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketLinearMaps

/-!
# Homogeneous Jacobi identities and defects of the legacy five-graded bracket

This module proves selected homogeneous Jacobi identities for the legacy
operation `fiveGradedBracket` on `FiveGradedCarrier D`. The extreme-charge
component has an explicit defect; these selected identities do not make the
legacy operation a Lie bracket.

## Mathematical Structure:
1. `fiveJacobiator D u v w`: the trilinear Jacobiator
   $[u, [v, w]] + [v, [w, u]] + [w, [u, v]]$.
2. Cyclic symmetry:
   `fiveJacobiator_cyclic_left`, `fiveJacobiator_cyclic_right`.
3. Homogeneous Orbit Closures:
   - $(-1, -1, +1)$ lane: `jacobi_chargeMinus_chargeMinus_chargePlus`
   - $(+1, +1, -1)$ lane: `jacobi_chargePlus_chargePlus_chargeMinus`
   - $(0, 0, 0)$ lane: `jacobi_zero_zero_zero`

The statements below distinguish vanishing components from nonzero defects.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The Jacobiator for three elements in the 5-graded carrier. -/
def fiveJacobiator (u v w : FiveGradedCarrier D) : FiveGradedCarrier D :=
  fiveGradedBracket D u (fiveGradedBracket D v w) +
  fiveGradedBracket D v (fiveGradedBracket D w u) +
  fiveGradedBracket D w (fiveGradedBracket D u v)

/-- The legacy extreme-plus/extreme-minus/positive-charge Jacobi defect for
arbitrary extreme coefficients. This formula prevents promotion of the
selected homogeneous vanishing laws to a full Jacobi identity. -/
theorem fiveJacobiator_extreme_plus_minus_charge_plus
    (a b : ℝ) (y : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEminus D b) (injChargePlus D y) =
      injChargePlus D ((-2 * a * b) • y) := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveJacobiator, fiveGradedBracket, genEplus, genEminus, injChargePlus]
  module

/-- Exact vanishing criterion for the legacy extreme-charge Jacobi component.
A nonzero charge and two nonzero extreme coefficients always give a defect. -/
theorem fiveJacobiator_extreme_plus_minus_charge_plus_eq_zero_iff
    (a b : ℝ) (y : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEminus D b) (injChargePlus D y) = 0 ↔
      a = 0 ∨ b = 0 ∨ y = 0 := by
  rw [fiveJacobiator_extreme_plus_minus_charge_plus]
  constructor
  · intro h
    have hy : (-2 * a * b) • y = 0 :=
      congrArg (fun u : FiveGradedCarrier D => u.plus1) h
    rcases smul_eq_zero.mp hy with hc | hy
    · rcases mul_eq_zero.mp hc with ha | hb
      · have ha' : a = 0 := (mul_eq_zero.mp ha).resolve_left (by norm_num)
        exact Or.inl ha'
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hy)
  · rintro (ha | hb | hy)
    · subst a
      apply FiveGradedCarrier.ext <;> simp [injChargePlus]
    · subst b
      apply FiveGradedCarrier.ext <;> simp [injChargePlus]
    · subst y
      apply FiveGradedCarrier.ext <;> simp [injChargePlus]

/-- Every additive map preserving the legacy bracket into any genuine Lie
ring annihilates its positive-charge sector. This is a structural
obstruction to faithful representation, not a finite-coordinate example. -/
theorem bracket_preserving_map_annihilates_positive_charge
    {L : Type*} [LieRing L]
    (f : FiveGradedCarrier D →+ L)
    (hf : ∀ u v, f (fiveGradedBracket D u v) = ⁅f u, f v⁆)
    (y : FreudenthalCharge J) : f (injChargePlus D y) = 0 := by
  have hj : f (fiveJacobiator D (genEplus D (-1 / 2)) (genEminus D 1)
      (injChargePlus D y)) = 0 := by
    simp only [fiveJacobiator, map_add, hf]
    exact lie_jacobi _ _ _
  rw [fiveJacobiator_extreme_plus_minus_charge_plus] at hj
  norm_num at hj
  exact hj

/-- The extreme lowering action propagates the representation obstruction
to the negative-charge sector as well. -/
theorem bracket_preserving_map_annihilates_negative_charge
    {L : Type*} [LieRing L]
    (f : FiveGradedCarrier D →+ L)
    (hf : ∀ u v, f (fiveGradedBracket D u v) = ⁅f u, f v⁆)
    (y : FreudenthalCharge J) : f (injChargeMinus D y) = 0 := by
  rw [← extreme_minus2_action_plus1 D y, hf,
    bracket_preserving_map_annihilates_positive_charge D f hf y, lie_zero]

/-- The positive Heisenberg bracket is also killed in every genuine Lie-ring
image. The coefficient is the actual symplectic pairing of arbitrary charges. -/
theorem bracket_preserving_map_annihilates_positive_heisenberg
    {L : Type*} [LieRing L]
    (f : FiveGradedCarrier D →+ L)
    (hf : ∀ u v, f (fiveGradedBracket D u v) = ⁅f u, f v⁆)
    (x y : FreudenthalCharge J) :
    f (genEplus D (2 * FreudenthalCharge.symplecticForm D x y)) = 0 := by
  rw [← bracket_plus1_plus1 D x y, hf,
    bracket_preserving_map_annihilates_positive_charge D f hf x, zero_lie]

/-- The negative Heisenberg bracket has the same universal obstruction. -/
theorem bracket_preserving_map_annihilates_negative_heisenberg
    {L : Type*} [LieRing L]
    (f : FiveGradedCarrier D →+ L)
    (hf : ∀ u v, f (fiveGradedBracket D u v) = ⁅f u, f v⁆)
    (x y : FreudenthalCharge J) :
    f (genEminus D (2 * FreudenthalCharge.symplecticForm D x y)) = 0 := by
  rw [← bracket_minus1_minus1 D x y, hf,
    bracket_preserving_map_annihilates_negative_charge D f hf x, zero_lie]

/-! ## 1. Cyclic Symmetries of the Jacobiator -/

theorem fiveJacobiator_cyclic_left (u v w : FiveGradedCarrier D) :
    fiveJacobiator D v w u = fiveJacobiator D u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

theorem fiveJacobiator_cyclic_right (u v w : FiveGradedCarrier D) :
    fiveJacobiator D w u v = fiveJacobiator D u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

/-! ## 2. Core Homogeneous Orbit Closures -/

/-- 🏆 Orbit 7 [(-1, -1, +1)]: The charge-minus charge-plus Jacobiator vanishes identically. -/
theorem jacobi_chargeMinus_chargeMinus_chargePlus (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargeMinus D x) (injChargeMinus D y) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  exact fiveGraded_minus_minus_plus_jacobi D x y z

/-- 🏆 Orbit 7-dual [(+1, +1, -1)]: The charge-plus charge-minus Jacobiator vanishes identically. -/
theorem jacobi_chargePlus_chargePlus_chargeMinus (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargePlus D x) (injChargePlus D y) (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  exact fiveGraded_plus_plus_minus_jacobi D x y z

theorem jacobi_chargeMinus_chargeMinus_chargeMinus
    (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargeMinus D x) (injChargeMinus D y)
        (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_chargePlus_chargePlus_chargePlus
    (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargePlus D x) (injChargePlus D y)
        (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_scale_chargeMinus
    (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D 1) (genHscale D 1)
        (injChargeMinus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_scale_chargePlus
    (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D 1) (genHscale D 1)
        (injChargePlus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_scale_extremeMinus :
    fiveJacobiator D (genHscale D 1) (genHscale D 1)
        (genEminus D 1) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEminus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_scale_extremePlus :
    fiveJacobiator D (genHscale D 1) (genHscale D 1)
        (genEplus D 1) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEplus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_scale_sympZero
    (T : SymplecticTKKZero D) :
    fiveJacobiator D (genHscale D 1) (genHscale D 1)
        (injSympZero D T) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injSympZero,
      FiveGradedCarrier.instAdd] <;>
    simp

@[simp] theorem fiveGradedBracket_sympZero_sympZero (T₁ T₂ : SymplecticTKKZero D) :
    fiveGradedBracket D (injSympZero D T₁) (injSympZero D T₂) = injSympZero D ⁅T₁, T₂⁆ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injSympZero] <;>
    simp

/-- 🏆 Orbit 12 [(0, 0, 0)]: The zero-grade subalgebra satisfies the Jacobi identity. -/
theorem jacobi_zero_zero_zero (T₁ T₂ T₃ : SymplecticTKKZero D) :
    fiveJacobiator D (injSympZero D T₁) (injSympZero D T₂) (injSympZero D T₃) = 0 := by
  dsimp [fiveJacobiator]
  rw [fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero]
  apply FiveGradedCarrier.ext <;>
    dsimp [injSympZero] <;>
    simp only [lie_jacobi, add_zero]

theorem zeroGrade_mixed_bracket_compatibility
    (T : SymplecticTKKZero D) (X Y : FreudenthalCharge J) :
    ⁅T, mixedSymplecticBracket D X Y⁆ =
      mixedSymplecticBracket D ((T : Module.End ℝ (FreudenthalCharge J)) X) Y +
        mixedSymplecticBracket D X
          ((T : Module.End ℝ (FreudenthalCharge J)) Y) := by
  exact zeroGrade_action_mixedSymplecticBracket D T X Y

theorem zeroGrade_symplectic_form_skew
    (T : SymplecticTKKZero D) (X Y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D
          ((T : Module.End ℝ (FreudenthalCharge J)) X) Y +
        FreudenthalCharge.symplecticForm D X
          ((T : Module.End ℝ (FreudenthalCharge J)) Y) = 0 := by
  exact T.property X Y

theorem zeroGrade_symplectic_form_transfer
    (T : SymplecticTKKZero D) (X Y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D
          ((T : Module.End ℝ (FreudenthalCharge J)) X) Y =
      -FreudenthalCharge.symplecticForm D X
          ((T : Module.End ℝ (FreudenthalCharge J)) Y) := by
  exact eq_neg_of_add_eq_zero_left (zeroGrade_symplectic_form_skew D T X Y)

theorem fiveGradedBracket_sympZero_chargeMinus
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveGradedBracket D (injSympZero D T) (injChargeMinus D x) =
      injChargeMinus D ((T : Module.End ℝ (FreudenthalCharge J)) x) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injSympZero, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem fiveGradedBracket_sympZero_chargePlus
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveGradedBracket D (injSympZero D T) (injChargePlus D x) =
      injChargePlus D ((T : Module.End ℝ (FreudenthalCharge J)) x) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injSympZero, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem fiveGradedBracket_sympZero_mixedBlock
    (T : SymplecticTKKZero D) (X Y : FreudenthalCharge J) :
    fiveGradedBracket D (injSympZero D T)
        ⟨0, 0, mixedSymplecticBracket D X Y,
          FreudenthalCharge.symplecticForm D X Y, 0, 0⟩ =
      injSympZero D ⁅T, mixedSymplecticBracket D X Y⁆ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injSympZero,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem fiveGradedBracket_neg_left
    (u v : FiveGradedCarrier D) :
    fiveGradedBracket D (-u) v = -fiveGradedBracket D u v :=
  (fiveGradedBracket_left D v).map_neg u

theorem fiveGradedBracket_neg_right
    (u v : FiveGradedCarrier D) :
    fiveGradedBracket D u (-v) = -fiveGradedBracket D u v :=
  (fiveGradedBracket_right D u).map_neg v

theorem fiveGradedBracket_chargeMinus_sympZero
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injSympZero D T) =
      injChargeMinus D (-((T : Module.End ℝ (FreudenthalCharge J)) x)) := by
  rw [fiveGradedBracket_skew, fiveGradedBracket_sympZero_chargeMinus]
  apply FiveGradedCarrier.ext <;>
    simp [injChargeMinus, FiveGradedCarrier.neg_minus1]

theorem fiveGradedBracket_chargePlus_sympZero
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x) (injSympZero D T) =
      injChargePlus D (-((T : Module.End ℝ (FreudenthalCharge J)) x)) := by
  rw [fiveGradedBracket_skew, fiveGradedBracket_sympZero_chargePlus]
  apply FiveGradedCarrier.ext <;>
    simp [injChargePlus, FiveGradedCarrier.neg_plus1]

theorem jacobi_extremeMinus_chargeMinus_chargeMinus
    (a : ℝ) (x y : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (injChargeMinus D x)
        (injChargeMinus D y) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremePlus_chargePlus_chargePlus
    (a : ℝ) (x y : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (injChargePlus D x)
        (injChargePlus D y) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_extremeMinus_chargePlus
    (a b : ℝ) (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D a) (genEminus D b)
        (injChargePlus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEminus, injChargePlus,
      injChargeMinus, FiveGradedCarrier.instAdd] <;>
    simp; module

theorem jacobi_scale_extremePlus_chargeMinus
    (a b : ℝ) (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D a) (genEplus D b)
        (injChargeMinus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEplus, injChargeMinus,
      injChargePlus, FiveGradedCarrier.instAdd] <;>
    simp; module

theorem jacobi_extremeMinus_extremeMinus_extremeMinus
    (a b c : ℝ) :
    fiveJacobiator D (genEminus D a) (genEminus D b)
        (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremePlus_extremePlus_extremePlus
    (a b c : ℝ) :
    fiveJacobiator D (genEplus D a) (genEplus D b)
        (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremeMinus_extremeMinus_extremePlus
    (a b c : ℝ) :
    fiveJacobiator D (genEminus D a) (genEminus D b)
        (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, genEplus,
      FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_extremePlus_extremePlus_extremeMinus
    (a b c : ℝ) :
    fiveJacobiator D (genEplus D a) (genEplus D b)
        (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, genEminus,
      FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_extremeMinus_extremePlus_extremeMinus
    (a b c : ℝ) :
    fiveJacobiator D (genEminus D a) (genEplus D b)
        (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, genEplus,
      genHscale, FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_extremePlus_extremeMinus_extremePlus
    (a b c : ℝ) :
    fiveJacobiator D (genEplus D a) (genEminus D b)
        (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, genEminus,
      genHscale, FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_scale_extremeMinus_extremePlus
    (a b c : ℝ) :
    fiveJacobiator D (genHscale D a) (genEminus D b)
        (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEminus, genEplus,
      FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_scale_extremePlus_extremeMinus
    (a b c : ℝ) :
    fiveJacobiator D (genHscale D a) (genEplus D b)
        (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEplus, genEminus,
      FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_extremeMinus_extremePlus_extremePlus
    (a b c : ℝ) :
    fiveJacobiator D (genEminus D a) (genEplus D b)
        (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, genEplus,
      genHscale, FiveGradedCarrier.instAdd] <;>
    simp; ring

theorem jacobi_scale_sympZero_chargeMinus
    (a : ℝ) (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D a) (injSympZero D T)
        (injChargeMinus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injSympZero, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_scale_sympZero_chargePlus
    (a : ℝ) (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    fiveJacobiator D (genHscale D a) (injSympZero D T)
        (injChargePlus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injSympZero, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremeMinus_extremeMinus_chargeMinus
    (a b : ℝ) (x : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b)
        (injChargeMinus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_chargeMinus_chargeMinus_sympZero
    (x y : FreudenthalCharge J) (T : SymplecticTKKZero D) :
    fiveJacobiator D (injChargeMinus D x) (injChargeMinus D y)
        (injSympZero D T) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, injSympZero,
      FiveGradedCarrier.instAdd] <;>
    simp
  have h := T.property x y
  have hs := FreudenthalCharge.symplectic_form_skew D
    ((T : Module.End ℝ (FreudenthalCharge J)) x) y
  have hn := symplecticForm_neg_right D x
    ((T : Module.End ℝ (FreudenthalCharge J)) y)
  linarith

theorem jacobi_chargeMinus_chargeMinus_scale
    (x y : FreudenthalCharge J) (h : ℝ) :
    fiveJacobiator D (injChargeMinus D x) (injChargeMinus D y)
        (genHscale D h) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, genHscale,
      FiveGradedCarrier.instAdd]
  · have h1 : FreudenthalCharge.symplecticForm D x (h • y) = h * FreudenthalCharge.symplecticForm D x y :=
      (symplecticFormLinear D x).map_smul h y
    have h2 : FreudenthalCharge.symplecticForm D y (-h • x) = h * FreudenthalCharge.symplecticForm D x y := by
      have hs : FreudenthalCharge.symplecticForm D y (-h • x) = -h * FreudenthalCharge.symplecticForm D y x :=
        (symplecticFormLinear D y).map_smul (-h) x
      have hsk : FreudenthalCharge.symplecticForm D y x = -FreudenthalCharge.symplecticForm D x y :=
        FreudenthalCharge.symplectic_form_skew D x y
      calc
        FreudenthalCharge.symplecticForm D y (-h • x) =
            -h * FreudenthalCharge.symplecticForm D y x := hs
        _ = -h * (-FreudenthalCharge.symplecticForm D x y) := by rw [hsk]
        _ = h * FreudenthalCharge.symplecticForm D x y := by ring
    simp only [zero_smul, smul_zero, add_zero, zero_add, sub_self, mul_zero,
      neg_zero, symplecticForm_zero_left, symplecticForm_zero_right]
    rw [h1, h2]
    ring
  · simp
  · simp
  · simp
  · simp
  · simp

@[simp] theorem symplecticRankTwo_zero_left (x : FreudenthalCharge J) :
    symplecticRankTwo D 0 x = 0 := by
  apply LinearMap.ext
  intro z
  simp [symplecticRankTwo_apply]

@[simp] theorem symplecticRankTwo_zero_right (x : FreudenthalCharge J) :
    symplecticRankTwo D x 0 = 0 := by
  apply LinearMap.ext
  intro z
  simp [symplecticRankTwo_apply]

theorem jacobi_chargePlus_chargePlus_scale
    (x y : FreudenthalCharge J) (h : ℝ) :
    fiveJacobiator D (injChargePlus D x) (injChargePlus D y)
        (genHscale D h) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus, genHscale,
      FiveGradedCarrier.instAdd]
  all_goals
    simp
  all_goals
    try ring
    try rw [symplecticForm_neg_right, symplecticForm_smul_right,
      FreudenthalCharge.symplectic_form_skew D x y]
    try ring

end InfoGeometry.Exceptional.Freudenthal
