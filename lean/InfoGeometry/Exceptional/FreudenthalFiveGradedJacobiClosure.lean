import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierAddGroup
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierModule
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketScalarBilinearity
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketLinearMaps

/-!
# Five-Graded Freudenthal-TKK Lie Homogeneous Jacobi Closure

This module establishes the core homogeneous Jacobi identities for the 5-graded Lie bracket
on `FiveGradedCarrier D`.

## Mathematical Structure:
1. `fiveJacobiator D u v w`: the trilinear Jacobiator
   $[u, [v, w]] + [v, [w, u]] + [w, [u, v]]$.
2. Cyclic symmetry:
   `fiveJacobiator_cyclic_left`, `fiveJacobiator_cyclic_right`.
3. Homogeneous Orbit Closures:
   - $(-1, -1, +1)$ lane: `jacobi_chargeMinus_chargeMinus_chargePlus`
   - $(+1, +1, -1)$ lane: `jacobi_chargePlus_chargePlus_chargeMinus`
   - $(0, 0, 0)$ lane: `jacobi_zero_zero_zero`

All proofs are complete with 0 sorries and 0 axioms.
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
  linarith [zeroGrade_symplectic_form_skew D T X Y]

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

theorem jacobi_extremeMinus_extremeMinus_chargePlus
    (a b : ℝ) (x : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b)
        (injChargePlus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargePlus,
      injChargeMinus, FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremePlus_extremePlus_chargeMinus
    (a b : ℝ) (x : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEplus D b)
        (injChargeMinus D x) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargeMinus,
      injChargePlus, FiveGradedCarrier.instAdd] <;>
    simp

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
    simp <;> ring

theorem jacobi_extremePlus_extremePlus_extremeMinus
    (a b c : ℝ) :
    fiveJacobiator D (genEplus D a) (genEplus D b)
        (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, genEminus,
      FiveGradedCarrier.instAdd] <;>
    simp <;> ring

end InfoGeometry.Exceptional.Freudenthal
