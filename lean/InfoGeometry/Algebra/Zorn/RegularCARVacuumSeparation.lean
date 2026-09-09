import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.ZornDerivationBridge

set_option maxHeartbeats 800000

/-!
# Native Zorn generators, associative regular CAR, and the actual vacuum

The raw Zorn product is nonassociative. Polarized alternativity nevertheless
makes the left regular generators satisfy the associative operator CAR.
The representation map L is not multiplicative. The three-mode vacuum
projector is a product of three operator projectors, not L of a Peirce pole.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "U" => InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ)
local notation "V" => InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ)
local notation "polePlus" => InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ)
local notation "poleMinus" => InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)

@[simp] theorem L_zero : L (0 : Zorn) = 0 := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul x

@[simp] theorem L_one : L (1 : Zorn) = 1 := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul x

/-- Additivity of the left regular map; multiplicativity is deliberately absent. -/
theorem L_add (a b : Zorn) : L (a + b) = L a + L b := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul a b x

theorem L_smul (r : ℝ) (a : Zorn) : L (r • a) = r • L a := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r a x

/-- The associative regular action retains the polarized alternative identity. -/
theorem regular_anticommutator (a b : Zorn) :
    L a * L b + L b * L a = L (a * b + b * a) := by
  apply LinearMap.ext
  intro x
  change a * (b * x) + b * (a * x) = (a * b + b * a) * x
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul]
  apply canonicalVectorEquiv.injective
  simpa only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add] using
    (InfoGeometry.Algebra.alternative_left_linearized
      InfoGeometry.Algebra.zorn_left_alternative
      (canonicalVectorEquiv a) (canonicalVectorEquiv b) (canonicalVectorEquiv x)).symm

/-- Repeated left factors can be reassociated, by alternativity rather than associativity. -/
theorem regular_square (a : Zorn) : L a * L a = L (a * a) := by
  apply LinearMap.ext
  intro x
  change a * (a * x) = (a * a) * x
  apply canonicalVectorEquiv.injective
  simpa only [canonicalVectorEquiv_mul] using
    (InfoGeometry.Algebra.zorn_left_alternative
      (canonicalVectorEquiv a) (canonicalVectorEquiv x)).symm

/-- Exact raw upper/lower anticommutator in the canonical Zorn carrier. -/
theorem raw_mixed_CAR (i j : Fin 3) :
    U i * V j + V j * U i = if i = j then (1 : Zorn) else 0 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalUpperLower_mul,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalLowerUpper_mul]
    simpa using (InfoGeometry.Canonical.ZornMatrix.zornPlus_add_zornMinus (R := ℝ))
  · have h' : ¬j = i := by simpa [eq_comm] using h
    rw [if_neg h]
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalUpperLower_mul,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalLowerUpper_mul]
    simp [h, h']

theorem raw_upper_CAR (i j : Fin 3) : U i * U j + U j * U i = (0 : Zorn) := by
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalUpperUpper_anticomm i j

theorem raw_lower_CAR (i j : Fin 3) : V i * V j + V j * V i = (0 : Zorn) := by
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalLowerLower_anticomm i j

/-- Actual associative creation and annihilation operators. -/
def create (i : Fin 3) : Module.End ℝ Zorn := L (U i)
def annihilate (i : Fin 3) : Module.End ℝ Zorn := L (V i)

theorem regular_mixed_CAR (i j : Fin 3) :
    create i * annihilate j + annihilate j * create i =
      if i = j then (1 : Module.End ℝ Zorn) else 0 := by
  simp only [create, annihilate]
  rw [regular_anticommutator, raw_mixed_CAR]
  split_ifs with h
  · simpa using L_one
  · simpa using L_zero

theorem regular_upper_CAR (i j : Fin 3) :
    create i * create j + create j * create i = 0 := by
  simp only [create]
  rw [regular_anticommutator, raw_upper_CAR, L_zero]

theorem regular_lower_CAR (i j : Fin 3) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  simp only [annihilate]
  rw [regular_anticommutator, raw_lower_CAR, L_zero]

/-- The same genuine CAR transport to the already installed circular operator basis. -/
theorem circular_regular_CAR (i j : Fin 3) :
    circularOperatorReadout (create i) * circularOperatorReadout (annihilate j) +
      circularOperatorReadout (annihilate j) * circularOperatorReadout (create i) =
        if i = j then 1 else 0 := by
  rw [← map_mul, ← map_mul, ← map_add, regular_mixed_CAR]
  split_ifs <;> simp

/-- With upper generators designated creation, the lower pole is the vacuum VECTOR. -/
theorem regular_vacuum (i : Fin 3) :
    annihilate i poleMinus = 0 ∧ create i poleMinus = U i ∧ create i polePlus = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals fin_cases i
  all_goals apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals norm_num [create, annihilate, L_apply,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
    InfoGeometry.Canonical.ZornMatrix.zornPlus, InfoGeometry.Canonical.ZornMatrix.zornMinus,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] <;> decide

/-- Product of three empty-mode projectors in the ASSOCIATIVE endomorphism algebra. -/
def vacuumProjector : Module.End ℝ Zorn :=
  (annihilate 0 * create 0) * (annihilate 1 * create 1) * (annihilate 2 * create 2)

/-- This operator has precisely the one-dimensional vacuum range. -/
theorem vacuumProjector_apply (X : Zorn) : vacuumProjector X = X.b • poleMinus := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [vacuumProjector, create, annihilate, Module.End.mul_apply, L_apply,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
    InfoGeometry.Canonical.ZornMatrix.zornMinus,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply,
    InfoGeometry.Canonical.ZornMatrix.smul_a,
    InfoGeometry.Canonical.ZornMatrix.smul_b,
    InfoGeometry.Canonical.ZornMatrix.smul_x,
    InfoGeometry.Canonical.ZornMatrix.smul_y]

/-- Idempotence of the actual three-mode vacuum projector. -/
theorem vacuumProjector_idempotent : vacuumProjector * vacuumProjector = vacuumProjector := by
  apply LinearMap.ext
  intro X
  change vacuumProjector (vacuumProjector X) = vacuumProjector X
  simp only [vacuumProjector_apply]
  simp [InfoGeometry.Canonical.ZornMatrix.smul_b,
    InfoGeometry.Canonical.ZornMatrix.smul_a,
    InfoGeometry.Canonical.ZornMatrix.zornMinus]

/-- Its range is exactly the vacuum line, not a four-dimensional Peirce half. -/
theorem vacuumProjector_range : LinearMap.range vacuumProjector =
    Submodule.span ℝ ({poleMinus} : Set Zorn) := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    rw [vacuumProjector_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro X hX
    have hx : X = poleMinus := by simpa using hX
    subst X
    exact ⟨poleMinus, by
      rw [vacuumProjector_apply]
      simp [InfoGeometry.Canonical.ZornMatrix.zornMinus]⟩

/-- Left multiplication by the Peirce idempotent is not this rank-one projector. -/
theorem vacuumProjector_ne_pole_action : vacuumProjector ≠ L poleMinus := by
  intro h
  have hv := congrArg (fun T : Module.End ℝ Zorn => (T (V 0)).y 0) h
  simp [vacuumProjector_apply, L_apply,
    InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
    InfoGeometry.Canonical.ZornMatrix.zornMinus,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at hv

/-- Multiplication of Zorn elements and composition of their regular actions differ. -/
theorem regular_action_not_multiplicative : L (U 0 * U 1) ≠ L (U 0) * L (U 1) := by
  intro h
  have ha := congrArg (fun T : Module.End ℝ Zorn => (T (U 2)).a) h
  simp [Module.End.mul_apply, L_apply,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at ha

/-- An internal square-minus-one sandwich exchanges, rather than fixes, the poles. -/
theorem quaternion_sandwich_exchanges_pole :
    (iUnit * polePlus) * (-iUnit) = poleMinus := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [iUnit, InfoGeometry.Canonical.ZornMatrix.zornPlus,
    InfoGeometry.Canonical.ZornMatrix.zornMinus,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]

end InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
