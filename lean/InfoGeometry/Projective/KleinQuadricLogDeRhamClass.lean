import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D
import InfoGeometry.Projective.KleinQuadricTime
import InfoGeometry.Clifford.UniversalCoverLog
import InfoGeometry.Canonical.FilteredDirectInverseColimit

import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-!
# Klein-complement logarithmic period class

This owner packages the existing logarithmic and winding theorems at the
Klein-complement interface.  Its finite content is the local
primitive/period pairing.  The repository does not treat `infinity` as a
terminal stage or a category: an analytic/completed object is introduced only
through a specified filtered colimit, inverse limit, or Ind/Pro completion of
finite stages, together with its universal property.  Accordingly, this file
does not assert a classical manifold-level `H¹_dR` isomorphism; it exposes the
period class that a later colimit owner can transport.
-/

namespace InfoGeometry.Projective.KleinQuadric.LogDeRhamClass

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Projective.KleinQuadric.Time
open InfoGeometry.Clifford.UniversalCoverLog
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D

/-! ## The Klein complement and its logarithmic coefficient -/

def KleinComplement : Type :=
  {P : Plucker6 ℂ // kleinPotential P ≠ 0}

noncomputable def kleinPotentialUnit (P : KleinComplement) : ℂˣ :=
  Units.mk0 (kleinPotential P.1) P.2

@[simp] theorem kleinPotentialUnit_val (P : KleinComplement) :
    (kleinPotentialUnit P : ℂ) = kleinPotential P.1 := by
  rfl

def kleinDLogCoefficient (P : KleinComplement) : ℂ :=
  1 / kleinPotential P.1

theorem kleinPotentialUnit_inv_val (P : KleinComplement) :
    (kleinPotentialUnit P : ℂ)⁻¹ = kleinDLogCoefficient P := by
  rw [kleinPotentialUnit_val]
  simp [kleinDLogCoefficient]

theorem kleinDLogCoefficient_eq_pullback (P : KleinComplement) :
    kleinDLogCoefficient P = grothendieck_dlog (kleinPotential P.1) := by
  rfl

theorem kleinDLogCoefficient_ne_zero (P : KleinComplement) :
    kleinDLogCoefficient P ≠ 0 := by
  exact one_div_ne_zero P.2

theorem kleinPotential_mul_kleinDLogCoefficient (P : KleinComplement) :
    kleinPotential P.1 * kleinDLogCoefficient P = 1 := by
  unfold kleinDLogCoefficient
  simpa [div_eq_mul_inv] using mul_inv_cancel₀ P.2

/-! The directional form is the pullback coefficient `dQ / Q` already
    owned by `KleinQuadricTime`.  Keeping this bridge explicit prevents the
    complement API from introducing a second logarithmic derivative. -/

theorem kleinDLogAlong_eq_coefficient_mul_polar
    (P : KleinComplement) (X : Plucker6 ℂ) :
    kleinDLogAlong P.1 X = kleinDLogCoefficient P * Plucker6.polar P.1 X := by
  unfold kleinDLogAlong kleinDLogCoefficient kleinPotential
  ring

theorem kleinDLogAlong_eq_unit_inv_mul_polar
    (P : KleinComplement) (X : Plucker6 ℂ) :
    kleinDLogAlong P.1 X =
      (kleinPotentialUnit P : ℂ)⁻¹ * Plucker6.polar P.1 X := by
  rw [kleinPotentialUnit_inv_val,
    kleinDLogAlong_eq_coefficient_mul_polar]

theorem kleinDLogAlong_mul_potential
    (P : KleinComplement) (X : Plucker6 ℂ) :
    kleinDLogAlong P.1 X * kleinPotential P.1 =
      Plucker6.polar P.1 X := by
  rw [kleinDLogAlong_eq_coefficient_mul_polar]
  calc
    (kleinDLogCoefficient P * Plucker6.polar P.1 X) * kleinPotential P.1 =
        Plucker6.polar P.1 X *
          (kleinPotential P.1 * kleinDLogCoefficient P) := by ring
    _ = Plucker6.polar P.1 X * 1 := by
      rw [kleinPotential_mul_kleinDLogCoefficient]
    _ = Plucker6.polar P.1 X := by simp

theorem kleinDLogAlong_eq_coefficient_mul_gradient_pairing
    (P : KleinComplement) (X : Plucker6 ℂ) :
    kleinDLogAlong P.1 X =
      kleinDLogCoefficient P *
        Plucker6.coordinatePairing (Plucker6.kleinGradient P.1) X := by
  rw [kleinDLogAlong_eq_gradient_pairing_div]
  simp only [kleinDLogCoefficient, kleinPotential, div_eq_mul_inv]
  rw [mul_comm]
  ring

theorem kleinComplement_not_null (P : KleinComplement) :
    ¬ Plucker6.IsKlein P.1 := by
  intro h
  exact P.2 h

theorem kleinComplement_not_selfOrthogonal (P : KleinComplement) :
    Plucker6.polar P.1 P.1 ≠ 0 := by
  intro h
  apply P.2
  exact (chiralNullConductor_eq_selfOrthogonal P.1).mpr h

/-! ## Local exactness on a logarithm branch -/

theorem logarithmic_coefficient_local_exact
    (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt grothendieckLog (1 / z) z := by
  exact grothendieckLog_deriv_log z hz

theorem klein_logarithmic_coefficient_local_exact
    (P : KleinComplement)
    (hbranch : kleinPotential P.1 ∈ Complex.slitPlane) :
    HasDerivAt grothendieckLog (kleinDLogCoefficient P) (kleinPotential P.1) := by
  simpa [kleinDLogCoefficient, grothendieck_dlog] using
    (logarithmic_coefficient_local_exact (kleinPotential P.1) hbranch)

/-! The universal-cover lift is exact in the only sense currently encoded by
    the repository: its deck increment is the period of `d log`.  The older
    `sheet_increment` name is retained as a compatibility theorem name; the
    indexed objects are deck/winding representatives, not separate surfaces. -/

theorem klein_logarithmic_sheet_increment (z : ℂ) (n : ℤ) :
    uLog (z, n + 1) - uLog (z, n) = (2 * Real.pi * Complex.I : ℂ) := by
  exact universalCoverLog_sheet_increment z n

theorem klein_logarithmic_deck_increment (z : ℂ) (n : ℤ) :
    uLog (z, n + 1) - uLog (z, n) = (2 * Real.pi * Complex.I : ℂ) := by
  exact klein_logarithmic_sheet_increment z n

theorem klein_logarithmic_sheet_shift (z : ℂ) (n k : ℤ) :
    uLog (z, n + k) - uLog (z, n) =
      (2 * Real.pi * Complex.I : ℂ) * (k : ℂ) := by
  unfold uLog
  push_cast
  ring

/-! ## The period pairing already owned by the punctured-plane model -/

def logarithmicPeriod (R : ℝ) : ℂ :=
  ∮ z in C((0 : ℂ), R), poleForm z

theorem logarithmicPeriod_eq_residue (R : ℝ) (hR : 0 < R) :
    logarithmicPeriod R = (2 * Real.pi * Complex.I : ℂ) := by
  exact circleIntegral_one_div R hR

theorem normalized_logarithmicPeriod_eq_one (R : ℝ) (hR : 0 < R) :
    logarithmicPeriod R / (2 * Real.pi * Complex.I : ℂ) = 1 := by
  rw [logarithmicPeriod_eq_residue R hR]
  field_simp

theorem normalized_logarithmicPeriod_of_winding
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    ((n : ℂ) * logarithmicPeriod R) /
        (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  rw [logarithmicPeriod_eq_residue R hR]
  field_simp

theorem logarithmicPeriod_ne_zero (R : ℝ) (hR : 0 < R) :
    logarithmicPeriod R ≠ 0 := by
  rw [logarithmicPeriod_eq_residue R hR]
  intro h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hprod : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  exact hprod h

/-! ## Winding and holonomy readouts -/

theorem klein_logarithmic_period_class_of_winding
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    (n : ℂ) * logarithmicPeriod R = logarithmicPhase n := by
  exact deRhamClass_of_winding R hR n

theorem klein_logarithmic_period_class_add
    (R : ℝ) (hR : 0 < R) (m n : ℤ) :
    ((m + n : ℤ) : ℂ) * logarithmicPeriod R =
      (m : ℂ) * logarithmicPeriod R + (n : ℂ) * logarithmicPeriod R := by
  rw [logarithmicPeriod_eq_residue R hR]
  norm_num [Int.cast_add]
  ring

theorem klein_logarithmic_period_class_neg
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    ((-n : ℤ) : ℂ) * logarithmicPeriod R =
      -((n : ℂ) * logarithmicPeriod R) := by
  rw [logarithmicPeriod_eq_residue R hR]
  norm_num [Int.cast_neg]

theorem klein_logarithmic_sheet_shift_eq_period
    (z : ℂ) (n k : ℤ) (R : ℝ) (hR : 0 < R) :
    uLog (z, n + k) - uLog (z, n) =
      (k : ℂ) * logarithmicPeriod R := by
  rw [klein_logarithmic_sheet_shift, logarithmicPeriod_eq_residue R hR]
  ring

theorem klein_logarithmic_period_class_ne_zero_iff
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    (n : ℂ) * logarithmicPeriod R ≠ 0 ↔ n ≠ 0 := by
  constructor
  · intro h
    intro hn
    apply h
    simp [hn]
  · intro hn
    exact mul_ne_zero (by exact_mod_cast hn) (logarithmicPeriod_ne_zero R hR)

theorem logarithmicPeriod_winding_injective
    (R : ℝ) (hR : 0 < R) :
    Function.Injective (fun n : ℤ => (n : ℂ) * logarithmicPeriod R) := by
  intro m n hmn
  have hzero : ((m - n : ℤ) : ℂ) * logarithmicPeriod R = 0 := by
    rw [Int.cast_sub]
    calc
      ((m : ℂ) - (n : ℂ)) * logarithmicPeriod R =
          (m : ℂ) * logarithmicPeriod R -
            (n : ℂ) * logarithmicPeriod R := by ring
      _ = 0 := sub_eq_zero.mpr hmn
  by_contra hne
  have hdiff : m - n ≠ 0 := sub_ne_zero.mpr hne
  exact (klein_logarithmic_period_class_ne_zero_iff R hR (m - n)).2 hdiff hzero

theorem klein_logarithmic_holonomy_of_winding
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp ((n : ℂ) * logarithmicPeriod R) = 1 := by
  exact wilsonPhase_of_winding R hR n

/-! Characters of the parent winding group.  We keep the codomain as `ℂ`
    because the repository has not introduced a bundled `U(1)` carrier here;
    the exponential identities are the exact algebraic holonomy statements. -/

noncomputable def windingCharacter (α : ℝ) (n : ℤ) : ℂ :=
  Complex.exp ((α : ℂ) * (n : ℂ) * (2 * Real.pi * Complex.I))

theorem windingCharacter_eq_logarithmicPeriod_holonomy
    (R : ℝ) (hR : 0 < R) (α : ℝ) (n : ℤ) :
    windingCharacter α n =
      Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R)) := by
  rw [logarithmicPeriod_eq_residue R hR]
  unfold windingCharacter
  congr 1
  ring

theorem windingCharacter_norm (α : ℝ) (n : ℤ) :
    ‖windingCharacter α n‖ = 1 := by
  simpa [windingCharacter, mul_assoc, mul_left_comm, mul_comm] using
    Complex.norm_exp_ofReal_mul_I
      (α * (n : ℝ) * (2 * Real.pi))

theorem windingCharacter_zero (α : ℝ) :
    windingCharacter α 0 = 1 := by
  simp [windingCharacter]

theorem windingCharacter_add (α : ℝ) (m n : ℤ) :
    windingCharacter α (m + n) =
      windingCharacter α m * windingCharacter α n := by
  unfold windingCharacter
  rw [Int.cast_add]
  have harg :
      (α : ℂ) * ((m : ℂ) + (n : ℂ)) * (2 * Real.pi * Complex.I) =
        (α : ℂ) * (m : ℂ) * (2 * Real.pi * Complex.I) +
          (α : ℂ) * (n : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [harg, Complex.exp_add]

theorem windingCharacter_neg (α : ℝ) (n : ℤ) :
    windingCharacter α (-n) = (windingCharacter α n)⁻¹ := by
  unfold windingCharacter
  rw [Int.cast_neg]
  have harg :
      (α : ℂ) * (-(n : ℂ)) * (2 * Real.pi * Complex.I) =
        -((α : ℂ) * (n : ℂ) * (2 * Real.pi * Complex.I)) := by
    ring
  rw [harg, Complex.exp_neg]

noncomputable def windingCharacterCircle (α : ℝ) :
    Multiplicative ℤ →* Circle where
  toFun n :=
    ⟨windingCharacter α (Multiplicative.toAdd n),
      by
        change windingCharacter α (Multiplicative.toAdd n) ∈
          Metric.sphere (0 : ℂ) 1
        exact mem_sphere_zero_iff_norm.mpr
          (windingCharacter_norm α (Multiplicative.toAdd n))⟩
  map_one' := by
    apply Circle.ext
    change windingCharacter α (Multiplicative.toAdd 1) = 1
    simpa using windingCharacter_zero α
  map_mul' := by
    intro m n
    apply Circle.ext
    change windingCharacter α (Multiplicative.toAdd (m * n)) =
      windingCharacter α (Multiplicative.toAdd m) *
        windingCharacter α (Multiplicative.toAdd n)
    change windingCharacter α
        (Multiplicative.toAdd m + Multiplicative.toAdd n) =
      windingCharacter α (Multiplicative.toAdd m) *
        windingCharacter α (Multiplicative.toAdd n)
    exact windingCharacter_add α
      (Multiplicative.toAdd m) (Multiplicative.toAdd n)

@[simp] theorem windingCharacterCircle_apply_coe
    (α : ℝ) (n : Multiplicative ℤ) :
    (windingCharacterCircle α n : ℂ) =
      windingCharacter α (Multiplicative.toAdd n) := rfl

noncomputable def windingAddChar (α : ℝ) : AddChar ℤ Circle where
  toFun n := windingCharacterCircle α (Multiplicative.ofAdd n)
  map_zero_eq_one' := by
    change windingCharacterCircle α (Multiplicative.ofAdd 0) = 1
    simpa using (windingCharacterCircle α).map_one
  map_add_eq_mul' := by
    intro m n
    change windingCharacterCircle α (Multiplicative.ofAdd (m + n)) =
      windingCharacterCircle α (Multiplicative.ofAdd m) *
        windingCharacterCircle α (Multiplicative.ofAdd n)
    simpa using
      (windingCharacterCircle α).map_mul
        (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)

@[simp] theorem windingAddChar_apply_coe (α : ℝ) (n : ℤ) :
    (windingAddChar α n : ℂ) = windingCharacter α n := rfl

theorem windingAddChar_of_winding_period
    (R : ℝ) (hR : 0 < R) (α : ℝ) (n : ℤ) :
    (windingAddChar α n : ℂ) =
      Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R)) := by
  change windingCharacter α n =
    Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R))
  exact windingCharacter_eq_logarithmicPeriod_holonomy R hR α n

theorem windingCharacterCircle_of_winding_period
    (R : ℝ) (hR : 0 < R) (α : ℝ) (n : ℤ) :
    (windingCharacterCircle α (Multiplicative.ofAdd n) : ℂ) =
      Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R)) := by
  change windingCharacter α n =
    Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R))
  exact windingCharacter_eq_logarithmicPeriod_holonomy R hR α n

theorem windingCharacterCircle_ofAdd_neg
    (α : ℝ) (n : ℤ) :
    windingCharacterCircle α (Multiplicative.ofAdd (-n)) =
      (windingCharacterCircle α (Multiplicative.ofAdd n))⁻¹ := by
  apply Circle.ext
  simp only [windingCharacterCircle_apply_coe, Circle.coe_inv]
  exact windingCharacter_neg α n

noncomputable def windingCharacterAddCircle (α : ℝ) : ℤ →+ Additive Circle where
  toFun n := Additive.ofMul (windingCharacterCircle α (Multiplicative.ofAdd n))
  map_zero' := by
    change windingCharacterCircle α (Multiplicative.ofAdd 0) = 1
    simpa using (windingCharacterCircle α).map_one
  map_add' := by
    intro m n
    change windingCharacterCircle α (Multiplicative.ofAdd (m + n)) =
      windingCharacterCircle α (Multiplicative.ofAdd m) *
        windingCharacterCircle α (Multiplicative.ofAdd n)
    simpa using
      (windingCharacterCircle α).map_mul
        (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)

@[simp] theorem windingCharacterAddCircle_apply_coe
    (α : ℝ) (n : ℤ) :
    ((windingCharacterAddCircle α n).toMul : ℂ) = windingCharacter α n := by
  rfl

theorem windingCharacterAddCircle_of_winding_period
    (R : ℝ) (hR : 0 < R) (α : ℝ) (n : ℤ) :
    ((windingCharacterAddCircle α n).toMul : ℂ) =
      Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R)) := by
  exact windingCharacterCircle_of_winding_period R hR α n

noncomputable def windingCharacterUnit (α : ℝ) :
    Multiplicative ℤ →* ℂˣ where
  toFun n := Units.mk0 (windingCharacter α n) (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    change windingCharacter α (Multiplicative.toAdd 1) = 1
    simpa using windingCharacter_zero α
  map_mul' := by
    intro m n
    apply Units.ext
    change windingCharacter α (Multiplicative.toAdd (m * n)) =
      windingCharacter α (Multiplicative.toAdd m) *
        windingCharacter α (Multiplicative.toAdd n)
    change windingCharacter α (Multiplicative.toAdd m + Multiplicative.toAdd n) =
      windingCharacter α (Multiplicative.toAdd m) *
        windingCharacter α (Multiplicative.toAdd n)
    exact windingCharacter_add α (Multiplicative.toAdd m) (Multiplicative.toAdd n)

@[simp] theorem windingCharacterUnit_apply_val (α : ℝ) (n : Multiplicative ℤ) :
    (windingCharacterUnit α n : ℂ) = windingCharacter α n := by
  rfl

theorem windingCharacterUnit_ofAdd_apply (α : ℝ) (n : ℤ) :
    windingCharacterUnit α (Multiplicative.ofAdd n) =
      Units.mk0 (windingCharacter α n) (Complex.exp_ne_zero _) := by
  rfl

theorem windingCharacterUnit_of_winding_period
    (R : ℝ) (hR : 0 < R) (α : ℝ) (n : ℤ) :
    (windingCharacterUnit α (Multiplicative.ofAdd n) : ℂ) =
      Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R)) := by
  change windingCharacter α n =
    Complex.exp ((α : ℂ) * ((n : ℂ) * logarithmicPeriod R))
  exact windingCharacter_eq_logarithmicPeriod_holonomy R hR α n

theorem windingCharacterUnit_norm (α : ℝ) (n : ℤ) :
    ‖(windingCharacterUnit α (Multiplicative.ofAdd n) : ℂ)‖ = 1 := by
  simpa using windingCharacter_norm α n

theorem windingCharacterUnit_ofAdd_add (α : ℝ) (m n : ℤ) :
    windingCharacterUnit α (Multiplicative.ofAdd (m + n)) =
      windingCharacterUnit α (Multiplicative.ofAdd m) *
        windingCharacterUnit α (Multiplicative.ofAdd n) := by
  apply Units.ext
  simp only [windingCharacterUnit_apply_val, Units.val_mul]
  exact windingCharacter_add α m n

theorem windingCharacterUnit_ofAdd_neg (α : ℝ) (n : ℤ) :
    windingCharacterUnit α (Multiplicative.ofAdd (-n)) =
      (windingCharacterUnit α (Multiplicative.ofAdd n))⁻¹ := by
  apply Units.ext
  simp only [windingCharacterUnit_apply_val]
  exact windingCharacter_neg α n

theorem windingCharacter_one_is_trivial (n : ℤ) :
    windingCharacter 1 n = 1 := by
  simpa [windingCharacter, mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_int_mul_two_pi_mul_I n)

theorem windingCharacter_integer (m n : ℤ) :
    windingCharacter (m : ℝ) n = 1 := by
  unfold windingCharacter
  have harg :
      ((m : ℝ) : ℂ) * (n : ℂ) * (2 * Real.pi * Complex.I) =
        ((m * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_int_mul_two_pi_mul_I (m * n)

theorem windingCharacter_half_sq (n : ℤ) :
    windingCharacter (1 / 2 : ℝ) n *
        windingCharacter (1 / 2 : ℝ) n = 1 := by
  calc
    windingCharacter (1 / 2 : ℝ) n *
          windingCharacter (1 / 2 : ℝ) n =
        windingCharacter (1 / 2 : ℝ) (n + n) :=
      (windingCharacter_add (1 / 2 : ℝ) n n).symm
    _ = windingCharacter 1 n := by
      unfold windingCharacter
      rw [Int.cast_add]
      congr 1
      push_cast
      ring
    _ = 1 := windingCharacter_one_is_trivial n

theorem windingCharacter_third_cube (n : ℤ) :
    windingCharacter (1 / 3 : ℝ) n *
        windingCharacter (1 / 3 : ℝ) n *
          windingCharacter (1 / 3 : ℝ) n = 1 := by
  calc
    windingCharacter (1 / 3 : ℝ) n *
          windingCharacter (1 / 3 : ℝ) n *
            windingCharacter (1 / 3 : ℝ) n =
        windingCharacter (1 / 3 : ℝ) (n + n) *
          windingCharacter (1 / 3 : ℝ) n := by
      rw [windingCharacter_add]
    _ = windingCharacter (1 / 3 : ℝ) ((n + n) + n) :=
      (windingCharacter_add (1 / 3 : ℝ) (n + n) n).symm
    _ = windingCharacter 1 n := by
      unfold windingCharacter
      rw [Int.cast_add, Int.cast_add]
      congr 1
      push_cast
      ring
    _ = 1 := windingCharacter_one_is_trivial n

theorem windingCharacterUnit_half_sq (n : ℤ) :
    windingCharacterUnit (1 / 2 : ℝ) (Multiplicative.ofAdd n) *
        windingCharacterUnit (1 / 2 : ℝ) (Multiplicative.ofAdd n) =
      (1 : ℂˣ) := by
  apply Units.ext
  change windingCharacter (1 / 2 : ℝ) n *
      windingCharacter (1 / 2 : ℝ) n = 1
  exact windingCharacter_half_sq n

theorem windingCharacterUnit_third_cube (n : ℤ) :
    windingCharacterUnit (1 / 3 : ℝ) (Multiplicative.ofAdd n) ^ 3 =
      (1 : ℂˣ) := by
  apply Units.ext
  simpa [pow_succ, windingCharacterUnit] using windingCharacter_third_cube n

theorem windingCharacter_half_periodic (n : ℤ) :
    windingCharacter (1 / 2 : ℝ) (n + 2) =
      windingCharacter (1 / 2 : ℝ) n := by
  rw [windingCharacter_add]
  have hperiod : windingCharacter (1 / 2 : ℝ) 2 = 1 := by
    calc
      windingCharacter (1 / 2 : ℝ) 2 = windingCharacter 1 1 := by
        unfold windingCharacter
        congr 1
        push_cast
        ring
      _ = 1 := windingCharacter_one_is_trivial 1
  rw [hperiod, mul_one]

theorem windingCharacter_third_periodic (n : ℤ) :
    windingCharacter (1 / 3 : ℝ) (n + 3) =
      windingCharacter (1 / 3 : ℝ) n := by
  rw [windingCharacter_add]
  have hperiod : windingCharacter (1 / 3 : ℝ) 3 = 1 := by
    calc
      windingCharacter (1 / 3 : ℝ) 3 = windingCharacter 1 1 := by
        unfold windingCharacter
        congr 1
        push_cast
        ring
      _ = 1 := windingCharacter_one_is_trivial 1
  rw [hperiod, mul_one]

theorem windingCharacterUnit_half_periodic (n : ℤ) :
    windingCharacterUnit (1 / 2 : ℝ) (Multiplicative.ofAdd (n + 2)) =
      windingCharacterUnit (1 / 2 : ℝ) (Multiplicative.ofAdd n) := by
  apply Units.ext
  simpa only [windingCharacterUnit_apply_val] using
    windingCharacter_half_periodic n

theorem windingCharacterUnit_third_periodic (n : ℤ) :
    windingCharacterUnit (1 / 3 : ℝ) (Multiplicative.ofAdd (n + 3)) =
      windingCharacterUnit (1 / 3 : ℝ) (Multiplicative.ofAdd n) := by
  apply Units.ext
  simpa only [windingCharacterUnit_apply_val] using
    windingCharacter_third_periodic n

theorem windingCharacterCircle_half_sq (n : ℤ) :
    windingCharacterCircle (1 / 2 : ℝ) (Multiplicative.ofAdd n) *
        windingCharacterCircle (1 / 2 : ℝ) (Multiplicative.ofAdd n) = 1 := by
  apply Circle.ext
  simp only [Circle.coe_mul, windingCharacterCircle_apply_coe]
  exact windingCharacter_half_sq n

theorem windingCharacterCircle_third_cube (n : ℤ) :
    windingCharacterCircle (1 / 3 : ℝ) (Multiplicative.ofAdd n) *
        windingCharacterCircle (1 / 3 : ℝ) (Multiplicative.ofAdd n) *
          windingCharacterCircle (1 / 3 : ℝ) (Multiplicative.ofAdd n) = 1 := by
  apply Circle.ext
  simp only [Circle.coe_mul, windingCharacterCircle_apply_coe]
  exact windingCharacter_third_cube n

theorem windingAddChar_half_sq (n : ℤ) :
    windingAddChar (1 / 2 : ℝ) n * windingAddChar (1 / 2 : ℝ) n = 1 := by
  apply Circle.ext
  simp only [Circle.coe_mul, windingAddChar_apply_coe]
  exact windingCharacter_half_sq n

theorem windingAddChar_third_cube (n : ℤ) :
    windingAddChar (1 / 3 : ℝ) n * windingAddChar (1 / 3 : ℝ) n *
        windingAddChar (1 / 3 : ℝ) n = 1 := by
  apply Circle.ext
  simp only [Circle.coe_mul, windingAddChar_apply_coe]
  exact windingCharacter_third_cube n

theorem windingAddChar_half_periodic (n : ℤ) :
    windingAddChar (1 / 2 : ℝ) (n + 2) =
      windingAddChar (1 / 2 : ℝ) n := by
  apply Circle.ext
  simp only [windingAddChar_apply_coe]
  exact windingCharacter_half_periodic n

theorem windingAddChar_third_periodic (n : ℤ) :
    windingAddChar (1 / 3 : ℝ) (n + 3) =
      windingAddChar (1 / 3 : ℝ) n := by
  apply Circle.ext
  simp only [windingAddChar_apply_coe]
  exact windingCharacter_third_periodic n

theorem klein_period_index_is_integer
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    ((n : ℂ) * logarithmicPeriod R) /
        (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  exact normalized_logarithmicPeriod_of_winding R hR n

/-! ## Categorical analytic readout

The repository's analytic/continuum boundary is a filtered categorical
construction: finite-stage direct inductive data are transported through a
cocone, while the dual functionals form the corresponding inverse system.
There is no terminal stage called `∞`; the universal cocone/compatible-family
objects are the relevant readouts.  The theorem below is the exact
period-readout compatibility needed by this owner.  It deliberately does not
identify `KleinComplement` with a chosen colimit object; such an
identification requires an explicit stage system and universal-property
witness.
-/

section FilteredAnalyticReadout

open CategoryTheory
open CategoryTheory.Limits

variable {R I : Type*} [CommRing R] [Preorder I]
variable {A : I → Type*}
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {AInf : Type*} [AddCommGroup AInf] [Module R AInf]

theorem klein_logarithmic_period_colimit_readout
    (sys : FilteredColimit.DirectInductiveSystem R I A)
    (cocone : FilteredColimit.InductiveCocone R sys AInf)
    (periodInf : AInf →ₗ[R] R)
    {i j : I} (hij : i ≤ j) (x : A i) :
    periodInf (cocone.psi j (sys.f hij x)) =
      periodInf (cocone.psi i x) := by
  exact FilteredColimit.InductiveCocone.colimit_functional_trace_comm
    cocone periodInf hij x

/-! The direct/inverse boundary itself is inherited from the canonical
    filtered-colimit owner.  This is an interface theorem: the Klein module
    supplies no ad hoc replacement for either categorical universal property.
    The finite diagram hypothesis is exactly the one required by the native
    preservation theorem. -/

universe u

variable {R₀ : Type u} [CommRing R₀]
variable {J L : Type u} [Category.{u} J] [IsFiltered J] [Category.{u} L]
variable [FinCategory L]

noncomputable def klein_logarithmic_direct_inverse_colimit_iso
    (F : L ⥤ J ⥤ ModuleCat.{u} R₀) :
    colimit (limit F) ≅ limit (colimit F.flip) :=
  FilteredColimit.Native.filteredColimitFiniteLimitIso F

end FilteredAnalyticReadout

end
end InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
