import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AkivisIdentity
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Left-regular Jordan/Lie channels and the associator defect

The left-regular maps of a non-associative algebra are honest linear maps,
but their composition does not in general agree with multiplication in the
carrier.  This file records the resulting associator correction.  It makes
no metric, curvature, Lie, or Malcev identification.
-/

namespace InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

noncomputable def associatorOperator (x y : A) : A →ₗ[ℝ] A :=
  L_map (R := ℝ) (x * y) -
    (L_map (R := ℝ) x).comp (L_map (R := ℝ) y)

omit [IsScalarTower ℝ A A] in
@[simp] theorem associatorOperator_apply (x y z : A) :
    associatorOperator x y z = _root_.associator x y z := by
  rfl

noncomputable def jordanRegularChannel (x y : A) : A →ₗ[ℝ] A :=
  (2 : ℝ)⁻¹ •
    ((L_map (R := ℝ) x).comp (L_map (R := ℝ) y) +
      (L_map (R := ℝ) y).comp (L_map (R := ℝ) x))

noncomputable def lieRegularChannel (x y : A) : A →ₗ[ℝ] A :=
  (2 : ℝ)⁻¹ •
    ((L_map (R := ℝ) x).comp (L_map (R := ℝ) y) -
      (L_map (R := ℝ) y).comp (L_map (R := ℝ) x))

theorem jordanRegularChannel_apply (x y z : A) :
    jordanRegularChannel x y z =
      L_map (R := ℝ) (jordanChannel x y) z -
        (2 : ℝ)⁻¹ •
          (associatorOperator x y z + associatorOperator y x z) := by
  change (2 : ℝ)⁻¹ • (x * (y * z) + y * (x * z)) =
    ((2 : ℝ)⁻¹ • (x * y + y * x)) * z -
      (2 : ℝ)⁻¹ •
        (((x * y) * z - x * (y * z)) +
          ((y * x) * z - y * (x * z)))
  rw [smul_mul_assoc, ← smul_sub]
  congr 1
  simp only [add_mul]
  abel

theorem lieRegularChannel_apply (x y z : A) :
    lieRegularChannel x y z =
      L_map (R := ℝ) (lieChannel x y) z -
        (2 : ℝ)⁻¹ •
          (associatorOperator x y z - associatorOperator y x z) := by
  change (2 : ℝ)⁻¹ • (x * (y * z) - y * (x * z)) =
    ((2 : ℝ)⁻¹ • (x * y - y * x)) * z -
      (2 : ℝ)⁻¹ •
        (((x * y) * z - x * (y * z)) -
          ((y * x) * z - y * (x * z)))
  rw [smul_mul_assoc, ← smul_sub]
  congr 1
  simp only [sub_mul]
  abel

theorem alternative_jordanRegularChannel_apply
    (hleft : ∀ x y z : A,
      _root_.associator y x z = -_root_.associator x y z)
    (x y z : A) :
    jordanRegularChannel x y z = L_map (R := ℝ) (jordanChannel x y) z := by
  rw [jordanRegularChannel_apply]
  have hxy : associatorOperator x y z = _root_.associator x y z :=
    associatorOperator_apply x y z
  have hyx : associatorOperator y x z = -_root_.associator x y z := by
    rw [associatorOperator_apply, hleft]
  rw [hxy, hyx, add_neg_cancel, smul_zero, sub_zero]

theorem alternative_lieRegularChannel_apply
    (hleft : ∀ x y z : A,
      _root_.associator y x z = -_root_.associator x y z)
    (x y z : A) :
    lieRegularChannel x y z =
      L_map (R := ℝ) (lieChannel x y) z - _root_.associator x y z := by
  rw [lieRegularChannel_apply]
  have hxy : associatorOperator x y z = _root_.associator x y z :=
    associatorOperator_apply x y z
  have hyx : associatorOperator y x z = -_root_.associator x y z := by
    rw [associatorOperator_apply, hleft]
  rw [hxy, hyx,
    sub_neg_eq_add, ← two_smul ℝ (_root_.associator x y z), smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]

/-! ## Operator-level obstruction and Lie Jacobi

Composition of linear endomorphisms is associative.  Thus its normalized
commutator is a Lie bracket; the carrier associator only obstructs the
left-regular map from intertwining the carrier bracket.
-/

noncomputable def leftRegularCommutatorObstruction (x y : A) : A →ₗ[ℝ] A :=
  lieRegularChannel x y - L_map (R := ℝ) (lieChannel x y)

theorem leftRegular_commutator_obstruction_apply
    (hleft : ∀ x y z : A,
      _root_.associator y x z = -_root_.associator x y z)
    (x y z : A) :
    leftRegularCommutatorObstruction x y z = -_root_.associator x y z := by
  unfold leftRegularCommutatorObstruction
  simp only [LinearMap.sub_apply]
  rw [alternative_lieRegularChannel_apply hleft x y z]
  abel

theorem leftRegular_commutator_obstruction_eq_neg_associatorOperator
    (hleft : ∀ x y z : A,
      _root_.associator y x z = -_root_.associator x y z)
    (x y : A) :
    leftRegularCommutatorObstruction x y = -associatorOperator x y := by
  ext z
  simp only [LinearMap.neg_apply]
  rw [leftRegular_commutator_obstruction_apply hleft,
    associatorOperator_apply]

noncomputable def operatorLieChannel
    (T U : A →ₗ[ℝ] A) : A →ₗ[ℝ] A :=
  (2 : ℝ)⁻¹ • (T.comp U - U.comp T)

noncomputable def operatorJacobiator
    (T U V : A →ₗ[ℝ] A) : A →ₗ[ℝ] A :=
  operatorLieChannel (operatorLieChannel T U) V +
    operatorLieChannel (operatorLieChannel U V) T +
    operatorLieChannel (operatorLieChannel V T) U

theorem operatorLieChannel_jacobiator_zero
    (T U V : A →ₗ[ℝ] A) :
    operatorJacobiator T U V = 0 := by
  ext z
  simp [operatorJacobiator, operatorLieChannel,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  module

theorem zero_associator_triple_regular_recovery
    (x y z : A)
    (hxy : _root_.associator x y z = 0)
    (hyx : _root_.associator y x z = 0) :
    jordanRegularChannel x y z = L_map (R := ℝ) (jordanChannel x y) z ∧
      lieRegularChannel x y z = L_map (R := ℝ) (lieChannel x y) z := by
  constructor
  · rw [jordanRegularChannel_apply, associatorOperator_apply,
      associatorOperator_apply, hxy, hyx, add_zero, smul_zero, sub_zero]
  · rw [lieRegularChannel_apply, associatorOperator_apply,
      associatorOperator_apply, hxy, hyx, sub_zero, smul_zero, sub_zero]

/-! ## Native Zorn specialization

The concrete Zorn carrier supplies the alternative law upstream.  This
specialization only packages its first-two-slot associator antisymmetry for
the generic regular-channel theorems above.
-/

theorem zornVectorMatrix_alternative_associator_swap12
    (x y z : ZornVectorMatrix ℝ) :
    _root_.associator y x z = -_root_.associator x y z := by
  exact alternative_associator_swap12
    (fun p q => zorn_left_alternative p q) y x z

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem alternative_akivisJacobiator_eq_six_smul_associator
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    akivisJacobiator x y z =
      (6 : ℝ) • _root_.associator x y z := by
  rw [akivis_identity]
  have hxy : _root_.associator y x z =
      -_root_.associator x y z :=
    alternative_associator_swap12 hleft y x z
  have hyz : _root_.associator y z x =
      _root_.associator x y z :=
    alternative_associator_cycle hleft hright x y z
  have hzx : _root_.associator z x y =
      _root_.associator x y z := by
    exact (alternative_associator_cycle hleft hright y z x).trans hyz
  have hzy : _root_.associator z y x =
      -_root_.associator x y z := by
    calc
      _root_.associator z y x = _root_.associator y x z :=
        (alternative_associator_cycle hleft hright z y x).symm
      _ = -_root_.associator x y z := hxy
  have hxz : _root_.associator x z y =
      -_root_.associator x y z := by
    have h := alternative_associator_swap23 hright x y z
    calc
      _root_.associator x z y =
          -(-_root_.associator x z y) := by simp
      _ = -_root_.associator x y z := congrArg Neg.neg h.symm
  rw [hyz, hzx, hxy, hzy, hxz]
  module

noncomputable def normalizedAkivisJacobiator (x y z : A) : A :=
  lieChannel (lieChannel x y) z +
    lieChannel (lieChannel y z) x +
    lieChannel (lieChannel z x) y

theorem normalizedAkivisJacobiator_eq_quarter_akivisJacobiator
    (x y z : A) :
    normalizedAkivisJacobiator x y z =
      (1 / 4 : ℝ) • akivisJacobiator x y z := by
  change
    ((2 : ℝ)⁻¹ •
        ((2 : ℝ)⁻¹ • (x * y - y * x) * z -
          z * ((2 : ℝ)⁻¹ • (x * y - y * x))) +
      (2 : ℝ)⁻¹ •
        ((2 : ℝ)⁻¹ • (y * z - z * y) * x -
          x * ((2 : ℝ)⁻¹ • (y * z - z * y))) +
      (2 : ℝ)⁻¹ •
        ((2 : ℝ)⁻¹ • (z * x - x * z) * y -
          y * ((2 : ℝ)⁻¹ • (z * x - x * z)))) =
      (1 / 4 : ℝ) •
        ((x * y - y * x) * z - z * (x * y - y * x) +
          ((y * z - z * y) * x - x * (y * z - z * y)) +
          ((z * x - x * z) * y - y * (z * x - x * z)))
  simp only [smul_mul_assoc, mul_smul_comm]
  module

theorem alternative_normalizedAkivisJacobiator_eq_three_halves_associator
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    normalizedAkivisJacobiator x y z =
      (3 / 2 : ℝ) • _root_.associator x y z := by
  rw [normalizedAkivisJacobiator_eq_quarter_akivisJacobiator]
  rw [alternative_akivisJacobiator_eq_six_smul_associator hleft hright]
  module

theorem zornVectorMatrix_akivisJacobiator_eq_six_smul_associator
    (x y z : ZornVectorMatrix ℝ) :
    akivisJacobiator x y z =
      (6 : ℝ) • _root_.associator x y z := by
  exact alternative_akivisJacobiator_eq_six_smul_associator
    (fun p q => zorn_left_alternative p q)
    (fun p q => zorn_right_alternative p q) x y z

theorem zornVectorMatrix_normalizedAkivisJacobiator_eq_three_halves_associator
    (x y z : ZornVectorMatrix ℝ) :
    normalizedAkivisJacobiator x y z =
      (3 / 2 : ℝ) • _root_.associator x y z := by
  rw [normalizedAkivisJacobiator_eq_quarter_akivisJacobiator]
  rw [zornVectorMatrix_akivisJacobiator_eq_six_smul_associator]
  module

end InfoGeometry.Algebra
