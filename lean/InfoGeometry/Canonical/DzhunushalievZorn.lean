/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CanonicalZornNonUnitalNonAssocRing
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornMultiplicationOperators
import InfoGeometry.Algebra.NonAssociativeMyung
import InfoGeometry.Algebra.AssociativityObstruction
import Mathlib.Data.ZMod.Basic

/-!
# Dzhunushaliev's real basis on the canonical Zorn carrier

The basis here follows Eqs. (23)--(26) of arXiv:0805.3221v6 consistently.
It therefore differs from several entries of the paper's printed Table I.
`qSpin i` names the paper's `q_(i+1)`, `qSpace i` names `q_(i+4)`, and
`qCut7` names `q_7`; all indices in Lean are zero-based.

The polynomial identities hold over every commutative ring. Nonvanishing,
failure of the derivation law, and the faithful-representation obstruction
are stated separately over the reals. No physical unobservability statement
or identification with a normalized quantum spin operator is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.DzhunushalievZorn

open ZornMatrix
open InfoGeometry.Algebra

variable {R : Type*} [CommRing R]

attribute [local simp] Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply
  Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero Matrix.cons_val_one
  Matrix.cons_val_two Matrix.cons_val_succ

/-- Quaternion basis element, with square `-1`. -/
def qSpin (i : Fin 3) : ZornMatrix R := chiralLowerBasis i - chiralUpperBasis i

/-- Hyperbolic basis element, with square `1`. -/
def qSpace (i : Fin 3) : ZornMatrix R := chiralUpperBasis i + chiralLowerBasis i

/-- The seventh basis element is the negative diagonal Peirce cut. -/
def qCut7 : ZornMatrix R := zornMinus - zornPlus

theorem qCut7_eq_neg_peirce_cut :
    qCut7 (R := R) = -(zornPlus - zornMinus) := by
  unfold qCut7
  abel

/-- Left alternativity on the existing canonical carrier. -/
theorem associator_left_alternative (x y : ZornMatrix R) :
    _root_.associator x x y = 0 := by
  apply ZornMatrix.ext
  · simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def]
    ring
  · simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def]
    ring
  · funext k
    fin_cases k <;>
      simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def] <;> ring
  · funext k
    fin_cases k <;>
      simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def] <;> ring

/-- Right alternativity on the existing canonical carrier. -/
theorem associator_right_alternative (x y : ZornMatrix R) :
    _root_.associator x y y = 0 := by
  apply ZornMatrix.ext
  · simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def]
    ring
  · simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def]
    ring
  · funext k
    fin_cases k <;>
      simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def] <;> ring
  · funext k
    fin_cases k <;>
      simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def] <;> ring

/-- Polarization of left alternativity; valid also in characteristic two. -/
theorem associator_swap12 (x y z : ZornMatrix R) :
    _root_.associator x y z = -_root_.associator y x z := by
  apply eq_neg_of_add_eq_zero_left
  calc
    _root_.associator x y z + _root_.associator y x z =
        _root_.associator (x + y) (x + y) z -
          _root_.associator x x z - _root_.associator y y z := by
      simp only [_root_.associator_apply, add_mul, mul_add]
      abel
    _ = 0 := by rw [associator_left_alternative, associator_left_alternative,
      associator_left_alternative]; simp

/-- Polarization of right alternativity; valid also in characteristic two. -/
theorem associator_swap23 (x y z : ZornMatrix R) :
    _root_.associator x y z = -_root_.associator x z y := by
  apply eq_neg_of_add_eq_zero_left
  calc
    _root_.associator x y z + _root_.associator x z y =
        _root_.associator x (y + z) (y + z) -
          _root_.associator x y y - _root_.associator x z z := by
      simp only [_root_.associator_apply, add_mul, mul_add]
      abel
    _ = 0 := by rw [associator_right_alternative, associator_right_alternative,
      associator_right_alternative]; simp

/-- Ordinary flexibility, including in characteristic two. -/
theorem associator_flexible (x y : ZornMatrix R) :
    _root_.associator x y x = 0 := by
  rw [associator_swap12, associator_right_alternative, neg_zero]

/-- Composition for the canonical quadratic norm already used by the Clifford action. -/
theorem zornNormFun_mul (x y : ZornMatrix R) :
    ZornClifford.zornNormFun (x * y) =
      ZornClifford.zornNormFun x * ZornClifford.zornNormFun y := by
  simp [ZornClifford.zornNormFun, mul_def, mul, dot, cross]
  ring

theorem qSpin_sq (i : Fin 3) :
    qSpin (R := R) i * qSpin i = -(1 : ZornMatrix R) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def, neg_def]

theorem qSpace_sq (i : Fin 3) :
    qSpace (R := R) i * qSpace i = (1 : ZornMatrix R) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross]

theorem qCut7_sq : qCut7 (R := R) * qCut7 = (1 : ZornMatrix R) := by
  ext k <;> (try fin_cases k) <;> simp [qCut7, zornMinus, zornPlus, mul_def, mul, dot, cross, sub_def]

/-- All three oriented quaternion products, with cyclic `Fin 3` indices. -/
theorem qSpin_mul_next (i : Fin 3) :
    qSpin (R := R) i * qSpin (i + 1) = qSpin (i + 2) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def]

theorem qSpin_next_mul (i : Fin 3) :
    qSpin (R := R) (i + 1) * qSpin i = -qSpin (i + 2) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def, neg_def]

/-- Consistent Zorn multiplication gives the same orientation in the hyperbolic sector. -/
theorem qSpace_mul_next (i : Fin 3) :
    qSpace (R := R) i * qSpace (i + 1) = qSpin (i + 2) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def]

theorem qSpace_next_mul (i : Fin 3) :
    qSpace (R := R) (i + 1) * qSpace i = -qSpin (i + 2) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def, neg_def]

theorem qSpin_comm_next (i : Fin 3) :
    akivisBracket (qSpin (R := R) i) (qSpin (i + 1)) =
      (2 : ℤ) • qSpin (i + 2) := by
  rw [akivisBracket, qSpin_mul_next, qSpin_next_mul]
  abel

theorem qSpace_comm_next (i : Fin 3) :
    akivisBracket (qSpace (R := R) i) (qSpace (i + 1)) =
      (2 : ℤ) • qSpin (i + 2) := by
  rw [akivisBracket, qSpace_mul_next, qSpace_next_mul]
  abel

/-- One mixed sign correction relative to printed Table I. -/
theorem qSpin_mul_qSpace_same (i : Fin 3) :
    qSpin (R := R) i * qSpace i = qCut7 := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, qSpin, qCut7, chiralLowerBasis, chiralUpperBasis, zornMinus, zornPlus,
      mul_def, mul, dot, cross, sub_def]

/-- A second mixed sign correction relative to printed Table I. -/
theorem qSpin_mul_qSpace_next (i : Fin 3) :
    qSpin (R := R) i * qSpace (i + 1) = -qSpace (i + 2) := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, qSpin, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_def, neg_def]

/-- The seventh axis also requires a sign correction relative to printed Table I. -/
theorem qSpin_mul_qCut7 (i : Fin 3) :
    qSpin (R := R) i * qCut7 = -qSpace i := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [qSpace, qSpin, qCut7, chiralLowerBasis, chiralUpperBasis, zornMinus, zornPlus,
      mul_def, mul, dot, cross, sub_def, neg_def]

theorem qSpin_basis_associator :
    _root_.associator (qSpin (R := R) 0) (qSpin 1) (qSpin 2) = 0 := by
  ext k <;> (try fin_cases k) <;>
    simp [_root_.associator_apply, qSpin, chiralLowerBasis, chiralUpperBasis,
      mul_def, mul, dot, cross, sub_def]

/-- The entire four-coordinate quaternion slice is closed under the canonical product. -/
theorem quaternionSlice_mul (a b : R) (u v : Fin 3 → R) :
    (⟨a, a, -u, u⟩ : ZornMatrix R) * ⟨b, b, -v, v⟩ =
      ⟨a * b - dot u v, a * b - dot u v,
        -(a • v + b • u + cross u v), a • v + b • u + cross u v⟩ := by
  ext k <;> (try fin_cases k) <;> simp [mul_def, mul, dot, cross] <;> ring

/-- Associativity holds for every triple in the full quaternion slice, not only the basis. -/
theorem quaternionSlice_associator (a b c : R) (u v w : Fin 3 → R) :
    _root_.associator (⟨a, a, -u, u⟩ : ZornMatrix R)
      ⟨b, b, -v, v⟩ ⟨c, c, -w, w⟩ = 0 := by
  ext k <;> (try fin_cases k) <;>
    simp [_root_.associator_apply, mul_def, mul, dot, cross, sub_def] <;> ring

/-- The chiral-cut associator is preserved by the consistent Zorn convention. -/
theorem qSpace_basis_associator :
    _root_.associator (qSpace (R := R) 0) (qSpace 1) (qSpace 2) =
      (2 : ℤ) • qCut7 := by
  rw [show (2 : ℤ) • qCut7 (R := R) = qCut7 + qCut7 by abel]
  ext k <;> (try fin_cases k) <;>
    simp [_root_.associator_apply, qSpace, qCut7, chiralLowerBasis, chiralUpperBasis,
      zornMinus, zornPlus, mul_def, mul, dot, cross, sub_def]; ring

theorem qSpace_basis_jacobiator :
    akivisJacobiator (qSpace (R := R) 0) (qSpace 1) (qSpace 2) =
      (12 : ℤ) • qCut7 := by
  rw [akivisJacobiator_eq_six_zsmul_associator associator_swap12 associator_swap23,
    qSpace_basis_associator, smul_smul]; norm_num

theorem qSpace_basis_leibniz_defect :
    commutatorLeibnizDefect (qSpace (R := R) 0) (qSpace 1) (qSpace 2) =
      (-6 : ℤ) • qCut7 := by
  rw [commutatorLeibnizDefect_eq_neg_three_zsmul_associator
    associator_swap12 associator_swap23, qSpace_basis_associator, smul_smul]; norm_num

/-- The pure upper Peirce triple measures the diagonal cut with coefficient one. -/
theorem upper_basis_associator :
    _root_.associator (chiralUpperBasis (R := R) 0)
      (chiralUpperBasis 1) (chiralUpperBasis 2) = qCut7 := by
  ext k <;> (try fin_cases k) <;>
    simp [_root_.associator_apply, qCut7, chiralUpperBasis, zornMinus, zornPlus,
      mul_def, mul, dot, cross, sub_def]

/-- In characteristic two the two diagonal signs coincide. -/
theorem charTwo_qCut7_eq_one : qCut7 (R := ZMod 2) = 1 := by
  ext k <;> (try fin_cases k) <;>
    simp [qCut7, zornMinus, zornPlus, sub_def]

/-- The alternative Zorn algebra is Lie-admissible in characteristic two. -/
theorem charTwo_jacobiator_eq_zero (x y z : ZornMatrix (ZMod 2)) :
    akivisJacobiator x y z = 0 := by
  rw [akivisJacobiator_eq_six_zsmul_associator associator_swap12 associator_swap23,
    ← Int.cast_smul_eq_zsmul (ZMod 2),
    show ((6 : ℤ) : ZMod 2) = 0 from rfl, zero_smul]

/-- The characteristic-two upper Peirce triple still violates the derivation law. -/
theorem charTwo_upper_leibniz_defect :
    commutatorLeibnizDefect (chiralUpperBasis (R := ZMod 2) 0)
      (chiralUpperBasis 1) (chiralUpperBasis 2) = 1 := by
  rw [commutatorLeibnizDefect_eq_neg_three_zsmul_associator
    associator_swap12 associator_swap23, upper_basis_associator,
    ← Int.cast_smul_eq_zsmul (ZMod 2),
    show ((-3 : ℤ) : ZMod 2) = 1 from rfl, one_smul, charTwo_qCut7_eq_one]

/-- Myung's converse cannot drop its additive two-torsion restriction. -/
theorem charTwo_not_every_commutator_is_derivation :
    ¬ ∀ x y z : ZornMatrix (ZMod 2),
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y := by
  intro h
  have hz := (commutatorLeibnizDefect_eq_zero_iff
    (chiralUpperBasis 0) (chiralUpperBasis 1) (chiralUpperBasis 2)).2
      (h (chiralUpperBasis 0) (chiralUpperBasis 1) (chiralUpperBasis 2))
  rw [charTwo_upper_leibniz_defect] at hz
  have ha := congrArg (fun z : ZornMatrix (ZMod 2) => z.a) hz
  norm_num at ha

private theorem zorn_mul_one (x : ZornMatrix R) : x * 1 = x := by
  ext k <;> (try fin_cases k) <;> simp [mul_def, mul, dot, cross]

/-- The existing left multiplication operators distinguish every Zorn element. -/
theorem leftMulLinear_injective :
    Function.Injective (leftMulLinear : ZornMatrix R → Module.End R (ZornMatrix R)) := by
  intro x y h
  have h1 := LinearMap.congr_fun h (1 : ZornMatrix R)
  simpa [leftMulLinear_apply, ← mul_def, zorn_mul_one] using h1

/-- The left regular map is itself linear in the represented element. -/
def leftRegularLinear : ZornMatrix R →ₗ[R] Module.End R (ZornMatrix R) where
  toFun := leftMulLinear
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact add_mul x y z
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    exact ZornClifford.smul_mul' c x z

/-- Operator composition has precisely the multiplication-associator defect. -/
theorem leftMulLinear_mul_defect_apply (x y z : ZornMatrix R) :
    (leftMulLinear (x * y) - leftMulLinear x * leftMulLinear y) z =
      _root_.associator x y z := rfl

/-- Over the reals the displayed associator is nonzero. -/
theorem qSpace_basis_associator_ne_zero :
    _root_.associator (qSpace (R := ℝ) 0) (qSpace 1) (qSpace 2) ≠ 0 := by
  rw [qSpace_basis_associator, ← Int.cast_smul_eq_zsmul ℝ]
  intro h
  have ha := congrArg (fun z : ZornMatrix ℝ => z.a) h
  norm_num [qCut7, zornMinus, zornPlus, sub_def] at ha

theorem qSpace_basis_jacobiator_ne_zero :
    akivisJacobiator (qSpace (R := ℝ) 0) (qSpace 1) (qSpace 2) ≠ 0 := by
  rw [qSpace_basis_jacobiator, ← Int.cast_smul_eq_zsmul ℝ]
  intro h
  have ha := congrArg (fun z : ZornMatrix ℝ => z.a) h
  norm_num [qCut7, zornMinus, zornPlus, sub_def] at ha

theorem qSpace_basis_leibniz_defect_ne_zero :
    commutatorLeibnizDefect (qSpace (R := ℝ) 0) (qSpace 1) (qSpace 2) ≠ 0 := by
  rw [qSpace_basis_leibniz_defect, ← Int.cast_smul_eq_zsmul ℝ]
  intro h
  have ha := congrArg (fun z : ZornMatrix ℝ => z.a) h
  norm_num [qCut7, zornMinus, zornPlus, sub_def] at ha

/-- The general representation obstruction applied to this concrete real witness. -/
theorem no_faithful_multiplicative_representation {B : Type*} [Semigroup B] :
    ¬ ∃ f : ZornMatrix ℝ → B, Function.Injective f ∧
      (∀ x y : ZornMatrix ℝ, f (x * y) = f x * f y) := by
  apply no_injective_mul_map_to_semigroup_of_nonassociative
  refine ⟨qSpace 0, qSpace 1, qSpace 2, ?_⟩
  intro h
  apply qSpace_basis_associator_ne_zero
  rw [_root_.associator_apply, h, sub_self]

/-- The faithful linear left regular map cannot also preserve multiplication over `ℝ`. -/
theorem leftMulLinear_not_multiplicative :
    ¬ ∀ x y : ZornMatrix ℝ,
      leftMulLinear (x * y) = leftMulLinear x * leftMulLinear y := by
  intro h
  exact no_faithful_multiplicative_representation
    ⟨leftMulLinear, leftMulLinear_injective, h⟩

end InfoGeometry.Canonical.DzhunushalievZorn
