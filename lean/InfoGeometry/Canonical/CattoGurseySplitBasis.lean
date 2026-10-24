/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GunaydinGurseyTripleProducts
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Signed split basis and the nonassociative CAR identities

Contract: the existing Zorn product, over any commutative ring, with
`uZero = E22`, `uStarZero = E11`, `u i = V i`, `uStar i = -U i`.
The native linear equivalence below and its multiplication transport describe
all eight coordinates, not just a selection of products. No associative CAR
algebra, physical interpretation, or central-extension structure is inferred.
The reference * in the basis names is not the canonical octonion conjugation.

Convention check: `scripts/check_catto_gursey_conventions.py` checks all 64
integer structure constants. The general-ring identities are proved here.
-/

namespace InfoGeometry.Canonical.GunaydinGursey
open InfoGeometry.Algebra
open ZornVectorMatrix Module
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Coefficients of `(uZero,uStarZero,u_i,uStar_i)` as native module coordinates. -/
def splitCoordinates : (R × R × ZornVec3 R × ZornVec3 R) ≃ₗ[R] ZornVectorMatrix R where
  toFun x := ⟨x.2.1, -x.2.2.2, x.2.2.1, x.1⟩
  invFun X := (X.b, X.a, X.w, -X.v)
  left_inv x := by rcases x with ⟨a,b,x,y⟩; simp
  right_inv X := by ext i <;> simp
  map_add' x y := by ext i <;> simp; ring
  map_smul' r x := by ext i <;> simp

/-- Full multiplication transport in the signed split coordinates. -/
theorem splitCoordinates_mul (a b c d : R) (x y z t : ZornVec3 R) :
    mul (splitCoordinates (a,b,x,y)) (splitCoordinates (c,d,z,t)) =
      splitCoordinates
        (a*c - ZornVec3.dot x t, b*d - ZornVec3.dot y z,
         a • z + d • x + ZornVec3.cross y t,
         c • y + b • t + ZornVec3.cross x z) := by
  ext i <;> simp [splitCoordinates, mul, ZornVec3.dot, ZornVec3.cross] <;> ring

@[simp] theorem splitCoordinates_uZero :
    splitCoordinates (1,0,0,0) = (uZero : ZornVectorMatrix R) := by
  ext i <;> simp [splitCoordinates, uZero, E22]

@[simp] theorem splitCoordinates_uStarZero :
    splitCoordinates (0,1,0,0) = (uStarZero : ZornVectorMatrix R) := by
  ext i <;> simp [splitCoordinates, uStarZero, E11]

@[simp] theorem splitCoordinates_u (i : Fin 3) :
    splitCoordinates (0,0,ZornVec3.basis i,0) = (u i : ZornVectorMatrix R) := by
  ext j <;> simp [splitCoordinates, u, V]

@[simp] theorem splitCoordinates_uStar (i : Fin 3) :
    splitCoordinates (0,0,0,ZornVec3.basis i) = (uStar i : ZornVectorMatrix R) := by
  ext j <;> simp [splitCoordinates, uStar, U, neg]

/-- The eight signed generators form an actual native Mathlib basis. -/
noncomputable def signedBasis :
    Basis (Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3) R (ZornVectorMatrix R) :=
  ((Basis.singleton Unit R).prod ((Basis.singleton Unit R).prod
    ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))))).map splitCoordinates

theorem signedBasis_singlets :
    signedBasis (R := R) (.inl ()) = uZero ∧
    signedBasis (R := R) (.inr (.inl ())) = uStarZero := by
  constructor <;> ext i <;>
    simp [signedBasis, Basis.prod_apply, splitCoordinates, uZero, uStarZero, E11, E22]

theorem signedBasis_colors (i : Fin 3) :
    signedBasis (R := R) (.inr (.inr (.inl i))) = u i ∧
    signedBasis (R := R) (.inr (.inr (.inr i))) = uStar i := by
  constructor <;> ext j <;>
    simp [signedBasis, Basis.prod_apply, splitCoordinates, u, uStar, U, V, neg,
      Pi.basisFun_apply, ZornVec3.basis, Pi.single_apply, eq_comm]

/-- The complementary singlets resolve the actual Zorn unit. -/
theorem singlet_sum : (uZero : ZornVectorMatrix R) + uStarZero = one := by
  ext i <;> simp [uZero, uStarZero, E11, E22, one]

/-- Remaining directed absorption laws for the signed anti-triplet. -/
theorem antitriplet_absorption (i : Fin 3) :
    mul (uStarZero : ZornVectorMatrix R) (uStar i) = uStar i ∧
    mul (uStar i : ZornVectorMatrix R) uZero = uStar i ∧
    mul (uZero : ZornVectorMatrix R) (uStar i) = 0 ∧
    mul (uStar i : ZornVectorMatrix R) uStarZero = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext j <;>
    simp [uZero, uStarZero, uStar, E11, E22, U, neg, mul, ZornVec3.dot, ZornVec3.cross]

/-- Both fusion orientations, including repeated indices and reverse orders. -/
theorem fusion_table (i j : Fin 3) :
    mul (u i : ZornVectorMatrix R) (u j) =
      ∑ k : Fin 3, ZornVec3.cross (ZornVec3.basis i : ZornVec3 R) (ZornVec3.basis j) k • uStar k ∧
    mul (uStar i : ZornVectorMatrix R) (uStar j) =
      ∑ k : Fin 3, ZornVec3.cross (ZornVec3.basis i : ZornVec3 R) (ZornVec3.basis j) k • u k := by
  fin_cases i <;> fin_cases j <;> constructor <;> ext k <;>
    simp [u, uStar, U, V, neg, mul, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis, Fin.sum_univ_three]
  all_goals fin_cases k <;> simp

/-- Mixed contractions retain their two distinct singlet endpoints. -/
theorem mixed_table (i j : Fin 3) :
    mul (u i : ZornVectorMatrix R) (uStar j) = (if i = j then -uZero else 0) ∧
    mul (uStar j : ZornVectorMatrix R) (u i) = (if i = j then -uStarZero else 0) := by
  fin_cases i <;> fin_cases j <;> constructor <;> ext k <;>
    simp [u, uStar, uZero, uStarZero, U, V, E11, E22, neg, mul,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

/-- CAR-type anticommutator identities, without an associativity assertion. -/
theorem car_relations (i j : Fin 3) :
    mul (u i : ZornVectorMatrix R) (u j) + mul (u j) (u i) = 0 ∧
    mul (uStar i : ZornVectorMatrix R) (uStar j) + mul (uStar j) (uStar i) = 0 ∧
    mul (u i : ZornVectorMatrix R) (uStar j) + mul (uStar j) (u i) =
      scalar (if i = j then -1 else 0) := by
  fin_cases i <;> fin_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> ext k <;>
    simp [u, uStar, U, V, neg, mul, scalar, ZornVec3.dot,
      ZornVec3.cross, ZornVec3.basis]
  all_goals fin_cases k <;> simp

/-- Generic three-triplet contraction: both parenthesizations are retained. -/
theorem baryon_parenthesizations (x y z : ZornVec3 R) :
    mul (mul (offDiagonal 0 x) (offDiagonal 0 y)) (offDiagonal 0 z) =
      smul (-ZornVec3.dot x (ZornVec3.cross y z)) uStarZero ∧
    mul (offDiagonal 0 x) (mul (offDiagonal 0 y) (offDiagonal 0 z)) =
      smul (-ZornVec3.dot x (ZornVec3.cross y z)) uZero := by
  constructor <;> ext i <;>
    simp [offDiagonal, mul, smul, uZero, uStarZero, E11, E22,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Each nested commutator has coefficient -2 in this basis convention. -/
theorem nested_commutator :
    commutator (u 0 : ZornVectorMatrix R) (commutator (u 1) (u 2)) =
      smul (-2 : R) (uZero - uStarZero) := by
  ext i <;> simp [_root_.sub_eq_add_neg, ZornVectorMatrix.commutator, sub, add, neg,
    u, V, mul, smul, uZero, uStarZero,
    E11, E22, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis] <;> ring

/-- Nonvanishing requires exactly nonvanishing of six in the coefficient ring. -/
theorem jacobiator_ne_zero_iff :
    commutatorJacobiator (u 0 : ZornVectorMatrix R) (u 1) (u 2) ≠ 0 ↔ (6 : R) ≠ 0 := by
  rw [triple_jacobiator]
  constructor
  · intro h hz
    apply h
    rw [show (-6 : R) = 0 by simp [hz]]
    exact zero_smul _
  · intro h heq
    have ha := congrArg ZornVectorMatrix.a heq
    apply h
    simpa [smul, sub, neg, uZero, uStarZero, E11, E22] using ha

/-- The grading diagonal anticommutes with both color families. -/
theorem grading_anticommutes (i : Fin 3) :
    mul (uZero - uStarZero : ZornVectorMatrix R) (u i) +
      mul (u i) (uZero - uStarZero) = 0 ∧
    mul (uZero - uStarZero : ZornVectorMatrix R) (uStar i) +
      mul (uStar i) (uZero - uStarZero) = 0 := by
  constructor <;> ext j <;> simp [_root_.sub_eq_add_neg, uZero, uStarZero, u, uStar, E11, E22,
    U, V, neg, mul, ZornVec3.dot, ZornVec3.cross]

/-- The signed grading element squares to the Zorn unit. -/
theorem grading_square :
    mul (uZero - uStarZero : ZornVectorMatrix R) (uZero - uStarZero) = one := by
  ext i <;> simp [_root_.sub_eq_add_neg, uZero, uStarZero, E11, E22,
    one, mul, ZornVec3.dot, ZornVec3.cross]

/-- No faithful additive multiplication-preserving map into an associative ring
exists. In particular the octonion product cannot be identified with the
ordinary multiplication of the 6|21 supermatrices. -/
theorem no_injective_associative_realization [Nontrivial R]
    {A : Type*} [Ring A] (f : ZornVectorMatrix R →+ A)
    (hmul : ∀ x y, f (mul x y) = f x * f y) : ¬ Function.Injective f := by
  intro hi
  have ha : associator (u 0 : ZornVectorMatrix R) (u 1) (u 2) = 0 := by
    apply hi
    change f (mul (mul (u 0) (u 1)) (u 2) - mul (u 0) (mul (u 1) (u 2))) = f 0
    simp only [map_sub, hmul, _root_.mul_assoc, sub_self, map_zero]
  rw [triple_associator] at ha
  have hb := congrArg ZornVectorMatrix.b ha
  simp [sub, neg, uZero, uStarZero, E11, E22] at hb

end InfoGeometry.Canonical.GunaydinGursey
