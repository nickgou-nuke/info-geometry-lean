/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Sp4Contact
import InfoGeometry.OperatorAlgebra.DerivationCurvatureDetection
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Module

/-!
# A faithful contact-algebra action and its curvature

The concrete symplectic Lie algebra acts on the full real four-by-four matrix
algebra by inner derivations. Faithfulness is proved from the matrix center
and the symplectic equation; it is not assumed as an interface field.

The connection `Γ_c(X) = c X` on this derivation lane has curvature
`F_c(X,Y) = c(c+1)[X,Y]`. Thus `c = -1` gives a nonzero flat connection whose
values need not commute, while `c = 1` gives nonzero curvature. Both satisfy
the existing native CE Bianchi identity. These are algebraic connections;
no manifold Cartan connection or analytic holonomy is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Sp4ContactConnection

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Sp4Contact
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- A symplectic matrix commuting with every full matrix is zero. -/
theorem commute_all_iff_zero (X : Sp) :
    (∀ a : Mat, Commute (X : Mat) a) ↔ X = 0 := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single
      (fun i j _ => (h (Matrix.single i j 1)).symm)
    have heq := congrArg (fun M : Mat => M 0 3) (symplectic_equation X)
    rw [← hr] at heq
    norm_num [Matrix.scalar, omega, Matrix.mul_apply, Fin.sum_univ_succ] at heq
    have hr0 : r = 0 := by linarith
    apply Subtype.ext
    rw [← hr, hr0]
    simp
  · rintro rfl a
    exact Commute.zero_left a

/-- The existing native inner-derivation homomorphism restricted to sp4. -/
def innerAction : Sp →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ Mat :=
  (matrixInnerLieHom ℝ (Fin 4)).comp algebra.incl

@[simp] theorem innerAction_apply (X : Sp) (a : Mat) :
    (innerAction X : Module.End ℝ Mat) a = (X : Mat) * a - a * (X : Mat) := rfl

/-- Faithfulness follows from the actual matrix representation. -/
theorem innerAction_injective : Function.Injective innerAction := by
  intro X Y h
  have hz : innerAction (X - Y) = 0 := by rw [map_sub, h, sub_self]
  have hc : ∀ a : Mat, Commute ((X - Y : Sp) : Mat) a := by
    intro a
    have ha := congrArg (fun D : NonAssocDerivation.derivations ℝ Mat =>
      (D : Module.End ℝ Mat) a) hz
    change ((X - Y : Sp) : Mat) * a - a * ((X - Y : Sp) : Mat) = 0 at ha
    exact sub_eq_zero.mp ha
  exact sub_eq_zero.mp ((commute_all_iff_zero (X - Y)).mp hc)

/-- Constructed faithful derivation lane on the full noncommutative matrix algebra. -/
abbrev lane : DerivationLieLane ℝ Mat where
  L := Sp
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := innerAction
  faithful := innerAction_injective

@[simp] theorem lane_action (X : Sp) (a : Mat) :
    lane.operatorAction X a = (X : Mat) * a - a * (X : Mat) := rfl

/-- A genuine one-cochain, with scalar parameter and full matrix values. -/
def scaledConnection (c : ℝ) : OneForm lane := c • algebra.incl.toLinearMap

@[simp] theorem scaledConnection_apply (c : ℝ) (X : Sp) :
    scaledConnection c X = c • (X : Mat) := rfl

/-- In this inner-derivation model the total covariant operator is explicit. -/
theorem scaledConnection_covariantDerivative (c : ℝ) (X : Sp) (a : Mat) :
    covariantDerivative lane (scaledConnection c) X a =
      (c + 1) • ((X : Mat) * a - a * (X : Mat)) := by
  change (X : Mat) * a - a * (X : Mat) +
      (c • (X : Mat)) * a - a * (c • (X : Mat)) = _
  simp only [mul_smul_comm, smul_mul_assoc]
  module

/-- Exact curvature of the scaled-inclusion family, retaining matrix order. -/
theorem scaledConnection_curvature (c : ℝ) (X Y : Sp) :
    connectionCurvature lane (scaledConnection c) X Y =
      (c * (c + 1)) • ((⁅X, Y⁆ : Sp) : Mat) := by
  change (X : Mat) * (c • (Y : Mat)) - (c • (Y : Mat)) * (X : Mat) -
      ((Y : Mat) * (c • (X : Mat)) - (c • (X : Mat)) * (Y : Mat)) -
      c • ((X : Mat) * (Y : Mat) - (Y : Mat) * (X : Mat)) +
      ((c • (X : Mat)) * (c • (Y : Mat)) -
        (c • (Y : Mat)) * (c • (X : Mat))) =
      (c * (c + 1)) • ((X : Mat) * (Y : Mat) - (Y : Mat) * (X : Mat))
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  module

/-- Curvature values stay in the actual symplectic Lie subalgebra. -/
theorem scaledConnection_curvature_mem (c : ℝ) (X Y : Sp) :
    connectionCurvature lane (scaledConnection c) X Y ∈ algebra := by
  rw [scaledConnection_curvature]
  exact algebra.smul_mem _ (⁅X, Y⁆ : Sp).property

/-- The negative inclusion satisfies the Maurer--Cartan equation. -/
theorem negative_inclusion_flat :
    SatisfiesMaurerCartan lane (scaledConnection (-1)) := by
  change connectionCurvature lane (scaledConnection (-1)) = 0
  apply Subtype.ext
  ext X Y : 2
  change connectionCurvature lane (scaledConnection (-1)) X Y = 0
  simpa only [neg_add_cancel, mul_zero, zero_smul] using
    (scaledConnection_curvature (-1) X Y)

/-- This flat example cancels the background inner action completely.
It is not an example of nontrivial analytic parallel transport. -/
theorem negative_inclusion_covariantDerivative (X : Sp) (a : Mat) :
    covariantDerivative lane (scaledConnection (-1)) X a = 0 := by
  simp [scaledConnection_covariantDerivative]

/-- Flatness does not require commuting connection values. -/
theorem negative_inclusion_values_noncommute :
    ¬ Commute (scaledConnection (-1) u1) (scaledConnection (-1) u2) := by
  intro h
  change (-1 : ℝ) • (u1 : Mat) * ((-1 : ℝ) • (u2 : Mat)) =
    (-1 : ℝ) • (u2 : Mat) * ((-1 : ℝ) • (u1 : Mat)) at h
  exact u1_mul_u2_ne (by simpa only [neg_one_smul, neg_mul_neg] using h)

/-- An exact parameter criterion for flatness of this constructed family. -/
theorem scaledConnection_flat_iff (c : ℝ) :
    SatisfiesMaurerCartan lane (scaledConnection c) ↔ c = 0 ∨ c = -1 := by
  constructor
  · intro h
    have hF := congrArg (fun F : TwoForm lane => F u1 u2) h
    rw [scaledConnection_curvature] at hF
    have hc0 : c * (c + 1) = 0 := (smul_eq_zero.mp hF).resolve_right
      (fun hz => lie_u1_u2_ne_zero (Subtype.ext hz))
    rcases mul_eq_zero.mp hc0 with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · change connectionCurvature lane (scaledConnection 0) = 0
      apply Subtype.ext
      ext X Y : 2
      change connectionCurvature lane (scaledConnection 0) X Y = 0
      simpa only [zero_mul, zero_smul] using (scaledConnection_curvature 0 X Y)
    · exact negative_inclusion_flat

theorem positive_inclusion_nonflat :
    ¬ SatisfiesMaurerCartan lane (scaledConnection 1) := by
  rw [scaledConnection_flat_iff]
  norm_num

/-- The existing CE Bianchi theorem applies to every member of the family. -/
theorem scaledConnection_bianchi (c : ℝ) (X Y Z : Sp) :
    covariantExteriorDerivativeTwo lane (scaledConnection c)
      (connectionCurvature lane (scaledConnection c)) X Y Z = 0 :=
  connectionCurvature_bianchi lane (scaledConnection c) X Y Z

/-- For these symplectic curvature values, all full-matrix observables
detect zero curvature exactly. This strengthens the general centrality
criterion using the proved faithful representation. -/
theorem scaledConnection_action_zero_iff_curvature_zero (c : ℝ) (X Y : Sp) :
    (∀ a : Mat,
      covariantDerivative lane (scaledConnection c) X
          (covariantDerivative lane (scaledConnection c) Y a) -
        covariantDerivative lane (scaledConnection c) Y
          (covariantDerivative lane (scaledConnection c) X a) -
        covariantDerivative lane (scaledConnection c) ⁅X, Y⁆ a = 0) ↔
      connectionCurvature lane (scaledConnection c) X Y = 0 := by
  rw [covariant_commutator_zero_iff_central]
  let F : Sp := ⟨connectionCurvature lane (scaledConnection c) X Y,
    scaledConnection_curvature_mem c X Y⟩
  exact (commute_all_iff_zero F).trans Subtype.ext_iff

/-! ## Nonzero central curvature in the same full matrix coefficient algebra -/

/-- A central-valued connection on the same nonabelian direction algebra.
It is used as a counterexample to inferring nonzero adjoint action from
nonzero curvature. It is not asserted to take values in the sp4 subalgebra. -/
def centralConnection : OneForm lane where
  toFun X := coordinates X 3 • (1 : Mat)
  map_add' X Y := by simp [coordinates_add, add_smul]
  map_smul' r X := by simp [coordinates_smul, smul_smul]

@[simp] theorem centralConnection_apply (X : Sp) :
    centralConnection X = coordinates X 3 • (1 : Mat) := rfl

/-- Its CE differential can be nonzero even though the wedge square and
the action of the directions on its values vanish. -/
theorem centralConnection_curvature (X Y : Sp) :
    connectionCurvature lane centralConnection X Y =
      -(coordinates ⁅X, Y⁆ 3) • (1 : Mat) := by
  change (X : Mat) * (coordinates Y 3 • (1 : Mat)) -
      (coordinates Y 3 • (1 : Mat)) * (X : Mat) -
      ((Y : Mat) * (coordinates X 3 • (1 : Mat)) -
        (coordinates X 3 • (1 : Mat)) * (Y : Mat)) -
      coordinates ⁅X, Y⁆ 3 • (1 : Mat) +
      ((coordinates X 3 • (1 : Mat)) * (coordinates Y 3 • (1 : Mat)) -
        (coordinates Y 3 • (1 : Mat)) * (coordinates X 3 • (1 : Mat))) = _
  simp [smul_smul, mul_comm (coordinates X 3) (coordinates Y 3)]

theorem centralConnection_curvature_endpoints :
    connectionCurvature lane centralConnection zPlus zMinus = -(1 : Mat) := by
  rw [centralConnection_curvature, lie_zPlus_zMinus]
  simp [gradingElement, generator]

/-- This is a nonflat connection in the full matrix coefficient algebra. -/
theorem centralConnection_nonflat :
    ¬ SatisfiesMaurerCartan lane centralConnection := by
  intro h
  have heq := congrArg (fun F : TwoForm lane => F zPlus zMinus) h
  rw [centralConnection_curvature_endpoints] at heq
  have h00 := congrArg (fun M : Mat => M 0 0) heq
  change (-1 : ℝ) = 0 at h00
  norm_num at h00

/-- Its entire adjoint curvature action nevertheless vanishes. -/
theorem centralConnection_action_zero (X Y : Sp) (a : Mat) :
    covariantDerivative lane centralConnection X
        (covariantDerivative lane centralConnection Y a) -
      covariantDerivative lane centralConnection Y
        (covariantDerivative lane centralConnection X a) -
      covariantDerivative lane centralConnection ⁅X, Y⁆ a = 0 := by
  rw [covariantDerivative_commutator, centralConnection_curvature]
  simp

theorem centralConnection_bianchi (X Y Z : Sp) :
    covariantExteriorDerivativeTwo lane centralConnection
      (connectionCurvature lane centralConnection) X Y Z = 0 :=
  connectionCurvature_bianchi lane centralConnection X Y Z

end InfoGeometry.OperatorAlgebra.Sp4ContactConnection
