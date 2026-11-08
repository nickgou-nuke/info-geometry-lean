/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.Zorn.AssociatorObstruction
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly

/-!
# Jacobi obstruction to identifying associative Peirce brackets with the Zorn commutator

Ground-truth contract: an additive, bracket-preserving surjection from an
associative-ring commutator algebra onto the concrete integer Zorn carrier
would transport Jacobi to every Zorn element. The repository's basis witness
`(u1,u2,u3)` has nonzero Zorn commutator Jacobiator, so such a surjection
cannot exist. The result concerns these exact carriers and operations; it
does not rule out maps into a Jacobi subalgebra or maps that do not preserve
the displayed brackets.
-/

namespace InfoGeometry.Algebra.Zorn.PeirceLieTransportObstruction

open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

variable {A : Type*} [Ring A]

/-- The ordinary commutator on an associative ring. -/
def ringCommutator (x y : A) : A := x * y - y * x

/-- The cyclic Jacobi expression, with the cyclic order fixed explicitly. -/
def ringCommutatorJacobiator (x y z : A) : A :=
  ringCommutator x (ringCommutator y z) +
    (ringCommutator y (ringCommutator z x) +
      ringCommutator z (ringCommutator x y))

/-- The associative-ring commutator satisfies the cyclic Jacobi identity. -/
theorem ringCommutator_jacobi (x y z : A) :
    ringCommutatorJacobiator x y z = 0 := by
  simp only [ringCommutatorJacobiator, ringCommutator]
  noncomm_ring

/-- Jacobi transports through a map preserving zero, addition, and brackets.
No injectivity or scalar-linearity assumption is needed for this image-level
conclusion. -/
theorem bracket_jacobi_transports
    {C : Type*} (addC : C → C → C) (zeroC : C)
    (bracketC : C → C → C) (f : A → C)
    (hzero : f 0 = zeroC)
    (hadd : ∀ x y, f (x + y) = addC (f x) (f y))
    (hbracket : ∀ x y, f (ringCommutator x y) = bracketC (f x) (f y))
    (x y z : A) :
    addC (bracketC (f x) (bracketC (f y) (f z)))
      (addC (bracketC (f y) (bracketC (f z) (f x)))
        (bracketC (f z) (bracketC (f x) (f y)))) = zeroC := by
  have h := ringCommutator_jacobi x y z
  calc
    _ = f (ringCommutatorJacobiator x y z) := by
      simp only [ringCommutatorJacobiator, hadd, hbracket]
    _ = f 0 := congrArg f h
    _ = zeroC := hzero

/-- A surjective additive bracket map from an associative commutator algebra
would force Jacobi on the entire target bracket. -/
theorem surjective_bracket_map_forces_target_jacobi
    {C : Type*} (addC : C → C → C) (zeroC : C)
    (bracketC : C → C → C) (f : A → C)
    (hzero : f 0 = zeroC)
    (hadd : ∀ x y, f (x + y) = addC (f x) (f y))
    (hbracket : ∀ x y, f (ringCommutator x y) = bracketC (f x) (f y))
    (hsurj : Function.Surjective f) (x y z : C) :
    addC (bracketC x (bracketC y z))
      (addC (bracketC y (bracketC z x)) (bracketC z (bracketC x y))) = zeroC := by
  obtain ⟨x₀, rfl⟩ := hsurj x
  obtain ⟨y₀, rfl⟩ := hsurj y
  obtain ⟨z₀, rfl⟩ := hsurj z
  exact bracket_jacobi_transports addC zeroC bracketC f hzero hadd hbracket x₀ y₀ z₀

/-- Jacobi transport for a source bracket other than the ambient ring
commutator. The source needs only an additive group and its stated Jacobi
law; this is the form used for associative Peirce homotope brackets. -/
theorem source_jacobi_transports
    {C : Type*} (addC : C → C → C) (zeroC : C)
    (bracketA : A → A → A) (bracketC : C → C → C) (f : A → C)
    (hzero : f 0 = zeroC)
    (hadd : ∀ x y, f (x + y) = addC (f x) (f y))
    (hbracket : ∀ x y, f (bracketA x y) = bracketC (f x) (f y))
    (hJacobi : ∀ x y z,
      bracketA x (bracketA y z) +
        (bracketA y (bracketA z x) + bracketA z (bracketA x y)) = 0)
    (x y z : A) :
    addC (bracketC (f x) (bracketC (f y) (f z)))
      (addC (bracketC (f y) (bracketC (f z) (f x)))
        (bracketC (f z) (bracketC (f x) (f y)))) = zeroC := by
  have h := hJacobi x y z
  calc
    _ = f (bracketA x (bracketA y z) +
        (bracketA y (bracketA z x) + bracketA z (bracketA x y))) := by
      simp only [hadd, hbracket]
    _ = f 0 := congrArg f h
    _ = zeroC := hzero

/-- Surjectivity promotes source-Jacobi transport from the image to every
triple in the target. -/
theorem surjective_source_jacobi_forces_target_jacobi
    {C : Type*} (addC : C → C → C) (zeroC : C)
    (bracketA : A → A → A) (bracketC : C → C → C) (f : A → C)
    (hzero : f 0 = zeroC)
    (hadd : ∀ x y, f (x + y) = addC (f x) (f y))
    (hbracket : ∀ x y, f (bracketA x y) = bracketC (f x) (f y))
    (hJacobi : ∀ x y z,
      bracketA x (bracketA y z) +
        (bracketA y (bracketA z x) + bracketA z (bracketA x y)) = 0)
    (hsurj : Function.Surjective f) (x y z : C) :
    addC (bracketC x (bracketC y z))
      (addC (bracketC y (bracketC z x)) (bracketC z (bracketC x y))) = zeroC := by
  obtain ⟨x₀, rfl⟩ := hsurj x
  obtain ⟨y₀, rfl⟩ := hsurj y
  obtain ⟨z₀, rfl⟩ := hsurj z
  exact source_jacobi_transports addC zeroC bracketA bracketC f
    hzero hadd hbracket hJacobi x₀ y₀ z₀

/-- There is no surjective additive map from an associative ring to the
concrete integer Zorn carrier that preserves the ring commutator as the
concrete Zorn element commutator. The explicit nonzero basis Jacobiator is
the obstruction. -/
theorem no_surjective_ring_commutator_map_to_concrete_zorn :
    ¬ ∃ f : A → InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ,
      f 0 = SignedBasis.cell SignedBasis.zero ∧
      (∀ x y, f (x + y) = addZ (f x) (f y)) ∧
      (∀ x y, f (ringCommutator x y) = commutatorZ (f x) (f y)) ∧
      Function.Surjective f := by
  rintro ⟨f, hzero, hadd, hbracket, hsurj⟩
  have hJacobi :=
    surjective_bracket_map_forces_target_jacobi
      addZ (SignedBasis.cell SignedBasis.zero) commutatorZ f
      hzero hadd hbracket hsurj
      (cell Basis8.u1) (cell Basis8.u2) (cell Basis8.u3)
  exact commutator_jacobi_u1_u2_u3_ne_zero hJacobi

/-- The Peirce upper-homotope bracket also cannot map surjectively and
bracket-preservingly onto the full concrete Zorn commutator. Its Jacobi law
is proved for every idempotent in the Peirce owner; the concrete target
fails Jacobi on its standard upper-sector basis triple. -/
theorem no_surjective_upper_homotope_map_to_concrete_zorn
    {B : Type*} [Ring B] (P C : B) (hP : P * P = P) :
    ¬ ∃ f : B → InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℤ,
      f 0 = SignedBasis.cell SignedBasis.zero ∧
      (∀ x y, f (x + y) = addZ (f x) (f y)) ∧
      (∀ x y, f (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct
        P C x y) = commutatorZ (f x) (f y)) ∧
      Function.Surjective f := by
  rintro ⟨f, hzero, hadd, hbracket, hsurj⟩
  have hJacobi (x y z : B) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C x
          (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C y z) +
        (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C y
            (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C z x) +
          InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C z
            (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C x y)) = 0 := by
    simpa only [add_assoc] using
      (InfoGeometry.OperatorAlgebra.PeirceSpine.upper_corner_cross_product_jacobi
        hP C x y z)
  have hTarget :=
    surjective_source_jacobi_forces_target_jacobi
      addZ (SignedBasis.cell SignedBasis.zero)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.upperCornerCrossProduct P C)
      commutatorZ f hzero hadd hbracket hJacobi hsurj
      (cell Basis8.u1) (cell Basis8.u2) (cell Basis8.u3)
  exact commutator_jacobi_u1_u2_u3_ne_zero hTarget

end InfoGeometry.Algebra.Zorn.PeirceLieTransportObstruction
