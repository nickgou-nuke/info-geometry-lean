/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-!
# First Fréchet jets of continuous operator derivations

These lemmas connect the generic iterated Fréchet-jet carrier to the
continuous noncommutative derivation carrier.  They concern the first jet only;
they do not assert that higher jets satisfy a first-order Leibniz rule.
-/

namespace InfoGeometry.Canonical.OperatorFrechetDerivationJet

open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The full real-linear Leibniz derivation Lie algebra acting on its
coefficient algebra by evaluation. -/
noncomputable def realDerivationsLane (A : Type*)
    [NormedRing A] [NormedAlgebra ℝ A] : DerivationLieLane ℝ A where
  L := NonAssocDerivation.derivations ℝ A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := (LieHom.id : NonAssocDerivation.derivations ℝ A →ₗ⁅ℝ⁆
    NonAssocDerivation.derivations ℝ A)
  faithful := fun _ _ h => h

namespace FrechetBridge

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A continuous real Fréchet derivation, with continuity forgotten, is a
real-linear Leibniz endomorphism in the native derivation Lie algebra. -/
noncomputable def toRealDerivation
    (D : FrechetOperatorDerivation ℝ A) :
    (realDerivationsLane A).L :=
  ⟨D.toContinuousLinearMap.toLinearMap, D.leibniz⟩

/-- The Fréchet commutator adapter preserves the native derivation bracket. -/
theorem toRealDerivation_commutator
    (D E : FrechetOperatorDerivation ℝ A) :
    toRealDerivation (FrechetOperatorDerivation.commutator D E) =
      ⁅toRealDerivation D, toRealDerivation E⁆ := by
  show (FrechetBridge.toRealDerivation (FrechetOperatorDerivation.commutator D E) :
    NonAssocDerivation.derivations ℝ A) = _
  apply Subtype.ext
  ext a
  change (realDerivationsLane A).operatorAction
      (toRealDerivation (FrechetOperatorDerivation.commutator D E)) a =
    (realDerivationsLane A).operatorAction
      ⁅toRealDerivation D, toRealDerivation E⁆ a
  rw [DerivationLieLane.operatorAction_map_lie]
  rfl

end FrechetBridge

/-- Evaluation of the first iterated Fréchet jet of a continuous operator
derivation is its continuous linear representative applied to the direction. -/
theorem operatorFrechetJet_one_apply
    (D : FrechetOperatorDerivation ℂ A) (x v : A) :
    operatorFrechetJet 1 (D : A → A) x (fun _ : Fin 1 => v) =
      D.toContinuousLinearMap v := by
  rw [operatorFrechetJet, iteratedFDeriv_one_apply]
  exact congrArg (fun L => L v) (D.hasFDerivAt x).fderiv

/-- The first Fréchet jet of a continuous operator derivation obeys the
noncommutative product rule on the product direction, by the derivation's
Leibniz law. -/
theorem operatorFrechetJet_one_mul
    (D : FrechetOperatorDerivation ℂ A) (x a b : A) :
    operatorFrechetJet 1 (D : A → A) x (fun _ : Fin 1 => a * b) =
      D.toContinuousLinearMap a * b + a * D.toContinuousLinearMap b := by
  rw [operatorFrechetJet_one_apply]
  exact D.leibniz a b

/-- Restricting the scalars of a complex continuous operator derivation to
`ℝ` preserves its operator Leibniz law. -/
noncomputable def restrictScalarsReal
    (D : FrechetOperatorDerivation ℂ A) :
    FrechetOperatorDerivation ℝ A where
  toContinuousLinearMap := D.toContinuousLinearMap.restrictScalars ℝ
  leibniz := by
    intro a b
    exact D.leibniz a b

@[simp] theorem restrictScalarsReal_apply
    (D : FrechetOperatorDerivation ℂ A) (a : A) :
    restrictScalarsReal D a = D.toContinuousLinearMap a :=
  rfl

/-- The complex first-jet readout agrees with the coefficient readout of the
real `NCDerivation` obtained from the existing scalar-forgetting adapter. This
coefficient identity alone does not construct a Lie action or CE differential. -/
theorem operatorFrechetJet_one_apply_eq_toNCDerivation
    (D : FrechetOperatorDerivation ℂ A) (x v : A) :
    operatorFrechetJet 1 (D : A → A) x (fun _ : Fin 1 => v) =
      FrechetOperatorDerivation.toNCDerivation
        (restrictScalarsReal D) v := by
  rw [operatorFrechetJet_one_apply]
  rfl

/-- The first Fréchet jet of a complex continuous derivation equals the
degree-zero CE differential evaluated on its real derivation direction.
This is the explicit jet-to-CE evaluation map; it makes no claim that the
full algebraic derivation lane consists only of continuous derivations. -/
theorem operatorFrechetJet_one_apply_eq_exteriorDerivativeZero
    (D : FrechetOperatorDerivation ℂ A) (x v : A) :
    operatorFrechetJet 1 (D : A → A) x (fun _ : Fin 1 => v) =
      exteriorDerivativeZero (realDerivationsLane A) v
        (FrechetBridge.toRealDerivation (restrictScalarsReal D)) := by
  rw [operatorFrechetJet_one_apply, exteriorDerivativeZero_apply]
  rfl

end InfoGeometry.Canonical.OperatorFrechetDerivationJet
