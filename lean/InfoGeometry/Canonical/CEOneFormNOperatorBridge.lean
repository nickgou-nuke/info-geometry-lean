/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Canonical.OperatorFrechetDerivationJet
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

/-!
# Finite CE one-cochain families as operator-valued forms

The existing `NOperatorForm` carrier is a finite family of unrestricted
pointwise functions. This bridge embeds families of native CE one-cochains
using a singleton point carrier; linearity remains supplied by the CE
cochain, and is proved explicitly for each extracted component.
-/

noncomputable section

namespace InfoGeometry.Canonical.CEOneFormNOperatorBridge

open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
open InfoGeometry.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable (K : DerivationLieLane ℝ A)

/-- Encode a finite family of CE one-cochains as a finite family of
operator-valued functions with singleton point carrier. -/
def ofCEFamily (n : ℕ) (ω : Fin n → OneForm K) :
    NOperatorForm n (Point := Unit) (Tangent := K.L) (Value := A) :=
  fun i _ x => ω i x

/-- Extract one actual real-linear operator one-form from an encoded CE
family. The construction is restricted to the image of `ofCEFamily`; no
linearity is asserted for arbitrary `NOperatorForm` values. -/
def component (n : ℕ) (ω : Fin n → OneForm K) (i : Fin n) :
    Op1Form ℝ K.L A :=
  { toFun := fun x => ofCEFamily K n ω i () x
    map_add' := by
      intro x y
      change ω i (x + y) = ω i x + ω i y
      exact map_add (ω i) x y
    map_smul' := by
      intro r x
      change ω i (r • x) = r • ω i x
      exact map_smul (ω i) r x }

@[simp] theorem component_apply (n : ℕ) (ω : Fin n → OneForm K)
    (i : Fin n) (x : K.L) :
    component K n ω i x = ω i x := rfl

/-- The one-component `NOperatorForm` obtained from the CE differential of
an operator has, on a continuous Fréchet derivation direction, exactly the
first Fréchet-jet readout. -/
theorem singleton_exteriorDerivativeZero_eq_firstFrechetJet
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (D : FrechetOperatorDerivation ℂ A) (x v : A) :
    ofCEFamily (K := realDerivationsLane A) 1
        (fun _ : Fin 1 => exteriorDerivativeZero (realDerivationsLane A) v)
        0 () (FrechetBridge.toRealDerivation
          (restrictScalarsReal D)) =
      component (K := realDerivationsLane A) 1
          (fun _ : Fin 1 => exteriorDerivativeZero (realDerivationsLane A) v)
          0 (FrechetBridge.toRealDerivation (restrictScalarsReal D)) ∧
    component (K := realDerivationsLane A) 1
        (fun _ : Fin 1 => exteriorDerivativeZero (realDerivationsLane A) v)
        0 (FrechetBridge.toRealDerivation (restrictScalarsReal D)) =
      operatorFrechetJet 1 (D : A → A) x (fun _ : Fin 1 => v) := by
  constructor
  · rfl
  · rw [component_apply]
    symm
    exact operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D x v

abbrev GibbsOperator (n : ℕ) :=
  InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge.Operator n

/-- The degree-zero CE one-form of a finite operator, represented in the
singleton `NOperatorForm` family and extracted as a genuine linear form. -/
noncomputable def finiteCEOperatorForm (n : ℕ) (a : GibbsOperator n) :
    Op1Form ℝ (realDerivationsLane (GibbsOperator n)).L
      (GibbsOperator n) :=
  component (K := realDerivationsLane (GibbsOperator n)) 1
    (fun _ : Fin 1 =>
      exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a) 0

/-- The singleton finite CE family in the existing `NOperatorForm` carrier. -/
noncomputable def finiteCEOperatorFamily (n : ℕ) (a : GibbsOperator n) :
    NOperatorForm 1 (Point := Unit)
      (Tangent := (realDerivationsLane (GibbsOperator n)).L)
      (Value := GibbsOperator n) :=
  ofCEFamily (realDerivationsLane (GibbsOperator n)) 1
    (fun _ : Fin 1 =>
      exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a)

/-- Real derivation direction induced by a continuous complex Fréchet
derivation on the finite operator algebra. -/
noncomputable def finiteCEFrechetDirection {n : ℕ}
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    (realDerivationsLane (GibbsOperator n)).L :=
  FrechetBridge.toRealDerivation (restrictScalarsReal D)

/-- The singleton CE family for `d₀ a` supplies both a Fréchet first-jet
readout and the two independent perturbations in the finite Gibbs/BKM
Hessian. The self-adjointness condition is required only on the first Gibbs
perturbation, exactly as in the Hessian owner's theorem. -/
theorem singletonCE_gibbsHessian_chain
    {n : ℕ} (H a : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (x : GibbsOperator n)
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))) :
    finiteCEOperatorFamily n a 0 () (finiteCEFrechetDirection D) =
      finiteCEOperatorForm n a (finiteCEFrechetDirection D) ∧
    finiteCEOperatorForm n a (finiteCEFrechetDirection D) =
      operatorFrechetJet 1 (D : GibbsOperator n → GibbsOperator n) x
        (fun _ : Fin 1 => a) ∧
    (secondFDerivLogPartitionReadout H
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))
      (finiteCEOperatorForm n a (finiteCEFrechetDirection E))).re =
    centeredBKMOperatorBilinForm
      (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (finiteCEOperatorForm n a)
      (finiteCEOperatorForm n a)
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) := by
  refine ⟨rfl, ?_, ?_⟩
  · change
      component (K := realDerivationsLane (GibbsOperator n)) 1
        (fun _ : Fin 1 =>
          exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a)
        0 (finiteCEFrechetDirection D) = _
    rw [component_apply]
    symm
    exact operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D x a
  · exact secondFDeriv_logPartition_pullback_eq_centeredBKMOperatorBilinForm
      H hH hZ
      (finiteCEOperatorForm n a)
      (finiteCEOperatorForm n a)
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) hD

end InfoGeometry.Canonical.CEOneFormNOperatorBridge
