/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra
import InfoGeometry.Canonical.G2ToBraidChain
import InfoGeometry.Lie.BaezG2SplitOctonion
import InfoGeometry.Lie.RealSplitOctonionDerivation
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationLane
import InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
import InfoGeometry.Canonical.CanonicalZornNonUnitalNonAssocRing
import InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations
import InfoGeometry.Canonical.OperatorCoefficientZornExtension
import InfoGeometry.Exceptional.AlbertDerivationsF4
import InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
import InfoGeometry.Canonical.BraidedDerivation

/-!
# Gap D Bridge: Exceptional, Zorn, Super, and Braided Derivation Lanes

Additive, Lie-compatible, and Onsager-pairing bridges connecting the
unconsolidated exceptional, Zorn, Jordan, super/Peirce, and braided derivation
lanes to the canonical `NonAssocDerivation.derivations`, `LieActionLane` /
`DerivationLieLane`, and `OnsagerFormPairing` spine without introducing any
global typeclass diamonds on pre-existing carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## Section 1: Canonical Spine Helpers (F8.4) -/

section SpineHelpers

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- Pull an `OnsagerCasimirSystem A` back along any `LieActionLane ℝ A` evaluated at `a : A`. -/
def inducedActionLaneOnsagerSystem
    {A : Type*} [AddCommGroup A] [Module ℝ A]
    (S : OnsagerCasimirSystem A) (K : LieActionLane ℝ A) (a : A) :
    OnsagerCasimirSystem K.L :=
  let evalD : K.L →ₗ[ℝ] A :=
    { toFun := fun x => K.operatorAction x a
      map_add' := fun x y => by simp [map_add, LinearMap.add_apply]
      map_smul' := fun c x => by simp [map_smul, LinearMap.smul_apply] }
  { dissipative := S.dissipative.compl₁₂ evalD evalD
    reversible := S.reversible.compl₁₂ evalD evalD
    dissipative_symm := fun x y => S.dissipative_symm _ _
    reversible_skew := fun x y => S.reversible_skew _ _
    dissipative_nonneg := fun x => S.dissipative_nonneg _ }

@[simp]
theorem inducedActionLaneOnsagerSystem_totalGenerator
    {A : Type*} [AddCommGroup A] [Module ℝ A]
    (S : OnsagerCasimirSystem A) (K : LieActionLane ℝ A) (a : A) (x y : K.L) :
    (inducedActionLaneOnsagerSystem S K a).totalGenerator x y =
      S.totalGenerator (K.operatorAction x a) (K.operatorAction y a) :=
  rfl

/-- Master Onsager–Casimir reciprocity for `ActionOperatorForm K n` without requiring `[Ring A]`. -/
theorem onsager_pairing_actionForm_reciprocity_module
    {A : Type*} [AddCommGroup A] [Module ℝ A]
    (K : LieActionLane ℝ A) {n : ℕ}
    (PP : ParityOnsagerFormPairing K.L A n)
    (ω η : ActionOperatorForm K n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_general_form_reciprocity PP ω η

/-- Convert an additive endomorphism `B →+ B` to a `ℤ`-linear endomorphism `Module.End ℤ B`. -/
def addHomToIntEnd {B : Type*} [AddCommGroup B] (d : B →+ B) : Module.End ℤ B where
  toFun := d
  map_add' := d.map_add
  map_smul' n x := d.map_zsmul n x

@[simp]
theorem addHomToIntEnd_apply {B : Type*} [AddCommGroup B] (d : B →+ B) (x : B) :
    addHomToIntEnd d x = d x :=
  rfl

/-- Inner commutator derivation `X ↦ K * X - X * K` over `ℤ` on an associative ring. -/
def innerIntDerivation {B : Type*} [Ring B] (K : B) :
    InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ B :=
  ⟨{ toFun := fun X => K * X - X * K
     map_add' := fun X Y => by noncomm_ring
     map_smul' := fun n X => by
       change K * (n • X) - (n • X) * K = n • (K * X - X * K)
       rw [mul_smul_comm, smul_mul_assoc, ← smul_sub] },
   fun X Y => by
     change K * (X * Y) - (X * Y) * K =
       (K * X - X * K) * Y + X * (K * Y - Y * K)
     noncomm_ring⟩

@[simp]
theorem innerIntDerivation_apply {B : Type*} [Ring B] (K X : B) :
    (innerIntDerivation K : Module.End ℤ B) X = K * X - X * K :=
  rfl

end SpineHelpers

/-! ## Section 2: `G2DerivationLieAlgebra.G2Derivation` (`CrossProdCarrier R`, F8.1) -/

section G2CrossProdLane

/-- Dedicated newtype wrapper equipping `Fin 7 → R` with the Fano cross product
without polluting Mathlib's pointwise `Pi.instMul` on `Fin 7 → R`. -/
@[ext]
structure CrossProdCarrier (R : Type*) where
  val : Fin 7 → R

/-- Coordinate equivalence between `CrossProdCarrier R` and `Fin 7 → R`. -/
def crossProdCarrierEquiv (R : Type*) : CrossProdCarrier R ≃ (Fin 7 → R) where
  toFun := CrossProdCarrier.val
  invFun := CrossProdCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupCrossProdCarrier (R : Type*) [Ring R] :
    AddCommGroup (CrossProdCarrier R) :=
  Equiv.addCommGroup (crossProdCarrierEquiv R)

/-- Additive equivalence between `CrossProdCarrier R` and `Fin 7 → R`. -/
def crossProdCarrierAddEquiv (R : Type*) [Ring R] :
    CrossProdCarrier R ≃+ (Fin 7 → R) where
  toEquiv := crossProdCarrierEquiv R
  map_add' _ _ := rfl

@[simp]
theorem crossProdCarrier_zero_val {R : Type*} [Ring R] :
    (0 : CrossProdCarrier R).val = 0 :=
  rfl

@[simp]
theorem crossProdCarrier_add_val {R : Type*} [Ring R] (x y : CrossProdCarrier R) :
    (x + y).val = x.val + y.val :=
  rfl

@[simp]
theorem crossProdCarrier_sub_val {R : Type*} [Ring R] (x y : CrossProdCarrier R) :
    (x - y).val = x.val - y.val :=
  rfl

@[simp]
theorem crossProdCarrier_neg_val {R : Type*} [Ring R] (x : CrossProdCarrier R) :
    (-x).val = -x.val :=
  rfl

instance instMulCrossProdCarrier (R : Type*) [Ring R] : Mul (CrossProdCarrier R) where
  mul x y := ⟨InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd x.val y.val⟩

@[simp]
theorem crossProdCarrier_mul_val {R : Type*} [Ring R] (x y : CrossProdCarrier R) :
    (x * y).val = InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd x.val y.val :=
  rfl

instance instNonUnitalNonAssocRingCrossProdCarrier (R : Type*) [Ring R] :
    NonUnitalNonAssocRing (CrossProdCarrier R) where
  zero_mul x := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd]
  mul_zero x := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd]
  left_distrib x y z := by
    apply CrossProdCarrier.ext
    exact InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd_add_right x.val y.val z.val
  right_distrib x y z := by
    apply CrossProdCarrier.ext
    exact InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd_add_left x.val y.val z.val

private theorem g2Derivation_map_zero {R : Type*} [Ring R]
    (D : InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R) :
    D 0 = 0 := by
  have h := D.map_sub 0 0
  simpa using h

/-- Embed `G2DerivationLieAlgebra.G2Derivation R` into `NonAssocDerivation.derivations ℤ (CrossProdCarrier R)`. -/
def g2DerivationToIntDerivations {R : Type*} [Ring R]
    (D : InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R) :
    InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ (CrossProdCarrier R) :=
  let f : CrossProdCarrier R →+ CrossProdCarrier R :=
    { toFun := fun x => ⟨D x.val⟩
      map_zero' := by
        apply CrossProdCarrier.ext
        exact g2Derivation_map_zero D
      map_add' := fun x y => by
        apply CrossProdCarrier.ext
        exact D.map_add x.val y.val }
  ⟨addHomToIntEnd f, fun x y => by
    apply CrossProdCarrier.ext
    exact D.leibniz x.val y.val⟩

/-- Recover `G2DerivationLieAlgebra.G2Derivation R` from `NonAssocDerivation.derivations ℤ (CrossProdCarrier R)`. -/
def intDerivationsToG2Derivation {R : Type*} [Ring R]
    (D : InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ (CrossProdCarrier R)) :
    InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R where
  toFun u := ((D : Module.End ℤ (CrossProdCarrier R)) ⟨u⟩).val
  map_add u v := by
    have h := (D : Module.End ℤ (CrossProdCarrier R)).map_add ⟨u⟩ ⟨v⟩
    exact congrArg CrossProdCarrier.val h
  map_sub u v := by
    have h := (D : Module.End ℤ (CrossProdCarrier R)).map_sub ⟨u⟩ ⟨v⟩
    exact congrArg CrossProdCarrier.val h
  leibniz u v := by
    have h := D.property ⟨u⟩ ⟨v⟩
    exact congrArg CrossProdCarrier.val h

/-- Equivalence between `G2DerivationLieAlgebra.G2Derivation R` and
`NonAssocDerivation.derivations ℤ (CrossProdCarrier R)`. -/
def g2DerivationEquivIntDerivations (R : Type*) [Ring R] :
    InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R ≃
      InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ (CrossProdCarrier R) where
  toFun := g2DerivationToIntDerivations
  invFun := intDerivationsToG2Derivation
  left_inv D := by cases D; rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    cases x
    rfl

theorem g2DerivationEquivIntDerivations_bracket {R : Type*} [Ring R]
    (D₁ D₂ : InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R) :
    g2DerivationEquivIntDerivations R
        (InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.g2Bracket D₁ D₂) =
      ⁅g2DerivationEquivIntDerivations R D₁, g2DerivationEquivIntDerivations R D₂⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

section CommRingCrossProd

instance instModuleCrossProdCarrier (R : Type*) [CommRing R] :
    Module R (CrossProdCarrier R) :=
  AddEquiv.module R (crossProdCarrierAddEquiv R)

@[simp]
theorem crossProdCarrier_smul_val {R : Type*} [CommRing R] (r : R) (x : CrossProdCarrier R) :
    (r • x).val = r • x.val :=
  rfl

instance instIsScalarTowerCrossProdCarrier (R : Type*) [CommRing R] :
    IsScalarTower R (CrossProdCarrier R) (CrossProdCarrier R) where
  smul_assoc r x y := by
    ext i
    change InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd (r • x.val) y.val i =
      r * InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd x.val y.val i
    fin_cases i <;>
      · dsimp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd]
        ring

instance instSMulCommClassCrossProdCarrier (R : Type*) [CommRing R] :
    SMulCommClass R (CrossProdCarrier R) (CrossProdCarrier R) where
  smul_comm r x y := by
    ext i
    change r * InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd x.val y.val i =
      InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd x.val (r • y.val) i
    fin_cases i <;>
      · dsimp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.crossProd]
        ring

/-- `R`-linear refinement of `G2DerivationLieAlgebra.G2Derivation R`. -/
structure LinearG2Derivation (R : Type*) [CommRing R] extends
    InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.G2Derivation R where
  map_smul : ∀ (r : R) (u : Fin 7 → R), toFun (r • u) = r • toFun u

/-- `R`-linear `G2Derivation`s satisfy `NonAssocDerivation.IsLeibniz R (CrossProdCarrier R)`. -/
def linearG2DerivationToEnd {R : Type*} [CommRing R] (D : LinearG2Derivation R) :
    Module.End R (CrossProdCarrier R) where
  toFun x := ⟨D.toFun x.val⟩
  map_add' x y := by
    apply CrossProdCarrier.ext
    exact D.map_add x.val y.val
  map_smul' r x := by
    apply CrossProdCarrier.ext
    exact D.map_smul r x.val

theorem linearG2Derivation_isLeibniz {R : Type*} [CommRing R] (D : LinearG2Derivation R) :
    InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz R (CrossProdCarrier R)
      (linearG2DerivationToEnd D) :=
  fun x y => by
    apply CrossProdCarrier.ext
    exact D.leibniz x.val y.val

/-- Equivalence between `LinearG2Derivation R` and `NonAssocDerivation.derivations R (CrossProdCarrier R)`. -/
def linearG2DerivationEquivDerivations (R : Type*) [CommRing R] :
    LinearG2Derivation R ≃
      InfoGeometry.Algebra.NonAssocDerivation.derivations R (CrossProdCarrier R) where
  toFun D := ⟨linearG2DerivationToEnd D, linearG2Derivation_isLeibniz D⟩
  invFun D :=
    { toFun := fun u => ((D : Module.End R (CrossProdCarrier R)) ⟨u⟩).val
      map_add := fun u v =>
        congrArg CrossProdCarrier.val ((D : Module.End R (CrossProdCarrier R)).map_add ⟨u⟩ ⟨v⟩)
      map_sub := fun u v =>
        congrArg CrossProdCarrier.val ((D : Module.End R (CrossProdCarrier R)).map_sub ⟨u⟩ ⟨v⟩)
      leibniz := fun u v => congrArg CrossProdCarrier.val (D.property ⟨u⟩ ⟨v⟩)
      map_smul := fun r u =>
        congrArg CrossProdCarrier.val ((D : Module.End R (CrossProdCarrier R)).map_smul r ⟨u⟩) }
  left_inv D := by
    rcases D with ⟨⟨_, _, _, _⟩, _⟩
    rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    cases x
    rfl

theorem linearG2DerivationEquivDerivations_bracket {R : Type*} [CommRing R]
    (D₁ D₂ : LinearG2Derivation R) :
    (linearG2DerivationEquivDerivations R
      ⟨InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.g2Bracket D₁.toG2Derivation D₂.toG2Derivation,
       fun r u => by
         dsimp [InfoGeometry.Algebra.Zorn.G2DerivationLieAlgebra.g2Bracket]
         rw [D₂.map_smul, D₁.map_smul, D₁.map_smul, D₂.map_smul, smul_sub]⟩) =
      ⁅linearG2DerivationEquivDerivations R D₁, linearG2DerivationEquivDerivations R D₂⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

/-- Canonical `DerivationLieLane` on `CrossProdCarrier R`. -/
def crossProdCarrierDerivationLieLane (R : Type*) [CommRing R] :
    InfoGeometry.Algebra.DerivationLieLane R (CrossProdCarrier R) :=
  InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.fullDerivationLieLane R
    (CrossProdCarrier R)

/-- F8.4 Onsager attachment for the real Fano cross-product derivation lane. -/
def crossProdCarrierOnsagerSystem
    (S : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem (CrossProdCarrier ℝ))
    (a : CrossProdCarrier ℝ) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem (crossProdCarrierDerivationLieLane ℝ).L :=
  InfoGeometry.Thermo.OnsagerFormsBridge.inducedDerivationLaneOnsagerSystem S
    (crossProdCarrierDerivationLieLane ℝ) a

theorem crossProdCarrier_onsager_reciprocity {n : ℕ}
    (PP : InfoGeometry.Thermo.OnsagerFormsBridge.ParityOnsagerFormPairing
      (crossProdCarrierDerivationLieLane ℝ).L (CrossProdCarrier ℝ) n)
    (ω η : InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.DerivationOperatorForm
      (crossProdCarrierDerivationLieLane ℝ) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  InfoGeometry.Thermo.OnsagerFormsBridge.onsager_pairing_derivationForm_reciprocity
    (crossProdCarrierDerivationLieLane ℝ) PP ω η

end CommRingCrossProd

end G2CrossProdLane

/-! ## Section 3: `ZornVectorMatrix`, `ZornMatrix ℝ`, `G2ToBraidChain`, & `SplitCayley*` (F8.1) -/

section ZornAndSplitCayleyLanes

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- Equivalence between `ZornVectorMatrix.Derivation` and `NonAssocDerivation.derivations R (ZornVectorMatrix R)`. -/
def zornVectorMatrixDerivationEquivDerivations (R : Type*) [CommRing R] :
    InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R) ≃
      NonAssocDerivation.derivations R (InfoGeometry.Algebra.ZornVectorMatrix R) :=
  (InfoGeometry.Algebra.derivationEquiv (R := R)).trans nonAssocDerivationEquivDerivations

@[simp]
theorem zornVectorMatrixDerivationEquivDerivations_apply {R : Type*} [CommRing R]
    (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R))
    (X : InfoGeometry.Algebra.ZornVectorMatrix R) :
    ((zornVectorMatrixDerivationEquivDerivations R D :
      NonAssocDerivation.derivations R (InfoGeometry.Algebra.ZornVectorMatrix R)) :
        Module.End R (InfoGeometry.Algebra.ZornVectorMatrix R)) X = D X :=
  rfl

theorem zornVectorMatrixDerivationEquivDerivations_zero {R : Type*} [CommRing R] :
    zornVectorMatrixDerivationEquivDerivations R
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation.zero = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

theorem zornVectorMatrixDerivationEquivDerivations_add {R : Type*} [CommRing R]
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R)) :
    zornVectorMatrixDerivationEquivDerivations R
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add D E) =
      zornVectorMatrixDerivationEquivDerivations R D +
        zornVectorMatrixDerivationEquivDerivations R E := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

theorem zornVectorMatrixDerivationEquivDerivations_neg {R : Type*} [CommRing R]
    (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R)) :
    zornVectorMatrixDerivationEquivDerivations R
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.neg D) =
      -(zornVectorMatrixDerivationEquivDerivations R D) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

theorem zornVectorMatrixDerivationEquivDerivations_smul {R : Type*} [CommRing R]
    (r : R) (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R)) :
    zornVectorMatrixDerivationEquivDerivations R
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul r D) =
      r • zornVectorMatrixDerivationEquivDerivations R D := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

theorem zornVectorMatrixDerivationEquivDerivations_bracket {R : Type*} [CommRing R]
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := R)) :
    zornVectorMatrixDerivationEquivDerivations R
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E) =
      ⁅zornVectorMatrixDerivationEquivDerivations R D,
        zornVectorMatrixDerivationEquivDerivations R E⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

/-- Canonical `DerivationLieLane` for `ZornVectorMatrix R`. -/
def zornVectorMatrixDerivationLieLane (R : Type*) [CommRing R] :
    DerivationLieLane R (InfoGeometry.Algebra.ZornVectorMatrix R) :=
  fullDerivationLieLane R (InfoGeometry.Algebra.ZornVectorMatrix R)

/-- F8.4 Onsager attachment for `ZornVectorMatrix ℝ`. -/
def zornVectorMatrixOnsagerSystem
    (S : OnsagerCasimirSystem (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
    (a : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    OnsagerCasimirSystem (zornVectorMatrixDerivationLieLane ℝ).L :=
  inducedDerivationLaneOnsagerSystem S (zornVectorMatrixDerivationLieLane ℝ) a

theorem zornVectorMatrix_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing (zornVectorMatrixDerivationLieLane ℝ).L
      (InfoGeometry.Algebra.ZornVectorMatrix ℝ) n)
    (ω η : DerivationOperatorForm
      (zornVectorMatrixDerivationLieLane ℝ) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (zornVectorMatrixDerivationLieLane ℝ) PP ω η

/-- Equivalence between `G2ToBraidChain.G2Derivation` and `canonicalZornDerivations`. -/
def g2ToBraidDerivationEquivCanonicalZorn :
    InfoGeometry.Canonical.G2ToBraidChain.G2Derivation ≃ canonicalZornDerivations where
  toFun D := ⟨D.toLinearMap, D.leibniz⟩
  invFun D := ⟨D.1, D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

/-- Equivalence between `BaezG2SplitOctonion.SplitCayleyG2Derivation` and `canonicalZornDerivations`. -/
def splitCayleyG2DerivationEquivCanonicalZorn :
    InfoGeometry.Lie.BaezG2SplitOctonion.SplitCayleyG2Derivation ≃ canonicalZornDerivations where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨D.1, D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

/-- Equivalence between `RealSplitOctonionDerivation.SplitCayleyLinearDerivation` and `canonicalZornDerivations`. -/
def splitCayleyLinearDerivationEquivCanonicalZorn :
    InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayleyLinearDerivation ≃
      canonicalZornDerivations where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨D.1, D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

theorem canonicalZornDerivation_isLeibniz (D : canonicalZornDerivations) :
    NonAssocDerivation.IsLeibniz ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) D.1 :=
  D.property

theorem g2ToBraidDerivation_isLeibniz
    (D : InfoGeometry.Canonical.G2ToBraidChain.G2Derivation) :
    NonAssocDerivation.IsLeibniz ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) D.toLinearMap :=
  D.leibniz

theorem splitCayleyG2Derivation_isLeibniz
    (D : InfoGeometry.Lie.BaezG2SplitOctonion.SplitCayleyG2Derivation) :
    NonAssocDerivation.IsLeibniz ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) D.1 :=
  D.property

theorem splitCayleyLinearDerivation_isLeibniz
    (D : InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayleyLinearDerivation) :
    NonAssocDerivation.IsLeibniz ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) D.1 :=
  D.property

theorem splitCayleyDerivation_isLeibniz
    (D : InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayleyDerivation) :
    NonAssocDerivation.IsLeibniz ℤ (InfoGeometry.Canonical.ZornMatrix ℝ)
      (addHomToIntEnd D.toAddHom) :=
  D.leibniz'

/-- Lie-algebra embedding of `canonicalZornDerivations` into `NonAssocDerivation.derivations ℤ (ZornMatrix ℝ)`. -/
def canonicalZornDerivationsToIntDerivations :
    canonicalZornDerivations →ₗ⁅ℤ⁆
      NonAssocDerivation.derivations ℤ (InfoGeometry.Canonical.ZornMatrix ℝ) where
  toFun D := ⟨(D.1 : Module.End ℝ _).restrictScalars ℤ, D.property⟩
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl
  map_smul' n D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp
  map_lie' {D E} := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl

theorem canonicalZornDerivationsToIntDerivations_injective :
    Function.Injective canonicalZornDerivationsToIntDerivations := by
  intro D E h
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  exact congrArg (fun f : NonAssocDerivation.derivations ℤ (InfoGeometry.Canonical.ZornMatrix ℝ) =>
    (f : Module.End ℤ (InfoGeometry.Canonical.ZornMatrix ℝ)) X) h

/-- Equivalence between `RealSplitOctonionDerivation.SplitCayleyDerivation` and
`NonAssocDerivation.derivations ℤ (ZornMatrix ℝ)`. -/
def splitCayleyDerivationEquivIntDerivations :
    InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayleyDerivation ≃
      NonAssocDerivation.derivations ℤ (InfoGeometry.Canonical.ZornMatrix ℝ) where
  toFun D := ⟨addHomToIntEnd D.toAddHom, D.leibniz'⟩
  invFun D := ⟨(D : Module.End ℤ (InfoGeometry.Canonical.ZornMatrix ℝ)).toAddMonoidHom, D.property⟩
  left_inv D := by
    cases D
    rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl

theorem splitCayleyDerivationEquivIntDerivations_add
    (D E : InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayleyDerivation) :
    splitCayleyDerivationEquivIntDerivations
        ⟨D.toAddHom + E.toAddHom, fun X Y => by
          simp only [AddMonoidHom.add_apply]
          rw [D.leibniz', E.leibniz', add_mul, mul_add]
          abel⟩ =
      splitCayleyDerivationEquivIntDerivations D + splitCayleyDerivationEquivIntDerivations E := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

/-- Transport `canonicalZornDerivations` to `NonAssocDerivation.derivations ℝ (ZornVectorMatrix ℝ)`
along `vectorCanonicalLieEquiv` and `zornVectorMatrixDerivationEquivDerivations`. -/
def canonicalZornDerivationsEquivVectorDerivations :
    canonicalZornDerivations ≃
      NonAssocDerivation.derivations ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
  vectorCanonicalLinearEquiv.symm.toEquiv.trans
    (zornVectorMatrixDerivationEquivDerivations ℝ)

theorem canonicalZornDerivationsEquivVectorDerivations_lie
    (D E : canonicalZornDerivations) :
    canonicalZornDerivationsEquivVectorDerivations ⁅D, E⁆ =
      ⁅canonicalZornDerivationsEquivVectorDerivations D,
        canonicalZornDerivationsEquivVectorDerivations E⁆ := by
  dsimp [canonicalZornDerivationsEquivVectorDerivations]
  have hsymm : vectorCanonicalLinearEquiv.symm ⁅D, E⁆ =
      InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket
        (vectorCanonicalLinearEquiv.symm D) (vectorCanonicalLinearEquiv.symm E) := by
    apply vectorCanonicalLieEquiv.injective
    have h1 : vectorCanonicalLieEquiv (vectorCanonicalLieEquiv.symm ⁅D, E⁆) = ⁅D, E⁆ :=
      vectorCanonicalLieEquiv.apply_symm_apply ⁅D, E⁆
    have h2 : vectorCanonicalLieEquiv
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket
          (vectorCanonicalLinearEquiv.symm D) (vectorCanonicalLinearEquiv.symm E)) =
        ⁅vectorCanonicalLieEquiv (vectorCanonicalLieEquiv.symm D),
          vectorCanonicalLieEquiv (vectorCanonicalLieEquiv.symm E)⁆ :=
      vectorCanonicalLieEquiv.map_lie _ _
    rw [vectorCanonicalLieEquiv.apply_symm_apply, vectorCanonicalLieEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  rw [hsymm]
  exact zornVectorMatrixDerivationEquivDerivations_bracket _ _

/-- Equivalence transporting `G2ToBraidChain.G2Derivation` into `NonAssocDerivation.derivations ℝ (ZornVectorMatrix ℝ)`. -/
def g2ToBraidDerivationEquivVectorDerivations :
    InfoGeometry.Canonical.G2ToBraidChain.G2Derivation ≃
      NonAssocDerivation.derivations ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
  g2ToBraidDerivationEquivCanonicalZorn.trans canonicalZornDerivationsEquivVectorDerivations

/-- Equivalence transporting `BaezG2SplitOctonion.SplitCayleyG2Derivation` into `NonAssocDerivation.derivations ℝ (ZornVectorMatrix ℝ)`. -/
def splitCayleyG2DerivationEquivVectorDerivations :
    InfoGeometry.Lie.BaezG2SplitOctonion.SplitCayleyG2Derivation ≃
      NonAssocDerivation.derivations ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
  splitCayleyG2DerivationEquivCanonicalZorn.trans canonicalZornDerivationsEquivVectorDerivations

/-- Dedicated newtype wrapper around `InfoGeometry.Canonical.ZornMatrix ℝ` that owns
`IsScalarTower ℝ` and `SMulCommClass ℝ` without adding global instances on `ZornMatrix ℝ`. -/
@[ext]
structure ZornMatrixCarrier where
  val : InfoGeometry.Canonical.ZornMatrix ℝ

/-- Coordinate equivalence between `ZornMatrixCarrier` and `ZornMatrix ℝ`. -/
def zornMatrixCarrierEquiv : ZornMatrixCarrier ≃ InfoGeometry.Canonical.ZornMatrix ℝ where
  toFun := ZornMatrixCarrier.val
  invFun := ZornMatrixCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupZornMatrixCarrier : AddCommGroup ZornMatrixCarrier :=
  Equiv.addCommGroup zornMatrixCarrierEquiv

/-- Additive equivalence `ZornMatrixCarrier ≃+ ZornMatrix ℝ`. -/
def zornMatrixCarrierAddEquiv : ZornMatrixCarrier ≃+ InfoGeometry.Canonical.ZornMatrix ℝ where
  toEquiv := zornMatrixCarrierEquiv
  map_add' _ _ := rfl

instance instModuleZornMatrixCarrier : Module ℝ ZornMatrixCarrier :=
  AddEquiv.module ℝ zornMatrixCarrierAddEquiv

instance instMulZornMatrixCarrier : Mul ZornMatrixCarrier where
  mul x y := ⟨x.val * y.val⟩

instance instNonUnitalNonAssocRingZornMatrixCarrier : NonUnitalNonAssocRing ZornMatrixCarrier where
  zero_mul x := by
    apply ZornMatrixCarrier.ext
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul x.val
  mul_zero x := by
    apply ZornMatrixCarrier.ext
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero x.val
  left_distrib x y z := by
    apply ZornMatrixCarrier.ext
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add x.val y.val z.val
  right_distrib x y z := by
    apply ZornMatrixCarrier.ext
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul x.val y.val z.val

instance instIsScalarTowerZornMatrixCarrier :
    IsScalarTower ℝ ZornMatrixCarrier ZornMatrixCarrier where
  smul_assoc r x y := by
    apply ZornMatrixCarrier.ext
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r x.val y.val

instance instSMulCommClassZornMatrixCarrier :
    SMulCommClass ℝ ZornMatrixCarrier ZornMatrixCarrier where
  smul_comm r x y := by
    apply ZornMatrixCarrier.ext
    exact (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul r x.val y.val).symm

/-- Lie algebra isomorphism `canonicalZornDerivations ≃ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ ZornMatrixCarrier`. -/
def canonicalZornDerivationsEquivCarrier :
    canonicalZornDerivations ≃ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ ZornMatrixCarrier where
  toFun D :=
    ⟨{ toFun := fun x => ⟨D.1 x.val⟩
       map_add' := fun x y => by apply ZornMatrixCarrier.ext; exact D.1.map_add x.val y.val
       map_smul' := fun r x => by apply ZornMatrixCarrier.ext; exact D.1.map_smul r x.val },
     fun x y => by apply ZornMatrixCarrier.ext; exact D.property x.val y.val⟩
  invFun D :=
    ⟨{ toFun := fun x => ((D : Module.End ℝ ZornMatrixCarrier) ⟨x⟩).val
       map_add' := fun x y =>
         congrArg ZornMatrixCarrier.val ((D : Module.End ℝ ZornMatrixCarrier).map_add ⟨x⟩ ⟨y⟩)
       map_smul' := fun r x =>
         congrArg ZornMatrixCarrier.val ((D : Module.End ℝ ZornMatrixCarrier).map_smul r ⟨x⟩) },
     fun x y => congrArg ZornMatrixCarrier.val (D.property ⟨x⟩ ⟨y⟩)⟩
  left_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; cases x; rfl
  map_add' D E := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_smul' r D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_lie' {D E} := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

/-- Faithful `DerivationLieLane ℝ ZornMatrixCarrier`. -/
def zornMatrixCarrierLieLane : DerivationLieLane ℝ ZornMatrixCarrier :=
  fullDerivationLieLane ℝ ZornMatrixCarrier

/-- F8.4 Onsager attachments for canonical `ZornMatrix ℝ` (`LieActionLane`),
`ZornMatrixCarrier` (`DerivationLieLane`), and `EndCZ` (`canonicalZornOperatorDerivationLane`). -/
def canonicalZornActionOnsagerSystem
    (S : OnsagerCasimirSystem (InfoGeometry.Canonical.ZornMatrix ℝ))
    (a : InfoGeometry.Canonical.ZornMatrix ℝ) :
    OnsagerCasimirSystem canonicalZornDerivationLane.L :=
  inducedActionLaneOnsagerSystem S canonicalZornDerivationLane a

theorem canonicalZornAction_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing canonicalZornDerivationLane.L
      (InfoGeometry.Canonical.ZornMatrix ℝ) n)
    (ω η : ActionOperatorForm canonicalZornDerivationLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_actionForm_reciprocity_module canonicalZornDerivationLane PP ω η

def zornMatrixCarrierOnsagerSystem
    (S : OnsagerCasimirSystem ZornMatrixCarrier) (a : ZornMatrixCarrier) :
    OnsagerCasimirSystem zornMatrixCarrierLieLane.L :=
  inducedDerivationLaneOnsagerSystem S zornMatrixCarrierLieLane a

theorem zornMatrixCarrier_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing zornMatrixCarrierLieLane.L ZornMatrixCarrier n)
    (ω η : DerivationOperatorForm zornMatrixCarrierLieLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity zornMatrixCarrierLieLane PP ω η

def canonicalZornOperatorOnsagerSystem
    (S : OnsagerCasimirSystem InfoGeometry.Lie.CanonicalZornOperatorDerivationLane.EndCZ)
    (a : InfoGeometry.Lie.CanonicalZornOperatorDerivationLane.EndCZ) :
    OnsagerCasimirSystem canonicalZornOperatorDerivationLane.L :=
  inducedDerivationLaneOnsagerSystem S canonicalZornOperatorDerivationLane a

theorem canonicalZornOperator_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing canonicalZornOperatorDerivationLane.L
      InfoGeometry.Lie.CanonicalZornOperatorDerivationLane.EndCZ n)
    (ω η : DerivationOperatorForm
      canonicalZornOperatorDerivationLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity canonicalZornOperatorDerivationLane PP ω η

end ZornAndSplitCayleyLanes

/- Optional strictly scoped scalar instances on `ZornMatrix ℝ`, kept unopened at top level
so no global typeclass diamond is ever introduced. -/
namespace ZornMatrixScalarInstances

scoped instance instIsScalarTowerZornMatrixReal :
    IsScalarTower ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)
      (InfoGeometry.Canonical.ZornMatrix ℝ) where
  smul_assoc := InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul

scoped instance instSMulCommClassZornMatrixReal :
    SMulCommClass ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)
      (InfoGeometry.Canonical.ZornMatrix ℝ) where
  smul_comm r X Y :=
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul r X Y).symm

end ZornMatrixScalarInstances

/-! ## Section 4: `G2H3ZornEntrywiseEmbedding` & `H3ZornF4Derivations` (F8.1) -/

section H3ZornLanes

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- `H3ZornJordanDerivation` coincides with `NonAssocDerivation.IsLeibniz ℝ (H3Zorn ℝ)`. -/
theorem h3ZornJordanDerivation_iff_isLeibniz (D : Module.End ℝ (H3Zorn ℝ)) :
    H3ZornJordanDerivation D ↔ NonAssocDerivation.IsLeibniz ℝ (H3Zorn ℝ) D :=
  Iff.rfl

/-- Lie algebra equivalence `H3ZornF4Derivations ≃ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ (H3Zorn ℝ)`
reusing the existing global `H3Zorn ℝ` Jordan/scalar instances with zero duplicates. -/
def h3ZornF4DerivationsEquivDerivations :
    H3ZornF4Derivations ≃ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ (H3Zorn ℝ) where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨D.1, D.2⟩
  left_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

/-- `LieActionLane ℝ (H3Zorn ℝ)` for `G2H3ZornEntrywiseEmbedding.G2Derivation`. -/
def g2EntrywiseActionLane : LieActionLane ℝ (H3Zorn ℝ) where
  L := InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.G2Derivation
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.g2EntrywiseLieHom

/-- Faithful Lie homomorphism from `entrywiseCompatibleG2` into `NonAssocDerivation.derivations ℝ (H3Zorn ℝ)`. -/
def compatibleG2ToH3ZornDerivationLieHom :
    InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.entrywiseCompatibleG2 →ₗ⁅ℝ⁆
      NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
  h3ZornF4DerivationsEquivDerivations.toLieHom.comp
    InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.compatibleG2ToF4LieHom

theorem compatibleG2ToH3ZornDerivationLieHom_injective :
    Function.Injective compatibleG2ToH3ZornDerivationLieHom :=
  h3ZornF4DerivationsEquivDerivations.injective.comp
    InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.compatibleG2ToF4LieHom_injective

/-- Faithful `DerivationLieLane ℝ (H3Zorn ℝ)` on `entrywiseCompatibleG2`. -/
def compatibleG2H3ZornDerivationLane : DerivationLieLane ℝ (H3Zorn ℝ) where
  L := InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding.entrywiseCompatibleG2
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := compatibleG2ToH3ZornDerivationLieHom
  faithful := compatibleG2ToH3ZornDerivationLieHom_injective

/-- Faithful `DerivationLieLane ℝ (H3Zorn ℝ)` on `H3ZornF4Derivations`. -/
def h3ZornF4DerivationLane : DerivationLieLane ℝ (H3Zorn ℝ) where
  L := H3ZornF4Derivations
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := h3ZornF4DerivationsEquivDerivations.toLieHom
  faithful := h3ZornF4DerivationsEquivDerivations.injective

/-- F8.4 Onsager attachments for `G2 -> H3Zorn` and `H3ZornF4Derivations`. -/
def g2EntrywiseOnsagerSystem
    (S : OnsagerCasimirSystem (H3Zorn ℝ)) (a : H3Zorn ℝ) :
    OnsagerCasimirSystem g2EntrywiseActionLane.L :=
  inducedActionLaneOnsagerSystem S g2EntrywiseActionLane a

theorem g2Entrywise_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing g2EntrywiseActionLane.L (H3Zorn ℝ) n)
    (ω η : ActionOperatorForm g2EntrywiseActionLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_actionForm_reciprocity_module g2EntrywiseActionLane PP ω η

def compatibleG2H3ZornOnsagerSystem
    (S : OnsagerCasimirSystem (H3Zorn ℝ)) (a : H3Zorn ℝ) :
    OnsagerCasimirSystem compatibleG2H3ZornDerivationLane.L :=
  inducedDerivationLaneOnsagerSystem S compatibleG2H3ZornDerivationLane a

theorem compatibleG2H3Zorn_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing compatibleG2H3ZornDerivationLane.L (H3Zorn ℝ) n)
    (ω η : DerivationOperatorForm
      compatibleG2H3ZornDerivationLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity compatibleG2H3ZornDerivationLane PP ω η

def h3ZornF4OnsagerSystem
    (S : OnsagerCasimirSystem (H3Zorn ℝ)) (a : H3Zorn ℝ) :
    OnsagerCasimirSystem h3ZornF4DerivationLane.L :=
  inducedDerivationLaneOnsagerSystem S h3ZornF4DerivationLane a

theorem h3ZornF4_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing h3ZornF4DerivationLane.L (H3Zorn ℝ) n)
    (ω η : DerivationOperatorForm h3ZornF4DerivationLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity h3ZornF4DerivationLane PP ω η

end H3ZornLanes

/-! ## Section 5: `SplitOctonionDerivationAutomorphism.SplitOctonionDerivation` (`SplitOctonionZornCarrier`, F8.1) -/

section SplitOctonionZornLane

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- Dedicated newtype wrapper around `InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion`
owning `NonUnitalNonAssocRing`, `IsScalarTower ℝ`, and `SMulCommClass ℝ`. -/
@[ext]
structure SplitOctonionZornCarrier where
  val : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion

private def splitOctonionZornCarrierEquiv :
    SplitOctonionZornCarrier ≃ InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion where
  toFun := SplitOctonionZornCarrier.val
  invFun := SplitOctonionZornCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupSplitOctonionZornCarrier :
    AddCommGroup SplitOctonionZornCarrier :=
  Equiv.addCommGroup splitOctonionZornCarrierEquiv

private def splitOctonionZornCarrierAddEquiv :
    SplitOctonionZornCarrier ≃+ InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion where
  toEquiv := splitOctonionZornCarrierEquiv
  map_add' _ _ := rfl

instance instModuleSplitOctonionZornCarrier : Module ℝ SplitOctonionZornCarrier :=
  AddEquiv.module ℝ splitOctonionZornCarrierAddEquiv

instance instMulSplitOctonionZornCarrier : Mul SplitOctonionZornCarrier where
  mul X Y := ⟨X.val * Y.val⟩

private theorem splitOctonionZornCarrier_ext_coords {X Y : SplitOctonionZornCarrier}
    (ha : X.val.a = Y.val.a)
    (hux : X.val.u.x = Y.val.u.x) (huy : X.val.u.y = Y.val.u.y) (huz : X.val.u.z = Y.val.u.z)
    (hvx : X.val.v.x = Y.val.v.x) (hvy : X.val.v.y = Y.val.v.y) (hvz : X.val.v.z = Y.val.v.z)
    (hd : X.val.d = Y.val.d) : X = Y := by
  apply SplitOctonionZornCarrier.ext
  apply InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.ext ha
  · exact InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext hux huy huz
  · exact InfoGeometry.Algebra.SplitOctonionZorn.Vector3.ext hvx hvy hvz
  · exact hd

private theorem splitOct_zero_a :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).a = 0 := rfl
private theorem splitOct_zero_ux :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).u.x = 0 := rfl
private theorem splitOct_zero_uy :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).u.y = 0 := rfl
private theorem splitOct_zero_uz :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).u.z = 0 := rfl
private theorem splitOct_zero_vx :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).v.x = 0 := rfl
private theorem splitOct_zero_vy :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).v.y = 0 := rfl
private theorem splitOct_zero_vz :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).v.z = 0 := rfl
private theorem splitOct_zero_d :
    (0 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion).d = 0 := rfl

private theorem splitOct_add_a (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).a = X.a + Y.a := rfl
private theorem splitOct_add_ux (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).u.x = X.u.x + Y.u.x := rfl
private theorem splitOct_add_uy (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).u.y = X.u.y + Y.u.y := rfl
private theorem splitOct_add_uz (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).u.z = X.u.z + Y.u.z := rfl
private theorem splitOct_add_vx (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).v.x = X.v.x + Y.v.x := rfl
private theorem splitOct_add_vy (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).v.y = X.v.y + Y.v.y := rfl
private theorem splitOct_add_vz (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).v.z = X.v.z + Y.v.z := rfl
private theorem splitOct_add_d (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X + Y).d = X.d + Y.d := rfl

private theorem splitOct_smul_a (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).a = r * X.a := rfl
private theorem splitOct_smul_ux (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).u.x = r * X.u.x := rfl
private theorem splitOct_smul_uy (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).u.y = r * X.u.y := rfl
private theorem splitOct_smul_uz (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).u.z = r * X.u.z := rfl
private theorem splitOct_smul_vx (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).v.x = r * X.v.x := rfl
private theorem splitOct_smul_vy (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).v.y = r * X.v.y := rfl
private theorem splitOct_smul_vz (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).v.z = r * X.v.z := rfl
private theorem splitOct_smul_d (r : ℝ) (X : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (r • X).d = r * X.d := rfl

private theorem splitOct_mul_a (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).a = X.a * Y.a + (X.u.x * Y.v.x + X.u.y * Y.v.y + X.u.z * Y.v.z) := rfl
private theorem splitOct_mul_ux (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).u.x = (X.a * Y.u.x + Y.d * X.u.x) - (X.v.y * Y.v.z - X.v.z * Y.v.y) := rfl
private theorem splitOct_mul_uy (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).u.y = (X.a * Y.u.y + Y.d * X.u.y) - (X.v.z * Y.v.x - X.v.x * Y.v.z) := rfl
private theorem splitOct_mul_uz (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).u.z = (X.a * Y.u.z + Y.d * X.u.z) - (X.v.x * Y.v.y - X.v.y * Y.v.x) := rfl
private theorem splitOct_mul_vx (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).v.x = (Y.a * X.v.x + X.d * Y.v.x) + (X.u.y * Y.u.z - X.u.z * Y.u.y) := rfl
private theorem splitOct_mul_vy (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).v.y = (Y.a * X.v.y + X.d * Y.v.y) + (X.u.z * Y.u.x - X.u.x * Y.u.z) := rfl
private theorem splitOct_mul_vz (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).v.z = (Y.a * X.v.z + X.d * Y.v.z) + (X.u.x * Y.u.y - X.u.y * Y.u.x) := rfl
private theorem splitOct_mul_d (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    (X * Y).d = X.d * Y.d + (X.v.x * Y.u.x + X.v.y * Y.u.y + X.v.z * Y.u.z) := rfl

private theorem splitOctCarrier_mul_val (X Y : SplitOctonionZornCarrier) :
    (X * Y).val = X.val * Y.val := rfl
private theorem splitOctCarrier_add_val (X Y : SplitOctonionZornCarrier) :
    (X + Y).val = X.val + Y.val := rfl
private theorem splitOctCarrier_zero_val :
    (0 : SplitOctonionZornCarrier).val = 0 := rfl
private theorem splitOctCarrier_smul_val (r : ℝ) (X : SplitOctonionZornCarrier) :
    (r • X).val = r • X.val := rfl

instance instNonUnitalNonAssocRingSplitOctonionZornCarrier :
    NonUnitalNonAssocRing SplitOctonionZornCarrier where
  zero_mul X := by
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_zero_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_zero_a, splitOct_zero_ux, splitOct_zero_uy, splitOct_zero_uz,
          splitOct_zero_vx, splitOct_zero_vy, splitOct_zero_vz, splitOct_zero_d]
        ring
  mul_zero X := by
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_zero_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_zero_a, splitOct_zero_ux, splitOct_zero_uy, splitOct_zero_uz,
          splitOct_zero_vx, splitOct_zero_vy, splitOct_zero_vz, splitOct_zero_d]
        ring
  left_distrib X Y Z := by
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_add_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_add_a, splitOct_add_ux, splitOct_add_uy, splitOct_add_uz,
          splitOct_add_vx, splitOct_add_vy, splitOct_add_vz, splitOct_add_d]
        ring
  right_distrib X Y Z := by
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_add_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_add_a, splitOct_add_ux, splitOct_add_uy, splitOct_add_uz,
          splitOct_add_vx, splitOct_add_vy, splitOct_add_vz, splitOct_add_d]
        ring

instance instIsScalarTowerSplitOctonionZornCarrier :
    IsScalarTower ℝ SplitOctonionZornCarrier SplitOctonionZornCarrier where
  smul_assoc r X Y := by
    change (r • X) * Y = r • (X * Y)
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_smul_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_smul_a, splitOct_smul_ux, splitOct_smul_uy, splitOct_smul_uz,
          splitOct_smul_vx, splitOct_smul_vy, splitOct_smul_vz, splitOct_smul_d]
        ring

instance instSMulCommClassSplitOctonionZornCarrier :
    SMulCommClass ℝ SplitOctonionZornCarrier SplitOctonionZornCarrier where
  smul_comm r X Y := by
    change r • (X * Y) = X * (r • Y)
    apply splitOctonionZornCarrier_ext_coords <;>
      · simp only [splitOctCarrier_mul_val, splitOctCarrier_smul_val,
          splitOct_mul_a, splitOct_mul_ux, splitOct_mul_uy, splitOct_mul_uz,
          splitOct_mul_vx, splitOct_mul_vy, splitOct_mul_vz, splitOct_mul_d,
          splitOct_smul_a, splitOct_smul_ux, splitOct_smul_uy, splitOct_smul_uz,
          splitOct_smul_vx, splitOct_smul_vy, splitOct_smul_vz, splitOct_smul_d]
        ring

/-- Equivalence between `SplitOctonionDerivationAutomorphism.SplitOctonionDerivation` and
`NonAssocDerivation.derivations ℝ SplitOctonionZornCarrier`. -/
def splitOctonionDerivationEquivDerivations :
    InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation ≃
      NonAssocDerivation.derivations ℝ SplitOctonionZornCarrier where
  toFun D :=
    ⟨{ toFun := fun X => ⟨D.toLinearMap X.val⟩
       map_add' := fun X Y => by
         apply SplitOctonionZornCarrier.ext
         exact D.toLinearMap.map_add X.val Y.val
       map_smul' := fun r X => by
         apply SplitOctonionZornCarrier.ext
         exact D.toLinearMap.map_smul r X.val },
     fun X Y => by
       apply SplitOctonionZornCarrier.ext
       exact D.leibniz X.val Y.val⟩
  invFun D :=
    { toLinearMap :=
        { toFun := fun X => ((D : Module.End ℝ SplitOctonionZornCarrier) ⟨X⟩).val
          map_add' := fun X Y =>
            congrArg SplitOctonionZornCarrier.val
              ((D : Module.End ℝ SplitOctonionZornCarrier).map_add ⟨X⟩ ⟨Y⟩)
          map_smul' := fun r X =>
            congrArg SplitOctonionZornCarrier.val
              ((D : Module.End ℝ SplitOctonionZornCarrier).map_smul r ⟨X⟩) }
      leibniz := fun X Y => congrArg SplitOctonionZornCarrier.val (D.property ⟨X⟩ ⟨Y⟩) }
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro X; cases X; rfl

theorem splitOctonionDerivationEquivDerivations_zero :
    splitOctonionDerivationEquivDerivations
        ⟨0, fun X Y => by
          simp only [LinearMap.zero_apply]
          change (0 : SplitOctonionZornCarrier).val =
            ((0 : SplitOctonionZornCarrier) * ⟨Y⟩ + ⟨X⟩ * 0).val
          rw [zero_mul, mul_zero, add_zero]⟩ = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem splitOctonionDerivationEquivDerivations_add
    (D₁ D₂ : InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation) :
    splitOctonionDerivationEquivDerivations
        ⟨D₁.toLinearMap + D₂.toLinearMap, fun X Y => by
          simp only [LinearMap.add_apply]
          rw [D₁.leibniz X Y, D₂.leibniz X Y]
          change (⟨D₁.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D₁.toLinearMap Y⟩ +
              (⟨D₂.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D₂.toLinearMap Y⟩ : SplitOctonionZornCarrier)).val =
            ((⟨D₁.toLinearMap X⟩ + ⟨D₂.toLinearMap X⟩ : SplitOctonionZornCarrier) * ⟨Y⟩ +
              ⟨X⟩ * (⟨D₁.toLinearMap Y⟩ + ⟨D₂.toLinearMap Y⟩ : SplitOctonionZornCarrier)).val
          rw [add_mul, mul_add]
          abel_nf⟩ =
      splitOctonionDerivationEquivDerivations D₁ +
        splitOctonionDerivationEquivDerivations D₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem splitOctonionDerivationEquivDerivations_smul (r : ℝ)
    (D : InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation) :
    splitOctonionDerivationEquivDerivations
        ⟨r • D.toLinearMap, fun X Y => by
          simp only [LinearMap.smul_apply]
          rw [D.leibniz X Y]
          change (r • (⟨D.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D.toLinearMap Y⟩ : SplitOctonionZornCarrier)).val =
            ((r • ⟨D.toLinearMap X⟩ : SplitOctonionZornCarrier) * ⟨Y⟩ +
              ⟨X⟩ * (r • ⟨D.toLinearMap Y⟩ : SplitOctonionZornCarrier)).val
          rw [smul_add, smul_mul_assoc, mul_smul_comm]⟩ =
      r • splitOctonionDerivationEquivDerivations D := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem splitOctonionDerivationEquivDerivations_bracket
    (D₁ D₂ : InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation) :
    splitOctonionDerivationEquivDerivations
        (InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.SplitOctonionDerivation.bracket
          D₁ D₂) =
      ⁅splitOctonionDerivationEquivDerivations D₁,
        splitOctonionDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

/-- Faithful `DerivationLieLane ℝ SplitOctonionZornCarrier`. -/
def splitOctonionZornDerivationLieLane :
    DerivationLieLane ℝ SplitOctonionZornCarrier :=
  fullDerivationLieLane ℝ SplitOctonionZornCarrier

/-- Direct `LieActionLane ℝ SplitOctonionZorn.SplitOctonion` without adding instances on `SplitOctonion`. -/
def splitOctonionZornActionLane :
    LieActionLane ℝ InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion where
  L := NonAssocDerivation.derivations ℝ SplitOctonionZornCarrier
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act :=
    { toFun := fun D =>
        { toFun := fun X => ((D : Module.End ℝ SplitOctonionZornCarrier) ⟨X⟩).val
          map_add' := fun X Y =>
            congrArg SplitOctonionZornCarrier.val
              ((D : Module.End ℝ SplitOctonionZornCarrier).map_add ⟨X⟩ ⟨Y⟩)
          map_smul' := fun r X =>
            congrArg SplitOctonionZornCarrier.val
              ((D : Module.End ℝ SplitOctonionZornCarrier).map_smul r ⟨X⟩) }
      map_add' := fun D E => by apply LinearMap.ext; intro X; rfl
      map_smul' := fun r D => by apply LinearMap.ext; intro X; rfl
      map_lie' := fun {D E} => by apply LinearMap.ext; intro X; rfl }

/-- F8.4 Onsager attachments on `SplitOctonionZornCarrier` and `SplitOctonionZorn.SplitOctonion`. -/
def splitOctonionZornOnsagerSystem
    (S : OnsagerCasimirSystem SplitOctonionZornCarrier) (a : SplitOctonionZornCarrier) :
    OnsagerCasimirSystem splitOctonionZornDerivationLieLane.L :=
  inducedDerivationLaneOnsagerSystem S splitOctonionZornDerivationLieLane a

theorem splitOctonionZorn_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing splitOctonionZornDerivationLieLane.L
      SplitOctonionZornCarrier n)
    (ω η : DerivationOperatorForm
      splitOctonionZornDerivationLieLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity splitOctonionZornDerivationLieLane PP ω η

def splitOctonionZornActionOnsagerSystem
    (S : OnsagerCasimirSystem InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion)
    (a : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) :
    OnsagerCasimirSystem splitOctonionZornActionLane.L :=
  inducedActionLaneOnsagerSystem S splitOctonionZornActionLane a

theorem splitOctonionZornAction_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing splitOctonionZornActionLane.L
      InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion n)
    (ω η : ActionOperatorForm splitOctonionZornActionLane n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_actionForm_reciprocity_module splitOctonionZornActionLane PP ω η

end SplitOctonionZornLane

/-! ## Section 6: `NoncommutativeZornBdGDerivations.ZornDerivation A` (`NCZornCarrier A`, F8.1) -/

section NCZornLane

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-- Dedicated newtype wrapper around `NCZorn A` owning `AddCommGroup` and `NonUnitalNonAssocRing`. -/
@[ext]
structure NCZornCarrier (A : Type*) where
  val : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn A

private def ncZornCarrierEquivCoord (A : Type*) :
    NCZornCarrier A ≃ (A × (Fin 3 → A) × (Fin 3 → A) × A) where
  toFun X := (X.val.a, X.val.u, X.val.v, X.val.b)
  invFun p := ⟨⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩⟩
  left_inv X := by rcases X with ⟨⟨a, u, v, b⟩⟩; rfl
  right_inv p := by rcases p with ⟨a, u, v, b⟩; rfl

instance instAddCommGroupNCZornCarrier (A : Type*) [Ring A] :
    AddCommGroup (NCZornCarrier A) :=
  Equiv.addCommGroup (ncZornCarrierEquivCoord A)

theorem ncZornCarrier_zero_val {A : Type*} [Ring A] :
    (0 : NCZornCarrier A).val = 0 :=
  rfl

@[simp]
theorem ncZornCarrier_add_val {A : Type*} [Ring A] (X Y : NCZornCarrier A) :
    (X + Y).val = InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd X.val Y.val :=
  rfl

instance instMulNCZornCarrier (A : Type*) [Ring A] : Mul (NCZornCarrier A) where
  mul X Y := ⟨X.val * Y.val⟩

private theorem ncZornCarrier_zero_a {A : Type*} [Ring A] :
    (0 : NCZornCarrier A).val.a = 0 := rfl
private theorem ncZornCarrier_zero_u {A : Type*} [Ring A] :
    (0 : NCZornCarrier A).val.u = 0 := rfl
private theorem ncZornCarrier_zero_v {A : Type*} [Ring A] :
    (0 : NCZornCarrier A).val.v = 0 := rfl
private theorem ncZornCarrier_zero_b {A : Type*} [Ring A] :
    (0 : NCZornCarrier A).val.b = 0 := rfl
private theorem ncZornCarrier_mul_a {A : Type*} [Ring A] (X Y : NCZornCarrier A) :
    (X * Y).val.a = X.val.a * Y.val.a +
      InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Y.val.v := rfl
private theorem ncZornCarrier_mul_u {A : Type*} [Ring A] (X Y : NCZornCarrier A) (i : Fin 3) :
    (X * Y).val.u i = X.val.a * Y.val.u i + X.val.u i * Y.val.b -
      InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Y.val.v i := rfl
private theorem ncZornCarrier_mul_v {A : Type*} [Ring A] (X Y : NCZornCarrier A) (i : Fin 3) :
    (X * Y).val.v i = X.val.v i * Y.val.a + X.val.b * Y.val.v i +
      InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Y.val.u i := rfl
private theorem ncZornCarrier_mul_b {A : Type*} [Ring A] (X Y : NCZornCarrier A) :
    (X * Y).val.b = X.val.b * Y.val.b +
      InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Y.val.u := rfl

instance instNonUnitalNonAssocRingNCZornCarrier (A : Type*) [Ring A] :
    NonUnitalNonAssocRing (NCZornCarrier A) where
  zero_mul X := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · simp [ncZornCarrier_mul_a, ncZornCarrier_zero_a, ncZornCarrier_zero_u,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
    · funext i
      fin_cases i <;>
        simp [ncZornCarrier_mul_u, ncZornCarrier_zero_a, ncZornCarrier_zero_u, ncZornCarrier_zero_v,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
    · funext i
      fin_cases i <;>
        simp [ncZornCarrier_mul_v, ncZornCarrier_zero_v, ncZornCarrier_zero_b, ncZornCarrier_zero_u,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
    · simp [ncZornCarrier_mul_b, ncZornCarrier_zero_b, ncZornCarrier_zero_v,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
  mul_zero X := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · simp [ncZornCarrier_mul_a, ncZornCarrier_zero_a, ncZornCarrier_zero_v,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
    · funext i
      fin_cases i <;>
        simp [ncZornCarrier_mul_u, ncZornCarrier_zero_u, ncZornCarrier_zero_b, ncZornCarrier_zero_v,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
    · funext i
      fin_cases i <;>
        simp [ncZornCarrier_mul_v, ncZornCarrier_zero_a, ncZornCarrier_zero_v, ncZornCarrier_zero_u,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
    · simp [ncZornCarrier_mul_b, ncZornCarrier_zero_b, ncZornCarrier_zero_u,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
  left_distrib X Y Z := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · change X.val.a * (Y.val.a + Z.val.a) +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u
            (fun i => Y.val.v i + Z.val.v i) =
        (X.val.a * Y.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Y.val.v) +
        (X.val.a * Z.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Z.val.v)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      noncomm_ring
    · funext i
      fin_cases i <;>
        · change X.val.a * (Y.val.u _ + Z.val.u _) + X.val.u _ * (Y.val.b + Z.val.b) -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v
                (fun k => Y.val.v k + Z.val.v k) _ =
            (X.val.a * Y.val.u _ + X.val.u _ * Y.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Y.val.v _) +
            (X.val.a * Z.val.u _ + X.val.u _ * Z.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Z.val.v _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          noncomm_ring
    · funext i
      fin_cases i <;>
        · change X.val.v _ * (Y.val.a + Z.val.a) + X.val.b * (Y.val.v _ + Z.val.v _) +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u
                (fun k => Y.val.u k + Z.val.u k) _ =
            (X.val.v _ * Y.val.a + X.val.b * Y.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Y.val.u _) +
            (X.val.v _ * Z.val.a + X.val.b * Z.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Z.val.u _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          noncomm_ring
    · change X.val.b * (Y.val.b + Z.val.b) +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v
            (fun i => Y.val.u i + Z.val.u i) =
        (X.val.b * Y.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Y.val.u) +
        (X.val.b * Z.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Z.val.u)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      noncomm_ring
  right_distrib X Y Z := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · change (X.val.a + Y.val.a) * Z.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC
            (fun i => X.val.u i + Y.val.u i) Z.val.v =
        (X.val.a * Z.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Z.val.v) +
        (Y.val.a * Z.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC Y.val.u Z.val.v)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      noncomm_ring
    · funext i
      fin_cases i <;>
        · change (X.val.a + Y.val.a) * Z.val.u _ + (X.val.u _ + Y.val.u _) * Z.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC
                (fun k => X.val.v k + Y.val.v k) Z.val.v _ =
            (X.val.a * Z.val.u _ + X.val.u _ * Z.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Z.val.v _) +
            (Y.val.a * Z.val.u _ + Y.val.u _ * Z.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC Y.val.v Z.val.v _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          noncomm_ring
    · funext i
      fin_cases i <;>
        · change (X.val.v _ + Y.val.v _) * Z.val.a + (X.val.b + Y.val.b) * Z.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC
                (fun k => X.val.u k + Y.val.u k) Z.val.u _ =
            (X.val.v _ * Z.val.a + X.val.b * Z.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Z.val.u _) +
            (Y.val.v _ * Z.val.a + Y.val.b * Z.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC Y.val.u Z.val.u _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          noncomm_ring
    · change (X.val.b + Y.val.b) * Z.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC
            (fun i => X.val.v i + Y.val.v i) Z.val.u =
        (X.val.b * Z.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Z.val.u) +
        (Y.val.b * Z.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC Y.val.v Z.val.u)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      noncomm_ring

/-- Equivalence between `NoncommutativeZornBdGDerivations.ZornDerivation A` and
`NonAssocDerivation.derivations ℤ (NCZornCarrier A)`. -/
def ncZornDerivationEquivIntDerivations (A : Type*) [Ring A] :
    InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ZornDerivation A ≃
      NonAssocDerivation.derivations ℤ (NCZornCarrier A) where
  toFun D :=
    let f : NCZornCarrier A →+ NCZornCarrier A :=
      AddMonoidHom.mk' (fun X => ⟨D.toFun X.val⟩) fun X Y => by
        apply NCZornCarrier.ext
        exact D.map_add X.val Y.val
    ⟨addHomToIntEnd f, fun X Y => by
      apply NCZornCarrier.ext
      exact D.leibniz X.val Y.val⟩
  invFun D :=
    { toFun := fun X => ((D : Module.End ℤ (NCZornCarrier A)) ⟨X⟩).val
      map_add := fun X Y =>
        congrArg NCZornCarrier.val
          ((D : Module.End ℤ (NCZornCarrier A)).map_add ⟨X⟩ ⟨Y⟩)
      leibniz := fun X Y =>
        congrArg NCZornCarrier.val (D.property ⟨X⟩ ⟨Y⟩) }
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro X; cases X; rfl

theorem ncZornDerivationEquivIntDerivations_add {A : Type*} [Ring A]
    (D₁ D₂ : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ZornDerivation A) :
    ncZornDerivationEquivIntDerivations A
        { toFun := fun X =>
            InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornAdd
              (D₁.toFun X) (D₂.toFun X)
          map_add := fun X Y => by
            rw [D₁.map_add, D₂.map_add]
            change ((⟨D₁.toFun X⟩ + ⟨D₁.toFun Y⟩ : NCZornCarrier A) +
                (⟨D₂.toFun X⟩ + ⟨D₂.toFun Y⟩)).val =
              ((⟨D₁.toFun X⟩ + ⟨D₂.toFun X⟩ : NCZornCarrier A) +
                (⟨D₁.toFun Y⟩ + ⟨D₂.toFun Y⟩)).val
            rw [add_add_add_comm]
          leibniz := fun X Y => by
            rw [D₁.leibniz, D₂.leibniz]
            change (⟨D₁.toFun X * Y⟩ + ⟨X * D₁.toFun Y⟩ +
                (⟨D₂.toFun X * Y⟩ + ⟨X * D₂.toFun Y⟩ : NCZornCarrier A)).val =
              ((⟨D₁.toFun X⟩ + ⟨D₂.toFun X⟩ : NCZornCarrier A) * ⟨Y⟩ +
                ⟨X⟩ * (⟨D₁.toFun Y⟩ + ⟨D₂.toFun Y⟩ : NCZornCarrier A)).val
            rw [add_mul, mul_add]
            simp only [show ∀ U V : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn A,
              (⟨U⟩ : NCZornCarrier A) * ⟨V⟩ = ⟨U * V⟩ from fun _ _ => rfl]
            abel_nf } =
      ncZornDerivationEquivIntDerivations A D₁ + ncZornDerivationEquivIntDerivations A D₂ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

/-- Faithful `DerivationLieLane ℤ (NCZornCarrier A)`. -/
def ncZornDerivationLieLane (A : Type*) [Ring A] :
    DerivationLieLane ℤ (NCZornCarrier A) :=
  fullDerivationLieLane ℤ (NCZornCarrier A)

section NCZornRealLinear

open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

private def ncZornCarrierAddEquivCoord (A : Type*) [Ring A] :
    NCZornCarrier A ≃+ (A × (Fin 3 → A) × (Fin 3 → A) × A) where
  toEquiv := ncZornCarrierEquivCoord A
  map_add' _ _ := rfl

/-- `ℝ`-module structure on `NCZornCarrier A` when `[Algebra ℝ A]`, avoiding any diamond
with `AddCommGroup.toIntModule`. -/
instance ncZornCarrierModule (A : Type*) [Ring A] [Algebra ℝ A] :
    Module ℝ (NCZornCarrier A) :=
  AddEquiv.module ℝ (ncZornCarrierAddEquivCoord A)

@[simp]
private theorem ncZornCarrier_smul_a {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (X : NCZornCarrier A) :
    (r • X).val.a = r • X.val.a := rfl

@[simp]
private theorem ncZornCarrier_smul_u {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (X : NCZornCarrier A) (i : Fin 3) :
    (r • X).val.u i = r • X.val.u i := rfl

@[simp]
private theorem ncZornCarrier_smul_v {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (X : NCZornCarrier A) (i : Fin 3) :
    (r • X).val.v i = r • X.val.v i := rfl

@[simp]
private theorem ncZornCarrier_smul_b {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (X : NCZornCarrier A) :
    (r • X).val.b = r • X.val.b := rfl

instance ncZornCarrierIsScalarTower (A : Type*) [Ring A] [Algebra ℝ A] :
    IsScalarTower ℝ (NCZornCarrier A) (NCZornCarrier A) where
  smul_assoc r X Y := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · change (r • X).val.a * Y.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC (r • X).val.u Y.val.v =
        r • (X.val.a * Y.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Y.val.v)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      simp only [smul_mul_assoc, smul_add]
    · funext i
      fin_cases i <;>
        · change (r • X).val.a * Y.val.u _ + (r • X).val.u _ * Y.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC (r • X).val.v Y.val.v _ =
            r • (X.val.a * Y.val.u _ + X.val.u _ * Y.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Y.val.v _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          simp only [smul_mul_assoc, smul_add, smul_sub]
    · funext i
      fin_cases i <;>
        · change (r • X).val.v _ * Y.val.a + (r • X).val.b * Y.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC (r • X).val.u Y.val.u _ =
            r • (X.val.v _ * Y.val.a + X.val.b * Y.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Y.val.u _)
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          simp only [smul_mul_assoc, smul_add, smul_sub]
    · change (r • X).val.b * Y.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC (r • X).val.v Y.val.u =
        r • (X.val.b * Y.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Y.val.u)
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      simp only [smul_mul_assoc, smul_add]

instance ncZornCarrierSMulCommClass (A : Type*) [Ring A] [Algebra ℝ A] :
    SMulCommClass ℝ (NCZornCarrier A) (NCZornCarrier A) where
  smul_comm r X Y := by
    apply NCZornCarrier.ext
    apply InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn.ext
    · change r • (X.val.a * Y.val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u Y.val.v) =
        X.val.a * (r • Y).val.a +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.u (r • Y).val.v
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      simp only [mul_smul_comm, smul_add]
    · funext i
      fin_cases i <;>
        · change r • (X.val.a * Y.val.u _ + X.val.u _ * Y.val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v Y.val.v _) =
            X.val.a * (r • Y).val.u _ + X.val.u _ * (r • Y).val.b -
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.v (r • Y).val.v _
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          simp only [mul_smul_comm, smul_add, smul_sub]
    · funext i
      fin_cases i <;>
        · change r • (X.val.v _ * Y.val.a + X.val.b * Y.val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u Y.val.u _) =
            X.val.v _ * (r • Y).val.a + X.val.b * (r • Y).val.v _ +
              InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC X.val.u (r • Y).val.u _
          dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC]
          simp only [mul_smul_comm, smul_add, smul_sub]
    · change r • (X.val.b * Y.val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v Y.val.u) =
        X.val.b * (r • Y).val.b +
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC X.val.v (r • Y).val.u
      dsimp [InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC]
      simp only [mul_smul_comm, smul_add]

/-- `ℝ`-linear refinement of `NoncommutativeZornBdGDerivations.ZornDerivation A`. -/
structure RealLinearNCZornDerivation (A : Type*) [Ring A] [Algebra ℝ A] extends
    InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ZornDerivation A where
  map_smul : ∀ (r : ℝ) (X : NCZornCarrier A),
    (⟨toFun (r • X).val⟩ : NCZornCarrier A) = r • (⟨toFun X.val⟩ : NCZornCarrier A)

/-- Equivalence between `ℝ`-linear `NCZorn` derivations and
`NonAssocDerivation.derivations ℝ (NCZornCarrier A)`. -/
def ncZornRealDerivationEquiv (A : Type*) [Ring A] [Algebra ℝ A] :
    RealLinearNCZornDerivation A ≃ NonAssocDerivation.derivations ℝ (NCZornCarrier A) where
  toFun D :=
    ⟨{ toFun := fun X => ⟨D.toFun X.val⟩
       map_add' := fun X Y => by
         apply NCZornCarrier.ext
         exact D.map_add X.val Y.val
       map_smul' := fun r X => D.map_smul r X },
     fun X Y => by
       apply NCZornCarrier.ext
       exact D.leibniz X.val Y.val⟩
  invFun D :=
    { toFun := fun X => ((D : Module.End ℝ (NCZornCarrier A)) ⟨X⟩).val
      map_add := fun X Y =>
        congrArg NCZornCarrier.val ((D : Module.End ℝ (NCZornCarrier A)).map_add ⟨X⟩ ⟨Y⟩)
      leibniz := fun X Y => congrArg NCZornCarrier.val (D.property ⟨X⟩ ⟨Y⟩)
      map_smul := fun r X => by
        apply NCZornCarrier.ext
        exact congrArg NCZornCarrier.val
          ((D : Module.End ℝ (NCZornCarrier A)).map_smul r ⟨X.val⟩) }
  left_inv D := by rcases D with ⟨⟨_, _, _⟩, _⟩; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro X; cases X; rfl

/-- Faithful `DerivationLieLane ℝ (NCZornCarrier A)`. -/
def ncZornRealDerivationLieLane (A : Type*) [Ring A] [Algebra ℝ A] :
    DerivationLieLane ℝ (NCZornCarrier A) :=
  fullDerivationLieLane ℝ (NCZornCarrier A)

/-- F8.4 Onsager attachment for `NCZornCarrier A` over `ℝ`. -/
def ncZornRealOnsagerSystem {A : Type*} [Ring A] [Algebra ℝ A]
    (S : OnsagerCasimirSystem (NCZornCarrier A)) (a : NCZornCarrier A) :
    OnsagerCasimirSystem (ncZornRealDerivationLieLane A).L :=
  inducedDerivationLaneOnsagerSystem S (ncZornRealDerivationLieLane A) a

theorem ncZornReal_onsager_reciprocity {A : Type*} [Ring A] [Algebra ℝ A] {n : ℕ}
    (PP : ParityOnsagerFormPairing (ncZornRealDerivationLieLane A).L (NCZornCarrier A) n)
    (ω η : DerivationOperatorForm (ncZornRealDerivationLieLane A) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (ncZornRealDerivationLieLane A) PP ω η

end NCZornRealLinear

end NCZornLane

/-! ## Section 7: `OperatorCoefficientZornExtension.OpDerivation H` (`OpZornCarrier H`, F8.1) -/

section OpZornLane

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- Dedicated newtype wrapper around `OpZorn H` owning `NonUnitalNonAssocRing`,
`Module ℝ`, `IsScalarTower ℂ/ℝ`, and `SMulCommClass ℂ/ℝ`. -/
@[ext]
structure OpZornCarrier (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  val : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn H

section OpZornInstances

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def opZornCarrierEquiv :
    OpZornCarrier H ≃ InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn H where
  toFun := OpZornCarrier.val
  invFun := OpZornCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupOpZornCarrier : AddCommGroup (OpZornCarrier H) :=
  Equiv.addCommGroup (opZornCarrierEquiv H)

private def opZornCarrierAddEquiv :
    OpZornCarrier H ≃+ InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn H where
  toEquiv := opZornCarrierEquiv H
  map_add' _ _ := rfl

instance instModuleComplexOpZornCarrier : Module ℂ (OpZornCarrier H) :=
  AddEquiv.module ℂ (opZornCarrierAddEquiv H)

instance instSMulRealOpZornCarrier : SMul ℝ (OpZornCarrier H) where
  smul r X := ⟨(r : ℂ) • X.val⟩

instance instModuleRealOpZornCarrier : Module ℝ (OpZornCarrier H) where
  one_smul X := by
    apply OpZornCarrier.ext
    change ((1 : ℝ) : ℂ) • X.val = X.val
    simp
  mul_smul r s X := by
    apply OpZornCarrier.ext
    change ((r * s : ℝ) : ℂ) • X.val = (r : ℂ) • ((s : ℂ) • X.val)
    push_cast
    rw [mul_smul]
  smul_zero r := by
    apply OpZornCarrier.ext
    change (r : ℂ) • (0 : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn H) = 0
    simp
  smul_add r X Y := by
    apply OpZornCarrier.ext
    change (r : ℂ) • (X.val + Y.val) = (r : ℂ) • X.val + (r : ℂ) • Y.val
    rw [smul_add]
  add_smul r s X := by
    apply OpZornCarrier.ext
    change ((r + s : ℝ) : ℂ) • X.val = (r : ℂ) • X.val + (s : ℂ) • X.val
    push_cast
    rw [add_smul]
  zero_smul X := by
    apply OpZornCarrier.ext
    change ((0 : ℝ) : ℂ) • X.val = 0
    simp

instance instIsScalarTowerRealComplexOpZornCarrier :
    IsScalarTower ℝ ℂ (OpZornCarrier H) where
  smul_assoc r c X := by
    apply OpZornCarrier.ext
    change ((r • c : ℂ) • X.val) = (r : ℂ) • (c • X.val)
    rw [Algebra.smul_def, mul_smul]
    rfl

instance instMulOpZornCarrier : Mul (OpZornCarrier H) where
  mul X Y := ⟨X.val * Y.val⟩

private theorem opZornCarrier_zero_a : (0 : OpZornCarrier H).val.a = 0 := rfl
private theorem opZornCarrier_zero_u : (0 : OpZornCarrier H).val.u = 0 := rfl
private theorem opZornCarrier_zero_v : (0 : OpZornCarrier H).val.v = 0 := rfl
private theorem opZornCarrier_zero_b : (0 : OpZornCarrier H).val.b = 0 := rfl
private theorem opZornCarrier_mul_a (X Y : OpZornCarrier H) :
    (X * Y).val.a = X.val.a * Y.val.a +
      InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Y.val.v := rfl
private theorem opZornCarrier_mul_u (X Y : OpZornCarrier H) (i : Fin 3) :
    (X * Y).val.u i = X.val.a * Y.val.u i + Y.val.b * X.val.u i -
      InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Y.val.v i := rfl
private theorem opZornCarrier_mul_v (X Y : OpZornCarrier H) (i : Fin 3) :
    (X * Y).val.v i = Y.val.a * X.val.v i + X.val.b * Y.val.v i +
      InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Y.val.u i := rfl
private theorem opZornCarrier_mul_b (X Y : OpZornCarrier H) :
    (X * Y).val.b = X.val.b * Y.val.b +
      InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Y.val.u := rfl

instance instNonUnitalNonAssocRingOpZornCarrier : NonUnitalNonAssocRing (OpZornCarrier H) where
  zero_mul X := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · simp [opZornCarrier_mul_a, opZornCarrier_zero_a, opZornCarrier_zero_u,
        InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
    · funext i
      fin_cases i <;>
        simp [opZornCarrier_mul_u, opZornCarrier_zero_a, opZornCarrier_zero_u, opZornCarrier_zero_v,
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
    · funext i
      fin_cases i <;>
        simp [opZornCarrier_mul_v, opZornCarrier_zero_u, opZornCarrier_zero_b, opZornCarrier_zero_v,
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
    · simp [opZornCarrier_mul_b, opZornCarrier_zero_b, opZornCarrier_zero_v,
        InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
  mul_zero X := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · simp [opZornCarrier_mul_a, opZornCarrier_zero_a, opZornCarrier_zero_v,
        InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
    · funext i
      fin_cases i <;>
        simp [opZornCarrier_mul_u, opZornCarrier_zero_u, opZornCarrier_zero_b, opZornCarrier_zero_v,
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
    · funext i
      fin_cases i <;>
        simp [opZornCarrier_mul_v, opZornCarrier_zero_a, opZornCarrier_zero_v, opZornCarrier_zero_u,
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
    · simp [opZornCarrier_mul_b, opZornCarrier_zero_b, opZornCarrier_zero_u,
        InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
  left_distrib X Y Z := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · change X.val.a * (Y.val.a + Z.val.a) +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u
            (fun i => Y.val.v i + Z.val.v i) =
        (X.val.a * Y.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Y.val.v) +
        (X.val.a * Z.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Z.val.v)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      noncomm_ring
    · funext i
      fin_cases i <;>
        · change X.val.a * (Y.val.u _ + Z.val.u _) + (Y.val.b + Z.val.b) * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v
                (fun k => Y.val.v k + Z.val.v k) _ =
            (X.val.a * Y.val.u _ + Y.val.b * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Y.val.v _) +
            (X.val.a * Z.val.u _ + Z.val.b * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Z.val.v _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          noncomm_ring
    · funext i
      fin_cases i <;>
        · change (Y.val.a + Z.val.a) * X.val.v _ + X.val.b * (Y.val.v _ + Z.val.v _) +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u
                (fun k => Y.val.u k + Z.val.u k) _ =
            (Y.val.a * X.val.v _ + X.val.b * Y.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Y.val.u _) +
            (Z.val.a * X.val.v _ + X.val.b * Z.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Z.val.u _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          noncomm_ring
    · change X.val.b * (Y.val.b + Z.val.b) +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v
            (fun i => Y.val.u i + Z.val.u i) =
        (X.val.b * Y.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Y.val.u) +
        (X.val.b * Z.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Z.val.u)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      noncomm_ring
  right_distrib X Y Z := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · change (X.val.a + Y.val.a) * Z.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot
            (fun i => X.val.u i + Y.val.u i) Z.val.v =
        (X.val.a * Z.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Z.val.v) +
        (Y.val.a * Z.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot Y.val.u Z.val.v)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      noncomm_ring
    · funext i
      fin_cases i <;>
        · change (X.val.a + Y.val.a) * Z.val.u _ + Z.val.b * (X.val.u _ + Y.val.u _) -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross
                (fun k => X.val.v k + Y.val.v k) Z.val.v _ =
            (X.val.a * Z.val.u _ + Z.val.b * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Z.val.v _) +
            (Y.val.a * Z.val.u _ + Z.val.b * Y.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross Y.val.v Z.val.v _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          noncomm_ring
    · funext i
      fin_cases i <;>
        · change Z.val.a * (X.val.v _ + Y.val.v _) + (X.val.b + Y.val.b) * Z.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross
                (fun k => X.val.u k + Y.val.u k) Z.val.u _ =
            (Z.val.a * X.val.v _ + X.val.b * Z.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Z.val.u _) +
            (Z.val.a * Y.val.v _ + Y.val.b * Z.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross Y.val.u Z.val.u _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          noncomm_ring
    · change (X.val.b + Y.val.b) * Z.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot
            (fun i => X.val.v i + Y.val.v i) Z.val.u =
        (X.val.b * Z.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Z.val.u) +
        (Y.val.b * Z.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot Y.val.v Z.val.u)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      noncomm_ring

instance instIsScalarTowerComplexOpZornCarrier :
    IsScalarTower ℂ (OpZornCarrier H) (OpZornCarrier H) where
  smul_assoc c X Y := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · change (c • X.val.a) * Y.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot
            (fun i => c • X.val.u i) Y.val.v =
        c • (X.val.a * Y.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Y.val.v)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      simp [smul_add]
    · funext i
      fin_cases i <;>
        · change (c • X.val.a) * Y.val.u _ + Y.val.b * (c • X.val.u _) -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross
                (fun k => c • X.val.v k) Y.val.v _ =
            c • (X.val.a * Y.val.u _ + Y.val.b * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Y.val.v _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          simp [smul_add, smul_sub]
    · funext i
      fin_cases i <;>
        · change Y.val.a * (c • X.val.v _) + (c • X.val.b) * Y.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross
                (fun k => c • X.val.u k) Y.val.u _ =
            c • (Y.val.a * X.val.v _ + X.val.b * Y.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Y.val.u _)
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          simp [smul_add, smul_sub]
    · change (c • X.val.b) * Y.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot
            (fun i => c • X.val.v i) Y.val.u =
        c • (X.val.b * Y.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Y.val.u)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      simp [smul_add]

instance instSMulCommClassComplexOpZornCarrier :
    SMulCommClass ℂ (OpZornCarrier H) (OpZornCarrier H) where
  smul_comm c X Y := by
    apply OpZornCarrier.ext
    apply InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpZorn.ext
    · change c • (X.val.a * Y.val.a +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u Y.val.v) =
        X.val.a * (c • Y.val.a) +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.u
            (fun i => c • Y.val.v i)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      simp [smul_add]
    · funext i
      fin_cases i <;>
        · change c • (X.val.a * Y.val.u _ + Y.val.b * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v Y.val.v _) =
            X.val.a * (c • Y.val.u _) + (c • Y.val.b) * X.val.u _ -
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.v
                (fun k => c • Y.val.v k) _
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          simp [smul_add, smul_sub]
    · funext i
      fin_cases i <;>
        · change c • (Y.val.a * X.val.v _ + X.val.b * Y.val.v _ +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u Y.val.u _) =
            (c • Y.val.a) * X.val.v _ + X.val.b * (c • Y.val.v _) +
              InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross X.val.u
                (fun k => c • Y.val.u k) _
          dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opCross]
          simp [smul_add, smul_sub]
    · change c • (X.val.b * Y.val.b +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v Y.val.u) =
        X.val.b * (c • Y.val.b) +
          InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot X.val.v
            (fun i => c • Y.val.u i)
      dsimp [InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDot]
      simp [smul_add]

instance instIsScalarTowerRealOpZornCarrier :
    IsScalarTower ℝ (OpZornCarrier H) (OpZornCarrier H) where
  smul_assoc r X Y := by
    change ((r : ℂ) • X) * Y = (r : ℂ) • (X * Y)
    exact smul_mul_assoc (r : ℂ) X Y

instance instSMulCommClassRealOpZornCarrier :
    SMulCommClass ℝ (OpZornCarrier H) (OpZornCarrier H) where
  smul_comm r X Y := by
    change (r : ℂ) • (X * Y) = X * ((r : ℂ) • Y)
    exact (mul_smul_comm (r : ℂ) X Y).symm

end OpZornInstances

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Equivalence between `OperatorCoefficientZornExtension.OpDerivation H` and
`NonAssocDerivation.derivations ℂ (OpZornCarrier H)`. -/
def opDerivationEquivComplexDerivations :
    InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H ≃
      NonAssocDerivation.derivations ℂ (OpZornCarrier H) where
  toFun D :=
    ⟨{ toFun := fun X => ⟨D.toLinearMap X.val⟩
       map_add' := fun X Y => by
         apply OpZornCarrier.ext
         exact D.toLinearMap.map_add X.val Y.val
       map_smul' := fun c X => by
         apply OpZornCarrier.ext
         exact D.toLinearMap.map_smul c X.val },
     fun X Y => by
       apply OpZornCarrier.ext
       exact D.leibniz X.val Y.val⟩
  invFun D :=
    { toLinearMap :=
        { toFun := fun X => ((D : Module.End ℂ (OpZornCarrier H)) ⟨X⟩).val
          map_add' := fun X Y =>
            congrArg OpZornCarrier.val ((D : Module.End ℂ (OpZornCarrier H)).map_add ⟨X⟩ ⟨Y⟩)
          map_smul' := fun c X =>
            congrArg OpZornCarrier.val ((D : Module.End ℂ (OpZornCarrier H)).map_smul c ⟨X⟩) }
      leibniz := fun X Y => congrArg OpZornCarrier.val (D.property ⟨X⟩ ⟨Y⟩) }
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply LinearMap.ext; intro X; cases X; rfl

theorem opDerivationEquivComplexDerivations_zero :
    opDerivationEquivComplexDerivations ⟨0, fun X Y => by
      simp only [LinearMap.zero_apply]
      change (0 : OpZornCarrier H).val = ((0 : OpZornCarrier H) * ⟨Y⟩ + ⟨X⟩ * 0).val
      rw [zero_mul, mul_zero, add_zero]⟩ = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem opDerivationEquivComplexDerivations_add
    (D₁ D₂ : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H) :
    opDerivationEquivComplexDerivations
        ⟨D₁.toLinearMap + D₂.toLinearMap, fun X Y => by
          simp only [LinearMap.add_apply]
          rw [D₁.leibniz X Y, D₂.leibniz X Y]
          change (⟨D₁.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D₁.toLinearMap Y⟩ +
              (⟨D₂.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D₂.toLinearMap Y⟩ : OpZornCarrier H)).val =
            ((⟨D₁.toLinearMap X⟩ + ⟨D₂.toLinearMap X⟩ : OpZornCarrier H) * ⟨Y⟩ +
              ⟨X⟩ * (⟨D₁.toLinearMap Y⟩ + ⟨D₂.toLinearMap Y⟩ : OpZornCarrier H)).val
          rw [add_mul, mul_add]
          abel_nf⟩ =
      opDerivationEquivComplexDerivations D₁ + opDerivationEquivComplexDerivations D₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem opDerivationEquivComplexDerivations_smul (c : ℂ)
    (D : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H) :
    opDerivationEquivComplexDerivations
        ⟨c • D.toLinearMap, fun X Y => by
          simp only [LinearMap.smul_apply]
          rw [D.leibniz X Y]
          change (c • (⟨D.toLinearMap X⟩ * ⟨Y⟩ + ⟨X⟩ * ⟨D.toLinearMap Y⟩ : OpZornCarrier H)).val =
            ((c • ⟨D.toLinearMap X⟩ : OpZornCarrier H) * ⟨Y⟩ +
              ⟨X⟩ * (c • ⟨D.toLinearMap Y⟩ : OpZornCarrier H)).val
          rw [smul_add, smul_mul_assoc, mul_smul_comm]⟩ =
      c • opDerivationEquivComplexDerivations D := by
  apply Subtype.ext; apply LinearMap.ext; intro X; rfl

theorem opDerivationEquivComplexDerivations_commutator
    (D₁ D₂ : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H) :
    opDerivationEquivComplexDerivations
        ⟨InfoGeometry.Canonical.OperatorCoefficientZornExtension.opDerivationCommutator D₁ D₂,
         InfoGeometry.Canonical.OperatorCoefficientZornExtension.liftDerivation_commutator D₁ D₂⟩ =
      ⁅opDerivationEquivComplexDerivations D₁, opDerivationEquivComplexDerivations D₂⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  rfl

/-- Restrict `OpDerivation H` to `NonAssocDerivation.derivations ℝ (OpZornCarrier H)` for Onsager attachment. -/
def opDerivationToRealDerivations
    (D : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H) :
    NonAssocDerivation.derivations ℝ (OpZornCarrier H) :=
  ⟨((opDerivationEquivComplexDerivations D : Module.End ℂ (OpZornCarrier H))).restrictScalars ℝ,
   (opDerivationEquivComplexDerivations D).property⟩

theorem opDerivationToRealDerivations_injective :
    Function.Injective (opDerivationToRealDerivations (H := H)) := by
  intro D₁ D₂ h
  apply opDerivationEquivComplexDerivations.injective
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  exact congrArg (fun f : NonAssocDerivation.derivations ℝ (OpZornCarrier H) =>
    (f : Module.End ℝ (OpZornCarrier H)) X) h

/-- Restrict `OpDerivation H` to `NonAssocDerivation.derivations ℤ (OpZornCarrier H)`. -/
def opDerivationToIntDerivations
    (D : InfoGeometry.Canonical.OperatorCoefficientZornExtension.OpDerivation H) :
    NonAssocDerivation.derivations ℤ (OpZornCarrier H) :=
  ⟨((opDerivationEquivComplexDerivations D : Module.End ℂ (OpZornCarrier H))).restrictScalars ℤ,
   (opDerivationEquivComplexDerivations D).property⟩

/-- Faithful `DerivationLieLane ℂ (OpZornCarrier H)`. -/
def opZornComplexDerivationLieLane :
    DerivationLieLane ℂ (OpZornCarrier H) :=
  fullDerivationLieLane ℂ (OpZornCarrier H)

/-- Faithful `DerivationLieLane ℝ (OpZornCarrier H)`. -/
def opZornRealDerivationLieLane :
    DerivationLieLane ℝ (OpZornCarrier H) :=
  fullDerivationLieLane ℝ (OpZornCarrier H)

/-- F8.4 Onsager attachment for `OpZornCarrier H` over `ℝ`. -/
def opZornRealOnsagerSystem
    (S : OnsagerCasimirSystem (OpZornCarrier H)) (a : OpZornCarrier H) :
    OnsagerCasimirSystem (opZornRealDerivationLieLane (H := H)).L :=
  inducedDerivationLaneOnsagerSystem S (opZornRealDerivationLieLane (H := H)) a

theorem opZornReal_onsager_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing (opZornRealDerivationLieLane (H := H)).L (OpZornCarrier H) n)
    (ω η : DerivationOperatorForm
      (opZornRealDerivationLieLane (H := H)) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (opZornRealDerivationLieLane (H := H)) PP ω η

end OpZornLane

/-! ## Section 8: `AlbertDerivationsF4.JordanDerivation circ` (`BilinearAlgCarrier`, F8.1) -/

section BilinearJordanLane

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

/-- Bundled additive bilinear product on `J` for `AlbertDerivations.JordanDerivation` (`[Ring R]`). -/
structure BilinearRingProduct (J : Type*) [AddCommGroup J] where
  circ : J → J → J
  add_left : ∀ x y z : J, circ (x + y) z = circ x z + circ y z
  add_right : ∀ x y z : J, circ x (y + z) = circ x y + circ x z

/-- Dedicated newtype wrapper around `J` equipped with `P.circ` as `*` (`NonUnitalNonAssocRing`). -/
@[ext]
structure BilinearAlgRingCarrier {J : Type*} [AddCommGroup J] (P : BilinearRingProduct J) where
  val : J

section RingCarrierInstances

variable {J : Type*} [AddCommGroup J] (P : BilinearRingProduct J)

private def bilinearAlgRingCarrierEquiv : BilinearAlgRingCarrier P ≃ J where
  toFun := BilinearAlgRingCarrier.val
  invFun := BilinearAlgRingCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupBilinearAlgRingCarrier :
    AddCommGroup (BilinearAlgRingCarrier P) :=
  Equiv.addCommGroup (bilinearAlgRingCarrierEquiv P)

private def bilinearAlgRingCarrierAddEquiv : BilinearAlgRingCarrier P ≃+ J where
  toEquiv := bilinearAlgRingCarrierEquiv P
  map_add' _ _ := rfl

instance instModuleBilinearAlgRingCarrier {R : Type*} [Ring R] [Module R J] :
    Module R (BilinearAlgRingCarrier P) :=
  AddEquiv.module R (bilinearAlgRingCarrierAddEquiv P)

instance instMulBilinearAlgRingCarrier : Mul (BilinearAlgRingCarrier P) where
  mul x y := ⟨P.circ x.val y.val⟩

private theorem bilinearRingProduct_zero_mul (x : J) : P.circ 0 x = 0 := by
  have h : P.circ 0 x + P.circ 0 x = P.circ 0 x + 0 := by
    calc
      P.circ 0 x + P.circ 0 x = P.circ (0 + 0) x := (P.add_left 0 0 x).symm
      _ = P.circ 0 x + 0 := by rw [zero_add, add_zero]
  exact add_left_cancel h

private theorem bilinearRingProduct_mul_zero (x : J) : P.circ x 0 = 0 := by
  have h : P.circ x 0 + P.circ x 0 = P.circ x 0 + 0 := by
    calc
      P.circ x 0 + P.circ x 0 = P.circ x (0 + 0) := (P.add_right x 0 0).symm
      _ = P.circ x 0 + 0 := by rw [zero_add, add_zero]
  exact add_left_cancel h

instance instNonUnitalNonAssocRingBilinearAlgRingCarrier :
    NonUnitalNonAssocRing (BilinearAlgRingCarrier P) where
  zero_mul x := by apply BilinearAlgRingCarrier.ext; exact bilinearRingProduct_zero_mul P x.val
  mul_zero x := by apply BilinearAlgRingCarrier.ext; exact bilinearRingProduct_mul_zero P x.val
  left_distrib x y z := by apply BilinearAlgRingCarrier.ext; exact P.add_right x.val y.val z.val
  right_distrib x y z := by apply BilinearAlgRingCarrier.ext; exact P.add_left x.val y.val z.val

end RingCarrierInstances

/-- For any `[Ring R]`, `AlbertDerivations.JordanDerivation P.circ` satisfies `NonAssocDerivation.IsLeibniz R`. -/
def jordanDerivationToEnd {R J : Type*} [Ring R] [AddCommGroup J] [Module R J]
    {P : BilinearRingProduct J}
    (D : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) P.circ) :
    Module.End R (BilinearAlgRingCarrier P) where
  toFun x := ⟨D.toFun x.val⟩
  map_add' x y := by apply BilinearAlgRingCarrier.ext; exact D.map_add x.val y.val
  map_smul' r x := by apply BilinearAlgRingCarrier.ext; exact D.map_smul r x.val

theorem jordanDerivation_isLeibniz {R J : Type*} [Ring R] [AddCommGroup J] [Module R J]
    {P : BilinearRingProduct J}
    (D : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) P.circ) :
    NonAssocDerivation.IsLeibniz R (BilinearAlgRingCarrier P) (jordanDerivationToEnd D) :=
  fun x y => by apply BilinearAlgRingCarrier.ext; exact D.leibniz x.val y.val

/-- Bundled `R`-bilinear product on `J` for `derivations R` and `DerivationLieLane R`. -/
structure BilinearAlgData (R J : Type*) [Ring R] [AddCommGroup J] [Module R J] extends
    BilinearRingProduct J where
  smul_left : ∀ (r : R) (x y : J), circ (r • x) y = r • circ x y
  smul_right : ∀ (r : R) (x y : J), circ x (r • y) = r • circ x y

/-- Dedicated newtype wrapper around `J` owning `NonUnitalNonAssocRing`, `IsScalarTower R`,
and `SMulCommClass R` for `D : BilinearAlgData R J`. -/
@[ext]
structure BilinearAlgCarrier {R J : Type*} [Ring R] [AddCommGroup J] [Module R J]
    (D : BilinearAlgData R J) where
  val : J

section BilinearAlgCarrierInstances

variable {R J : Type*} [Ring R] [AddCommGroup J] [Module R J] (D : BilinearAlgData R J)

private def bilinearAlgCarrierEquiv : BilinearAlgCarrier D ≃ J where
  toFun := BilinearAlgCarrier.val
  invFun := BilinearAlgCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroupBilinearAlgCarrier : AddCommGroup (BilinearAlgCarrier D) :=
  Equiv.addCommGroup (bilinearAlgCarrierEquiv D)

private def bilinearAlgCarrierAddEquiv : BilinearAlgCarrier D ≃+ J where
  toEquiv := bilinearAlgCarrierEquiv D
  map_add' _ _ := rfl

instance instModuleBilinearAlgCarrier : Module R (BilinearAlgCarrier D) :=
  AddEquiv.module R (bilinearAlgCarrierAddEquiv D)

instance instMulBilinearAlgCarrier : Mul (BilinearAlgCarrier D) where
  mul x y := ⟨D.circ x.val y.val⟩

instance instNonUnitalNonAssocRingBilinearAlgCarrier :
    NonUnitalNonAssocRing (BilinearAlgCarrier D) where
  zero_mul x := by
    apply BilinearAlgCarrier.ext
    exact bilinearRingProduct_zero_mul D.toBilinearRingProduct x.val
  mul_zero x := by
    apply BilinearAlgCarrier.ext
    exact bilinearRingProduct_mul_zero D.toBilinearRingProduct x.val
  left_distrib x y z := by
    apply BilinearAlgCarrier.ext
    exact D.add_right x.val y.val z.val
  right_distrib x y z := by
    apply BilinearAlgCarrier.ext
    exact D.add_left x.val y.val z.val

instance instIsScalarTowerBilinearAlgCarrier :
    IsScalarTower R (BilinearAlgCarrier D) (BilinearAlgCarrier D) where
  smul_assoc r x y := by
    apply BilinearAlgCarrier.ext
    exact D.smul_left r x.val y.val

instance instSMulCommClassBilinearAlgCarrier :
    SMulCommClass R (BilinearAlgCarrier D) (BilinearAlgCarrier D) where
  smul_comm r x y := by
    apply BilinearAlgCarrier.ext
    exact (D.smul_right r x.val y.val).symm

end BilinearAlgCarrierInstances

/-- Equivalence between `AlbertDerivations.JordanDerivation (R := R) D.circ` and
`NonAssocDerivation.derivations R (BilinearAlgCarrier D)` for `[CommRing R]`. -/
def jordanDerivationEquivDerivations {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (D : BilinearAlgData R J) :
    InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) D.circ ≃
      NonAssocDerivation.derivations R (BilinearAlgCarrier D) where
  toFun δ :=
    ⟨{ toFun := fun x => ⟨δ.toFun x.val⟩
       map_add' := fun x y => by apply BilinearAlgCarrier.ext; exact δ.map_add x.val y.val
       map_smul' := fun r x => by apply BilinearAlgCarrier.ext; exact δ.map_smul r x.val },
     fun x y => by apply BilinearAlgCarrier.ext; exact δ.leibniz x.val y.val⟩
  invFun δ :=
    { toFun := fun x => ((δ : Module.End R (BilinearAlgCarrier D)) ⟨x⟩).val
      map_add := fun x y =>
        congrArg BilinearAlgCarrier.val ((δ : Module.End R (BilinearAlgCarrier D)).map_add ⟨x⟩ ⟨y⟩)
      map_smul := fun r x =>
        congrArg BilinearAlgCarrier.val ((δ : Module.End R (BilinearAlgCarrier D)).map_smul r ⟨x⟩)
      leibniz := fun x y => congrArg BilinearAlgCarrier.val (δ.property ⟨x⟩ ⟨y⟩) }
  left_inv δ := by cases δ; rfl
  right_inv δ := by apply Subtype.ext; apply LinearMap.ext; intro x; cases x; rfl

theorem jordanDerivationEquivDerivations_zero {R J : Type*}
    [CommRing R] [AddCommGroup J] [Module R J] (D : BilinearAlgData R J) :
    jordanDerivationEquivDerivations D
        { toFun := fun _ => 0
          map_add := fun _ _ => (add_zero 0).symm
          map_smul := fun _ _ => (smul_zero _).symm
          leibniz := fun x y => by
            rw [bilinearRingProduct_zero_mul D.toBilinearRingProduct y,
              bilinearRingProduct_mul_zero D.toBilinearRingProduct x, add_zero] } = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro x; rfl

theorem jordanDerivationEquivDerivations_add {R J : Type*}
    [CommRing R] [AddCommGroup J] [Module R J] (D : BilinearAlgData R J)
    (δ₁ δ₂ : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) D.circ) :
    jordanDerivationEquivDerivations D
        { toFun := fun x => δ₁.toFun x + δ₂.toFun x
          map_add := fun x y => by rw [δ₁.map_add, δ₂.map_add]; abel
          map_smul := fun r x => by rw [δ₁.map_smul, δ₂.map_smul, smul_add]
          leibniz := fun x y => by
            rw [δ₁.leibniz, δ₂.leibniz, D.add_left, D.add_right]
            abel } =
      jordanDerivationEquivDerivations D δ₁ + jordanDerivationEquivDerivations D δ₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro x; rfl

theorem jordanDerivationEquivDerivations_smul {R J : Type*}
    [CommRing R] [AddCommGroup J] [Module R J] (D : BilinearAlgData R J) (r : R)
    (δ : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) D.circ) :
    jordanDerivationEquivDerivations D
        { toFun := fun x => r • δ.toFun x
          map_add := fun x y => by rw [δ.map_add, smul_add]
          map_smul := fun s x => by rw [δ.map_smul, smul_comm]
          leibniz := fun x y => by
            rw [δ.leibniz, smul_add, D.smul_left, D.smul_right] } =
      r • jordanDerivationEquivDerivations D δ := by
  apply Subtype.ext; apply LinearMap.ext; intro x; rfl

theorem jordanDerivationEquivDerivations_bracket {R J : Type*}
    [CommRing R] [AddCommGroup J] [Module R J]
    (D : BilinearAlgData R J)
    (h_comm : ∀ x y : J, D.circ x y = D.circ y x)
    (δ₁ δ₂ : InfoGeometry.Exceptional.AlbertDerivations.JordanDerivation (R := R) D.circ) :
    jordanDerivationEquivDerivations D
        { toFun := InfoGeometry.Exceptional.AlbertDerivations.bracket δ₁.toFun δ₂.toFun
          map_add := fun x y => by
            dsimp [InfoGeometry.Exceptional.AlbertDerivations.bracket]
            rw [δ₂.map_add, δ₁.map_add, δ₁.map_add, δ₂.map_add]
            abel
          map_smul := fun r x => by
            dsimp [InfoGeometry.Exceptional.AlbertDerivations.bracket]
            rw [δ₂.map_smul, δ₁.map_smul, δ₁.map_smul, δ₂.map_smul, smul_sub]
          leibniz := InfoGeometry.Exceptional.AlbertDerivations.bracket_is_derivation
            D.circ h_comm D.add_left D.add_right
            (fun x y z => by
              rw [sub_eq_add_neg, D.add_left]
              have hneg : D.circ (-y) z = -D.circ y z := by
                have h := D.add_left y (-y) z
                rw [add_neg_cancel] at h
                have hz : D.circ 0 z = 0 := bilinearRingProduct_zero_mul D.toBilinearRingProduct z
                rw [hz] at h
                exact eq_neg_of_add_eq_zero_right h.symm
              rw [hneg, sub_eq_add_neg])
            (fun x y z => by
              rw [sub_eq_add_neg, D.add_right]
              have hneg : D.circ x (-z) = -D.circ x z := by
                have h := D.add_right x z (-z)
                rw [add_neg_cancel] at h
                have hz : D.circ x 0 = 0 := bilinearRingProduct_mul_zero D.toBilinearRingProduct x
                rw [hz] at h
                exact eq_neg_of_add_eq_zero_right h.symm
              rw [hneg, sub_eq_add_neg])
            δ₁ δ₂ } =
      ⁅jordanDerivationEquivDerivations D δ₁, jordanDerivationEquivDerivations D δ₂⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

/-- Faithful `DerivationLieLane R (BilinearAlgCarrier D)`. -/
def bilinearAlgDerivationLieLane {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (D : BilinearAlgData R J) : DerivationLieLane R (BilinearAlgCarrier D) :=
  fullDerivationLieLane R (BilinearAlgCarrier D)

/-- F8.4 Onsager attachment for `BilinearAlgCarrier D` at `R = ℝ`. -/
def bilinearAlgOnsagerSystem {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : BilinearAlgData ℝ J)
    (S : OnsagerCasimirSystem (BilinearAlgCarrier D)) (a : BilinearAlgCarrier D) :
    OnsagerCasimirSystem (bilinearAlgDerivationLieLane D).L :=
  inducedDerivationLaneOnsagerSystem S (bilinearAlgDerivationLieLane D) a

theorem bilinearAlg_onsager_reciprocity {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : BilinearAlgData ℝ J) {n : ℕ}
    (PP : ParityOnsagerFormPairing (bilinearAlgDerivationLieLane D).L (BilinearAlgCarrier D) n)
    (ω η : DerivationOperatorForm (bilinearAlgDerivationLieLane D) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (bilinearAlgDerivationLieLane D) PP ω η

end BilinearJordanLane

/-! ## Section 9: Peirce $\mathbb{Z}_2$ / Superderivations (`PeirceGradedSuperderivations`, F8.2) -/

section PeirceSuperderivationLanes

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
open PureNonCommutativeOperatorSpine
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

section RingSuperderivations

variable {B : Type*} [Ring B]

/-- Embed a square-zero ring differential into `NonAssocDerivation.derivations ℤ B`. -/
def squareZeroRingDifferentialToDerivations (d : B →+ B)
    (hd : IsSquareZeroRingDifferential d) :
    NonAssocDerivation.derivations ℤ B :=
  ⟨addHomToIntEnd d, hd.1⟩

theorem squareZeroRingDifferentialToDerivations_injective :
    Function.Injective (fun d : { d : B →+ B // IsSquareZeroRingDifferential d } =>
      squareZeroRingDifferentialToDerivations d.1 d.2) := by
  intro d₁ d₂ h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  exact congrArg (fun f : NonAssocDerivation.derivations ℤ B =>
    (f : Module.End ℤ B) x) h

theorem squareZeroRingDifferentialToDerivations_sq_zero (d : B →+ B)
    (hd : IsSquareZeroRingDifferential d) :
    ((squareZeroRingDifferentialToDerivations d hd : Module.End ℤ B).comp
      (squareZeroRingDifferentialToDerivations d hd : Module.End ℤ B)) = 0 := by
  apply LinearMap.ext
  intro x
  exact hd.2 x

/-- Additive subgroup of additive Leibniz endomorphisms `B →+ B`. -/
def addLeibnizSubgroup (B : Type*) [Ring B] : AddSubgroup (B →+ B) where
  carrier := { d : B →+ B | ∀ x y : B, d (x * y) = d x * y + x * d y }
  zero_mem' x y := by simp
  add_mem' {d₁ d₂} h₁ h₂ x y := by
    simp only [AddMonoidHom.add_apply, h₁ x y, h₂ x y, add_mul, mul_add]
    abel
  neg_mem' {d} h x y := by
    simp only [AddMonoidHom.neg_apply, h x y, neg_mul, mul_neg]
    abel

/-- Additive equivalence between additive Leibniz derivations `B →+ B` and `NonAssocDerivation.derivations ℤ B`. -/
def addLeibnizEquivIntDerivations (B : Type*) [Ring B] :
    addLeibnizSubgroup B ≃+ NonAssocDerivation.derivations ℤ B where
  toFun d := ⟨addHomToIntEnd d.1, d.2⟩
  invFun D := ⟨(D : Module.End ℤ B).toAddMonoidHom, D.property⟩
  left_inv d := by ext x; rfl
  right_inv D := by ext x; rfl
  map_add' d₁ d₂ := by ext x; rfl

/-- Predicate characterizing an odd `twist S`-superderivation on `B`. -/
def IsOddTwistSuperderivation (S : B) (d : B →+ B) : Prop :=
  (∀ X Y : B, d (X * Y) = d X * Y + twist S X * d Y) ∧
  (∀ X : B, twist S (d X) = -d (twist S X))

/-- Bundled odd `twist S`-superderivation on `B`. -/
@[ext]
structure OddTwistSuperderivation (B : Type*) [Ring B] (S : B) where
  toAddHom : B →+ B
  graded_leibniz : ∀ X Y : B, toAddHom (X * Y) = toAddHom X * Y + twist S X * toAddHom Y
  parity_odd : ∀ X : B, twist S (toAddHom X) = -toAddHom (twist S X)

theorem isOddTwistSuperderivation_zero (S : B) :
    IsOddTwistSuperderivation S (0 : B →+ B) := by
  refine ⟨fun X Y => ?_, fun X => ?_⟩
  · simp
  · simp [twist]

theorem isOddTwistSuperderivation_add {S : B} {d₁ d₂ : B →+ B}
    (h₁ : IsOddTwistSuperderivation S d₁) (h₂ : IsOddTwistSuperderivation S d₂) :
    IsOddTwistSuperderivation S (d₁ + d₂) := by
  refine ⟨fun X Y => ?_, fun X => ?_⟩
  · simp only [AddMonoidHom.add_apply, h₁.1 X Y, h₂.1 X Y, add_mul, mul_add]
    abel
  · simp only [AddMonoidHom.add_apply, twist_add, h₁.2 X, h₂.2 X]
    abel

theorem isOddTwistSuperderivation_neg {S : B} {d : B →+ B}
    (h : IsOddTwistSuperderivation S d) :
    IsOddTwistSuperderivation S (-d) := by
  refine ⟨fun X Y => ?_, fun X => ?_⟩
  · simp only [AddMonoidHom.neg_apply, h.1 X Y, neg_mul, mul_neg]
    abel
  · simp only [AddMonoidHom.neg_apply, twist, mul_neg, neg_mul, neg_inj]
    exact h.2 X

theorem isOddTwistSuperderivation_sub {S : B} {d₁ d₂ : B →+ B}
    (h₁ : IsOddTwistSuperderivation S d₁) (h₂ : IsOddTwistSuperderivation S d₂) :
    IsOddTwistSuperderivation S (d₁ - d₂) := by
  rw [sub_eq_add_neg]
  exact isOddTwistSuperderivation_add h₁ (isOddTwistSuperderivation_neg h₂)

instance instZeroOddTwistSuperderivation (S : B) : Zero (OddTwistSuperderivation B S) where
  zero := ⟨0, (isOddTwistSuperderivation_zero S).1, (isOddTwistSuperderivation_zero S).2⟩

instance instAddOddTwistSuperderivation (S : B) : Add (OddTwistSuperderivation B S) where
  add d₁ d₂ :=
    ⟨d₁.toAddHom + d₂.toAddHom,
      (isOddTwistSuperderivation_add ⟨d₁.graded_leibniz, d₁.parity_odd⟩
        ⟨d₂.graded_leibniz, d₂.parity_odd⟩).1,
      (isOddTwistSuperderivation_add ⟨d₁.graded_leibniz, d₁.parity_odd⟩
        ⟨d₂.graded_leibniz, d₂.parity_odd⟩).2⟩

instance instNegOddTwistSuperderivation (S : B) : Neg (OddTwistSuperderivation B S) where
  neg d :=
    ⟨-d.toAddHom,
      (isOddTwistSuperderivation_neg ⟨d.graded_leibniz, d.parity_odd⟩).1,
      (isOddTwistSuperderivation_neg ⟨d.graded_leibniz, d.parity_odd⟩).2⟩

instance instSubOddTwistSuperderivation (S : B) : Sub (OddTwistSuperderivation B S) where
  sub d₁ d₂ :=
    ⟨d₁.toAddHom - d₂.toAddHom,
      (isOddTwistSuperderivation_sub ⟨d₁.graded_leibniz, d₁.parity_odd⟩
        ⟨d₂.graded_leibniz, d₂.parity_odd⟩).1,
      (isOddTwistSuperderivation_sub ⟨d₁.graded_leibniz, d₁.parity_odd⟩
        ⟨d₂.graded_leibniz, d₂.parity_odd⟩).2⟩

instance instAddCommGroupOddTwistSuperderivation (S : B) :
    AddCommGroup (OddTwistSuperderivation B S) where
  add_assoc d₁ d₂ d₃ := by ext x; exact add_assoc _ _ _
  zero_add d := by ext x; exact zero_add _
  add_zero d := by ext x; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel d := by ext x; exact neg_add_cancel _
  sub_eq_add_neg d₁ d₂ := by ext x; exact sub_eq_add_neg _ _
  add_comm d₁ d₂ := by ext x; exact add_comm _ _

/-- `oddDiff S N` as an additive homomorphism `B →+ B`. -/
def oddDiffAddHom (S N : B) : B →+ B where
  toFun := oddDiff S N
  map_zero' := by simp [oddDiff, twist]
  map_add' X Y := by
    simp only [oddDiff, twist_add, add_mul, mul_add, sub_eq_add_neg]
    abel

theorem oddDiff_isOddTwistSuperderivation {S N : B} (hS : S * S = 1)
    (hSN : S * N = -(N * S)) :
    IsOddTwistSuperderivation S (oddDiffAddHom S N) :=
  ⟨fun X Y => oddDiff_graded_leibniz hS X Y, fun X => oddDiff_twist_anticommute hS hSN X⟩

/-- Bundled `oddDiff` superderivation. -/
def oddDiffSuperderivation {S N : B} (hS : S * S = 1) (hSN : S * N = -(N * S)) :
    OddTwistSuperderivation B S :=
  ⟨oddDiffAddHom S N, (oddDiff_isOddTwistSuperderivation hS hSN).1,
    (oddDiff_isOddTwistSuperderivation hS hSN).2⟩

/-- `differentialPlus P A` as an `OddTwistSuperderivation B (invS P)`. -/
def differentialPlusAddHom (P A : B) : B →+ B :=
  oddDiffAddHom (invS P) (conePlus P A)

theorem differentialPlus_isOddTwistSuperderivation {P : B} (hP : P * P = P) (A : B) :
    IsOddTwistSuperderivation (invS P) (differentialPlusAddHom P A) :=
  oddDiff_isOddTwistSuperderivation (invS_sq hP)
    (by rw [invS_mul_conePlus hP A, conePlus_mul_invS hP A]; simp)

def differentialPlusSuperderivation {P : B} (hP : P * P = P) (A : B) :
    OddTwistSuperderivation B (invS P) :=
  ⟨differentialPlusAddHom P A, (differentialPlus_isOddTwistSuperderivation hP A).1,
    (differentialPlus_isOddTwistSuperderivation hP A).2⟩

/-- `differentialMinus P C` as an `OddTwistSuperderivation B (invS P)`. -/
def differentialMinusAddHom (P C : B) : B →+ B :=
  oddDiffAddHom (invS P) (coneMinus P C)

theorem differentialMinus_isOddTwistSuperderivation {P : B} (hP : P * P = P) (C : B) :
    IsOddTwistSuperderivation (invS P) (differentialMinusAddHom P C) :=
  oddDiff_isOddTwistSuperderivation (invS_sq hP)
    (by rw [invS_mul_coneMinus hP C, coneMinus_mul_invS hP C])

def differentialMinusSuperderivation {P : B} (hP : P * P = P) (C : B) :
    OddTwistSuperderivation B (invS P) :=
  ⟨differentialMinusAddHom P C, (differentialMinus_isOddTwistSuperderivation hP C).1,
    (differentialMinus_isOddTwistSuperderivation hP C).2⟩

/-- `differentialPhi P A C` as an `OddTwistSuperderivation B (invS P)`. -/
def differentialPhiAddHom (P A C : B) : B →+ B :=
  differentialPlusAddHom P A + differentialMinusAddHom P C

theorem differentialPhi_isOddTwistSuperderivation {P : B} (hP : P * P = P) (A C : B) :
    IsOddTwistSuperderivation (invS P) (differentialPhiAddHom P A C) :=
  isOddTwistSuperderivation_add (differentialPlus_isOddTwistSuperderivation hP A)
    (differentialMinus_isOddTwistSuperderivation hP C)

def differentialPhiSuperderivation {P : B} (hP : P * P = P) (A C : B) :
    OddTwistSuperderivation B (invS P) :=
  ⟨differentialPhiAddHom P A C, (differentialPhi_isOddTwistSuperderivation hP A C).1,
    (differentialPhi_isOddTwistSuperderivation hP A C).2⟩

/-- `differentialJ P A C` as an `OddTwistSuperderivation B (invS P)`. -/
def differentialJAddHom (P A C : B) : B →+ B :=
  differentialPlusAddHom P A - differentialMinusAddHom P C

theorem differentialJ_isOddTwistSuperderivation {P : B} (hP : P * P = P) (A C : B) :
    IsOddTwistSuperderivation (invS P) (differentialJAddHom P A C) :=
  isOddTwistSuperderivation_sub (differentialPlus_isOddTwistSuperderivation hP A)
    (differentialMinus_isOddTwistSuperderivation hP C)

def differentialJSuperderivation {P : B} (hP : P * P = P) (A C : B) :
    OddTwistSuperderivation B (invS P) :=
  ⟨differentialJAddHom P A C, (differentialJ_isOddTwistSuperderivation hP A C).1,
    (differentialJ_isOddTwistSuperderivation hP A C).2⟩

/-- Super-anticommutator `{d₁, d₂} = d₁ ∘ d₂ + d₂ ∘ d₁`. -/
def superAnticomm (d₁ d₂ : B →+ B) : B →+ B :=
  d₁.comp d₂ + d₂.comp d₁

@[simp]
theorem superAnticomm_apply (d₁ d₂ : B →+ B) (X : B) :
    superAnticomm d₁ d₂ X = d₁ (d₂ X) + d₂ (d₁ X) :=
  rfl

/-- The super-anticommutator of two odd `twist S`-superderivations is an ordinary
`ℤ`-linear Leibniz derivation on `B`. -/
theorem superAnticomm_isLeibniz {S : B} (hS : S * S = 1) {d₁ d₂ : B →+ B}
    (hd₁ : IsOddTwistSuperderivation S d₁) (hd₂ : IsOddTwistSuperderivation S d₂) :
    NonAssocDerivation.IsLeibniz ℤ B (addHomToIntEnd (superAnticomm d₁ d₂)) := by
  intro x y
  simp only [addHomToIntEnd_apply, superAnticomm_apply]
  have h12 : d₁ (d₂ (x * y)) =
      d₁ (d₂ x) * y + twist S (d₂ x) * d₁ y + d₁ (twist S x) * d₂ y +
        twist S (twist S x) * d₁ (d₂ y) := by
    rw [hd₂.1 x y, d₁.map_add, hd₁.1 (d₂ x) y, hd₁.1 (twist S x) (d₂ y)]
    abel
  have h21 : d₂ (d₁ (x * y)) =
      d₂ (d₁ x) * y + twist S (d₁ x) * d₂ y + d₂ (twist S x) * d₁ y +
        twist S (twist S x) * d₂ (d₁ y) := by
    rw [hd₁.1 x y, d₂.map_add, hd₂.1 (d₁ x) y, hd₂.1 (twist S x) (d₁ y)]
    abel
  have hc₂ : twist S (d₂ x) * d₁ y + d₂ (twist S x) * d₁ y = 0 := by
    rw [hd₂.2 x, neg_mul, neg_add_cancel]
  have hc₁ : d₁ (twist S x) * d₂ y + twist S (d₁ x) * d₂ y = 0 := by
    rw [hd₁.2 x, neg_mul, add_neg_cancel]
  rw [h12, h21, twist_twist hS x, add_mul, mul_add]
  calc
    d₁ (d₂ x) * y + twist S (d₂ x) * d₁ y + d₁ (twist S x) * d₂ y + x * d₁ (d₂ y) +
        (d₂ (d₁ x) * y + twist S (d₁ x) * d₂ y + d₂ (twist S x) * d₁ y + x * d₂ (d₁ y))
      = d₁ (d₂ x) * y + d₂ (d₁ x) * y + (x * d₁ (d₂ y) + x * d₂ (d₁ y)) +
          ((twist S (d₂ x) * d₁ y + d₂ (twist S x) * d₁ y) +
            (d₁ (twist S x) * d₂ y + twist S (d₁ x) * d₂ y)) := by abel
    _ = d₁ (d₂ x) * y + d₂ (d₁ x) * y + (x * d₁ (d₂ y) + x * d₂ (d₁ y)) := by
          rw [hc₂, hc₁, add_zero, add_zero]

/-- Bundle the super-anticommutator `{d₁, d₂}` into `NonAssocDerivation.derivations ℤ B`. -/
def superAnticommToDerivations {S : B} (hS : S * S = 1) {d₁ d₂ : B →+ B}
    (hd₁ : IsOddTwistSuperderivation S d₁) (hd₂ : IsOddTwistSuperderivation S d₂) :
    NonAssocDerivation.derivations ℤ B :=
  ⟨addHomToIntEnd (superAnticomm d₁ d₂), superAnticomm_isLeibniz hS hd₁ hd₂⟩

theorem superAnticomm_parity_even {S : B} {d₁ d₂ : B →+ B}
    (hd₁ : IsOddTwistSuperderivation S d₁) (hd₂ : IsOddTwistSuperderivation S d₂) (X : B) :
    twist S (superAnticomm d₁ d₂ X) = superAnticomm d₁ d₂ (twist S X) := by
  simp only [superAnticomm_apply, twist_add]
  rw [hd₁.2, hd₂.2, hd₂.2, hd₁.2]
  simp [neg_neg]

/-- Exact equality between `{oddDiff S N, oddDiff S M}` and `innerIntDerivation (N * M + M * N)`. -/
theorem superAnticommToDerivations_oddDiff_eq {S N M : B} (hS : S * S = 1)
    (hSN : S * N = -(N * S)) (hSM : S * M = -(M * S)) :
    superAnticommToDerivations hS (oddDiff_isOddTwistSuperderivation hS hSN)
        (oddDiff_isOddTwistSuperderivation hS hSM) =
      innerIntDerivation (N * M + M * N) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  exact oddDiff_pair hS hSN hSM X

/-- Exact equality between `{differentialPlus P A, differentialMinus P C}` and `innerIntDerivation (genV P A C)`. -/
theorem superAnticommToDerivations_differentialPlus_differentialMinus_eq
    {P : B} (hP : P * P = P) (A C : B) :
    superAnticommToDerivations (invS_sq hP)
        (differentialPlus_isOddTwistSuperderivation hP A)
        (differentialMinus_isOddTwistSuperderivation hP C) =
      innerIntDerivation (genV P A C) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  change differentialPlus P A (differentialMinus P C X) +
      differentialMinus P C (differentialPlus P A X) =
    genV P A C * X - X * genV P A C
  simpa [PureNonCommutativeOperatorSpine.comm] using
    differentialPlus_differentialMinus_pair A C X hP

/-- Even subring `{ X : B | twist S X = X }` for a grading involution `S * S = 1`. -/
def evenSubring (S : B) (hS : S * S = 1) : Subring B where
  carrier := { X : B | twist S X = X }
  one_mem' := by simp [twist, hS]
  mul_mem' {x y} hx hy := by
    change twist S (x * y) = x * y
    rw [twist_mul hS, hx, hy]
  zero_mem' := by simp [twist]
  add_mem' {x y} hx hy := by
    change twist S (x + y) = x + y
    rw [twist_add, hx, hy]
  neg_mem' {x} hx := by
    change twist S (-x) = -x
    dsimp [twist] at hx ⊢
    rw [mul_neg, neg_mul, hx]

/-- Odd additive subgroup `{ X : B | twist S X = -X }`. -/
def oddAddSubgroup (S : B) : AddSubgroup B where
  carrier := { X : B | twist S X = -X }
  zero_mem' := by simp [twist]
  add_mem' {x y} hx hy := by
    change twist S (x + y) = -(x + y)
    rw [twist_add, hx, hy]
    abel
  neg_mem' {x} hx := by
    change twist S (-x) = - -x
    dsimp [twist] at hx ⊢
    rw [mul_neg, neg_mul, hx]

/-- Odd superderivations map the even subring into the odd additive subgroup. -/
theorem oddSuperderivation_maps_even_to_odd {S : B} (hS : S * S = 1) {d : B →+ B}
    (hd : IsOddTwistSuperderivation S d) {x : B} (hx : x ∈ evenSubring S hS) :
    d x ∈ oddAddSubgroup S := by
  change twist S (d x) = -d x
  rw [hd.2 x]
  change twist S x = x at hx
  rw [hx]

/-- On the even subring, an odd superderivation restricts to an ordinary ungraded bimodule
derivation `evenSubring S hS →+ oddAddSubgroup S`. -/
def oddSuperderivationEvenBimoduleHom {S : B} (hS : S * S = 1) {d : B →+ B}
    (hd : IsOddTwistSuperderivation S d) :
    evenSubring S hS →+ oddAddSubgroup S where
  toFun x := ⟨d x.1, oddSuperderivation_maps_even_to_odd hS hd x.2⟩
  map_zero' := by apply Subtype.ext; exact d.map_zero
  map_add' x y := by apply Subtype.ext; exact d.map_add x.1 y.1

theorem oddSuperderivation_even_bimodule_leibniz {S : B} (hS : S * S = 1) {d : B →+ B}
    (hd : IsOddTwistSuperderivation S d) (x y : evenSubring S hS) :
    (oddSuperderivationEvenBimoduleHom hS hd (x * y) : B) =
      (oddSuperderivationEvenBimoduleHom hS hd x : B) * y.1 +
        x.1 * (oddSuperderivationEvenBimoduleHom hS hd y : B) := by
  change d (x.1 * y.1) = d x.1 * y.1 + x.1 * d y.1
  rw [hd.1 x.1 y.1]
  have hx : twist S x.1 = x.1 := x.2
  rw [hx]

/-- The super-anticommutator `{d₁, d₂}` preserves the even subring `evenSubring S hS`. -/
theorem superAnticomm_maps_even_to_even {S : B} (hS : S * S = 1) {d₁ d₂ : B →+ B}
    (hd₁ : IsOddTwistSuperderivation S d₁) (hd₂ : IsOddTwistSuperderivation S d₂)
    {x : B} (hx : x ∈ evenSubring S hS) :
    superAnticomm d₁ d₂ x ∈ evenSubring S hS := by
  change twist S (superAnticomm d₁ d₂ x) = superAnticomm d₁ d₂ x
  rw [superAnticomm_parity_even hd₁ hd₂ x]
  change twist S x = x at hx
  rw [hx]

/-- Restriction of `{d₁, d₂}` to `NonAssocDerivation.derivations ℤ (evenSubring S hS)`. -/
def superAnticommEvenRestrict {S : B} (hS : S * S = 1) {d₁ d₂ : B →+ B}
    (hd₁ : IsOddTwistSuperderivation S d₁) (hd₂ : IsOddTwistSuperderivation S d₂) :
    NonAssocDerivation.derivations ℤ (evenSubring S hS) :=
  let f : evenSubring S hS →+ evenSubring S hS :=
    { toFun := fun x => ⟨superAnticomm d₁ d₂ x.1, superAnticomm_maps_even_to_even hS hd₁ hd₂ x.2⟩
      map_zero' := by apply Subtype.ext; exact (superAnticomm d₁ d₂).map_zero
      map_add' := fun x y => by apply Subtype.ext; exact (superAnticomm d₁ d₂).map_add x.1 y.1 }
  ⟨addHomToIntEnd f, fun x y => by
    apply Subtype.ext
    exact superAnticomm_isLeibniz hS hd₁ hd₂ x.1 y.1⟩

end RingSuperderivations

section LinearSuperderivations

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- `R`-linear odd `twist S`-superderivation predicate. -/
def IsOddTwistSuperderivationLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (S : B) (d : Module.End R B) : Prop :=
  IsOddTwistSuperderivation S d.toAddMonoidHom

/-- `R`-linear super-anticommutator `{d₁, d₂} = d₁ ∘ d₂ + d₂ ∘ d₁`. -/
def superAnticommLinear (d₁ d₂ : Module.End R B) : Module.End R B :=
  d₁.comp d₂ + d₂.comp d₁

/-- Bundle `superAnticommLinear d₁ d₂` into `NonAssocDerivation.derivations R B`. -/
def superAnticommLinearToDerivations {S : B} (hS : S * S = 1) {d₁ d₂ : Module.End R B}
    (hd₁ : IsOddTwistSuperderivationLinear R S d₁)
    (hd₂ : IsOddTwistSuperderivationLinear R S d₂) :
    NonAssocDerivation.derivations R B :=
  ⟨superAnticommLinear d₁ d₂, fun x y =>
    superAnticomm_isLeibniz hS hd₁ hd₂ x y⟩

/-- Even subalgebra `{ X : B | twist S X = X } : Subalgebra R B`. -/
def evenSubalgebra (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (S : B) (hS : S * S = 1) : Subalgebra R B :=
  { evenSubring S hS with
    algebraMap_mem' := fun r => by
      change twist S (algebraMap R B r) = algebraMap R B r
      rw [Algebra.algebraMap_eq_smul_one]
      dsimp [twist]
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hS] }

/-- Restriction of `{d₁, d₂}` to `NonAssocDerivation.derivations R (evenSubalgebra R S hS)`. -/
def superAnticommLinearEvenRestrict {S : B} (hS : S * S = 1) {d₁ d₂ : Module.End R B}
    (hd₁ : IsOddTwistSuperderivationLinear R S d₁)
    (hd₂ : IsOddTwistSuperderivationLinear R S d₂) :
    NonAssocDerivation.derivations R (evenSubalgebra R S hS) :=
  ⟨{ toFun := fun x =>
        ⟨superAnticommLinear d₁ d₂ x.1, superAnticomm_maps_even_to_even hS hd₁ hd₂ x.2⟩
     map_add' := fun x y => by apply Subtype.ext; exact (superAnticommLinear d₁ d₂).map_add x.1 y.1
     map_smul' := fun r x => by apply Subtype.ext; exact (superAnticommLinear d₁ d₂).map_smul r x.1 },
   fun x y => by
     apply Subtype.ext
     exact superAnticomm_isLeibniz hS hd₁ hd₂ x.1 y.1⟩

/-- `oddDiff S N` as an `R`-linear endomorphism `Module.End R B`. -/
def oddDiffLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B] (S N : B) :
    Module.End R B where
  toFun := oddDiff S N
  map_add' := (oddDiffAddHom S N).map_add
  map_smul' r X := by
    dsimp [oddDiff, twist]
    rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_sub]

def differentialPlusLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A : B) : Module.End R B :=
  oddDiffLinear R (invS P) (conePlus P A)

def differentialMinusLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P C : B) : Module.End R B :=
  oddDiffLinear R (invS P) (coneMinus P C)

def differentialPhiLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A C : B) : Module.End R B :=
  differentialPlusLinear R P A + differentialMinusLinear R P C

def differentialJLinear (R : Type*) {B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A C : B) : Module.End R B :=
  differentialPlusLinear R P A - differentialMinusLinear R P C

theorem differentialPlusLinear_isOdd {P : B} (hP : P * P = P) (A : B) :
    IsOddTwistSuperderivationLinear R (invS P) (differentialPlusLinear R P A) :=
  differentialPlus_isOddTwistSuperderivation hP A

theorem differentialMinusLinear_isOdd {P : B} (hP : P * P = P) (C : B) :
    IsOddTwistSuperderivationLinear R (invS P) (differentialMinusLinear R P C) :=
  differentialMinus_isOddTwistSuperderivation hP C

theorem differentialJLinear_isOdd {P : B} (hP : P * P = P) (A C : B) :
    IsOddTwistSuperderivationLinear R (invS P) (differentialJLinear R P A C) :=
  differentialJ_isOddTwistSuperderivation hP A C

/-- F8.4 Onsager attachments on the `ℝ`-algebra `B` and its Peirce even subalgebra. -/
def peirceEvenSubalgebraOnsagerSystem {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1)
    (sys : OnsagerCasimirSystem (evenSubalgebra ℝ S hS)) (a : evenSubalgebra ℝ S hS) :
    OnsagerCasimirSystem (fullDerivationLieLane ℝ (evenSubalgebra ℝ S hS)).L :=
  inducedDerivationLaneOnsagerSystem sys (fullDerivationLieLane ℝ (evenSubalgebra ℝ S hS)) a

theorem peirceEvenSubalgebra_onsager_reciprocity {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) {n : ℕ}
    (PP : ParityOnsagerFormPairing
      (fullDerivationLieLane ℝ (evenSubalgebra ℝ S hS)).L (evenSubalgebra ℝ S hS) n)
    (ω η : DerivationOperatorForm
      (fullDerivationLieLane ℝ (evenSubalgebra ℝ S hS)) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity
    (fullDerivationLieLane ℝ (evenSubalgebra ℝ S hS)) PP ω η

end LinearSuperderivations

end PeirceSuperderivationLanes

/-! ## Section 10: Braided Derivations (`BraidedDerivation`, `GradedBraidedDerivation`, & `SylvesterGrading`, F8.3)

**Upstream `BraidedDerivation` Boundary Note:**
`InfoGeometry.Canonical.BraidedDerivation` (`BraidedDerivation.lean:18-35`) defines
`HomogeneousElement Γ A := { val : A, deg : Γ }` without a grading-membership predicate
`val ∈ grade deg`, and quantifies `BraidedDerivation.leibniz_homogeneous` universally
over all `a : HomogeneousElement Γ A`. Consequently, over any 2-torsion-free ring `R`
(such as `ℝ`) with a nontrivial sign bicharacter (such as `β i j = (-1)^(i*j)` on `ZMod 2`),
every `BraidedDerivation` of odd degree `deg = 1` is forced to vanish identically (since both
`⟨1, 0⟩` and `⟨1, 1⟩` satisfy `leibniz_homogeneous`), and the ungraded `BraidedDerivation`
span theorem could be formally bypassed by tagging arbitrary elements with degree `0`
(`⟨x, 0⟩`).

Below we:
1. Preserve all additive/ring/algebra/Onsager bridges for upstream `BraidedDerivation`
   (which faithfully capture degree-0 / trivial-braiding derivations); and
2. Provide the genuinely guarded `GradedBraidedDerivation` refinement indexed by
   `grade : Γ → AddSubgroup A` (requiring `a ∈ grade g`), together with an explicit
   `ZMod 2` Peirce grading bridge `oddTwistSuperderivationToGradedBraided` lifting every
   `IsOddTwistSuperderivationLinear R S d` (such as `differentialPlusLinear` on `M₂(ℝ)`)
   to a non-zero `deg = 1` `GradedBraidedDerivation`. -/

section BraidedDerivationLanes

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Canonical.SylvesterGrading
open InfoGeometry.Canonical.BraidedDerivation
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerFormsBridge

section BicharacterLemmas

variable {Γ R : Type*} [AddCommMonoid Γ] [Ring R]

theorem bicharacter_zero_left (B : GradingBicharacter Γ R) (h : Γ) : B.β 0 h = 1 := by
  have h0 : B.β (0 + 0) h = B.β 0 h := by rw [zero_add]
  rw [B.map_add_left] at h0
  exact mul_eq_left.mp h0

theorem bicharacter_zero_right (B : GradingBicharacter Γ R) (g : Γ) : B.β g 0 = 1 := by
  have h0 : B.β g (0 + 0) = B.β g 0 := by rw [add_zero]
  rw [B.map_add_right] at h0
  exact mul_eq_left.mp h0

/-- Predicate asserting that degree `d : Γ` braids trivially with every grade. -/
def IsTrivialBraidingDeg (B : GradingBicharacter Γ R) (d : Γ) : Prop :=
  ∀ g : Γ, B.β g d = 1

theorem isTrivialBraidingDeg_zero (B : GradingBicharacter Γ R) :
    IsTrivialBraidingDeg B 0 :=
  fun g => bicharacter_zero_right B g

/-- Submonoid of grades `g : Γ` that braid trivially with `d : Γ`. -/
def trivialBraidingGrades (B : GradingBicharacter Γ R) (d : Γ) : AddSubmonoid Γ where
  carrier := { g : Γ | B.β g d = 1 }
  zero_mem' := bicharacter_zero_left B d
  add_mem' {g₁ g₂} h₁ h₂ := by
    change B.β (g₁ + g₂) d = 1
    rw [B.map_add_left, h₁, h₂, mul_one]

end BicharacterLemmas

section BraidedRingBridges

variable {R Γ A : Type*} [Ring R] [AddCommMonoid Γ] [Ring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable {B : GradingBicharacter Γ R}

/-- Forget the braiding metadata to obtain the underlying `Module.End R A`. -/
def braidedDerivationToLinearMap (D : BraidedDerivation Γ R A B) : Module.End R A where
  toFun := D.toFun
  map_add' := D.map_add
  map_smul' := D.map_smul

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp]
theorem braidedDerivationToLinearMap_apply (D : BraidedDerivation Γ R A B) (x : A) :
    braidedDerivationToLinearMap D x = D x :=
  rfl

/-- Subring of elements `x : A` on which `D` acts by the ungraded left Leibniz rule. -/
def braidedLeibnizSubring (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0) : Subring A where
  carrier := { x : A | ∀ y : A, D (x * y) = D x * y + x * D y }
  zero_mem' y := by
    have h0 : D 0 = 0 := (braidedDerivationToLinearMap D).map_zero
    simp only [zero_mul]
    rw [h0, zero_mul, zero_add]
  one_mem' y := by
    rw [one_mul, h1, zero_mul, zero_add, one_mul]
  add_mem' {x₁ x₂} hx₁ hx₂ y := by
    rw [add_mul, D.map_add, hx₁ y, hx₂ y, D.map_add, add_mul, add_mul]
    abel
  neg_mem' {x} hx y := by
    have hneg : ∀ z : A, D (-z) = -D z := (braidedDerivationToLinearMap D).map_neg
    rw [neg_mul, hneg, hx y, hneg, neg_mul, neg_mul, neg_add]
  mul_mem' {x₁ x₂} hx₁ hx₂ y := by
    rw [mul_assoc, hx₁ (x₂ * y), hx₂ y, mul_add, ← mul_assoc, hx₁ x₂, add_mul, mul_assoc]
    simp only [mul_assoc]
    abel

/-- Set of carrier values extracted from a set of homogeneous elements with trivial braiding. -/
def trivialBraidingGenerators (H : Set (HomogeneousElement Γ A))
    (B : GradingBicharacter Γ R) (d : Γ) : Set A :=
  HomogeneousElement.val '' { a ∈ H | B.β a.deg d = 1 }

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Homogeneous elements whose grade braids trivially with `D.deg` lie in the ungraded Leibniz locus. -/
theorem braidedDerivation_leibniz_of_trivial_grade (D : BraidedDerivation Γ R A B)
    {a : HomogeneousElement Γ A} (ha : B.β a.deg D.deg = 1) (y : A) :
    D (a.val * y) = D a.val * y + a.val * D y := by
  rw [D.leibniz_homogeneous a y, ha, Units.val_one, one_smul]

omit [SMulCommClass R A A] in
/-- Span bridge (requires no `h1`): if `A` is `R`-spanned by homogeneous elements with trivial
braiding against `D.deg`, then `D` satisfies `NonAssocDerivation.IsLeibniz R A`. -/
theorem braidedDerivation_isLeibniz_of_span (D : BraidedDerivation Γ R A B)
    (H : Set (HomogeneousElement Γ A))
    (htriv : ∀ a ∈ H, B.β a.deg D.deg = 1)
    (hspan : Submodule.span R (HomogeneousElement.val '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ Submodule.span R (HomogeneousElement.val '' H) := by
    rw [hspan]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    exact braidedDerivation_leibniz_of_trivial_grade D (htriv a ha) y
  · have h0 : D 0 = 0 := (braidedDerivationToLinearMap D).map_zero
    simp only [braidedDerivationToLinearMap_apply, zero_mul]
    rw [h0, zero_mul, zero_add]
  · intro u v _ _ hu hv
    simp only [braidedDerivationToLinearMap_apply] at hu hv ⊢
    rw [add_mul, D.map_add, hu, hv, D.map_add, add_mul, add_mul]
    abel
  · intro r u _ hu
    simp only [braidedDerivationToLinearMap_apply] at hu ⊢
    rw [smul_mul_assoc, D.map_smul, hu, D.map_smul, smul_add, smul_mul_assoc, smul_mul_assoc]

omit [SMulCommClass R A A] in
theorem braidedDerivation_isLeibniz_of_trivialDeg_of_span (D : BraidedDerivation Γ R A B)
    (htriv : IsTrivialBraidingDeg B D.deg)
    (H : Set (HomogeneousElement Γ A))
    (hspan : Submodule.span R (HomogeneousElement.val '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D) :=
  braidedDerivation_isLeibniz_of_span D H (fun a _ => htriv a.deg) hspan

omit [SMulCommClass R A A] in
theorem braidedDerivation_isLeibniz_of_deg_zero_of_span (D : BraidedDerivation Γ R A B)
    (hdeg : D.deg = 0)
    (H : Set (HomogeneousElement Γ A))
    (hspan : Submodule.span R (HomogeneousElement.val '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D) :=
  braidedDerivation_isLeibniz_of_trivialDeg_of_span D
    (hdeg ▸ isTrivialBraidingDeg_zero B) H hspan

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Subring closure of trivial-braiding homogeneous elements lies inside `braidedLeibnizSubring D h1`. -/
theorem subring_closure_le_braidedLeibnizSubring (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (H : Set (HomogeneousElement Γ A)) :
    Subring.closure (trivialBraidingGenerators H B D.deg) ≤ braidedLeibnizSubring D h1 := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨a, ⟨_, htriv⟩, rfl⟩
  exact braidedDerivation_leibniz_of_trivial_grade D htriv

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem braidedDerivation_isLeibniz_of_subring_closure_eq_top
    (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (H : Set (HomogeneousElement Γ A))
    (htop : Subring.closure (trivialBraidingGenerators H B D.deg) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ braidedLeibnizSubring D h1 := by
    have hmem : x ∈ Subring.closure (trivialBraidingGenerators H B D.deg) := by
      rw [htop]; trivial
    exact subring_closure_le_braidedLeibnizSubring D h1 H hmem
  exact hx y

/-- Embed any ungraded-Leibniz `BraidedDerivation` over `[Ring R]` into `NonAssocDerivation.derivations ℤ A`. -/
def braidedDerivationToIntDerivations (D : BraidedDerivation Γ R A B)
    (hL : NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D)) :
    NonAssocDerivation.derivations ℤ A :=
  ⟨(braidedDerivationToLinearMap D).restrictScalars ℤ, hL⟩

/-- Restrict a `D`-invariant subring `S ≤ braidedLeibnizSubring D h1` to `NonAssocDerivation.derivations ℤ S`. -/
def braidedDerivationRestrictSubring (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (S : Subring A) (hS : S ≤ braidedLeibnizSubring D h1)
    (hpres : ∀ x ∈ S, D x ∈ S) :
    NonAssocDerivation.derivations ℤ S :=
  let f : S →+ S :=
    { toFun := fun x => ⟨D x.1, hpres x.1 x.2⟩
      map_zero' := by apply Subtype.ext; exact (braidedDerivationToLinearMap D).map_zero
      map_add' := fun x y => by apply Subtype.ext; exact D.map_add x.1 y.1 }
  ⟨addHomToIntEnd f, fun x y => by
    apply Subtype.ext
    exact hS x.2 y.1⟩

end BraidedRingBridges

section BraidedCommRingBridges

variable {R Γ A : Type*} [CommRing R] [AddCommMonoid Γ] [Ring A] [Algebra R A]
variable {B : GradingBicharacter Γ R}

/-- Subalgebra of elements `x : A` on which `D` acts by the ungraded left Leibniz rule. -/
def braidedLeibnizSubalgebra (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0) : Subalgebra R A :=
  { braidedLeibnizSubring D h1 with
    algebraMap_mem' := fun r y => by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, D.map_smul, D.map_smul, h1,
        smul_zero, zero_mul, zero_add, smul_mul_assoc, one_mul] }

/-- `Algebra.adjoin` of trivial-braiding homogeneous elements lies inside `braidedLeibnizSubalgebra D h1`. -/
theorem algebra_adjoin_le_braidedLeibnizSubalgebra (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (H : Set (HomogeneousElement Γ A)) :
    Algebra.adjoin R (trivialBraidingGenerators H B D.deg) ≤ braidedLeibnizSubalgebra D h1 := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨a, ⟨_, htriv⟩, rfl⟩
  exact braidedDerivation_leibniz_of_trivial_grade D htriv

theorem braidedDerivation_isLeibniz_of_algebra_adjoin_eq_top
    (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (H : Set (HomogeneousElement Γ A))
    (htop : Algebra.adjoin R (trivialBraidingGenerators H B D.deg) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ braidedLeibnizSubalgebra D h1 := by
    have hmem : x ∈ Algebra.adjoin R (trivialBraidingGenerators H B D.deg) := by
      rw [htop]; trivial
    exact algebra_adjoin_le_braidedLeibnizSubalgebra D h1 H hmem
  exact hx y

/-- Embed any ungraded-Leibniz `BraidedDerivation` over `[CommRing R]` into `NonAssocDerivation.derivations R A`. -/
def braidedDerivationToDerivations (D : BraidedDerivation Γ R A B)
    (hL : NonAssocDerivation.IsLeibniz R A (braidedDerivationToLinearMap D)) :
    NonAssocDerivation.derivations R A :=
  ⟨braidedDerivationToLinearMap D, hL⟩

/-- Restrict a `D`-invariant subalgebra `S ≤ braidedLeibnizSubalgebra D h1` to
`NonAssocDerivation.derivations R S`. -/
def braidedDerivationRestrictSubalgebra (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (S : Subalgebra R A) (hS : S ≤ braidedLeibnizSubalgebra D h1)
    (hpres : ∀ x ∈ S, D x ∈ S) :
    NonAssocDerivation.derivations R S :=
  ⟨{ toFun := fun x => ⟨D x.1, hpres x.1 x.2⟩
     map_add' := fun x y => by apply Subtype.ext; exact D.map_add x.1 y.1
     map_smul' := fun r x => by apply Subtype.ext; exact D.map_smul r x.1 },
   fun x y => by
     apply Subtype.ext
     exact hS x.2 y.1⟩

/-- Specialize subalgebra restriction to `Algebra.adjoin R (trivialBraidingGenerators H B D.deg)` when `D`-invariant. -/
def braidedDerivationRestrictTrivialAdjoin (D : BraidedDerivation Γ R A B) (h1 : D 1 = 0)
    (H : Set (HomogeneousElement Γ A))
    (hpres : ∀ x ∈ Algebra.adjoin R (trivialBraidingGenerators H B D.deg),
      D x ∈ Algebra.adjoin R (trivialBraidingGenerators H B D.deg)) :
    NonAssocDerivation.derivations R (Algebra.adjoin R (trivialBraidingGenerators H B D.deg)) :=
  braidedDerivationRestrictSubalgebra D h1
    (Algebra.adjoin R (trivialBraidingGenerators H B D.deg))
    (algebra_adjoin_le_braidedLeibnizSubalgebra D h1 H) hpres

/-- On trivial-braiding homogeneous elements, `innerBraidedOp B x a` equals the ordinary commutator. -/
theorem innerBraidedOp_eq_commutator_of_trivial (B : GradingBicharacter Γ R)
    (x a : HomogeneousElement Γ A) (htriv : B.β a.deg x.deg = 1) :
    innerBraidedOp B x a = x.val * a.val - a.val * x.val := by
  dsimp [innerBraidedOp]
  rw [htriv, Units.val_one, one_smul]

/-- F8.4 Onsager attachment for `ℝ`-linear braided derivation lanes on `A` and on invariant `Subalgebra ℝ A`. -/
def braidedAlgebraOnsagerSystem {Γ A : Type*} [AddCommMonoid Γ] [Ring A] [Algebra ℝ A]
    (sys : OnsagerCasimirSystem A) (a : A) :
    OnsagerCasimirSystem (fullDerivationLieLane ℝ A).L :=
  inducedDerivationLaneOnsagerSystem sys (fullDerivationLieLane ℝ A) a

theorem braidedAlgebra_onsager_reciprocity {Γ A : Type*} [AddCommMonoid Γ] [Ring A] [Algebra ℝ A]
    {n : ℕ}
    (PP : ParityOnsagerFormPairing (fullDerivationLieLane ℝ A).L A n)
    (ω η : DerivationOperatorForm (fullDerivationLieLane ℝ A) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (fullDerivationLieLane ℝ A) PP ω η

def braidedSubalgebraOnsagerSystem {Γ A : Type*} [AddCommMonoid Γ] [Ring A] [Algebra ℝ A]
    (S : Subalgebra ℝ A)
    (sys : OnsagerCasimirSystem S) (a : S) :
    OnsagerCasimirSystem (fullDerivationLieLane ℝ S).L :=
  inducedDerivationLaneOnsagerSystem sys (fullDerivationLieLane ℝ S) a

theorem braidedSubalgebra_onsager_reciprocity {Γ A : Type*}
    [AddCommMonoid Γ] [Ring A] [Algebra ℝ A]
    (S : Subalgebra ℝ A) {n : ℕ}
    (PP : ParityOnsagerFormPairing (fullDerivationLieLane ℝ S).L S n)
    (ω η : DerivationOperatorForm (fullDerivationLieLane ℝ S) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (fullDerivationLieLane ℝ S) PP ω η

end BraidedCommRingBridges

section GuardedGradedBraidedDerivations

/-- Guarded braided derivation of degree `deg : Γ` on an `R`-module ring `A` graded by
`grade : Γ → AddSubgroup A`. Unlike upstream `BraidedDerivation.leibniz_homogeneous`,
the graded Leibniz rule is enforced **only** for `a ∈ grade g`, preventing zero-grade
tag bypasses (`⟨x, 0⟩`) and admitting genuine non-zero odd-degree derivations. -/
structure GradedBraidedDerivation
    (Γ : Type*) [AddCommMonoid Γ] (R : Type*) [Ring R]
    (A : Type*) [Ring A] [Module R A]
    (B : GradingBicharacter Γ R) (grade : Γ → AddSubgroup A) where
  toFun : A → A
  deg : Γ
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (r : R) (x : A), toFun (r • x) = r • toFun x
  leibniz_graded : ∀ (g : Γ) (a : A), a ∈ grade g → ∀ b : A,
    toFun (a * b) = toFun a * b + (B.β g deg : R) • (a * toFun b)

instance {Γ R A : Type*} [AddCommMonoid Γ] [Ring R] [Ring A] [Module R A]
    (B : GradingBicharacter Γ R) (grade : Γ → AddSubgroup A) :
    CoeFun (GradedBraidedDerivation Γ R A B grade) (fun _ => A → A) where
  coe D := D.toFun

section GuardedRingBridges

variable {R Γ A : Type*} [Ring R] [AddCommMonoid Γ] [Ring A] [Module R A]
variable {B : GradingBicharacter Γ R} {grade : Γ → AddSubgroup A}

/-- Forget the grading metadata to obtain the underlying `Module.End R A`. -/
def gradedBraidedDerivationToLinearMap
    (D : GradedBraidedDerivation Γ R A B grade) : Module.End R A where
  toFun := D.toFun
  map_add' := D.map_add
  map_smul' := D.map_smul

@[simp]
theorem gradedBraidedDerivationToLinearMap_apply
    (D : GradedBraidedDerivation Γ R A B grade) (x : A) :
    gradedBraidedDerivationToLinearMap D x = D x :=
  rfl

/-- Embed any unguarded `BraidedDerivation` into `GradedBraidedDerivation` for any `grade`. -/
def braidedDerivationToGraded
    (D : BraidedDerivation Γ R A B) (grade : Γ → AddSubgroup A) :
    GradedBraidedDerivation Γ R A B grade where
  toFun := D.toFun
  deg := D.deg
  map_add := D.map_add
  map_smul := D.map_smul
  leibniz_graded := fun g a _ b => D.leibniz_homogeneous ⟨a, g⟩ b

theorem braidedDerivationToGraded_injective :
    Function.Injective (fun D : BraidedDerivation Γ R A B => braidedDerivationToGraded D grade) := by
  intro D₁ D₂ h
  cases D₁
  cases D₂
  cases h
  rfl

/-- Subring of elements `x : A` on which `D` acts by the ungraded left Leibniz rule. -/
def gradedBraidedLeibnizSubring (D : GradedBraidedDerivation Γ R A B grade)
    (h1 : D 1 = 0) : Subring A where
  carrier := { x : A | ∀ y : A, D (x * y) = D x * y + x * D y }
  zero_mem' y := by
    have h0 : D 0 = 0 := (gradedBraidedDerivationToLinearMap D).map_zero
    simp only [zero_mul]
    rw [h0, zero_mul, zero_add]
  one_mem' y := by
    rw [one_mul, h1, zero_mul, zero_add, one_mul]
  add_mem' {x₁ x₂} hx₁ hx₂ y := by
    rw [add_mul, D.map_add, hx₁ y, hx₂ y, D.map_add, add_mul, add_mul]
    abel
  neg_mem' {x} hx y := by
    have hneg : ∀ z : A, D (-z) = -D z := (gradedBraidedDerivationToLinearMap D).map_neg
    rw [neg_mul, hneg, hx y, hneg, neg_mul, neg_mul, neg_add]
  mul_mem' {x₁ x₂} hx₁ hx₂ y := by
    rw [mul_assoc, hx₁ (x₂ * y), hx₂ y, mul_add, ← mul_assoc, hx₁ x₂, add_mul, mul_assoc]
    simp only [mul_assoc]
    abel

/-- Guarded set of generators: `p.2` MUST genuinely belong to `grade p.1` AND braid trivially with `d`. -/
def gradedTrivialBraidingGenerators (H : Set (Σ _g : Γ, A))
    (B : GradingBicharacter Γ R) (grade : Γ → AddSubgroup A) (d : Γ) : Set A :=
  Sigma.snd '' { p ∈ H | p.2 ∈ grade p.1 ∧ B.β p.1 d = 1 }

/-- Homogeneous elements in `grade g` whose grade braids trivially with `D.deg` satisfy ungraded Leibniz. -/
theorem gradedBraidedDerivation_leibniz_of_trivial_grade
    (D : GradedBraidedDerivation Γ R A B grade)
    {g : Γ} {a : A} (ha : a ∈ grade g) (htriv : B.β g D.deg = 1) (y : A) :
    D (a * y) = D a * y + a * D y := by
  rw [D.leibniz_graded g a ha y, htriv, Units.val_one, one_smul]

/-- Guarded span bridge: requires actual membership `p.2 ∈ grade p.1` for every `p ∈ H`. -/
theorem gradedBraidedDerivation_isLeibniz_of_span [IsScalarTower R A A]
    (D : GradedBraidedDerivation Γ R A B grade)
    (H : Set (Σ _g : Γ, A))
    (hmem : ∀ p ∈ H, p.2 ∈ grade p.1)
    (htriv : ∀ p ∈ H, B.β p.1 D.deg = 1)
    (hspan : Submodule.span R (Sigma.snd '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ Submodule.span R (Sigma.snd '' H) := by
    rw [hspan]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, hp, rfl⟩
    exact gradedBraidedDerivation_leibniz_of_trivial_grade D (hmem p hp) (htriv p hp) y
  · have h0 : D 0 = 0 := (gradedBraidedDerivationToLinearMap D).map_zero
    simp only [gradedBraidedDerivationToLinearMap_apply, zero_mul]
    rw [h0, zero_mul, zero_add]
  · intro u v _ _ hu hv
    simp only [gradedBraidedDerivationToLinearMap_apply] at hu hv ⊢
    rw [add_mul, D.map_add, hu, hv, D.map_add, add_mul, add_mul]
    abel
  · intro r u _ hu
    simp only [gradedBraidedDerivationToLinearMap_apply] at hu ⊢
    rw [smul_mul_assoc, D.map_smul, hu, D.map_smul, smul_add, smul_mul_assoc, smul_mul_assoc]

theorem gradedBraidedDerivation_isLeibniz_of_trivialDeg_of_span [IsScalarTower R A A]
    (D : GradedBraidedDerivation Γ R A B grade)
    (htriv : IsTrivialBraidingDeg B D.deg)
    (H : Set (Σ _g : Γ, A))
    (hmem : ∀ p ∈ H, p.2 ∈ grade p.1)
    (hspan : Submodule.span R (Sigma.snd '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D) :=
  gradedBraidedDerivation_isLeibniz_of_span D H hmem (fun p _ => htriv p.1) hspan

theorem gradedBraidedDerivation_isLeibniz_of_deg_zero_of_span [IsScalarTower R A A]
    (D : GradedBraidedDerivation Γ R A B grade)
    (hdeg : D.deg = 0)
    (H : Set (Σ _g : Γ, A))
    (hmem : ∀ p ∈ H, p.2 ∈ grade p.1)
    (hspan : Submodule.span R (Sigma.snd '' H) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D) :=
  gradedBraidedDerivation_isLeibniz_of_trivialDeg_of_span D
    (hdeg ▸ isTrivialBraidingDeg_zero B) H hmem hspan

/-- Subring closure of genuinely graded, trivial-braiding generators lies inside `gradedBraidedLeibnizSubring`. -/
theorem subring_closure_le_gradedBraidedLeibnizSubring
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (H : Set (Σ _g : Γ, A)) :
    Subring.closure (gradedTrivialBraidingGenerators H B grade D.deg) ≤
      gradedBraidedLeibnizSubring D h1 := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨p, ⟨_, hmem, htriv⟩, rfl⟩
  exact gradedBraidedDerivation_leibniz_of_trivial_grade D hmem htriv

theorem gradedBraidedDerivation_isLeibniz_of_subring_closure_eq_top
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (H : Set (Σ _g : Γ, A))
    (htop : Subring.closure (gradedTrivialBraidingGenerators H B grade D.deg) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ gradedBraidedLeibnizSubring D h1 := by
    have hmem : x ∈ Subring.closure (gradedTrivialBraidingGenerators H B grade D.deg) := by
      rw [htop]; trivial
    exact subring_closure_le_gradedBraidedLeibnizSubring D h1 H hmem
  exact hx y

/-- Embed any ungraded-Leibniz `GradedBraidedDerivation` over `[Ring R]` into `NonAssocDerivation.derivations ℤ A`. -/
def gradedBraidedDerivationToIntDerivations
    (D : GradedBraidedDerivation Γ R A B grade)
    (hL : NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D)) :
    NonAssocDerivation.derivations ℤ A :=
  ⟨(gradedBraidedDerivationToLinearMap D).restrictScalars ℤ, hL⟩

/-- Restrict a `D`-invariant subring `S ≤ gradedBraidedLeibnizSubring D h1` to `NonAssocDerivation.derivations ℤ S`. -/
def gradedBraidedDerivationRestrictSubring
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (S : Subring A) (hS : S ≤ gradedBraidedLeibnizSubring D h1)
    (hpres : ∀ x ∈ S, D x ∈ S) :
    NonAssocDerivation.derivations ℤ S :=
  let f : S →+ S :=
    { toFun := fun x => ⟨D x.1, hpres x.1 x.2⟩
      map_zero' := by apply Subtype.ext; exact (gradedBraidedDerivationToLinearMap D).map_zero
      map_add' := fun x y => by apply Subtype.ext; exact D.map_add x.1 y.1 }
  ⟨addHomToIntEnd f, fun x y => by
    apply Subtype.ext
    exact hS x.2 y.1⟩

end GuardedRingBridges

section GuardedCommRingBridges

variable {R Γ A : Type*} [CommRing R] [AddCommMonoid Γ] [Ring A] [Algebra R A]
variable {B : GradingBicharacter Γ R} {grade : Γ → AddSubgroup A}

/-- Subalgebra of elements `x : A` on which `D` acts by the ungraded left Leibniz rule. -/
def gradedBraidedLeibnizSubalgebra (D : GradedBraidedDerivation Γ R A B grade)
    (h1 : D 1 = 0) : Subalgebra R A :=
  { gradedBraidedLeibnizSubring D h1 with
    algebraMap_mem' := fun r y => by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, D.map_smul, D.map_smul, h1,
        smul_zero, zero_mul, zero_add, smul_mul_assoc, one_mul] }

/-- `Algebra.adjoin` of genuinely graded trivial-braiding generators lies inside `gradedBraidedLeibnizSubalgebra`. -/
theorem algebra_adjoin_le_gradedBraidedLeibnizSubalgebra
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (H : Set (Σ _g : Γ, A)) :
    Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg) ≤
      gradedBraidedLeibnizSubalgebra D h1 := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, ⟨_, hmem, htriv⟩, rfl⟩
  exact gradedBraidedDerivation_leibniz_of_trivial_grade D hmem htriv

theorem gradedBraidedDerivation_isLeibniz_of_algebra_adjoin_eq_top
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (H : Set (Σ _g : Γ, A))
    (htop : Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg) = ⊤) :
    NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D) := by
  intro x y
  have hx : x ∈ gradedBraidedLeibnizSubalgebra D h1 := by
    have hmem : x ∈ Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg) := by
      rw [htop]; trivial
    exact algebra_adjoin_le_gradedBraidedLeibnizSubalgebra D h1 H hmem
  exact hx y

/-- Embed any ungraded-Leibniz `GradedBraidedDerivation` over `[CommRing R]` into `NonAssocDerivation.derivations R A`. -/
def gradedBraidedDerivationToDerivations
    (D : GradedBraidedDerivation Γ R A B grade)
    (hL : NonAssocDerivation.IsLeibniz R A (gradedBraidedDerivationToLinearMap D)) :
    NonAssocDerivation.derivations R A :=
  ⟨gradedBraidedDerivationToLinearMap D, hL⟩

/-- Restrict a `D`-invariant subalgebra `S ≤ gradedBraidedLeibnizSubalgebra D h1` to
`NonAssocDerivation.derivations R S`. -/
def gradedBraidedDerivationRestrictSubalgebra
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (S : Subalgebra R A) (hS : S ≤ gradedBraidedLeibnizSubalgebra D h1)
    (hpres : ∀ x ∈ S, D x ∈ S) :
    NonAssocDerivation.derivations R S :=
  ⟨{ toFun := fun x => ⟨D x.1, hpres x.1 x.2⟩
     map_add' := fun x y => by apply Subtype.ext; exact D.map_add x.1 y.1
     map_smul' := fun r x => by apply Subtype.ext; exact D.map_smul r x.1 },
   fun x y => by
     apply Subtype.ext
     exact hS x.2 y.1⟩

/-- Specialize subalgebra restriction to `Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg)`. -/
def gradedBraidedDerivationRestrictTrivialAdjoin
    (D : GradedBraidedDerivation Γ R A B grade) (h1 : D 1 = 0)
    (H : Set (Σ _g : Γ, A))
    (hpres : ∀ x ∈ Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg),
      D x ∈ Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg)) :
    NonAssocDerivation.derivations R
      (Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg)) :=
  gradedBraidedDerivationRestrictSubalgebra D h1
    (Algebra.adjoin R (gradedTrivialBraidingGenerators H B grade D.deg))
    (algebra_adjoin_le_gradedBraidedLeibnizSubalgebra D h1 H) hpres

/-- Faithful `DerivationLieLane R A` for the guarded `GradedBraidedDerivation` spine. -/
def gradedBraidedDerivationLieLane (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    DerivationLieLane R A :=
  fullDerivationLieLane R A

/-- F8.4 Onsager attachment for the guarded `GradedBraidedDerivation` lane over `ℝ`. -/
def gradedBraidedAlgebraOnsagerSystem {A : Type*} [Ring A] [Algebra ℝ A]
    (sys : OnsagerCasimirSystem A) (a : A) :
    OnsagerCasimirSystem (gradedBraidedDerivationLieLane ℝ A).L :=
  inducedDerivationLaneOnsagerSystem sys (gradedBraidedDerivationLieLane ℝ A) a

theorem gradedBraidedAlgebra_onsager_reciprocity {A : Type*} [Ring A] [Algebra ℝ A] {n : ℕ}
    (PP : ParityOnsagerFormPairing (gradedBraidedDerivationLieLane ℝ A).L A n)
    (ω η : DerivationOperatorForm (gradedBraidedDerivationLieLane ℝ A) n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity (gradedBraidedDerivationLieLane ℝ A) PP ω η

end GuardedCommRingBridges

section ZMod2PeirceOddLink

open InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations

private theorem zmod2_eq_zero_or_one (g : ZMod 2) : g = 0 ∨ g = 1 := by
  fin_cases g
  · left; rfl
  · right; rfl

/-- Sign unit `(-1)^(i*j)` in `Rˣ` for `i j : ZMod 2`. -/
def zmod2SignUnit (R : Type*) [Ring R] (i j : ZMod 2) : Rˣ :=
  if i = 1 ∧ j = 1 then -1 else 1

/-- Canonical `ZMod 2` sign bicharacter `β i j = (-1)^(i*j)` over any ring `R`. -/
def zmod2SignBicharacter (R : Type*) [Ring R] : GradingBicharacter (ZMod 2) R where
  β := zmod2SignUnit R
  map_add_left g₁ g₂ h := by
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rcases zmod2_eq_zero_or_one g₁ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one g₂ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one h with rfl | rfl <;>
      simp [zmod2SignUnit, h01, h11]
  map_add_right g h₁ h₂ := by
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rcases zmod2_eq_zero_or_one g with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one h₁ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one h₂ with rfl | rfl <;>
      simp [zmod2SignUnit, h01, h11]

@[simp]
theorem zmod2SignBicharacter_0_0 (R : Type*) [Ring R] :
    ((zmod2SignBicharacter R).β 0 0 : R) = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [zmod2SignBicharacter, zmod2SignUnit, h01]

@[simp]
theorem zmod2SignBicharacter_0_1 (R : Type*) [Ring R] :
    ((zmod2SignBicharacter R).β 0 1 : R) = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [zmod2SignBicharacter, zmod2SignUnit, h01]

@[simp]
theorem zmod2SignBicharacter_1_0 (R : Type*) [Ring R] :
    ((zmod2SignBicharacter R).β 1 0 : R) = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [zmod2SignBicharacter, zmod2SignUnit, h01]

@[simp]
theorem zmod2SignBicharacter_1_1 (R : Type*) [Ring R] :
    ((zmod2SignBicharacter R).β 1 1 : R) = -1 := by
  simp [zmod2SignBicharacter, zmod2SignUnit]

/-- Peirce `ZMod 2` grading `0 ↦ evenSubring S hS`, `1 ↦ oddAddSubgroup S`. -/
def peirceZMod2Grade {B : Type*} [Ring B] (S : B) (hS : S * S = 1) :
    ZMod 2 → AddSubgroup B
  | 0 => (evenSubring S hS).toAddSubgroup
  | 1 => oddAddSubgroup S

@[simp]
theorem peirceZMod2Grade_zero {B : Type*} [Ring B] (S : B) (hS : S * S = 1) :
    peirceZMod2Grade S hS 0 = (evenSubring S hS).toAddSubgroup :=
  rfl

@[simp]
theorem peirceZMod2Grade_one {B : Type*} [Ring B] (S : B) (hS : S * S = 1) :
    peirceZMod2Grade S hS 1 = oddAddSubgroup S :=
  rfl

/-- Lift any `R`-linear odd Peirce superderivation `IsOddTwistSuperderivationLinear R S d`
to a genuine degree-`1` `GradedBraidedDerivation (ZMod 2) R B (zmod2SignBicharacter R) (peirceZMod2Grade S hS)`.
Over `M₂(ℝ)` with `differentialPlusLinear`, this yields a concrete non-zero `deg = 1`
`GradedBraidedDerivation`. -/
def oddTwistSuperderivationToGradedBraided
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {S : B} (hS : S * S = 1) (d : Module.End R B)
    (hd : IsOddTwistSuperderivationLinear R S d) :
    GradedBraidedDerivation (ZMod 2) R B (zmod2SignBicharacter R)
      (peirceZMod2Grade S hS) where
  toFun := d
  deg := 1
  map_add := d.map_add
  map_smul := d.map_smul
  leibniz_graded := fun g a ha b => by
    have hleib : d (a * b) = d a * b + twist S a * d b := hd.1 a b
    rcases zmod2_eq_zero_or_one g with rfl | rfl
    · have ha0 : twist S a = a := ha
      rw [zmod2SignBicharacter_0_1, one_smul, hleib, ha0]
    · have ha1 : twist S a = -a := ha
      rw [zmod2SignBicharacter_1_1, neg_one_smul, hleib, ha1, neg_mul]

@[simp]
theorem oddTwistSuperderivationToGradedBraided_deg
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {S : B} (hS : S * S = 1) (d : Module.End R B)
    (hd : IsOddTwistSuperderivationLinear R S d) :
    (oddTwistSuperderivationToGradedBraided hS d hd).deg = 1 :=
  rfl

@[simp]
theorem oddTwistSuperderivationToGradedBraided_apply
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {S : B} (hS : S * S = 1) (d : Module.End R B)
    (hd : IsOddTwistSuperderivationLinear R S d) (x : B) :
    oddTwistSuperderivationToGradedBraided hS d hd x = d x :=
  rfl

theorem oddTwistSuperderivationToGradedBraided_injective
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {S : B} (hS : S * S = 1)
    {d₁ d₂ : Module.End R B}
    (hd₁ : IsOddTwistSuperderivationLinear R S d₁)
    (hd₂ : IsOddTwistSuperderivationLinear R S d₂)
    (h : oddTwistSuperderivationToGradedBraided hS d₁ hd₁ =
      oddTwistSuperderivationToGradedBraided hS d₂ hd₂) :
    d₁ = d₂ := by
  ext x
  exact congrArg (fun D => D x) h

end ZMod2PeirceOddLink

end GuardedGradedBraidedDerivations

end BraidedDerivationLanes

end InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge
