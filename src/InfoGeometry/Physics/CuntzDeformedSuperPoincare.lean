import InfoGeometry.Physics.SupergradedCuntzBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SuperPoincareOperatorCharges
import InfoGeometry.Physics.LorentzBoostMinkowski
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import Mathlib.Tactic

/-!
# Cuntz-deformed supergrading and operator super-Poincaré presentation

This file keeps the requested bridge algebraic and finite:

* the Cuntz/BdG affine deformation from `SupergradedCuntzBdG` is reused;
* odd--odd deformation endpoints are proved as Lie bracket (`β=0`) and
  anticommutator/Jordan product (`β=1`);
* the super-Poincaré relation is operator-valued: `{Q,Qbar}=2P` is a matrix
  equation in an operator spinor presentation, not a scalar central charge;
* Lorentz covariance is stated as transport of the defining operator equation
  by explicit left/right spin matrices;
* the Poincaré group layer is a theorem-honest finite presentation: a Lorentz
  map preserving the Minkowski pairing plus translations, with composition and
  mass-Casimir preservation.
-/

noncomputable section

namespace InfoGeometry.Physics.CuntzDeformedSuperPoincare

open Matrix
open scoped BigOperators

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ## Cuntz-deformed superbracket endpoints -/

/-- The deformation parameter `β=0` gives the ordinary Lie/commutator sector. -/
theorem cuntzDeformed_odd_odd_beta_zero {A : Type*} [Semiring A] [Algebra ℂ A]
    (x y : A) :
    SupergradedCuntzBdG.affineSuperBracket 0
      SupergradedCuntzBdG.Z2Parity.odd SupergradedCuntzBdG.Z2Parity.odd x y =
      SupergradedCuntzBdG.lieBracket x y := by
  exact SupergradedCuntzBdG.affineSuperBracket_zero
    SupergradedCuntzBdG.Z2Parity.odd SupergradedCuntzBdG.Z2Parity.odd x y

/-- The deformation parameter `β=1` gives the odd--odd anticommutator/Jordan sector. -/
theorem cuntzDeformed_odd_odd_beta_one {A : Type*} [Semiring A] [Algebra ℂ A]
    (x y : A) :
    SupergradedCuntzBdG.affineSuperBracket 1
      SupergradedCuntzBdG.Z2Parity.odd SupergradedCuntzBdG.Z2Parity.odd x y =
      SupergradedCuntzBdG.jordanProduct x y := by
  exact SupergradedCuntzBdG.affineSuperBracket_odd_odd_one x y

/-- The odd--odd Cuntz deformation is exactly the affine Lie/Jordan split. -/
theorem cuntzDeformed_odd_odd_lie_jordan_split {A : Type*} [Semiring A] [Algebra ℂ A]
    (β : ℂ) (x y : A) :
    SupergradedCuntzBdG.affineSuperBracket β
      SupergradedCuntzBdG.Z2Parity.odd SupergradedCuntzBdG.Z2Parity.odd x y =
      (1 - β : ℂ) • SupergradedCuntzBdG.lieBracket x y +
        β • SupergradedCuntzBdG.jordanProduct x y := by
  exact SupergradedCuntzBdG.affineSuperBracket_odd_odd_jordan_lie_split β x y

/-! ## Operator-valued chiral super-Poincaré spinor presentation -/

/-- Matrix anticommutator, reusing the existing operator anticommutator. -/
def antiM (X Y : M2C) : M2C := SuperPoincareOperatorCharges.anti X Y

/-- Spinorial operator presentation of `{Q,Qbar}=2P`.

`antiQQbar` records the operator-valued anticommutator matrix.  The momentum
`Pspinor` is an operator matrix, not a scalar central charge.  The actual
supercharges may come from a representation; this structure records the
operator equation rather than manufacturing supercharges. -/
structure ChiralOperatorPresentation where
  antiQQbar : M2C
  Pspinor : M2C
  super_poincare : antiQQbar = (2 : ℂ) • Pspinor

/-- Existing Pauli-soldered chiral SUSY data gives the operator presentation. -/
def fromChiralSUSYMomentum
    (S : ChiralPoincareSouriauBridge.ChiralSUSYMomentum) : ChiralOperatorPresentation where
  antiQQbar := S.antiQQbar
  Pspinor := ChiralPoincareSouriauBridge.pauliMomentum S.P
  super_poincare := S.susy_anticomm

/-- The reused Pauli presentation has the already-proved determinant/Casimir. -/
theorem fromChiralSUSYMomentum_det
    (S : ChiralPoincareSouriauBridge.ChiralSUSYMomentum) :
    (fromChiralSUSYMomentum S).Pspinor.det = ChiralPoincareSouriauBridge.minkowskiSq S.P := by
  exact ChiralPoincareSouriauBridge.det_pauliMomentum S.P

/-- Left/right spin transport of an operator spinor matrix. -/
def spinTransport (L R X : M2C) : M2C := L * X * R

/-- The operator equation `{Q,Qbar}=2P` is preserved by applying the same
left/right spin transport to both sides. -/
theorem spinTransport_super_poincare
    (L R : M2C) (S : ChiralOperatorPresentation) :
    spinTransport L R S.antiQQbar = (2 : ℂ) • spinTransport L R S.Pspinor := by
  rw [S.super_poincare]
  ext i j
  simp [spinTransport, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Transport only the displayed operator-valued anticommutator relation.  This
is the honest covariant presentation: transformed supercharges require their
own representation law; the relation itself transports functorially. -/
def transportedRelation (L R : M2C) (S : ChiralOperatorPresentation) : Prop :=
  spinTransport L R S.antiQQbar = (2 : ℂ) • spinTransport L R S.Pspinor

/-- Every chiral operator presentation satisfies its transported relation. -/
theorem transportedRelation_holds (L R : M2C) (S : ChiralOperatorPresentation) :
    transportedRelation L R S :=
  spinTransport_super_poincare L R S

/-- The central-charge commutation rule remains operator-valued after transport,
provided the transported charge is central in the target operator algebra. -/
theorem transported_central_charge_commutes
    (Z X : M2C) (hZ : ∀ Y : M2C, Z * Y = Y * Z) :
    SuperPoincareOperatorCharges.comm Z X = 0 := by
  exact SuperPoincareOperatorCharges.comm_eq_zero_of_commutes (hZ X)

/-! ## Operator Poincaré group presentation -/

abbrev FourVector := LorentzBoostMinkowski.FourVector
abbrev minkowskiPair := LorentzBoostMinkowski.minkowskiPair
abbrev minkowskiSq := LorentzBoostMinkowski.minkowskiSq

/-- A finite theorem-honest Poincaré presentation: a Lorentz linear map preserving
`η`, plus a translation four-vector.  Linearity is recorded only by the fields
needed for composition; no analytic Lie group structure is asserted. -/
structure OperatorPoincareElement where
  Λ : FourVector → FourVector
  a : FourVector
  preserves_pair : ∀ p q, minkowskiPair (Λ p) (Λ q) = minkowskiPair p q

/-- Action on momentum ignores translations, as usual for the coadjoint momentum
four-vector in this finite presentation. -/
def actMomentum (g : OperatorPoincareElement) (p : FourVector) : FourVector := g.Λ p

/-- Lorentz part of a Poincaré element preserves the mass Casimir. -/
theorem actMomentum_preserves_mass (g : OperatorPoincareElement) (p : FourVector) :
    minkowskiSq (actMomentum g p) = minkowskiSq p := by
  exact g.preserves_pair p p

/-- Identity Poincaré element. -/
def poincareId : OperatorPoincareElement where
  Λ := id
  a := ⟨0, 0, 0, 0⟩
  preserves_pair := by intro p q; rfl

/-- Composition of the Lorentz parts, with translations composed by the usual
affine rule `a₁ + Λ₁ a₂`. -/
def poincareComp (g h : OperatorPoincareElement) : OperatorPoincareElement where
  Λ := g.Λ ∘ h.Λ
  a := {
    t := g.a.t + (g.Λ h.a).t
    x := g.a.x + (g.Λ h.a).x
    y := g.a.y + (g.Λ h.a).y
    z := g.a.z + (g.Λ h.a).z }
  preserves_pair := by
    intro p q
    simp
    rw [g.preserves_pair, h.preserves_pair]

/-- Composition acts on momentum by composition of Lorentz maps. -/
theorem poincareComp_actMomentum (g h : OperatorPoincareElement) (p : FourVector) :
    actMomentum (poincareComp g h) p = actMomentum g (actMomentum h p) := rfl

/-- A concrete x-boost is a Poincaré element. -/
def boostXPoincare (φ : ℝ) : OperatorPoincareElement where
  Λ := LorentzBoostMinkowski.boostX φ
  a := ⟨0, 0, 0, 0⟩
  preserves_pair := LorentzBoostMinkowski.boostX_preserves_minkowskiPair φ

/-- The operator Poincaré presentation recovers the standard x-boost mass invariance. -/
theorem boostXPoincare_preserves_mass (φ : ℝ) (p : FourVector) :
    minkowskiSq (actMomentum (boostXPoincare φ) p) = minkowskiSq p :=
  actMomentum_preserves_mass (boostXPoincare φ) p

#check cuntzDeformed_odd_odd_beta_zero
#check cuntzDeformed_odd_odd_beta_one
#check cuntzDeformed_odd_odd_lie_jordan_split
#check fromChiralSUSYMomentum
#check fromChiralSUSYMomentum_det
#check spinTransport_super_poincare
#check transportedRelation_holds
#check transported_central_charge_commutes
#check poincareComp_actMomentum
#check boostXPoincare_preserves_mass

end InfoGeometry.Physics.CuntzDeformedSuperPoincare
