import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Equiv.Basic
import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Algebra.LorentzBiquaternionEquivalence

/-!
# Finite Cuntz supergrading and Lorentz/Poincare presentation packet

This file proves a finite, theorem-safe bridge between:

* the algebraic Cuntz supercharge packet from `CuntzSupergradedSUSY`, and
* the determinant-preserving finite Lorentz transport lane from
  `LorentzBiquaternionEquivalence`.

It does not claim a full analytic C*-representation, a full super-Poincare Lie
superalgebra, or a global Lorentz-group classification.  The closed content is
finite algebra: `{Q,Q}=2P`, odd/even grade bookkeeping, and determinant
invariance of the exact Pauli-spacetime transport.
-/

noncomputable section

namespace CuntzLorentzPoincarePresentation

open Matrix
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzSuperalgebra
open InfoGeometry.Algebra.LorentzBiquaternionEquivalence

/-! ## Cuntz deformation and labeled supergrading -/

/-- The q-deformed Cuntz pair relation `s₁† s₂ = q • (s₂ s₁†)`. -/
def qDeformedCuntzPairRelation {A : Type*} [Mul A] [SMul ℂ A]
    (q : ℂ) (s₁dag s₂ : A) : Prop :=
  s₁dag * s₂ = q • (s₂ * s₁dag)

theorem q_zero_cuntz_pair_relation_of_distinct {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    qDeformedCuntzPairRelation (0 : ℂ) (cuntzSdag n i) (cuntzS n j) := by
  simp [qDeformedCuntzPairRelation, cuntz_distinct_orthogonal n hij]

/-- Finite Cuntz grading/deformation parameters: a binary grading label and a q-parameter. -/
structure CuntzGradingDeformation (n : ℕ) where
  label : Fin n → Bool
  q : ℂ

namespace CuntzGradingDeformation

variable {n : ℕ} (D : CuntzGradingDeformation n)

/-- The algebra automorphism implementing the labeled finite Cuntz supergrading. -/
noncomputable def gradingOperator : CuntzAlg n →ₐ[ℂ] CuntzAlg n :=
  labeledParity D.label

/-- Odd/even predicates relative to the labeled grading operator. -/
def IsOdd (x : CuntzAlg n) : Prop := D.gradingOperator x = -x

def IsEven (x : CuntzAlg n) : Prop := D.gradingOperator x = x

@[simp] theorem gradingOperator_sq (x : CuntzAlg n) :
    D.gradingOperator (D.gradingOperator x) = x :=
  labeledParity_sq D.label x

@[simp] theorem gradingOperator_S (i : Fin n) :
    D.gradingOperator (cuntzS n i) = labelSign D.label i • cuntzS n i :=
  labeledParity_S D.label i

@[simp] theorem gradingOperator_Sdag (i : Fin n) :
    D.gradingOperator (cuntzSdag n i) = labelSign D.label i • cuntzSdag n i :=
  labeledParity_Sdag D.label i

/-- If the label marks a mode odd, its Majorana Cuntz supercharge is odd. -/
theorem majoranaSupercharge_odd_of_label_true {i : Fin n} (hi : D.label i = true) :
    D.IsOdd (cuntzMajoranaSupercharge n i) := by
  unfold IsOdd gradingOperator cuntzMajoranaSupercharge
  rw [map_add, labeledParity_S, labeledParity_Sdag]
  simp only [labelSign, hi, if_true]
  module

/-- If the label marks a mode even, its Majorana Cuntz supercharge is even. -/
theorem majoranaSupercharge_even_of_label_false {i : Fin n} (hi : D.label i = false) :
    D.IsEven (cuntzMajoranaSupercharge n i) := by
  simp [IsEven, gradingOperator, cuntzMajoranaSupercharge, labelSign, hi]

/-- The square of an odd labeled Cuntz supercharge is even. -/
theorem superMomentum_even_of_label_true {i : Fin n} (hi : D.label i = true) :
    D.IsEven (cuntzSuperMomentum n i) := by
  unfold IsEven gradingOperator cuntzSuperMomentum superMomentum
  rw [map_mul]
  have hQ := majoranaSupercharge_odd_of_label_true D hi
  unfold IsOdd gradingOperator at hQ
  rw [hQ]
  exact neg_mul_neg (cuntzMajoranaSupercharge n i) (cuntzMajoranaSupercharge n i)

/-- The undeformed `q = 0` off-diagonal relation is the Cuntz orthogonality relation. -/
theorem q_zero_pair_relation_of_distinct {i j : Fin n} (hij : i ≠ j) (hq : D.q = 0) :
    qDeformedCuntzPairRelation D.q (cuntzSdag n i) (cuntzS n j) := by
  rw [hq]
  exact q_zero_cuntz_pair_relation_of_distinct hij

end CuntzGradingDeformation

/-! ## Concrete finite Poincare transform presentation -/

/-- Finite real four-vectors used by the explicit Poincare presentation. -/
abbrev FiniteFourVector := Fin 4 → ℝ

/-- Minkowski pairing with signature `(+---)`. -/
def minkowskiPair4 (x y : FiniteFourVector) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- Squared Minkowski interval between two finite four-vectors. -/
def minkowskiInterval4 (x y : FiniteFourVector) : ℝ :=
  minkowskiPair4 (x - y) (x - y)

/--
The finite Poincare group as the subgroup of spacetime permutations preserving
the squared Minkowski interval.
-/
def PoincareTransformGroup : Subgroup (Equiv.Perm FiniteFourVector) where
  carrier := {f | ∀ x y, minkowskiInterval4 (f x) (f y) = minkowskiInterval4 x y}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro f g hf hg x y
    calc
      minkowskiInterval4 ((f * g) x) ((f * g) y)
          = minkowskiInterval4 (g x) (g y) := by
            simpa using hf (g x) (g y)
      _ = minkowskiInterval4 x y := hg x y
  inv_mem' := by
    intro f hf x y
    have h := hf (f⁻¹ x) (f⁻¹ y)
    simpa using h.symm

/-- Type alias for the finite Poincare group used by Cuntz presentation operators. -/
abbrev FinitePoincareGroup := PoincareTransformGroup

theorem poincareTransform_preserves_interval
    (g : FinitePoincareGroup) (x y : FiniteFourVector) :
    minkowskiInterval4 ((g : Equiv.Perm FiniteFourVector) x)
      ((g : Equiv.Perm FiniteFourVector) y) = minkowskiInterval4 x y :=
  g.property x y

/-- Linear Lorentz part of an affine finite Poincare presentation. -/
structure LorentzLinearPresentation where
  toEquiv : Equiv.Perm FiniteFourVector
  map_zero : toEquiv 0 = 0
  map_add : ∀ x y, toEquiv (x + y) = toEquiv x + toEquiv y
  map_neg : ∀ x, toEquiv (-x) = -toEquiv x
  preserves_pair : ∀ x y, minkowskiPair4 (toEquiv x) (toEquiv y) = minkowskiPair4 x y

namespace LorentzLinearPresentation

theorem map_sub (L : LorentzLinearPresentation) (x y : FiniteFourVector) :
    L.toEquiv (x - y) = L.toEquiv x - L.toEquiv y := by
  rw [sub_eq_add_neg, L.map_add, L.map_neg, sub_eq_add_neg]

/-- The identity Lorentz presentation. -/
def identity : LorentzLinearPresentation where
  toEquiv := Equiv.refl FiniteFourVector
  map_zero := rfl
  map_add := by intro x y; rfl
  map_neg := by intro x; rfl
  preserves_pair := by intro x y; rfl

/-- Affine action `x ↦ Lx + a` generated by a Lorentz part and a translation. -/
def affineEquiv (L : LorentzLinearPresentation) (a : FiniteFourVector) :
    Equiv.Perm FiniteFourVector where
  toFun := fun x => L.toEquiv x + a
  invFun := fun x => L.toEquiv.symm (x - a)
  left_inv := by
    intro x
    have h : L.toEquiv x + a - a = L.toEquiv x := by
      ext μ
      simp
    simp [h]
  right_inv := by
    intro x
    have h : L.toEquiv (L.toEquiv.symm (x - a)) = x - a := L.toEquiv.apply_symm_apply (x - a)
    calc
      L.toEquiv (L.toEquiv.symm (x - a)) + a = (x - a) + a := by rw [h]
      _ = x := by
        ext μ
        simp

@[simp] theorem affineEquiv_apply
    (L : LorentzLinearPresentation) (a x : FiniteFourVector) :
    affineEquiv L a x = L.toEquiv x + a :=
  rfl

theorem affineEquiv_sub
    (L : LorentzLinearPresentation) (a x y : FiniteFourVector) :
    affineEquiv L a x - affineEquiv L a y = L.toEquiv (x - y) := by
  calc
    affineEquiv L a x - affineEquiv L a y = L.toEquiv x - L.toEquiv y := by
      ext μ
      simp [affineEquiv]
    _ = L.toEquiv (x - y) := (L.map_sub x y).symm

theorem affineEquiv_preserves_interval
    (L : LorentzLinearPresentation) (a : FiniteFourVector) (x y : FiniteFourVector) :
    minkowskiInterval4 (affineEquiv L a x) (affineEquiv L a y) =
      minkowskiInterval4 x y := by
  calc
    minkowskiInterval4 (affineEquiv L a x) (affineEquiv L a y)
        = minkowskiPair4 (L.toEquiv (x - y)) (L.toEquiv (x - y)) := by
          rw [minkowskiInterval4, affineEquiv_sub]
    _ = minkowskiPair4 (x - y) (x - y) := L.preserves_pair (x - y) (x - y)
    _ = minkowskiInterval4 x y := rfl

/-- Affine Lorentz-plus-translation data as an element of the finite Poincare group. -/
def affinePoincareElement
    (L : LorentzLinearPresentation) (a : FiniteFourVector) : FinitePoincareGroup :=
  ⟨affineEquiv L a, affineEquiv_preserves_interval L a⟩

theorem affinePoincareElement_preserves_interval
    (L : LorentzLinearPresentation) (a : FiniteFourVector) (x y : FiniteFourVector) :
    minkowskiInterval4 (((affinePoincareElement L a : FinitePoincareGroup) :
      Equiv.Perm FiniteFourVector) x)
      (((affinePoincareElement L a : FinitePoincareGroup) :
        Equiv.Perm FiniteFourVector) y) = minkowskiInterval4 x y :=
  (affinePoincareElement L a).property x y

theorem identity_affinePoincareElement_zero :
    affinePoincareElement identity 0 = (1 : FinitePoincareGroup) := by
  ext x μ
  simp [affinePoincareElement, affineEquiv, identity]

end LorentzLinearPresentation

/-! ## Presentation operators for Lorentz/Poincare actions -/

/--
An algebraic presentation operator for a group action on the finite Cuntz quotient.
The fields are explicit: each group element acts by a complex algebra homomorphism,
the action laws hold, and the action commutes with the chosen grading operator.
-/
structure CuntzPresentationOperator
    (n : ℕ) (D : CuntzGradingDeformation n) (G : Type*) [Group G] where
  op : G → CuntzAlg n →ₐ[ℂ] CuntzAlg n
  op_one : ∀ x, op 1 x = x
  op_mul : ∀ g h x, op (g * h) x = op g (op h x)
  commutes_grading : ∀ g x, D.gradingOperator (op g x) = op g (D.gradingOperator x)

namespace CuntzPresentationOperator

variable {n : ℕ} {D : CuntzGradingDeformation n} {G : Type*} [Group G]
variable (T : CuntzPresentationOperator n D G)

theorem map_anticommutator (g : G) (x y : CuntzAlg n) :
    T.op g (algebraicAnticommutator x y) =
      algebraicAnticommutator (T.op g x) (T.op g y) := by
  simp [algebraicAnticommutator]

theorem map_superMomentum (g : G) (Q : CuntzAlg n) :
    T.op g (superMomentum Q) = superMomentum (T.op g Q) := by
  simp [superMomentum]

theorem preserves_superMomentum_of_preserves_supercharge
    (g : G) (Q : CuntzAlg n) (hQ : T.op g Q = Q) :
    T.op g (superMomentum Q) = superMomentum Q := by
  rw [map_superMomentum, hQ]

theorem preserves_odd (g : G) {x : CuntzAlg n} (hx : D.IsOdd x) :
    D.IsOdd (T.op g x) := by
  unfold CuntzGradingDeformation.IsOdd at hx ⊢
  rw [T.commutes_grading, hx, map_neg]

theorem preserves_even (g : G) {x : CuntzAlg n} (hx : D.IsEven x) :
    D.IsEven (T.op g x) := by
  unfold CuntzGradingDeformation.IsEven at hx ⊢
  rw [T.commutes_grading, hx]

end CuntzPresentationOperator

/--
Finite Cuntz deformation/supergrading presentation with separate Lorentz and
Poincare group operators.  This is an action/presentation interface, not a
global classification theorem for the Lorentz or Poincare groups.
-/
structure CuntzLorentzPoincareOperatorPresentation (n : ℕ) where
  deformation : CuntzGradingDeformation n
  mode : Fin n
  LorentzGroup : Type
  PoincareGroup : Type
  [lorentzGroup : Group LorentzGroup]
  [poincareGroup : Group PoincareGroup]
  lorentz : CuntzPresentationOperator n deformation LorentzGroup
  poincare : CuntzPresentationOperator n deformation PoincareGroup
  lorentz_preserves_supercharge :
    ∀ Λ, lorentz.op Λ (cuntzMajoranaSupercharge n mode) = cuntzMajoranaSupercharge n mode
  poincare_preserves_supercharge :
    ∀ a, poincare.op a (cuntzMajoranaSupercharge n mode) = cuntzMajoranaSupercharge n mode

namespace CuntzLorentzPoincareOperatorPresentation

variable {n : ℕ} (P : CuntzLorentzPoincareOperatorPresentation n)

attribute [instance] CuntzLorentzPoincareOperatorPresentation.lorentzGroup
attribute [instance] CuntzLorentzPoincareOperatorPresentation.poincareGroup

/-- The distinguished Cuntz supercharge in the presentation. -/
def supercharge : CuntzAlg n :=
  cuntzMajoranaSupercharge n P.mode

/-- The distinguished translation/momentum operator generated by the supercharge square. -/
def momentum : CuntzAlg n :=
  superMomentum P.supercharge

theorem lorentz_preserves_momentum (Λ : P.LorentzGroup) :
    P.lorentz.op Λ P.momentum = P.momentum := by
  unfold momentum supercharge
  exact P.lorentz.preserves_superMomentum_of_preserves_supercharge Λ
    (cuntzMajoranaSupercharge n P.mode) (P.lorentz_preserves_supercharge Λ)

theorem poincare_preserves_momentum (a : P.PoincareGroup) :
    P.poincare.op a P.momentum = P.momentum := by
  unfold momentum supercharge
  exact P.poincare.preserves_superMomentum_of_preserves_supercharge a
    (cuntzMajoranaSupercharge n P.mode) (P.poincare_preserves_supercharge a)

theorem lorentz_preserves_self_anticommutator (Λ : P.LorentzGroup) :
    P.lorentz.op Λ (algebraicAnticommutator P.supercharge P.supercharge) =
      algebraicAnticommutator P.supercharge P.supercharge := by
  rw [P.lorentz.map_anticommutator]
  simp [supercharge, P.lorentz_preserves_supercharge Λ]

theorem poincare_preserves_self_anticommutator (a : P.PoincareGroup) :
    P.poincare.op a (algebraicAnticommutator P.supercharge P.supercharge) =
      algebraicAnticommutator P.supercharge P.supercharge := by
  rw [P.poincare.map_anticommutator]
  simp [supercharge, P.poincare_preserves_supercharge a]

theorem supercharge_anticommutator_presents_momentum :
    algebraicAnticommutator P.supercharge P.supercharge = (2 : ℂ) • P.momentum := by
  unfold momentum
  exact algebraicAnticommutator_self_eq_two_smul_momentum P.supercharge

theorem lorentz_operator_packet (Λ : P.LorentzGroup) :
    P.lorentz.op Λ P.momentum = P.momentum ∧
      P.lorentz.op Λ (algebraicAnticommutator P.supercharge P.supercharge) =
        algebraicAnticommutator P.supercharge P.supercharge :=
  ⟨P.lorentz_preserves_momentum Λ, P.lorentz_preserves_self_anticommutator Λ⟩

theorem poincare_operator_packet (a : P.PoincareGroup) :
    P.poincare.op a P.momentum = P.momentum ∧
      P.poincare.op a (algebraicAnticommutator P.supercharge P.supercharge) =
        algebraicAnticommutator P.supercharge P.supercharge :=
  ⟨P.poincare_preserves_momentum a, P.poincare_preserves_self_anticommutator a⟩

end CuntzLorentzPoincareOperatorPresentation

/-! ## Existing finite Lorentz determinant lane -/

/-- Exact Lorentz transport composes with itself as matrix multiplication dictates. -/
theorem exactBoostTransport_comp_self (X : Mat2) :
    exactBoostTransport (exactBoostTransport X) =
      exactBoostQ * exactBoostQ * X * (exactBoostQ * exactBoostQ) := by
  simp [exactBoostTransport]
  noncomm_ring

/-- The twice-composed exact boost still preserves determinant. -/
theorem exactBoostTransport_comp_self_det (X : Mat2) :
    Matrix.det (exactBoostTransport (exactBoostTransport X)) = Matrix.det X := by
  rw [exactBoostTransport_det]
  exact exactBoostTransport_det X

/-- The twice-composed exact boost preserves the Pauli/Minkowski determinant readout. -/
theorem exactBoostTransport_comp_self_preserves_spacetime_det (t x y z : ℂ) :
    Matrix.det (exactBoostTransport (exactBoostTransport (hermitianSpacetimePoint t x y z))) =
      t * t - (x * x + y * y + z * z) := by
  rw [exactBoostTransport_comp_self_det]
  exact hermitianSpacetimePoint_det t x y z

/-- The canonical Cuntz packet has odd supercharge and even generated translation. -/
theorem canonical_cuntz_packet_supergrading {n : ℕ} (i : Fin n) :
    let P := canonicalCuntzSuperPoincarePacket n i
    P.superchargeGrade = 1 ∧ P.momentumGrade = 0 ∧
      P.poincareTranslation = superMomentum P.supercharge := by
  exact ⟨rfl, rfl, rfl⟩

/-- The canonical Cuntz packet anticommutator presents the translation generator. -/
theorem canonical_cuntz_packet_anticommutator_translation {n : ℕ} (i : Fin n) :
    let P := canonicalCuntzSuperPoincarePacket n i
    algebraicAnticommutator P.supercharge P.supercharge = (2 : ℂ) • P.poincareTranslation := by
  simp [canonicalCuntzSuperPoincarePacket, cuntzSuperMomentum]
  exact algebraicAnticommutator_self_eq_two_smul_momentum (cuntzMajoranaSupercharge n i)

/-- Combined finite Cuntz-super/Poincare-Lorentz presentation packet. -/
theorem finite_cuntz_super_poincare_lorentz_packet {n : ℕ} (i : Fin n) (t x y z : ℂ) :
    let P := canonicalCuntzSuperPoincarePacket n i
    P.superchargeGrade = 1 ∧
    P.momentumGrade = 0 ∧
    algebraicAnticommutator P.supercharge P.supercharge = (2 : ℂ) • P.poincareTranslation ∧
    Matrix.det (exactBoostTransport (exactBoostTransport (hermitianSpacetimePoint t x y z))) =
      t * t - (x * x + y * y + z * z) := by
  simp only
  exact ⟨rfl, rfl, canonical_cuntz_packet_anticommutator_translation i,
    exactBoostTransport_comp_self_preserves_spacetime_det t x y z⟩

end CuntzLorentzPoincarePresentation

end noncomputable section
