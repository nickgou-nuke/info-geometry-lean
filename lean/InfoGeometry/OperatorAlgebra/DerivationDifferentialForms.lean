/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus

/-!
# Derivation-based operator differential forms

This file builds the low-degree Chevalley--Eilenberg complex attached to a
faithful `DerivationLieLane`.  It uses Mathlib's native low-degree Lie
cochains and coboundary maps, rather than storing exterior-derivative laws as
fields.

For a Lie lane `K` acting by derivations on a carrier `A`, the complex is

`A -> C¹(K.L, A) -> C²(K.L, A) -> C³(K.L, A)`.

The degree-zero differential is evaluation of the represented derivation.
The degree-one and degree-two differentials are Mathlib's
`LieModule.Cohomology.d₁₂` and `LieModule.Cohomology.d₂₃`.

On an associative coefficient algebra this file also constructs:

* the commutator wedge square of a connection one-form;
* curvature `F = dΓ + Γ ∧ Γ`;
* the covariant derivation `∇`;
* the exact commutator-curvature identity;
* the Maurer--Cartan flatness condition;
* the covariant Bianchi identity.

No coordinate commutativity, manifold chart, or supplied Bianchi axiom is
used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open LieModule.Cohomology

section LowDegree

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

variable (K : DerivationLieLane R A)

/-- Derivation-valued zero-forms are coefficient-algebra elements. -/
abbrev ZeroForm (_K : DerivationLieLane R A) := A

abbrev ZeroForm' := DerivationOperatorForm K 0

/-- Native Mathlib degree-one Lie cochains. -/
abbrev OneForm := LieModule.Cohomology.oneCochain R K.L A

abbrev OneForm' := DerivationOperatorForm K 1

/-- Canonical identification of one-forms with one-direction alternating maps.
This is the native bridge between the historical CE `oneCochain` carrier and
the generic derivation-form carrier. -/
noncomputable def oneFormAlternatingEquiv :
    (K.L →ₗ[R] A) ≃ DerivationOperatorForm K 1 :=
  AlternatingMap.ofSubsingleton R K.L A (0 : Fin 1)

/-- Native Mathlib alternating degree-two Lie cochains. -/
abbrev TwoForm := LieModule.Cohomology.twoCochain R K.L A

abbrev TwoForm' := DerivationOperatorForm K 2

/-- The target of Mathlib's low-degree `d₂₃` coboundary. -/
abbrev ThreeCochain := K.L →ₗ[R] K.L →ₗ[R] K.L →ₗ[R] A

/-- Degree-zero exterior derivative: `(d a)(x) = ρ(x) a`. -/
def exteriorDerivativeZero : ZeroForm K →ₗ[R] OneForm K :=
  { toFun := fun a =>
      { toFun := fun x => K.operatorActionLieHom x a
        map_add' := fun x y => by
          simp
        map_smul' := fun r x => by
          simp }
    map_add' := fun a b => by
      ext x
      simp
    map_smul' := fun r a => by
      ext x
      simp }

@[simp] theorem exteriorDerivativeZero_apply (a : A) (x : K.L) :
    exteriorDerivativeZero K a x = K.operatorAction x a :=
  rfl

/-- Degree-one Chevalley--Eilenberg differential, using the represented action. -/
noncomputable def exteriorDerivativeOne : OneForm K →ₗ[R] TwoForm K := by
  letI : LieRingModule K.L A :=
    LieRingModule.compLieHom A K.operatorActionLieHom
  letI : LieModule R K.L A :=
    LieModule.compLieHom A K.operatorActionLieHom
  exact LieModule.Cohomology.d₁₂ R K.L A

@[simp] theorem exteriorDerivativeOne_apply
    (ω : OneForm K) (x y : K.L) :
    exteriorDerivativeOne K ω x y =
      K.operatorAction x (ω y) -
        K.operatorAction y (ω x) -
          ω ⁅x, y⁆ :=
  rfl

/-- Degree-two Chevalley--Eilenberg differential. -/
noncomputable def exteriorDerivativeTwo : TwoForm K →ₗ[R] ThreeCochain K := by
  letI : LieRingModule K.L A :=
    LieRingModule.compLieHom A K.operatorActionLieHom
  letI : LieModule R K.L A :=
    LieModule.compLieHom A K.operatorActionLieHom
  exact LieModule.Cohomology.d₂₃ R K.L A

@[simp] theorem exteriorDerivativeTwo_apply
    (ω : TwoForm K) (x y z : K.L) :
    exteriorDerivativeTwo K ω x y z =
      K.operatorAction x (ω y z) -
        K.operatorAction y (ω x z) +
          K.operatorAction z (ω x y) -
            ω ⁅x, y⁆ z +
              ω ⁅x, z⁆ y -
                ω ⁅y, z⁆ x :=
  rfl

/-! The raw degree-three target already has the diagonal vanishing required
of an alternating cochain.  This is the first reusable boundary fact before
constructing the full arbitrary-degree alternating wrapper. -/
theorem exteriorDerivativeTwo_apply_all_repeat
    (ω : TwoForm K) (x : K.L) :
    exteriorDerivativeTwo K ω x x x = 0 := by
  rw [exteriorDerivativeTwo_apply]
  simp

theorem exteriorDerivativeTwo_apply_left_repeat
    (ω : TwoForm K) (x z : K.L) :
    exteriorDerivativeTwo K ω x x z = 0 := by
  rw [exteriorDerivativeTwo_apply]
  simp

theorem exteriorDerivativeTwo_apply_middle_repeat
    (ω : TwoForm K) (x y : K.L) :
    exteriorDerivativeTwo K ω x y y = 0 := by
  rw [exteriorDerivativeTwo_apply]
  have hω : ω ⁅x, y⁆ y = -ω y ⁅x, y⁆ := by
    simpa only [neg_neg] using congrArg Neg.neg
      (LieModule.Cohomology.twoCochain_skew ω ⁅x, y⁆ y)
  rw [hω]
  simp

theorem exteriorDerivativeTwo_apply_outer_repeat
    (ω : TwoForm K) (x y : K.L) :
    exteriorDerivativeTwo K ω x y x = 0 := by
  rw [exteriorDerivativeTwo_apply]
  have hω : ω y x = -ω x y := by
    simpa only [neg_neg] using congrArg Neg.neg
      (LieModule.Cohomology.twoCochain_skew ω y x)
  have hbr : ⁅y, x⁆ = -⁅x, y⁆ := (lie_skew y x).symm
  have hωbr : ω ⁅y, x⁆ x = -ω ⁅x, y⁆ x := by
    rw [hbr]
    simp only [map_neg, map_smul]
    change -(ω ⁅x, y⁆ x) = -(ω ⁅x, y⁆ x)
    rfl
  rw [hωbr]
  simp only [LieModule.Cohomology.twoCochain_alt, lie_self, map_zero,
    sub_zero, add_zero, zero_add, neg_neg]
  rw [hω]
  simp only [map_neg, smul_eq_mul, neg_mul]
  abel
  rfl

/-! Faithful native `Fin 3` multilinear presentation of the existing nested
`d₂₃` map. -/
noncomputable def exteriorDerivativeTwoMultilinear
    (ω : TwoForm K) :
    MultilinearMap R (fun _ : Fin 3 => K.L) A := by
  exact MultilinearMap.mk' (fun v => exteriorDerivativeTwo K ω (v 0) (v 1) (v 2))
    (by
      intro v i x y
      fin_cases i <;> simp [Function.update] <;> abel)
    (by
      intro v i c x
      fin_cases i <;> simp [Function.update])

@[simp] theorem exteriorDerivativeTwoMultilinear_apply
    (ω : TwoForm K) (v : Fin 3 → K.L) :
    exteriorDerivativeTwoMultilinear K ω v =
      exteriorDerivativeTwo K ω (v 0) (v 1) (v 2) := by
  rfl

/-! The native alternating-map form of `d₂₃`. -/
noncomputable def exteriorDerivativeTwoAlternating
    (ω : TwoForm K) : DerivationOperatorForm K 3 := by
  let m : MultilinearMap R (fun _ : Fin 3 => K.L) A :=
    exteriorDerivativeTwoMultilinear K ω
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        change exteriorDerivativeTwo K ω (v 0) (v 1) (v 2) = 0
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · have h' : v 0 = v 1 := by simpa using h
          rw [h']
          exact exteriorDerivativeTwo_apply_left_repeat K ω (v 1) (v 2)
        · have h' : v 0 = v 2 := by simpa using h
          rw [← h']
          exact exteriorDerivativeTwo_apply_outer_repeat K ω (v 0) (v 1)
        · have h' : v 1 = v 0 := by simpa using h
          rw [h']
          exact exteriorDerivativeTwo_apply_left_repeat K ω (v 0) (v 2)
        · exact (hij rfl).elim
        · have h' : v 1 = v 2 := by simpa using h
          rw [h']
          exact exteriorDerivativeTwo_apply_middle_repeat K ω (v 0) (v 2)
        · have h' : v 2 = v 0 := by simpa using h
          rw [h']
          exact exteriorDerivativeTwo_apply_outer_repeat K ω (v 0) (v 1)
        · have h' : v 2 = v 1 := by simpa using h
          rw [h']
          exact exteriorDerivativeTwo_apply_middle_repeat K ω (v 0) (v 1)
        · exact (hij rfl).elim }

@[simp] theorem exteriorDerivativeTwoAlternating_apply
    (ω : TwoForm K) (v : Fin 3 → K.L) :
    exteriorDerivativeTwoAlternating K ω v =
      exteriorDerivativeTwo K ω (v 0) (v 1) (v 2) := by
  rfl

/-- The first two positive-degree differentials compose to zero. -/
theorem exteriorDerivativeTwo_comp_exteriorDerivativeOne :
    exteriorDerivativeTwo K ∘ₗ exteriorDerivativeOne K = 0 := by
  letI : LieRingModule K.L A :=
    LieRingModule.compLieHom A K.operatorActionLieHom
  letI : LieModule R K.L A :=
    LieModule.compLieHom A K.operatorActionLieHom
  simpa [exteriorDerivativeOne, exteriorDerivativeTwo] using
    (LieModule.Cohomology.d₂₃_comp_d₁₂ R K.L A)

/-- Pointwise form of `d₂ ∘ d₁ = 0`. -/
theorem exteriorDerivativeTwo_exteriorDerivativeOne
    (ω : OneForm K) :
    exteriorDerivativeTwo K (exteriorDerivativeOne K ω) = 0 := by
  have h := LinearMap.congr_fun
    (exteriorDerivativeTwo_comp_exteriorDerivativeOne K) ω
  simpa using h

/-- The degree-zero and degree-one differentials compose to zero. -/
theorem exteriorDerivativeOne_exteriorDerivativeZero (a : A) :
    exteriorDerivativeOne K (exteriorDerivativeZero K a) = 0 := by
  apply Subtype.ext
  ext x y
  change (exteriorDerivativeOne K (exteriorDerivativeZero K a)) x y = 0
  rw [exteriorDerivativeOne_apply]
  simp only [exteriorDerivativeZero_apply]
  rw [← K.operatorAction_commutator_apply x y a]
  exact sub_self _

/-- Closed operator one-forms. -/
def IsClosedOneForm (ω : OneForm K) : Prop :=
  exteriorDerivativeOne K ω = 0

/-- Exact operator one-forms. -/
def IsExactOneForm (ω : OneForm K) : Prop :=
  ∃ a : A, exteriorDerivativeZero K a = ω

/-- Exact derivation-based one-forms are closed. -/
theorem IsExactOneForm.isClosed {ω : OneForm K}
    (hω : IsExactOneForm K ω) :
    IsClosedOneForm K ω := by
  rcases hω with ⟨a, rfl⟩
  exact exteriorDerivativeOne_exteriorDerivativeZero K a

end LowDegree

section AssociativeConnection

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- The full commutator wedge square
`(Γ ∧ Γ)(x,y) = Γ(x)Γ(y) - Γ(y)Γ(x)`. -/
noncomputable def connectionWedgeSquare (Γ : OneForm K) : TwoForm K :=
  ⟨LinearMap.mk₂ R
      (fun x y => Γ x * Γ y - Γ y * Γ x)
      (by
        intro x₁ x₂ y
        simp only [map_add, add_mul, mul_add]
        abel)
      (by
        intro r x y
        simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
      (by
        intro x y₁ y₂
        simp only [map_add, mul_add, add_mul]
        abel)
      (by
        intro r x y
        simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_sub]),
    by
      intro x
      simp⟩

@[simp] theorem connectionWedgeSquare_apply
    (Γ : OneForm K) (x y : K.L) :
    connectionWedgeSquare K Γ x y =
      Γ x * Γ y - Γ y * Γ x :=
  rfl

/-- Curvature of a derivation-based operator connection:
`F = dΓ + Γ ∧ Γ`. -/
noncomputable def connectionCurvature (Γ : OneForm K) : TwoForm K :=
  exteriorDerivativeOne K Γ + connectionWedgeSquare K Γ

@[simp] theorem connectionCurvature_apply
    (Γ : OneForm K) (x y : K.L) :
    connectionCurvature K Γ x y =
      K.operatorAction x (Γ y) -
        K.operatorAction y (Γ x) -
          Γ ⁅x, y⁆ +
            (Γ x * Γ y - Γ y * Γ x) :=
  rfl

/-- Covariant derivative along a represented derivation. -/
def covariantDerivative
    (Γ : OneForm K) (x : K.L) (a : A) : A :=
  K.operatorAction x a + Γ x * a - a * Γ x

/-- Every connection-corrected derivative still satisfies Leibniz. -/
theorem covariantDerivative_leibniz
    (Γ : OneForm K) (x : K.L) (a b : A) :
    covariantDerivative K Γ x (a * b) =
      covariantDerivative K Γ x a * b +
        a * covariantDerivative K Γ x b := by
  have hD := K.operatorAction_leibniz x a b
  unfold covariantDerivative
  rw [hD]
  noncomm_ring

/-- The commutator of covariant derivatives is the inner derivation generated
by curvature:
`[∇ₓ,∇ᵧ] - ∇_[x,y] = ad_(F(x,y))`. -/
theorem covariantDerivative_commutator
    (Γ : OneForm K) (x y : K.L) (a : A) :
    covariantDerivative K Γ x (covariantDerivative K Γ y a) -
        covariantDerivative K Γ y (covariantDerivative K Γ x a) -
          covariantDerivative K Γ ⁅x, y⁆ a =
      connectionCurvature K Γ x y * a -
        a * connectionCurvature K Γ x y := by
  have hLeib (z : K.L) (u v : A) :
      K.operatorAction z (u * v) =
        K.operatorAction z u * v + u * K.operatorAction z v :=
    K.operatorAction_leibniz z u v
  have hLie :
      K.operatorAction ⁅x, y⁆ a =
        K.operatorAction x (K.operatorAction y a) -
          K.operatorAction y (K.operatorAction x a) :=
    K.operatorAction_commutator_apply x y a
  unfold covariantDerivative
  simp only [map_add, map_sub]
  rw [hLeib x (Γ y) a, hLeib x a (Γ y),
    hLeib y (Γ x) a, hLeib y a (Γ x), hLie,
    connectionCurvature_apply]
  noncomm_ring

/-- Maurer--Cartan flatness for a derivation-valued connection one-form. -/
def SatisfiesMaurerCartan (Γ : OneForm K) : Prop :=
  connectionCurvature K Γ = 0

theorem satisfiesMaurerCartan_iff_curvature_zero
    (Γ : OneForm K) :
    SatisfiesMaurerCartan K Γ ↔ connectionCurvature K Γ = 0 :=
  Iff.rfl

/-- Under the Maurer--Cartan equation, covariant derivatives represent the
original Lie bracket without a curvature defect. -/
theorem covariantDerivative_commutator_of_maurerCartan
    (Γ : OneForm K) (hΓ : SatisfiesMaurerCartan K Γ)
    (x y : K.L) (a : A) :
    covariantDerivative K Γ x (covariantDerivative K Γ y a) -
        covariantDerivative K Γ y (covariantDerivative K Γ x a) -
          covariantDerivative K Γ ⁅x, y⁆ a = 0 := by
  rw [covariantDerivative_commutator K Γ x y a, hΓ]
  change (0 : A) * a - a * 0 = 0
  simp

/-- Covariant exterior derivative of a two-form, written in the native
low-degree Chevalley--Eilenberg convention. -/
def covariantExteriorDerivativeTwo
    (Γ : OneForm K) (F : TwoForm K)
    (x y z : K.L) : A :=
  exteriorDerivativeTwo K F x y z +
      (Γ x * F y z - F y z * Γ x) -
        (Γ y * F x z - F x z * Γ y) +
          (Γ z * F x y - F x y * Γ z)

/-- The curvature of every derivation-based associative connection satisfies
the covariant Bianchi identity. -/
theorem connectionCurvature_bianchi
    (Γ : OneForm K) (x y z : K.L) :
    covariantExteriorDerivativeTwo K Γ
      (connectionCurvature K Γ) x y z = 0 := by
  have hdd :
      exteriorDerivativeTwo K (exteriorDerivativeOne K Γ) = 0 :=
    exteriorDerivativeTwo_exteriorDerivativeOne K Γ
  have hdF :
      exteriorDerivativeTwo K (connectionCurvature K Γ) x y z =
        exteriorDerivativeTwo K (connectionWedgeSquare K Γ) x y z := by
    rw [connectionCurvature, map_add, hdd]
    simp
  have hLeib (w : K.L) (u v : A) :
      K.operatorAction w (u * v) =
        K.operatorAction w u * v + u * K.operatorAction w v :=
    K.operatorAction_leibniz w u v
  unfold covariantExteriorDerivativeTwo
  rw [hdF, exteriorDerivativeTwo_apply]
  simp only [connectionWedgeSquare_apply, connectionCurvature_apply, map_sub]
  rw [hLeib x (Γ y) (Γ z), hLeib x (Γ z) (Γ y),
    hLeib y (Γ x) (Γ z), hLeib y (Γ z) (Γ x),
    hLeib z (Γ x) (Γ y), hLeib z (Γ y) (Γ x)]
  noncomm_ring

end AssociativeConnection

section ArbitraryDegreeBridges

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
variable (K : DerivationLieLane R A)

private theorem ceLieDeriv_apply (x : K.L) {n : ℕ}
    (ω : DerivationOperatorForm K n) (v : Fin n → K.L) :
    ceLieDeriv K x ω v =
      K.operatorAction x (ω v) - ∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆) :=
  rfl

/-- Degree-0 compatibility between `ceExteriorDerivative K 0` and `exteriorDerivativeZero K`. -/
theorem ceExteriorDerivative_zero_eq (a : ZeroForm K) :
    ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) =
      oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K a) := by
  ext v
  have hv : v = Matrix.vecCons (v 0) Fin.elim0 := funext fun i => by fin_cases i; rfl
  rw [hv, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_zero_curryLeft,
    ceLieDeriv_apply]
  simp [oneFormAlternatingLinearEquiv_apply, exteriorDerivativeZero_apply]

/-- Degree-1 compatibility between `ceExteriorDerivative K 1` and `exteriorDerivativeOne K`. -/
theorem ceExteriorDerivative_one_eq (ω : OneForm K) :
    ceExteriorDerivative K 1 (oneFormAlternatingLinearEquiv K ω) =
      twoCochainEquivDerivationOperatorForm K (exteriorDerivativeOne K ω) := by
  ext v
  have hv : v = Matrix.vecCons (v 0) ![v 1] := funext fun i => by fin_cases i <;> rfl
  have h1 : ![v 1] = Matrix.vecCons (v 1) Fin.elim0 := funext fun i => by fin_cases i; rfl
  rw [hv, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_succ_curryLeft,
    AlternatingMap.sub_apply, ceLieDeriv_apply]
  simp only [Fin.sum_univ_succ, Fin.isValue, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero]
  have h1' : (ceExteriorDerivative K 0 ((oneFormAlternatingLinearEquiv K ω).curryLeft (v 0)))
      ![v 1] = K.operatorAction (v 1) (ω (v 0)) := by
    rw [h1, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_zero_curryLeft,
      ceLieDeriv_apply]
    simp
  rw [h1']
  change K.operatorAction (v 0) (ω (v 1)) -
      ω (Function.update ![v 1] (0 : Fin 1) ⁅v 0, ![v 1] 0⁆ 0) -
      K.operatorAction (v 1) (ω (v 0)) =
    K.operatorAction (v 0) (ω (v 1)) - K.operatorAction (v 1) (ω (v 0)) - ω ⁅v 0, v 1⁆
  simp only [Matrix.cons_val_zero, Function.update_self]
  abel

/-- Degree-2 compatibility between `ceExteriorDerivative K 2` and `exteriorDerivativeTwo K`. -/
theorem ceExteriorDerivative_two_eq (ω : TwoForm K) :
    threeFormToThreeCochain K
        (ceExteriorDerivative K 2 (twoCochainEquivDerivationOperatorForm K ω)) =
      exteriorDerivativeTwo K ω := by
  ext x y z
  simp only [threeFormToThreeCochain_apply, exteriorDerivativeTwo_apply]
  have hxyz : ![x, y, z] = Matrix.vecCons x ![y, z] := by
    ext i; fin_cases i <;> rfl
  have hyz : ![y, z] = Matrix.vecCons y ![z] := by
    ext i; fin_cases i <;> rfl
  have hz : ![z] = Matrix.vecCons z Fin.elim0 := by
    ext i; fin_cases i; rfl
  rw [hxyz, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_succ_curryLeft,
    AlternatingMap.sub_apply, ceLieDeriv_apply]
  have h1 : (ceExteriorDerivative K 1 ((twoCochainEquivDerivationOperatorForm K ω).curryLeft x))
      ![y, z] = K.operatorAction y (ω.1 x z) - ω.1 x ⁅y, z⁆ - K.operatorAction z (ω.1 x y) := by
    rw [hyz, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_succ_curryLeft,
      AlternatingMap.sub_apply, ceLieDeriv_apply]
    have h0 : (ceExteriorDerivative K 0
        (((twoCochainEquivDerivationOperatorForm K ω).curryLeft x).curryLeft y)) ![z] =
        K.operatorAction z (ω.1 x y) := by
      rw [hz, ← AlternatingMap.curryLeft_apply_apply, ceExteriorDerivative_zero_curryLeft,
        ceLieDeriv_apply]
      simp
    rw [h0]
    simp only [Fin.sum_univ_succ, Fin.isValue, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have hz0 : Function.update ![z] (0 : Fin 1) ⁅y, ![z] 0⁆ 0 = ⁅y, z⁆ := by simp
    change K.operatorAction y (ω.1 x z) -
        ω.1 x (Function.update ![z] (0 : Fin 1) ⁅y, ![z] 0⁆ 0) -
        K.operatorAction z (ω.1 x y) =
      K.operatorAction y (ω.1 x z) - ω.1 x ⁅y, z⁆ - K.operatorAction z (ω.1 x y)
    rw [hz0]
  rw [h1]
  simp only [Fin.sum_univ_succ, Fin.isValue, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have h00 : Function.update ![y, z] (0 : Fin 2) ⁅x, ![y, z] 0⁆ 0 = ⁅x, y⁆ := by simp
  have h01 : Function.update ![y, z] (0 : Fin 2) ⁅x, ![y, z] 0⁆ 1 = z := by simp
  have h10 : Function.update ![y, z] (1 : Fin 2) ⁅x, ![y, z] 1⁆ 0 = y := by simp
  have h11 : Function.update ![y, z] (1 : Fin 2) ⁅x, ![y, z] 1⁆ 1 = ⁅x, z⁆ := by simp
  change K.operatorAction x (ω.1 y z) -
      (ω.1 (Function.update ![y, z] 0 ⁅x, ![y, z] 0⁆ 0)
          (Function.update ![y, z] 0 ⁅x, ![y, z] 0⁆ 1) +
        ω.1 (Function.update ![y, z] 1 ⁅x, ![y, z] 1⁆ 0)
          (Function.update ![y, z] 1 ⁅x, ![y, z] 1⁆ 1)) -
      (K.operatorAction y (ω.1 x z) - ω.1 x ⁅y, z⁆ - K.operatorAction z (ω.1 x y)) =
    K.operatorAction x (ω.1 y z) - K.operatorAction y (ω.1 x z) +
      K.operatorAction z (ω.1 x y) - ω.1 ⁅x, y⁆ z + ω.1 ⁅x, z⁆ y - ω.1 ⁅y, z⁆ x
  rw [h00, h01, h10, h11]
  have hskew1 : ω.1 y ⁅x, z⁆ = -ω.1 ⁅x, z⁆ y := by
    simpa [neg_neg] using congrArg Neg.neg (LieModule.Cohomology.twoCochain_skew ω y ⁅x, z⁆)
  have hskew2 : ω.1 x ⁅y, z⁆ = -ω.1 ⁅y, z⁆ x := by
    simpa [neg_neg] using congrArg Neg.neg (LieModule.Cohomology.twoCochain_skew ω x ⁅y, z⁆)
  rw [hskew1, hskew2]
  abel

end ArbitraryDegreeBridges

section AssociativeArbitraryDegreeBridges

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Compatibility between `ceWedge` in degree `(1, 1)` and `connectionWedgeSquare`. -/
theorem ceWedge_one_one_eq_connectionWedgeSquare (Γ : OneForm K) :
    ceWedge K (oneFormAlternatingLinearEquiv K Γ) (oneFormAlternatingLinearEquiv K Γ) =
      twoCochainEquivDerivationOperatorForm K (connectionWedgeSquare K Γ) := by
  ext v
  have hv : v = ![v 0, v 1] := funext fun i => by fin_cases i <;> rfl
  rw [hv, ceWedge_one_one_apply]
  rfl

/-- Compatibility between arbitrary-degree `ceCurvature` and low-degree `connectionCurvature`. -/
theorem ceCurvature_eq (Γ : OneForm K) :
    ceCurvature K (oneFormAlternatingLinearEquiv K Γ) =
      twoCochainEquivDerivationOperatorForm K (connectionCurvature K Γ) := by
  rw [ceCurvature, ceExteriorDerivative_one_eq, ceWedge_one_one_eq_connectionWedgeSquare,
    ← map_add]
  rfl

/-- Degree-0 compatibility between `covariantExteriorDerivativeN` and `covariantDerivative`. -/
theorem covariantExteriorDerivativeN_zero_eq (Γ : OneForm K) (a : ZeroForm K) (x : K.L) :
    covariantExteriorDerivativeN K (oneFormAlternatingLinearEquiv K Γ) 0
        (zeroFormAlternatingEquiv K a) ![x] =
      covariantDerivative K Γ x a := by
  dsimp [covariantExteriorDerivativeN, covariantDerivative]
  simp only [reindexForm_apply, pow_zero, one_smul, ceWedge_zero_left, ceWedge_zero_right,
    LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', LinearMap.flip_apply,
    zeroFormAlternatingEquiv_apply, oneFormAlternatingLinearEquiv_apply]
  have hdx : ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x] = K.operatorAction x a := by
    rw [ceExteriorDerivative_zero_eq]
    rfl
  rw [hdx]
  rfl

/-- Degree-2 compatibility between `covariantExteriorDerivativeN` and `covariantExteriorDerivativeTwo`. -/
theorem covariantExteriorDerivativeN_two_eq (Γ : OneForm K) (F : TwoForm K) (x y z : K.L) :
    threeFormToThreeCochain K
        (covariantExteriorDerivativeN K (oneFormAlternatingLinearEquiv K Γ) 2
          (twoCochainEquivDerivationOperatorForm K F)) x y z =
      covariantExteriorDerivativeTwo K Γ F x y z := by
  simp only [threeFormToThreeCochain_apply]
  dsimp [covariantExteriorDerivativeN, covariantExteriorDerivativeTwo]
  simp only [pow_two, neg_one_mul, neg_neg, one_smul]
  have hd : ceExteriorDerivative K 2 (twoCochainEquivDerivationOperatorForm K F) ![x, y, z] =
      exteriorDerivativeTwo K F x y z := by
    simpa [threeFormToThreeCochain_apply] using
      congrArg (fun T : ThreeCochain K => T x y z) (ceExteriorDerivative_two_eq K F)
  rw [exteriorDerivativeTwo_apply] at hd
  have hxyz : ![x, y, z] = Matrix.vecCons x ![y, z] := by
    ext i; fin_cases i <;> rfl
  have hxyz' : ![x, y, z] ∘ finCongr (Nat.add_comm 1 2) = Matrix.vecCons x ![y, z] := by
    ext i; fin_cases i <;> rfl
  have hyz : ![y, z] = Matrix.vecCons y ![z] := by
    ext i; fin_cases i <;> rfl
  have hGF : ceWedge K (oneFormAlternatingLinearEquiv K Γ)
      (twoCochainEquivDerivationOperatorForm K F)
      (![x, y, z] ∘ finCongr (Nat.add_comm 1 2)) =
      Γ x * F y z - (Γ y * F x z - Γ z * F x y) := by
    rw [hxyz', ← AlternatingMap.curryLeft_apply_apply, ceWedge_succ_succ_curryLeft]
    simp only [AlternatingMap.add_apply, reindexForm_apply,
      ceWedge_zero_left, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
      oneFormAlternatingLinearEquiv_apply, AlternatingMap.curryLeft_apply_apply,
      Matrix.cons_val_zero, Nat.zero_add, pow_one, neg_one_smul, AlternatingMap.neg_apply]
    have hcurF : (ceWedge K (oneFormAlternatingLinearEquiv K Γ)
        ((twoCochainEquivDerivationOperatorForm K F).curryLeft x)) ![y, z] =
        Γ y * F x z - Γ z * F x y := by
      rw [hyz, ← AlternatingMap.curryLeft_apply_apply, ceWedge_succ_succ_curryLeft]
      simp only [AlternatingMap.add_apply, reindexForm_apply,
        ceWedge_zero_left, ceWedge_zero_right, LinearMap.compAlternatingMap_apply,
        LinearMap.mul_apply', oneFormAlternatingLinearEquiv_apply,
        AlternatingMap.curryLeft_apply_apply, Matrix.cons_val_zero,
        Nat.zero_add, pow_one, neg_one_smul, AlternatingMap.neg_apply]
      have hz' : Matrix.vecCons x ((![z] ∘ finCongr (by omega : 0 + 1 = 0 + 1)) ∘
          finCongr (by omega : 1 = 0 + 1)) 1 = z := by
        simp
      have hy' : Matrix.vecCons x (Matrix.vecCons y (Fin.elim0 : Fin 0 → K.L)) 1 = y := rfl
      dsimp only [twoCochainEquivDerivationOperatorForm_apply]
      rw [hz', hy']
      change Γ y * F.1 x z + -(Γ z * F.1 x y) = Γ y * F.1 x z - Γ z * F.1 x y
      rw [sub_eq_add_neg]
    rw [hcurF]
    have hyz0 : ((![y, z] ∘ finCongr (by omega : 0 + 2 = 0 + 2)) ∘
        finCongr (by omega : 2 = 0 + 2)) 0 = y := rfl
    have hyz1 : ((![y, z] ∘ finCongr (by omega : 0 + 2 = 0 + 2)) ∘
        finCongr (by omega : 2 = 0 + 2)) 1 = z := rfl
    rw [twoCochainEquivDerivationOperatorForm_apply, hyz0, hyz1]
    exact (sub_eq_add_neg _ _).symm
  have hFG : ceWedge K (twoCochainEquivDerivationOperatorForm K F)
      (oneFormAlternatingLinearEquiv K Γ) ![x, y, z] =
      F y z * Γ x - (F x z * Γ y - F x y * Γ z) := by
    rw [hxyz, ← AlternatingMap.curryLeft_apply_apply, ceWedge_succ_succ_curryLeft]
    simp only [AlternatingMap.add_apply, reindexForm_apply, AlternatingMap.smul_apply,
      ceWedge_zero_right, LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', oneFormAlternatingLinearEquiv_apply,
      AlternatingMap.curryLeft_apply_apply, Matrix.cons_val_zero]
    have hcurF : (ceWedge K ((twoCochainEquivDerivationOperatorForm K F).curryLeft x)
        (oneFormAlternatingLinearEquiv K Γ)) (![y, z] ∘ finCongr (by omega : 1 + 1 = 1 + 1 + 0)) =
        F x y * Γ z - F x z * Γ y := by
      have hyz' : ![y, z] ∘ finCongr (by omega : 1 + 1 = 1 + 1 + 0) = ![y, z] := by
        ext i; fin_cases i <;> rfl
      rw [hyz', hyz, ← AlternatingMap.curryLeft_apply_apply, ceWedge_succ_succ_curryLeft]
      simp only [AlternatingMap.add_apply, reindexForm_apply,
        ceWedge_zero_left, ceWedge_zero_right, LinearMap.compAlternatingMap_apply,
        LinearMap.mul_apply', oneFormAlternatingLinearEquiv_apply,
        AlternatingMap.curryLeft_apply_apply, Matrix.cons_val_zero,
        Nat.zero_add, pow_one, neg_one_smul, AlternatingMap.neg_apply]
      change F.1 x y * Γ z + -(F.1 x z * Γ y) = F.1 x y * Γ z - F.1 x z * Γ y
      rw [sub_eq_add_neg]
    rw [hcurF]
    have h11 : ((-1 : R) ^ (1 + 1)) = 1 := by norm_num
    rw [h11, one_smul]
    change F.1 x y * Γ z - F.1 x z * Γ y + F.1 y z * Γ x =
      F.1 y z * Γ x - (F.1 x z * Γ y - F.1 x y * Γ z)
    abel
  rw [hd, hGF, hFG]
  abel

end AssociativeArbitraryDegreeBridges

section CommutativeLowDegreeSpecialization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (K : DerivationLieLane R A)

theorem covariantDerivative_eq_operatorAction_of_commRing
    (Γ : OneForm K) (x : K.L) (a : A) :
    covariantDerivative K Γ x a = K.operatorAction x a := by
  unfold covariantDerivative
  rw [mul_comm (Γ x) a]
  ring

theorem connectionWedgeSquare_eq_zero_of_commRing (Γ : OneForm K) :
    connectionWedgeSquare K Γ = 0 := by
  ext x y
  simp [connectionWedgeSquare_apply, mul_comm]

theorem connectionCurvature_eq_exteriorDerivativeOne_of_commRing (Γ : OneForm K) :
    connectionCurvature K Γ = exteriorDerivativeOne K Γ := by
  rw [connectionCurvature, connectionWedgeSquare_eq_zero_of_commRing, add_zero]

theorem satisfiesMaurerCartan_iff_isClosed_of_commRing (Γ : OneForm K) :
    SatisfiesMaurerCartan K Γ ↔ IsClosedOneForm K Γ := by
  rw [SatisfiesMaurerCartan, connectionCurvature_eq_exteriorDerivativeOne_of_commRing,
    IsClosedOneForm]

end CommutativeLowDegreeSpecialization

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
