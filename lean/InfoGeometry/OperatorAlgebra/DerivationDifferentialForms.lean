import Mathlib.Algebra.Lie.Cochain
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic
import InfoGeometry.Algebra.DerivationLieLaneRepresentation

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

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open LieModule.Cohomology

section LowDegree

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

variable (K : DerivationLieLane R A)

/-- Native derivation-based operator `n`-forms.

The arguments are alternating in the derivation directions, so this is the
finite-dimensional coefficient-valued form carrier used by the
Chevalley--Eilenberg differential. -/
abbrev DerivationOperatorForm (n : ℕ) :=
  K.L [⋀^(Fin n)]→ₗ[R] A

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

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
