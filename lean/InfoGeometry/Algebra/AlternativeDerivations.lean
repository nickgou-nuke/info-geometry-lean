import Mathlib.Tactic
import Mathlib.Algebra.Ring.Associator

/-!
# Derivations of Alternative Algebras

This file formalizes the concepts from the paper "Inner derivations of alternative
algebras over commutative rings" by O. Loos, H. P. Petersson, M. L. Racine.

Since Mathlib's `RingTheory.Derivation` requires `CommSemiring A`, we define 
a native `NonAssocDerivation` structure for `NonUnitalNonAssocRing` algebras, 
which captures generic derivations on non-associative algebras (like the octonions).

We define:
1. `NonAssocDerivation R A`
2. Associator derivations (`AssDer`)
3. Standard derivations (`StanDer`)
-/

namespace InfoGeometry.Algebra

variable (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- 
A derivation of a non-associative algebra `A` over `R` is an `R`-linear map 
that satisfies the Leibniz rule for the non-associative product.
-/
structure NonAssocDerivation extends A →ₗ[R] A where
  leibniz' (x y : A) : toLinearMap (x * y) = (toLinearMap x) * y + x * (toLinearMap y)

namespace NonAssocDerivation

variable {R A}

instance : CoeFun (NonAssocDerivation R A) (fun _ => A → A) where
  coe D := D.toLinearMap.toFun

instance : Coe (NonAssocDerivation R A) (A →ₗ[R] A) where
  coe D := D.toLinearMap

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp] theorem map_add (D : NonAssocDerivation R A) (x y : A) : D (x + y) = D x + D y :=
  D.toLinearMap.map_add x y

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp] theorem map_smul (D : NonAssocDerivation R A) (r : R) (x : A) : D (r • x) = r • D x :=
  D.toLinearMap.map_smul r x

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp] theorem leibniz (D : NonAssocDerivation R A) (x y : A) : D (x * y) = D x * y + x * D y :=
  D.leibniz' x y

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp] theorem toLinearMap_apply (D : NonAssocDerivation R A) (x : A) : D.toLinearMap x = D x := rfl

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem ext {D E : NonAssocDerivation R A} (h : ∀ x, D x = E x) : D = E := by
  cases D; cases E
  congr
  exact LinearMap.ext h

instance : Zero (NonAssocDerivation R A) where
  zero := 
    { toLinearMap := 0
      leibniz' := fun x y => by simp }

instance : Add (NonAssocDerivation R A) where
  add D E := 
    { toLinearMap := D.toLinearMap + E.toLinearMap
      leibniz' := fun x y => by 
        simp only [LinearMap.add_apply, toLinearMap_apply, leibniz, add_mul, mul_add]
        abel }

instance : Neg (NonAssocDerivation R A) where
  neg D :=
    { toLinearMap := -D.toLinearMap
      leibniz' := fun x y => by
        simp only [LinearMap.neg_apply, toLinearMap_apply, leibniz, neg_mul, mul_neg, neg_add] }

instance : SMul R (NonAssocDerivation R A) where
  smul r D := 
    { toLinearMap := r • D.toLinearMap
      leibniz' := fun x y => by 
        simp only [LinearMap.smul_apply, toLinearMap_apply, leibniz, smul_add, smul_mul_assoc, mul_smul_comm] }

end NonAssocDerivation

/-!
### Classes of Inner Derivations
Following Loos, Petersson, Racine, Section 2.
-/

variable {R A}

/-- Left multiplication operator as a linear map. -/
def L_map (a : A) : A →ₗ[R] A where
  toFun x := a * x
  map_add' := mul_add a
  map_smul' r x := mul_smul_comm r a x

/-- Right multiplication operator as a linear map. -/
def R_map (a : A) : A →ₗ[R] A where
  toFun x := x * a
  map_add' x y := add_mul x y a
  map_smul' r x := smul_mul_assoc r x a

/--
The standard endomorphism
`D_{a,b} = [L_a, L_b] + [L_a, R_b] + [R_a, R_b]`.

The Loos--Petersson--Racine theorem that this endomorphism is a derivation
requires alternativity hypotheses.  This declaration only defines the linear
map; it deliberately does not claim the theorem without those hypotheses.
-/
def stanDerMap (a b : A) : A →ₗ[R] A :=
  (L_map a).comp (L_map b) - (L_map b).comp (L_map a) +
  ((L_map a).comp (R_map b) - (R_map b).comp (L_map a)) +
  ((R_map a).comp (R_map b) - (R_map b).comp (R_map a))

/-!
### Standard derivations in an alternative algebra

The hypotheses below are the two alternative laws.  They are kept explicit
rather than hidden in an ad hoc typeclass: the theorem applies to every native
Mathlib non-unital nonassociative ring once its owner supplies those laws.
-/

section Alternative

variable (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
  (hright : ∀ x y : A, (y * x) * x = y * (x * x))

include hleft in
/-- Polarization of the left alternative law. -/
lemma alternative_left_linearized (x y z : A) :
    (x * y) * z + (y * x) * z = x * (y * z) + y * (x * z) := by
  have h := hleft (x + y) z
  simp only [add_mul, mul_add] at h
  rw [hleft x z, hleft y z] at h
  linear_combination (norm := abel) h

include hright in
/-- Polarization of the right alternative law. -/
lemma alternative_right_linearized (x y z : A) :
    (z * x) * y + (z * y) * x = z * (x * y) + z * (y * x) := by
  have h := hright (x + y) z
  simp only [add_mul, mul_add] at h
  rw [hright x z, hright y z] at h
  linear_combination (norm := abel) h

include hleft in
/-- In an alternative ring, the associator changes sign in its first two slots. -/
lemma alternative_associator_swap12 (x y z : A) :
    associator x y z = -associator y x z := by
  have h := hleft (x + y) z
  simp only [add_mul, mul_add] at h
  rw [hleft x z, hleft y z] at h
  simp only [associator_apply]
  linear_combination (norm := abel) h

include hright in
/-- In an alternative ring, the associator changes sign in its final two slots. -/
lemma alternative_associator_swap23 (x y z : A) :
    associator x y z = -associator x z y := by
  have h := hright (y + z) x
  simp only [add_mul, mul_add] at h
  rw [hright y x, hright z x] at h
  simp only [associator_apply]
  linear_combination (norm := abel) h

include hleft hright in
/-- Cyclic permutations preserve the associator in an alternative ring. -/
lemma alternative_associator_cycle (x y z : A) :
    associator y z x = associator x y z := by
  rw [alternative_associator_swap23 hright,
    alternative_associator_swap12 hleft]
  abel

private lemma associator_sub_left (u v x y : A) :
    associator (u - v) x y = associator u x y - associator v x y := by
  simp only [associator_apply, sub_mul]
  abel

include hleft hright in
/--
The product rule for an associator in an alternative ring.  The correction is
the associator with the commutator `a * b - b * a`; this is the structural
identity needed for the standard-derivation theorem.
-/
lemma alternative_associator_product (a b x y : A) :
    associator a b (x * y) =
      associator a b x * y + x * associator a b y -
        associator (a * b - b * a) x y := by
  have h1 := associator_cocycle b a x y
  have h2 := associator_cocycle b x y a
  have h3 := associator_cocycle x y b a
  have h4 := associator_cocycle y a b x
  have h5 := associator_cocycle y b a x
  rw [associator_sub_left]
  rw [alternative_associator_swap12 hleft b (a * x) y,
      alternative_associator_swap12 hleft b a (x * y),
      alternative_associator_swap12 hleft b a x] at h1
  rw [alternative_associator_cycle hleft hright a x y,
      alternative_associator_cycle hleft hright a (b * x) y,
      alternative_associator_cycle hleft hright a b (x * y)] at h2
  rw [alternative_associator_swap12 hleft y b a,
      alternative_associator_cycle hleft hright a b y,
      alternative_associator_swap12 hleft (x * y) b a,
      alternative_associator_cycle hleft hright a b (x * y),
      alternative_associator_cycle hleft hright a x (y * b),
      alternative_associator_cycle hleft hright (b * a) x y,
      alternative_associator_cycle hleft hright b x y] at h3
  rw [alternative_associator_cycle hleft hright x (y * a) b,
      alternative_associator_cycle hleft hright b x (y * a),
      alternative_associator_cycle hleft hright x y (a * b),
      alternative_associator_cycle hleft hright (a * b) x y,
      alternative_associator_cycle hleft hright (b * x) y a,
      alternative_associator_cycle hleft hright a (b * x) y,
      alternative_associator_cycle hleft hright b y a,
      alternative_associator_cycle hleft hright a b y] at h4
  rw [alternative_associator_swap12 hleft b a x,
      alternative_associator_cycle hleft hright x (y * b) a,
      alternative_associator_cycle hleft hright a x (y * b),
      alternative_associator_cycle hleft hright x y (b * a),
      alternative_associator_cycle hleft hright (b * a) x y,
      alternative_associator_cycle hleft hright (a * x) y b,
      alternative_associator_cycle hleft hright b (a * x) y,
      alternative_associator_swap12 hleft b (a * x) y,
      alternative_associator_cycle hleft hright a y b,
      alternative_associator_swap23 hright a y b] at h5
  simp only [neg_mul, mul_neg] at h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := abel) h1 - h2 + h3 + h4 + h5

include hleft hright in
/--
Kleinfeld's normal form
`D_{a,b}(x) = [[a,b],x] - 3 (a,b,x)` for the standard endomorphism.
-/
theorem stanDerMap_apply_normal_form (a b x : A) :
    stanDerMap (R := R) a b x =
      ((a * b - b * a) * x - x * (a * b - b * a)) -
        3 • associator a b x := by
  have hL := alternative_left_linearized hleft a b x
  have hR := alternative_right_linearized hright a b x
  have hA := alternative_associator_swap23 hright a b x
  have hC : associator x a b = associator a b x := by
    rw [alternative_associator_cycle hleft hright b x a,
      alternative_associator_cycle hleft hright a b x]
  have hLeft :
      a * (b * x) - b * (a * x) =
        (a * b) * x - (b * a) * x - 2 • associator a b x := by
    simp only [associator_apply]
    linear_combination (norm := abel) hL
  have hMixed : a * (x * b) - (a * x) * b = associator a b x := by
    rw [hA]
    simp only [associator_apply]
    abel
  have hRight :
      (x * b) * a - (x * a) * b =
        x * (b * a) - x * (a * b) - 2 • associator a b x := by
    simp only [associator_apply] at hC ⊢
    have hCeq : (x * a) * b = x * (a * b) + ((a * b) * x - a * (b * x)) :=
      by simpa [add_comm] using (sub_eq_iff_eq_add.mp hC)
    rw [hCeq] at hR ⊢
    linear_combination (norm := abel) hR
  change a * (b * x) - b * (a * x) +
      (a * (x * b) - (a * x) * b) +
      ((x * b) * a - (x * a) * b) = _
  rw [hLeft, hMixed, hRight]
  simp only [associator_apply, sub_mul, mul_sub]
  abel

include hleft hright in
lemma alternative_commutator_product (c x y : A) :
    c * (x * y) - (x * y) * c =
      (c * x - x * c) * y + x * (c * y - y * c) -
        3 • associator c x y := by
  have h12 := alternative_associator_swap12 hleft c x y
  have hcyc := alternative_associator_cycle hleft hright c x y
  have hcxy : c * (x * y) = (c * x) * y - associator c x y := by
    simp only [associator_apply]
    abel
  have hxyc : (x * y) * c = x * (y * c) + associator c x y := by
    rw [← hcyc]
    simp only [associator_apply]
    abel
  have hxc : (x * c) * y = x * (c * y) - associator c x y := by
    rw [h12]
    simp only [associator_apply]
    abel
  rw [hcxy, hxyc]
  simp only [sub_mul, mul_sub]
  rw [hxc]
  abel

include hleft hright in
theorem commutator_leibniz_defect (c x y : A) :
    (c * (x * y) - (x * y) * c) -
        ((c * x - x * c) * y + x * (c * y - y * c)) =
      -(3 • associator c x y) := by
  rw [alternative_commutator_product hleft hright]
  abel

include hleft hright in
/--
The standard endomorphism `D_{a,b}` obeys the Leibniz rule in every alternative
ring.  This is the derivation construction used in the octonionic model of
`g₂`; no coordinate expansion or external property is used.
-/
theorem stanDerMap_isLeibniz (a b : A) :
    ∀ x y : A,
      stanDerMap (R := R) a b (x * y) =
        stanDerMap (R := R) a b x * y +
          x * stanDerMap (R := R) a b y := by
  intro x y
  have hnsmul_mul (u v : A) : (3 • u) * v = 3 • (u * v) := by
    simp only [show 3 • u = u + u + u by abel,
      show 3 • (u * v) = u * v + u * v + u * v by abel, add_mul]
  have hmul_nsmul (u v : A) : u * (3 • v) = 3 • (u * v) := by
    simp only [show 3 • v = v + v + v by abel,
      show 3 • (u * v) = u * v + u * v + u * v by abel, mul_add]
  rw [stanDerMap_apply_normal_form hleft hright,
    stanDerMap_apply_normal_form hleft hright,
    stanDerMap_apply_normal_form hleft hright,
    alternative_commutator_product hleft hright,
    alternative_associator_product hleft hright]
  simp only [sub_mul, mul_sub, hnsmul_mul, hmul_nsmul]
  abel

include hleft hright in
/-- The standard endomorphism bundled as a genuine nonassociative derivation. -/
noncomputable def stanDerivation (a b : A) : NonAssocDerivation R A where
  toLinearMap := stanDerMap (R := R) a b
  leibniz' := stanDerMap_isLeibniz (R := R) hleft hright a b

@[simp] theorem stanDerivation_toLinearMap (a b : A) :
    (stanDerivation (R := R) hleft hright a b).toLinearMap =
      stanDerMap (R := R) a b := rfl

end Alternative

/-- A standard derivation is a derivation of the form ∑ D_{a_i, b_i}. -/
def StanDer (D : NonAssocDerivation R A) : Prop :=
  D.toLinearMap ∈ Submodule.span R (Set.range (fun (p : A × A) => stanDerMap p.1 p.2))

open scoped BigOperators

/-- An associator derivation is a derivation of the form ∑ [L_{a_i}, R_{b_i}] where ∑ [a_i, b_i] = 0. -/
def AssDer (D : NonAssocDerivation R A) : Prop :=
  ∃ (s : Finset (A × A)), 
    (∑ p ∈ s, (p.1 * p.2 - p.2 * p.1) = 0) ∧ 
    D.toLinearMap = ∑ p ∈ s, ((L_map p.1).comp (R_map p.2) - (R_map p.2).comp (L_map p.1))

end InfoGeometry.Algebra
