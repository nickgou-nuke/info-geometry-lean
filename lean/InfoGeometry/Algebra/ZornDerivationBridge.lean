import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Bridge: ZornVectorMatrix.Derivation ↔ NonAssocDerivation

This file installs a `NonUnitalNonAssocRing` instance on `ZornVectorMatrix R` using
the unbundled operations already proven correct in `ZornVectorMatrix.lean`, then
constructs an equivalence between the unbundled `ZornVectorMatrix.Derivation` and the
bundled `NonAssocDerivation R (ZornVectorMatrix R)`.

## Step 1: NonUnitalNonAssocRing instance
## Step 2: Derivation equivalence
## Step 3: Theorem 5.1 — Der(C) = AssDer(C)
-/

namespace InfoGeometry.Algebra

open ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-!
### Step 1: NonUnitalNonAssocRing instance on ZornVectorMatrix R

We install the typeclass instances so that `+` = `ZornVectorMatrix.add`,
`*` = `ZornVectorMatrix.mul`, `•` = `ZornVectorMatrix.smul`, etc.
This is done by defining each instance with the explicit operation as data.
-/

noncomputable instance zvmAdd : Add (ZornVectorMatrix R) where add := ZornVectorMatrix.add
noncomputable instance zvmNeg : Neg (ZornVectorMatrix R) where neg := ZornVectorMatrix.neg
noncomputable instance zvmZero : Zero (ZornVectorMatrix R) where zero := ZornVectorMatrix.zero
noncomputable instance zvmMul : Mul (ZornVectorMatrix R) where mul := ZornVectorMatrix.mul
noncomputable instance zvmSMul : SMul R (ZornVectorMatrix R) where smul := ZornVectorMatrix.smul

-- Definitional equalities — these must hold by construction
@[simp] theorem zvm_add_def (X Y : ZornVectorMatrix R) :
    X + Y = ZornVectorMatrix.add X Y := rfl
@[simp] theorem zvm_neg_def (X : ZornVectorMatrix R) :
    -X = ZornVectorMatrix.neg X := rfl
@[simp] theorem zvm_zero_def :
    (0 : ZornVectorMatrix R) = ZornVectorMatrix.zero := rfl
@[simp] theorem zvm_mul_def (X Y : ZornVectorMatrix R) :
    X * Y = ZornVectorMatrix.mul X Y := rfl
@[simp] theorem zvm_smul_def (r : R) (X : ZornVectorMatrix R) :
    r • X = ZornVectorMatrix.smul r X := rfl

noncomputable instance : Sub (ZornVectorMatrix R) where sub X Y := X + (-Y)

noncomputable instance : AddGroup (ZornVectorMatrix R) :=
  AddGroup.ofLeftAxioms ZornVectorMatrix.add_assoc ZornVectorMatrix.zero_add
    (fun X => ZornVectorMatrix.add_left_neg X)

noncomputable instance : AddCommGroup (ZornVectorMatrix R) :=
  AddCommGroup.mk ZornVectorMatrix.add_comm

noncomputable instance : NonUnitalNonAssocRing (ZornVectorMatrix R) where
  zero_mul := ZornVectorMatrix.zero_mul
  mul_zero := ZornVectorMatrix.mul_zero
  left_distrib := ZornVectorMatrix.mul_add
  right_distrib := ZornVectorMatrix.add_mul

noncomputable instance : Module R (ZornVectorMatrix R) where
  one_smul := ZornVectorMatrix.one_smul
  mul_smul := fun r s X => by
    show ZornVectorMatrix.smul (r * s) X = ZornVectorMatrix.smul r (ZornVectorMatrix.smul s X)
    ext i <;> simp [ZornVectorMatrix.smul, mul_assoc]
  smul_zero := fun r => ZornVectorMatrix.smul_zero r
  smul_add := ZornVectorMatrix.smul_add
  add_smul := ZornVectorMatrix.add_smul
  zero_smul := ZornVectorMatrix.zero_smul

noncomputable instance : IsScalarTower R (ZornVectorMatrix R) (ZornVectorMatrix R) where
  smul_assoc r X Y := by
    show ZornVectorMatrix.mul (ZornVectorMatrix.smul r X) Y =
         ZornVectorMatrix.smul r (ZornVectorMatrix.mul X Y)
    exact ZornVectorMatrix.smul_mul r X Y

noncomputable instance : SMulCommClass R (ZornVectorMatrix R) (ZornVectorMatrix R) where
  smul_comm r X Y := by
    show ZornVectorMatrix.smul r (ZornVectorMatrix.mul X Y) =
         ZornVectorMatrix.mul X (ZornVectorMatrix.smul r Y)
    exact (ZornVectorMatrix.mul_smul r X Y).symm

/-!
### Step 2: Derivation equivalence
-/

/-- Convert an unbundled `ZornVectorMatrix.Derivation` into a bundled `NonAssocDerivation`. -/
def toNonAssocDerivation (D : ZornVectorMatrix.Derivation (R := R)) :
    NonAssocDerivation R (ZornVectorMatrix R) where
  toLinearMap :=
    { toFun := D.toFun
      map_add' := fun X Y => by
        show D.toFun (X + Y) = D.toFun X + D.toFun Y
        exact D.map_add' X Y
      map_smul' := fun r X => by
        show D.toFun (r • X) = r • D.toFun X
        exact D.map_smul' r X }
  leibniz' := fun X Y => by
    show D.toFun (X * Y) = D.toFun X * Y + X * D.toFun Y
    exact D.map_mul' X Y

/-- Convert a bundled `NonAssocDerivation` into an unbundled `ZornVectorMatrix.Derivation`. -/
def fromNonAssocDerivation (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    ZornVectorMatrix.Derivation (R := R) where
  toFun := D.toLinearMap.toFun
  map_add' := fun X Y => by
    show D.toLinearMap.toFun (ZornVectorMatrix.add X Y) =
         ZornVectorMatrix.add (D.toLinearMap.toFun X) (D.toLinearMap.toFun Y)
    exact D.toLinearMap.map_add X Y
  map_smul' := fun r X => by
    show D.toLinearMap.toFun (ZornVectorMatrix.smul r X) =
         ZornVectorMatrix.smul r (D.toLinearMap.toFun X)
    exact D.toLinearMap.map_smul r X
  map_mul' := fun X Y => by
    show D.toLinearMap.toFun (ZornVectorMatrix.mul X Y) =
         ZornVectorMatrix.add
           (ZornVectorMatrix.mul (D.toLinearMap.toFun X) Y)
           (ZornVectorMatrix.mul X (D.toLinearMap.toFun Y))
    exact D.leibniz' X Y

/-- Round-trip: unbundled → bundled → unbundled is identity. -/
theorem derivation_equiv_left_inv (D : ZornVectorMatrix.Derivation (R := R)) :
    fromNonAssocDerivation (toNonAssocDerivation D) = D :=
  ZornVectorMatrix.Derivation.ext fun X => rfl

/-- Round-trip: bundled → unbundled → bundled is identity. -/
theorem derivation_equiv_right_inv (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    toNonAssocDerivation (fromNonAssocDerivation D) = D :=
  NonAssocDerivation.ext fun X => rfl

/-- The bundled ↔ unbundled derivation equivalence. -/
def derivationEquiv :
    ZornVectorMatrix.Derivation (R := R) ≃ NonAssocDerivation R (ZornVectorMatrix R) where
  toFun := toNonAssocDerivation
  invFun := fromNonAssocDerivation
  left_inv := derivation_equiv_left_inv
  right_inv := derivation_equiv_right_inv

/-!
### Step 3: Theorem 5.1 — Der(C) = AssDer(C) for Zorn split-octonions

Following Loos-Petersson-Racine, Theorem 5.1:
Every derivation of an octonion algebra over any commutative ring is an
associator derivation.
-/

/-- The identity element. -/
def one : ZornVectorMatrix R := ZornVectorMatrix.one

/-- Derivation of the identity element is zero. -/
@[simp] theorem map_one (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    D one = 0 := by
  have H := ZornVectorMatrix.Derivation.map_one (fromNonAssocDerivation D)
  exact H

/-- Evaluation of Derivation on E11 and E22. -/
theorem map_E11_add_E22 (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    D E11 + D E22 = 0 := by
  have H : (E11 : ZornVectorMatrix R) + E22 = one := by ext i <;> simp [E11, E22, one, ZornVectorMatrix.one, add, ZornVectorMatrix.add]
  have h1 : D ((E11 : ZornVectorMatrix R) + E22) = D one := congrArg D H
  rw [map_one, NonAssocDerivation.map_add] at h1
  exact h1

theorem map_E11_mul_E11 (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    D E11 = D E11 * E11 + E11 * D E11 := by
  have h : D (E11 * E11) = D E11 * E11 + E11 * D E11 := D.leibniz E11 E11
  have H : (E11 : ZornVectorMatrix R) * E11 = E11 := by rw [zvm_mul_def, E11_mul_E11]
  rwa [H] at h

theorem map_E22_mul_E22 (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    D E22 = D E22 * E22 + E22 * D E22 := by
  have h : D (E22 * E22) = D E22 * E22 + E22 * D E22 := D.leibniz E22 E22
  have H : (E22 : ZornVectorMatrix R) * E22 = E22 := by rw [zvm_mul_def, E22_mul_E22]
  rwa [H] at h


/-- **Loos-Petersson-Racine Theorem 5.1** (statement).
Every derivation of the split-octonion algebra (Zorn vector matrices) over
a commutative ring is an associator derivation. -/
theorem zorn_der_eq_assDer (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    AssDer D := by
  sorry

/-- Corollary: every derivation of the split-octonion algebra is a standard derivation. -/
theorem zorn_assDer_is_stanDer (D : NonAssocDerivation R (ZornVectorMatrix R))
    (hD : AssDer D) : StanDer D := by
  sorry

end InfoGeometry.Algebra
