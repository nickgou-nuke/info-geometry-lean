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
## Step 3: Derivation-comparison status
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

namespace ZornVectorMatrix

/-- Conjugation is scalar trace minus the original Zorn element. -/
lemma conj_eq_scalar_trace_sub (X : ZornVectorMatrix R) :
    conj X = sub (scalar (trace X)) X := by
  change conj X = scalar (trace X) - X
  have h : X + conj X = scalar (trace X) := conj_trace_identity X
  exact eq_sub_of_add_eq' h

/-- Kirmse's left contraction, derived from conjugation and left alternativity. -/
theorem kirmse_left (X Y : ZornVectorMatrix R) :
    mul (conj X) (mul X Y) = smul (norm X) Y := by
  rw [conj_eq_scalar_trace_sub, sub_mul, scalar_mul]
  have halt : mul X (mul X Y) = mul (mul X X) Y := by
    have h := associator_left_alternative X Y
    change sub (mul (mul X X) Y) (mul X (mul X Y)) = zero at h
    change mul (mul X X) Y - mul X (mul X Y) = 0 at h
    exact (sub_eq_zero.mp h).symm
  rw [halt, ← smul_mul, ← scalar_mul, ← sub_mul, ← sub_mul]
  rw [← conj_eq_scalar_trace_sub, conj_norm_identity_right, scalar_mul]

/-- Kirmse's right contraction, derived from conjugation and right alternativity. -/
theorem kirmse_right (X Y : ZornVectorMatrix R) :
    mul (mul Y X) (conj X) = smul (norm X) Y := by
  rw [conj_eq_scalar_trace_sub, mul_sub, mul_scalar]
  have halt : mul (mul Y X) X = mul Y (mul X X) := by
    have h := associator_right_alternative Y X
    change sub (mul (mul Y X) X) (mul Y (mul X X)) = zero at h
    change mul (mul Y X) X - mul Y (mul X X) = 0 at h
    exact sub_eq_zero.mp h
  rw [halt, ← mul_smul, ← mul_scalar, ← mul_sub, ← mul_sub]
  rw [← conj_eq_scalar_trace_sub, conj_norm_identity_left, mul_scalar]

/-- Scalar trace is insensitive to reassociation of a triple Zorn product. -/
theorem trace_mul_assoc (X Y Z : ZornVectorMatrix R) :
    trace (mul (mul X Y) Z) = trace (mul X (mul Y Z)) := by
  have h := trace_associator X Y Z
  change trace (sub (mul (mul X Y) Z) (mul X (mul Y Z))) = 0 at h
  rw [trace_sub] at h
  exact sub_eq_zero.mp h

/-- Scalar trace is cyclic on a triple Zorn product. -/
theorem trace_mul_cyclic (X Y Z : ZornVectorMatrix R) :
    trace (mul (mul X Y) Z) = trace (mul (mul Y Z) X) := by
  calc
    trace (mul (mul X Y) Z) = trace (mul Z (mul X Y)) := trace_mul_comm _ _
    _ = trace (mul (mul Z X) Y) := (trace_mul_assoc Z X Y).symm
    _ = trace (mul Y (mul Z X)) := trace_mul_comm _ _
    _ = trace (mul (mul Y Z) X) := (trace_mul_assoc Y Z X).symm

/-- Conjugating and reversing a triple product preserves its scalar trace. -/
theorem trace_conj_triple_reverse (X Y Z : ZornVectorMatrix R) :
    trace (mul (mul (conj Z) (conj Y)) (conj X)) =
      trace (mul (mul X Y) Z) := by
  calc
    trace (mul (mul (conj Z) (conj Y)) (conj X)) =
        trace (mul (conj Z) (mul (conj Y) (conj X))) :=
      trace_mul_assoc _ _ _
    _ = trace (conj (mul (mul X Y) Z)) := by
      rw [conj_mul, conj_mul]
    _ = trace (mul (mul X Y) Z) := trace_conj _

/-- Polarization of the Zorn composition norm, in trace-pairing form. -/
theorem norm_sub_eq_norm_add_norm_sub_trace_mul_conj
    (X Y : ZornVectorMatrix R) :
    norm (sub X Y) = norm X + norm Y - trace (mul X (conj Y)) := by
  simp [norm, sub, add, neg, trace, mul, conj, ZornVec3.dot, Fin.sum_univ_three]
  ring

end ZornVectorMatrix

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
  ZornVectorMatrix.Derivation.ext fun _ => rfl

/-- Round-trip: bundled → unbundled → bundled is identity. -/
theorem derivation_equiv_right_inv (D : NonAssocDerivation R (ZornVectorMatrix R)) :
    toNonAssocDerivation (fromNonAssocDerivation D) = D :=
  NonAssocDerivation.ext fun _ => rfl

/-- The bundled ↔ unbundled derivation equivalence. -/
def derivationEquiv :
    ZornVectorMatrix.Derivation (R := R) ≃ NonAssocDerivation R (ZornVectorMatrix R) where
  toFun := toNonAssocDerivation
  invFun := fromNonAssocDerivation
  left_inv := derivation_equiv_left_inv
  right_inv := derivation_equiv_right_inv

/-!
### Native standard derivations of the split octonions

This specializes the abstract alternative-ring theorem to the canonical Zorn
owner.  These standard derivations are the concrete inner derivations entering
the split-octonion realization of the Lie algebra of type `G₂`.
-/

/-- The bundled Zorn product satisfies the left alternative law. -/
theorem zorn_left_alternative (X Y : ZornVectorMatrix R) :
    (X * X) * Y = X * (X * Y) := by
  have h := ZornVectorMatrix.associator_left_alternative X Y
  change (X * X) * Y - X * (X * Y) = 0 at h
  exact sub_eq_zero.mp h

/-- The bundled Zorn product satisfies the right alternative law. -/
theorem zorn_right_alternative (X Y : ZornVectorMatrix R) :
    (Y * X) * X = Y * (X * X) := by
  have h := ZornVectorMatrix.associator_right_alternative Y X
  change (Y * X) * X - Y * (X * X) = 0 at h
  exact sub_eq_zero.mp h

/-- The standard operator `D_{a,b}` as a genuine derivation of Zorn split octonions. -/
noncomputable def zornStanDerivation (a b : ZornVectorMatrix R) :
    NonAssocDerivation R (ZornVectorMatrix R) :=
  stanDerivation (R := R) zorn_left_alternative zorn_right_alternative a b

@[simp] theorem zornStanDerivation_toLinearMap (a b : ZornVectorMatrix R) :
    (zornStanDerivation a b).toLinearMap = stanDerMap (R := R) a b := rfl

/-- Kleinfeld's normal form for the canonical Zorn standard derivation. -/
theorem zornStanDerivation_apply_normal_form
    (a b x : ZornVectorMatrix R) :
    zornStanDerivation a b x =
      ((a * b - b * a) * x - x * (a * b - b * a)) -
        3 • _root_.associator a b x := by
  exact stanDerMap_apply_normal_form
    (R := R) zorn_left_alternative zorn_right_alternative a b x

/-- Every canonical Zorn standard derivation belongs to the standard span. -/
theorem zornStanDerivation_isStandard (a b : ZornVectorMatrix R) :
    StanDer (zornStanDerivation a b) := by
  change stanDerMap (R := R) a b ∈
    Submodule.span R (Set.range (fun p : ZornVectorMatrix R × ZornVectorMatrix R =>
      stanDerMap (R := R) p.1 p.2))
  exact Submodule.subset_span ⟨(a, b), rfl⟩

/-!
### Step 3: Concrete consequences

Only proved consequences are exported below.  The stronger classification of
all derivations is not represented by a proposition-valued placeholder.
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


end InfoGeometry.Algebra
