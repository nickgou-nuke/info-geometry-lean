/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.LinearAlgebra.Matrix.Trace

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

variable {R : Type*} [Ring R]

/-!
### Step 1: NonUnitalNonAssocRing instance on ZornVectorMatrix R

We install the typeclass instances so that `+` = `ZornVectorMatrix.add`,
`*` = `ZornVectorMatrix.mul`, `•` = `ZornVectorMatrix.smul`, etc.
This is done by defining each instance with the explicit operation as data.
-/

noncomputable instance zvmMul : Mul (ZornVectorMatrix R) where mul := ZornVectorMatrix.mul

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

/-- The identity element. -/
def one : ZornVectorMatrix R := ZornVectorMatrix.one

section CommRing

variable {R : Type*} [CommRing R]

noncomputable instance : NonUnitalNonAssocRing (ZornVectorMatrix R) where
  zero_mul := ZornVectorMatrix.zero_mul
  mul_zero := ZornVectorMatrix.mul_zero
  left_distrib := ZornVectorMatrix.mul_add
  right_distrib := ZornVectorMatrix.add_mul

namespace ZornVectorMatrix

/-- Conjugation is scalar trace minus the original Zorn element. -/
lemma conj_eq_scalar_trace_sub (X : ZornVectorMatrix R) :
    conj X = sub (scalar (trace X)) X := by
  change conj X = scalar (trace X) - X
  have h : X + conj X = scalar (trace X) := conj_trace_identity X
  exact eq_sub_of_add_eq' h

end ZornVectorMatrix

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

/-!
### Step 4: Commutator Bracket and `sl₃(R) ↪ Der_R(𝕆_s)` Including McKinstrie–Kozlov `su(1,1)`
-/

section SL3AndSU11

open Matrix

/-- Commutator `[D, E]` of two non-associative derivations is a non-associative derivation. -/
noncomputable def zornDerBracket (D E : NonAssocDerivation R (ZornVectorMatrix R)) :
    NonAssocDerivation R (ZornVectorMatrix R) where
  toLinearMap := D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap
  leibniz' x y := by
    change D (E (x * y)) - E (D (x * y)) =
      (D (E x) - E (D x)) * y + x * (D (E y) - E (D y))
    rw [NonAssocDerivation.leibniz E x y, NonAssocDerivation.map_add D,
      NonAssocDerivation.leibniz D x y, NonAssocDerivation.map_add E,
      NonAssocDerivation.leibniz D (E x) y, NonAssocDerivation.leibniz D x (E y),
      NonAssocDerivation.leibniz E (D x) y, NonAssocDerivation.leibniz E x (D y),
      _root_.sub_mul, _root_.mul_sub]
    abel

@[simp] theorem zornDerBracket_apply
    (D E : NonAssocDerivation R (ZornVectorMatrix R)) (X : ZornVectorMatrix R) :
    zornDerBracket D E X = D (E X) - E (D X) :=
  rfl

/-- Infinitesimal `gl₃(R)` cross-product identity:
`A(u × v) + (Aᵀ u) × v + u × (Aᵀ v) = Tr(A) • (u × v)`. -/
theorem mulVec_cross_add_transpose
    (A : Matrix (Fin 3) (Fin 3) R) (u v : ZornVec3 R) :
    A.mulVec (ZornVec3.cross u v) + ZornVec3.cross (Aᵀ.mulVec u) v +
        ZornVec3.cross u (Aᵀ.mulVec v) =
      (Matrix.trace A) • ZornVec3.cross u v := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, ZornVec3.cross, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three] <;>
    ring

private theorem dot_mulVec_eq_transpose
    (A : Matrix (Fin 3) (Fin 3) R) (u w : ZornVec3 R) :
    ZornVec3.dot (A.mulVec u) w = ZornVec3.dot u (Aᵀ.mulVec w) := by
  simp only [ZornVec3.dot, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three, _root_.add_mul, _root_.mul_add, _root_.mul_assoc]
  ac_rfl

/-- Canonical `sl₃(R)` derivation on `ZornVectorMatrix R` preserving `E11` and `E22`. -/
def zornSL3Der (A : Matrix (Fin 3) (Fin 3) R) (hTr : Matrix.trace A = 0) :
    NonAssocDerivation R (ZornVectorMatrix R) where
  toFun X := ⟨0, A.mulVec X.v, fun i => -(Aᵀ.mulVec X.w i), 0⟩
  map_add' X Y := by
    ext i <;>
      simp [ZornVectorMatrix.add, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring
  map_smul' r X := by
    ext i <;>
      simp [ZornVectorMatrix.smul, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring
  leibniz' X Y := by
    have hCrossV := congrFun (mulVec_cross_add_transpose A X.w Y.w)
    have hTrT : Matrix.trace Aᵀ = 0 := by simp [Matrix.trace_transpose, hTr]
    have hCrossW := congrFun (mulVec_cross_add_transpose Aᵀ X.v Y.v)
    ext i
    · change 0 = (0 * Y.a + ZornVec3.dot (A.mulVec X.v) Y.w) +
        (X.a * 0 + ZornVec3.dot X.v (fun j => -(Aᵀ.mulVec Y.w j)))
      rw [ZornVec3.dot_neg_right, dot_mulVec_eq_transpose]
      ring
    · have hc := hCrossV i
      simp only [hTr, _root_.zero_smul, Pi.add_apply, Pi.zero_apply] at hc
      have hv : A.mulVec (fun j => X.a * Y.v j + Y.b * X.v j - ZornVec3.cross X.w Y.w j) i =
          X.a * A.mulVec Y.v i + Y.b * A.mulVec X.v i - A.mulVec (ZornVec3.cross X.w Y.w) i := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
      change A.mulVec (fun j => X.a * Y.v j + Y.b * X.v j - ZornVec3.cross X.w Y.w j) i =
        (0 * Y.v i + Y.b * A.mulVec X.v i -
          ZornVec3.cross (fun j => -(Aᵀ.mulVec X.w j)) Y.w i) +
        (X.a * A.mulVec Y.v i + 0 * X.v i -
          ZornVec3.cross X.w (fun j => -(Aᵀ.mulVec Y.w j)) i)
      have hcr1 : ZornVec3.cross (fun j => -(Aᵀ.mulVec X.w j)) Y.w i =
          -(ZornVec3.cross (Aᵀ.mulVec X.w) Y.w i) := by
        fin_cases i <;> simp [ZornVec3.cross] <;> ring
      have hcr2 : ZornVec3.cross X.w (fun j => -(Aᵀ.mulVec Y.w j)) i =
          -(ZornVec3.cross X.w (Aᵀ.mulVec Y.w) i) := by
        fin_cases i <;> simp [ZornVec3.cross] <;> ring
      rw [hv, hcr1, hcr2]
      change X.a * A.mulVec Y.v i + Y.b * A.mulVec X.v i - A.mulVec (ZornVec3.cross X.w Y.w) i =
        (0 * Y.v i + Y.b * A.mulVec X.v i - -(ZornVec3.cross (Aᵀ.mulVec X.w) Y.w i)) +
          (X.a * A.mulVec Y.v i + 0 * X.v i - -(ZornVec3.cross X.w (Aᵀ.mulVec Y.w) i))
      linear_combination -hc
    · have hc := hCrossW i
      simp only [Matrix.transpose_transpose, hTrT, _root_.zero_smul, Pi.add_apply, Pi.zero_apply] at hc
      have hw : Aᵀ.mulVec (fun j => Y.a * X.w j + X.b * Y.w j + ZornVec3.cross X.v Y.v j) i =
          Y.a * Aᵀ.mulVec X.w i + X.b * Aᵀ.mulVec Y.w i + Aᵀ.mulVec (ZornVec3.cross X.v Y.v) i := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
      change -(Aᵀ.mulVec (fun j => Y.a * X.w j + X.b * Y.w j + ZornVec3.cross X.v Y.v j) i) =
        (Y.a * -(Aᵀ.mulVec X.w i) + 0 * Y.w i + ZornVec3.cross (A.mulVec X.v) Y.v i) +
        (0 * X.w i + X.b * -(Aᵀ.mulVec Y.w i) + ZornVec3.cross X.v (A.mulVec Y.v) i)
      rw [hw]
      linear_combination -hc
    · change 0 = (ZornVec3.dot (fun j => -(Aᵀ.mulVec X.w j)) Y.v + 0 * Y.b) +
        (ZornVec3.dot X.w (A.mulVec Y.v) + X.b * 0)
      rw [ZornVec3.dot_neg_left, dot_mulVec_eq_transpose,
        Matrix.transpose_transpose, ZornVec3.dot_comm X.w]
      ring

/-- `zornSL3Der` is a Lie algebra homomorphism `sl₃(R) → Der_R(ZornVectorMatrix R)`. -/
theorem zornDerBracket_zornSL3Der
    (A B : Matrix (Fin 3) (Fin 3) R) (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    zornDerBracket (zornSL3Der A hA) (zornSL3Der B hB) =
      zornSL3Der (A * B - B * A) (by rw [Matrix.trace_sub, Matrix.trace_mul_comm]; exact _root_.sub_self _) := by
  apply NonAssocDerivation.ext
  intro X
  dsimp [zornDerBracket, zornSL3Der]
  rw [_root_.sub_eq_add_neg]
  simp only [zvm_add_def, zvm_neg_def, ZornVectorMatrix.add, ZornVectorMatrix.neg]
  ext i
  · change (0 : R) + -0 = 0; ring
  · change A.mulVec (B.mulVec X.v) i + -(B.mulVec (A.mulVec X.v) i) =
      (A * B - B * A).mulVec X.v i
    rw [← _root_.sub_eq_add_neg]
    simp [Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  · change -(Aᵀ.mulVec (fun j => -(Bᵀ.mulVec X.w j)) i) +
        -(-(Bᵀ.mulVec (fun j => -(Aᵀ.mulVec X.w j)) i)) =
      -(((A * B - B * A)ᵀ).mulVec X.w i)
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · change (0 : R) + -0 = 0; ring

/-- First non-compact `su(1,1) ⊂ sl₃(R)` generator acting on the `(0, 1)` color doublet. -/
def g22MatG1 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
/-- Second non-compact `su(1,1) ⊂ sl₃(R)` generator acting on the `(0, 1)` color doublet. -/
def g22MatG2 : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
/-- Compact `su(1,1) ⊂ sl₃(R)` Wigner rotation generator acting on the `(0, 1)` color doublet. -/
def g22MatG3 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; -1, 0, 0; 0, 0, 0]

theorem trace_g22MatG1 : Matrix.trace (g22MatG1 (R := R)) = 0 := by
  simp [g22MatG1, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

theorem trace_g22MatG2 : Matrix.trace (g22MatG2 (R := R)) = 0 := by
  simp [g22MatG2, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

theorem trace_g22MatG3 : Matrix.trace (g22MatG3 (R := R)) = 0 := by
  simp [g22MatG3, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-- Exact split-octonion derivation `G₁ ∈ Der_R(𝕆_s)` (non-compact boost). -/
def zornG22DerG1 : NonAssocDerivation R (ZornVectorMatrix R) :=
  zornSL3Der g22MatG1 trace_g22MatG1

/-- Exact split-octonion derivation `G₂ ∈ Der_R(𝕆_s)` (non-compact boost). -/
def zornG22DerG2 : NonAssocDerivation R (ZornVectorMatrix R) :=
  zornSL3Der g22MatG2 trace_g22MatG2

/-- Exact split-octonion derivation `G₃ ∈ Der_R(𝕆_s)` (compact Wigner rotation). -/
def zornG22DerG3 : NonAssocDerivation R (ZornVectorMatrix R) :=
  zornSL3Der g22MatG3 trace_g22MatG3

private theorem zornSL3Der_eq_smul
    (A B : Matrix (Fin 3) (Fin 3) R)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) (c : R)
    (hEq : A = c • B) :
    zornSL3Der A hA = c • zornSL3Der B hB := by
  apply NonAssocDerivation.ext
  intro X
  ext i
  · change (0 : R) = c * 0; ring
  · change A.mulVec X.v i = c * B.mulVec X.v i
    rw [hEq, Matrix.smul_mulVec]; rfl
  · change -(Aᵀ.mulVec X.w i) = c * -(Bᵀ.mulVec X.w i)
    rw [hEq, Matrix.transpose_smul, Matrix.smul_mulVec]
    change -(c * Bᵀ.mulVec X.w i) = c * -(Bᵀ.mulVec X.w i)
    ring
  · change (0 : R) = c * 0; ring

/-- Exact McKinstrie-Kozlov `su(1,1) ≅ sl₂(R)` derivation subalgebra inside
`Der_R(ZornVectorMatrix R) = g_{2(2)}(R)` with structure constants `(-2, +2, +2)`. -/
theorem zornG22_su11_derivation_subalgebra :
    zornDerBracket (zornG22DerG1 (R := R)) zornG22DerG2 = (-2 : R) • zornG22DerG3 ∧
    zornDerBracket (zornG22DerG2 (R := R)) zornG22DerG3 = (2 : R) • zornG22DerG1 ∧
    zornDerBracket (zornG22DerG3 (R := R)) zornG22DerG1 = (2 : R) • zornG22DerG2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [zornG22DerG1, zornG22DerG2, zornDerBracket_zornSL3Der]
    apply zornSL3Der_eq_smul
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [g22MatG1, g22MatG2, g22MatG3] <;> ring
  · rw [zornG22DerG2, zornG22DerG3, zornDerBracket_zornSL3Der]
    apply zornSL3Der_eq_smul
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [g22MatG1, g22MatG2, g22MatG3] <;> ring
  · rw [zornG22DerG3, zornG22DerG1, zornDerBracket_zornSL3Der]
    apply zornSL3Der_eq_smul
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [g22MatG1, g22MatG2, g22MatG3] <;> ring

/-- The `su(1,1) ⊂ g_{2(2)}` derivations fix the 4D split-quaternion slice `(E₁₁, E₂₂, U₂, V₂)`
pointwise, acting nontrivially on the orthogonal `(0, 1)` color doublet. -/
theorem zornG22_su11_annihilates_split_quaternion_slice :
    (zornG22DerG1 (R := R) E11 = 0 ∧ zornG22DerG1 (R := R) E22 = 0 ∧
     zornG22DerG1 (R := R) (U 2) = 0 ∧ zornG22DerG1 (R := R) (V 2) = 0) ∧
    (zornG22DerG2 (R := R) E11 = 0 ∧ zornG22DerG2 (R := R) E22 = 0 ∧
     zornG22DerG2 (R := R) (U 2) = 0 ∧ zornG22DerG2 (R := R) (V 2) = 0) ∧
    (zornG22DerG3 (R := R) E11 = 0 ∧ zornG22DerG3 (R := R) E22 = 0 ∧
     zornG22DerG3 (R := R) (U 2) = 0 ∧ zornG22DerG3 (R := R) (V 2) = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    { ext i <;> (try fin_cases i) <;>
        simp [zornG22DerG1, zornG22DerG2, zornG22DerG3, zornSL3Der,
          g22MatG1, g22MatG2, g22MatG3, E11, E22, U, V, ZornVec3.basis,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three] }

/-- On the `(0, 1)` color doublet `{U 0, U 1, V 0, V 1}`, the `su(1,1) ⊂ g_{2(2)}` derivations
satisfy `G₁² = +id`, `G₂² = +id`, and `G₃² = -id`. -/
theorem zornG22_su11_squares_on_color_doublet :
    ∀ X ∈ ([(U 0 : ZornVectorMatrix R), U 1, V 0, V 1] : List (ZornVectorMatrix R)),
      zornG22DerG1 (zornG22DerG1 X) = X ∧
      zornG22DerG2 (zornG22DerG2 X) = X ∧
      zornG22DerG3 (zornG22DerG3 X) = -X := by
  intro X hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    { ext i <;> (try fin_cases i) <;>
        simp [zornG22DerG1, zornG22DerG2, zornG22DerG3, zornSL3Der,
          g22MatG1, g22MatG2, g22MatG3, U, V, ZornVec3.basis,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, InfoGeometry.Algebra.zvm_neg_def,
          ZornVectorMatrix.neg] }

/-- Explicit non-commutativity witness in `sl₃(ℝ)`: `G₁ * G₂ ≠ G₂ * G₁`. -/
theorem g22MatG1_mul_g22MatG2_ne_comm :
    (g22MatG1 (R := ℝ)) * g22MatG2 ≠ g22MatG2 * g22MatG1 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  simp [g22MatG1, g22MatG2, Matrix.mul_apply, Fin.sum_univ_three] at h01
  norm_num at h01

/-- Explicit non-commutativity witness for the `su(1,1) ⊂ Der_ℝ(𝕆_s)` derivations. -/
theorem zornG22DerG1_bracket_zornG22DerG2_ne_zero :
    zornDerBracket (zornG22DerG1 (R := ℝ)) zornG22DerG2 ≠ 0 := by
  intro h
  have hU0 := congrArg (fun D : NonAssocDerivation ℝ (ZornVectorMatrix ℝ) => (D (U 0)).v 1) h
  have hBracket := congrArg (fun D : NonAssocDerivation ℝ (ZornVectorMatrix ℝ) => (D (U 0)).v 1)
    (zornG22_su11_derivation_subalgebra (R := ℝ)).1
  rw [hU0] at hBracket
  change (0 : ℝ) = (-2 : ℝ) * (zornG22DerG3 (R := ℝ) (U 0)).v 1 at hBracket
  simp [zornG22DerG3, zornSL3Der, g22MatG3, U, ZornVec3.basis, dotProduct,
    Fin.sum_univ_three] at hBracket

def g22MatE01 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def g22MatE10 : Matrix (Fin 3) (Fin 3) R := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- Explicit polymorphic non-commutativity witness on `Matrix (Fin 3) (Fin 3) R` (`sl₃(R)`). -/
theorem sl3_matrix_noncommutativity_witness [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨g22MatE01, g22MatE10, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  simp [g22MatE01, g22MatE10, Matrix.mul_apply, Fin.sum_univ_three] at h00

end SL3AndSU11

end CommRing


end InfoGeometry.Algebra
