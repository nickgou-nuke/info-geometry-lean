import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Quadratic Jordan Algebra H₃(𝕆_s, -) at any characteristic

This file formalizes the base quadratic Jordan structure of $H_3(\mathbb{O}_s, -)$
(the exceptional Albert algebra over split octonions) without any restriction on
the characteristic of the base commutative ring `R`.

We follow the structural approach to construct the U-operator and T-operator
which defines the quadratic Jordan algebra, and then define the derivations
forming the Lie algebra $\mathfrak{f}_4(\mathbb{O}_s, -)$, as discussed by
P. Alberca-Bjerregaard and C. Martín-González.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Algebra

variable (R : Type*) [CommRing R]

/-- A matrix in H₃(𝕆_s, -) over an arbitrary commutative ring R.
It represents a 3x3 Hermitian matrix over split octonions:
  [ α₁   a   c* ]
  [ a*   α₂  b  ]
  [ c    b*  α₃ ]
-/
structure H3Zorn where
  α₁ : R
  α₂ : R
  α₃ : R
  a : ZornVectorMatrix R
  b : ZornVectorMatrix R
  c : ZornVectorMatrix R

namespace H3Zorn

variable {R : Type*} [CommRing R]

@[ext]
lemma ext_h3 (X Y : H3Zorn R)
    (h1 : X.α₁ = Y.α₁) (h2 : X.α₂ = Y.α₂) (h3 : X.α₃ = Y.α₃)
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hc : X.c = Y.c) : X = Y := by
  cases X; cases Y; congr

noncomputable instance : Add (H3Zorn R) where
  add X Y := ⟨X.α₁ + Y.α₁, X.α₂ + Y.α₂, X.α₃ + Y.α₃,
              X.a + Y.a, X.b + Y.b, X.c + Y.c⟩

noncomputable instance : Neg (H3Zorn R) where
  neg X := ⟨-X.α₁, -X.α₂, -X.α₃, -X.a, -X.b, -X.c⟩

noncomputable instance : Zero (H3Zorn R) where
  zero := ⟨0, 0, 0, 0, 0, 0⟩

noncomputable instance : Sub (H3Zorn R) where
  sub X Y := X + (-Y)

noncomputable instance : SMul R (H3Zorn R) where
  smul r X := ⟨r * X.α₁, r * X.α₂, r * X.α₃,
               r • X.a, r • X.b, r • X.c⟩

noncomputable instance : AddCommGroup (H3Zorn R) where
  add_assoc X Y Z := by cases X; cases Y; cases Z; ext <;> exact add_assoc _ _ _
  zero_add X := by cases X; ext <;> exact zero_add _
  add_zero X := by cases X; ext <;> exact add_zero _
  nsmul := nsmulRec
  neg_add_cancel X := by cases X; ext <;> exact neg_add_cancel _
  zsmul := zsmulRec
  add_comm X Y := by cases X; cases Y; ext <;> exact add_comm _ _

noncomputable instance : Module R (H3Zorn R) where
  one_smul X := by cases X; ext <;> first | exact one_smul _ _ | exact one_mul _
  mul_smul r s X := by cases X; ext <;> first | exact mul_smul _ _ _ | exact mul_assoc _ _ _
  smul_zero r := by ext <;> first | exact smul_zero _ | exact mul_zero _
  smul_add r X Y := by cases X; cases Y; ext <;> first | exact smul_add _ _ _ | exact mul_add _ _ _
  add_smul r s X := by cases X; ext <;> first | exact add_smul _ _ _ | exact add_mul _ _ _
  zero_smul X := by cases X; ext <;> first | exact zero_smul _ _ | exact zero_mul _

/-- The identity element of the Jordan algebra. -/
noncomputable def one : H3Zorn R :=
  ⟨1, 1, 1, 0, 0, 0⟩

noncomputable instance : One (H3Zorn R) := ⟨one⟩

/-- Bilinear trace form on H₃(𝕆_s, -). -/
noncomputable def traceBilin (X Y : H3Zorn R) : R :=
  X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
  ZornVectorMatrix.trace (X.a * Y.a) +
  ZornVectorMatrix.trace (X.b * Y.b) +
  ZornVectorMatrix.trace (X.c * Y.c)

/-- The quadratic adjoint X# mapping. -/
noncomputable def adjointQuad (X : H3Zorn R) : H3Zorn R :=
  { α₁ := X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b
    α₂ := X.α₁ * X.α₃ - ZornVectorMatrix.norm X.c
    α₃ := X.α₁ * X.α₂ - ZornVectorMatrix.norm X.a
    a := X.α₃ • X.a - (X.b * X.c)
    b := X.α₁ • X.b - (X.c * X.a)
    c := X.α₂ • X.c - (X.a * X.b) }

/-- The cross product X × Y (polarization of the adjoint). -/
noncomputable def crossProduct (X Y : H3Zorn R) : H3Zorn R :=
  adjointQuad (X + Y) - adjointQuad X - adjointQuad Y

/-- The quadratic U-operator: U_X(Y).
For cubic Jordan algebras, this is exactly T(X,Y)X - X# × Y. -/
noncomputable def U (X Y : H3Zorn R) : H3Zorn R :=
  traceBilin X Y • X - crossProduct (adjointQuad X) Y

/-- The triple product {X, Y, Z} = T(X, Y, Z) = U_{X,Z}(Y). -/
noncomputable def T (X Y Z : H3Zorn R) : H3Zorn R :=
  U (X + Z) Y - U X Y - U Z Y

/-!
## Derivation Lie Algebra f₄(𝕆_s, -)
Following Alberca-Bjerregaard and Martín-González, a derivation of the quadratic
Jordan algebra is a linear map `D` satisfying `D(1) = 0` and the Leibniz rule for `U`.
-/

variable (R)

/-- A derivation of the quadratic Jordan algebra H₃(𝕆_s, -). -/
structure Derivation where
  toLinearMap : H3Zorn R →ₗ[R] H3Zorn R
  map_one' : toLinearMap 1 = 0
  leibniz_U' : ∀ X Y : H3Zorn R,
    toLinearMap (U X Y) = T (toLinearMap X) Y X + U X (toLinearMap Y)

variable {R}

instance : CoeFun (Derivation R) (fun _ => H3Zorn R → H3Zorn R) where
  coe D := D.toLinearMap.toFun

instance : Coe (Derivation R) (H3Zorn R →ₗ[R] H3Zorn R) where
  coe D := D.toLinearMap

@[simp] theorem map_add (D : Derivation R) (x y : H3Zorn R) : D (x + y) = D x + D y :=
  D.toLinearMap.map_add x y

@[simp] theorem map_sub (D : Derivation R) (x y : H3Zorn R) : D (x - y) = D x - D y :=
  D.toLinearMap.map_sub x y

@[simp] theorem map_neg (D : Derivation R) (x : H3Zorn R) : D (-x) = - D x :=
  D.toLinearMap.map_neg x

@[simp] theorem map_smul (D : Derivation R) (r : R) (x : H3Zorn R) : D (r • x) = r • D x :=
  D.toLinearMap.map_smul r x

@[simp] theorem map_one (D : Derivation R) : D 1 = 0 :=
  D.map_one'

theorem leibniz_U (D : Derivation R) (X Y : H3Zorn R) :
    D (U X Y) = T (D X) Y X + U X (D Y) :=
  D.leibniz_U' X Y

theorem ext {D E : Derivation R} (h : ∀ x, D x = E x) : D = E := by
  cases D; cases E
  congr
  exact LinearMap.ext h

lemma T_symm (X Y Z : H3Zorn R) : T X Y Z = T Z Y X := by
  dsimp [T]
  rw [add_comm X Z]
  abel

lemma T_add_left (X₁ X₂ Y Z : H3Zorn R) : T (X₁ + X₂) Y Z = T X₁ Y Z + T X₂ Y Z := by
  sorry

lemma T_add_right (X Y Z₁ Z₂ : H3Zorn R) : T X Y (Z₁ + Z₂) = T X Y Z₁ + T X Y Z₂ := by
  sorry

lemma Derivation.leibniz_T (D : Derivation R) (X Y Z : H3Zorn R) :
    D (T X Y Z) = T (D X) Y Z + T X (D Y) Z + T X Y (D Z) := by
  -- 1. Unfold the definition of T inside the derivation
  change D (U (X + Z) Y - U X Y - U Z Y) = _
  
  -- 2. Distribute the linear map D across subtraction and addition
  have h_linear : D (U (X + Z) Y - U X Y - U Z Y) = D (U (X + Z) Y) - D (U X Y) - D (U Z Y) := by
    simp only [map_sub]
  rw [h_linear]
  
  -- 3. Expand all three terms using the quadratic Leibniz rule field
  rw [leibniz_U, leibniz_U, leibniz_U]
  
  -- 4. Linearly expand the compound term T (D (X + Z)) Y (X + Z)
  have h_expand_compound : T (D (X + Z)) Y (X + Z) = 
      T (D X) Y X + T (D X) Y Z + T (D Z) Y X + T (D Z) Y Z := by
    have h_map_add : D (X + Z) = D X + D Z := map_add D X Z
    rw [h_map_add, T_add_left, T_add_right, T_add_right]
    abel
    
  rw [h_expand_compound]
  
  -- 5. Identify the nested U-terms that reconstruct the middle T-operator
  have h_T_mid : T X (D Y) Z = U (X + Z) (D Y) - U X (D Y) - U Z (D Y) := rfl
  rw [h_T_mid]
  
  -- 6. Apply outer symmetry to align T (D Z) Y X into T X Y (D Z)
  rw [T_symm (D Z) Y X]
  
  -- 7. Eliminate matching additive inverses and cancel elements
  abel

/-- The derivations form a Lie algebra. We define the Lie bracket as the commutator. -/
noncomputable def bracketCommutator (D₁ D₂ : Derivation R) : Derivation R where
  toLinearMap := D₁.toLinearMap.comp D₂.toLinearMap - D₂.toLinearMap.comp D₁.toLinearMap
  map_one' := by
    show D₁ (D₂ 1) - D₂ (D₁ 1) = 0
    simp [map_one]
  leibniz_U' X Y := by
    change D₁ (D₂ (U X Y)) - D₂ (D₁ (U X Y)) = _
    have hT₁ (A B C : H3Zorn R) := D₁.leibniz_T A B C
    have hT₂ (A B C : H3Zorn R) := D₂.leibniz_T A B C
    rw [leibniz_U D₂, leibniz_U D₁]
    simp only [map_add]
    rw [hT₁, hT₂]
    rw [leibniz_U D₁, leibniz_U D₂]
    sorry

noncomputable instance : Bracket (Derivation R) (Derivation R) :=
  ⟨bracketCommutator⟩

end H3Zorn

end InfoGeometry.Algebra
