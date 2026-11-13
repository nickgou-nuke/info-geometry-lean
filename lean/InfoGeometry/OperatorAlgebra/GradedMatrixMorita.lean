/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.RingTheory.Morita.Matrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Matrix Morita reduction with an arbitrary coefficient grading

The coefficient ring is not assumed commutative. A grading on an `A`-module
is an additive involution semilinear for a specified automorphism of `A`.
The two-by-two matrix grading applies that automorphism entrywise and changes
the signs of the off-diagonal entries. The actual matrix Morita functors lift
to these graded module categories; their unit and counit are proved even.

The coefficient automorphism may be outer. This is therefore distinct from
encoding only inner gradings as linear `C₂` actions. The construction below
keeps the complete coefficient action on every module and every morphism.

The general category is a category of semilinear additive involutions. We do
not identify it with a direct-sum `ZMod 2` grading over arbitrary rings, nor
assume that an arbitrary coefficient automorphism squares to the identity.
The real Clifford application supplies an involutive coefficient grading
and invertibility of two.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Matrix Matrix.Module

namespace InfoGeometry.OperatorAlgebra.GradedMatrixMorita

universe u

variable {A : Type u} [Ring A]

/-- The upper elementary operator in the two-coordinate Morita carrier. -/
def upperMatrixUnit : Matrix (Fin 2) (Fin 2) A := Matrix.single 0 1 1

/-- The lower elementary operator in the two-coordinate Morita carrier. -/
def lowerMatrixUnit : Matrix (Fin 2) (Fin 2) A := Matrix.single 1 0 1

/-- The two matrix units retain a concrete noncommuting action over every
nontrivial coefficient ring, independently of its own commutativity. -/
theorem matrix_units_noncomm [Nontrivial A] :
    (upperMatrixUnit : Matrix (Fin 2) (Fin 2) A) * lowerMatrixUnit ≠
      lowerMatrixUnit * upperMatrixUnit := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
  simpa [upperMatrixUnit, lowerMatrixUnit,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] using h00

private def matrixGradeHom (θ : A →+* A) :
    Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) A where
  toFun M := !![θ (M 0 0), -θ (M 0 1); -θ (M 1 0), θ (M 1 1)]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, add_comm]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_add, add_comm]

/-- The coefficient grading combined with the standard `1|1` matrix grading. -/
def matrixGrade (θ : A ≃+* A) :
    Matrix (Fin 2) (Fin 2) A ≃+* Matrix (Fin 2) (Fin 2) A where
  toFun := matrixGradeHom θ.toRingHom
  invFun := matrixGradeHom θ.symm.toRingHom
  left_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixGradeHom]
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixGradeHom]
  map_mul' := (matrixGradeHom θ.toRingHom).map_mul
  map_add' := (matrixGradeHom θ.toRingHom).map_add

@[simp] theorem matrixGrade_apply (θ : A ≃+* A) (M : Matrix (Fin 2) (Fin 2) A) :
    matrixGrade θ M =
      !![θ (M 0 0), -θ (M 0 1); -θ (M 1 0), θ (M 1 1)] := rfl

/-- The entry formula is conjugation of the coefficientwise grading by the
standard parity matrix. -/
theorem matrixGrade_eq_parity_conj (θ : A ≃+* A) (M : Matrix (Fin 2) (Fin 2) A) :
    matrixGrade θ M =
      !![(1 : A), 0; 0, -1] * M.map θ * !![(1 : A), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [matrixGrade_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.map_apply,
      one_mul, zero_mul, add_zero, zero_add, mul_one, mul_zero,
      neg_mul, mul_neg, neg_neg]

/-- The matrix automorphism is involutive when the coefficient grading is. -/
theorem matrixGrade_involutive (θ : A ≃+* A) (hθ : Function.Involutive θ) :
    Function.Involutive (matrixGrade θ) := by
  intro M
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> exact hθ _

@[simp] theorem matrixGrade_scalar (θ : A ≃+* A) (a : A) :
    matrixGrade θ (Matrix.scalar (Fin 2) a) = Matrix.scalar (Fin 2) (θ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem matrixGrade_corner (θ : A ≃+* A) :
    matrixGrade θ (Matrix.single (0 : Fin 2) 0 (1 : A)) =
      Matrix.single (0 : Fin 2) 0 (1 : A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

@[simp] theorem matrixGrade_lower (θ : A ≃+* A) :
    matrixGrade θ (Matrix.single (1 : Fin 2) 0 (1 : A)) =
      -Matrix.single (1 : Fin 2) 0 (1 : A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

/-- A native module with a square-one grading semilinear for the coefficient
automorphism. No equivalence or Morita conclusion is included in its data. -/
structure GradedModuleCat (θ : A ≃+* A) where
  V : ModuleCat.{u} A
  grade : V →+ V
  grade_smul : ∀ (a : A) (x : V), grade (a • x) = θ a • grade x
  grade_sq : ∀ x : V, grade (grade x) = x

namespace GradedModuleCat

variable {θ : A ≃+* A}

/-- Morphisms retain the entire coefficient action and preserve the grading. -/
structure Hom (X Y : GradedModuleCat θ) where
  hom : X.V ⟶ Y.V
  comm : ∀ x, hom (X.grade x) = Y.grade (hom x)

@[ext] theorem Hom.ext {X Y : GradedModuleCat θ} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (GradedModuleCat θ) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.V, fun _ => rfl⟩
  comp {X Y Z} f g :=
    ⟨f.hom ≫ g.hom, by
      intro x
      change g.hom (f.hom (X.grade x)) = Z.grade (g.hom (f.hom x))
      rw [f.comm, g.comm]⟩
  id_comp f := by apply Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply Hom.ext; exact Category.assoc f.hom g.hom h.hom

@[simp] theorem id_hom (X : GradedModuleCat θ) : (𝟙 X : X ⟶ X).hom = 𝟙 X.V := rfl

@[simp] theorem comp_hom {X Y Z : GradedModuleCat θ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

def forget : GradedModuleCat θ ⥤ ModuleCat A where
  obj X := X.V
  map f := f.hom

/-- An underlying module isomorphism that is even has an even inverse. -/
def isoOfUnderlying {X Y : GradedModuleCat θ} (e : X.V ≅ Y.V)
    (he : ∀ x, e.hom (X.grade x) = Y.grade (e.hom x)) : X ≅ Y where
  hom := ⟨e.hom, he⟩
  inv :=
    ⟨e.inv, by
      intro y
      have hi (x : X.V) : e.inv (e.hom x) = x :=
        congrArg (fun f : X.V ⟶ X.V => f x) e.hom_inv_id
      have hh (z : Y.V) : e.hom (e.inv z) = z :=
        congrArg (fun f : Y.V ⟶ Y.V => f z) e.inv_hom_id
      calc
        e.inv (Y.grade y) = e.inv (Y.grade (e.hom (e.inv y))) := by rw [hh]
        _ = e.inv (e.hom (X.grade (e.inv y))) := congrArg e.inv (he _).symm
        _ = X.grade (e.inv y) := hi _⟩
  hom_inv_id := by apply Hom.ext; exact e.hom_inv_id
  inv_hom_id := by apply Hom.ext; exact e.inv_hom_id

end GradedModuleCat

open GradedModuleCat

variable (θ : A ≃+* A)

section ChangeOfRings

variable {B : Type u} [Ring B] (η : B ≃+* B)

/-- Restriction of the coefficient action along a grading-preserving ring map. -/
def restrict (f : A →+* B) (hf : ∀ a, f (θ a) = η (f a)) :
    GradedModuleCat η ⥤ GradedModuleCat θ where
  obj Y :=
    letI := Module.compHom Y.V f
    { V := ModuleCat.of A Y.V
      grade := Y.grade
      grade_smul := by
        intro a x
        change Y.grade (f a • x) = f (θ a) • Y.grade x
        rw [Y.grade_smul, hf]
      grade_sq := Y.grade_sq }
  map g :=
    ⟨(ModuleCat.restrictScalars f).map g.hom, g.comm⟩
  map_id X := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_comp _ _ _

/-- A proved algebra-presentation change transports the actual graded module
category. The hypothesis is the grading equation for the given ring map, not
an assumed equivalence of module categories. -/
def ofRingEquiv (e : A ≃+* B) (he : ∀ a, e (θ a) = η (e a)) :
    GradedModuleCat θ ≌ GradedModuleCat η := by
  have he' : ∀ b, e.symm (η b) = θ (e.symm b) := by
    intro b
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let F := restrict η θ e.symm.toRingHom he'
  let G := restrict θ η e.toRingHom he
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm
  let unit : 𝟭 (GradedModuleCat θ) ≅ F ⋙ G :=
    NatIso.ofComponents (fun X =>
      GradedModuleCat.isoOfUnderlying (E.unitIso.app X.V) (by intro x; rfl)) (by
        intro X Y f
        apply GradedModuleCat.Hom.ext
        exact E.unitIso.hom.naturality f.hom)
  let counit : G ⋙ F ≅ 𝟭 (GradedModuleCat η) :=
    NatIso.ofComponents (fun Y =>
      GradedModuleCat.isoOfUnderlying (E.counitIso.app Y.V) (by intro y; rfl)) (by
        intro X Y f
        apply GradedModuleCat.Hom.ext
        exact E.counitIso.hom.naturality f.hom)
  exact
    { functor := F
      inverse := G
      unitIso := unit
      counitIso := counit
      functor_unitIso_comp := by
        intro X
        apply GradedModuleCat.Hom.ext
        exact E.functor_unitIso_comp X.V }

end ChangeOfRings

/-- Tensoring with the standard `1|1` carrier has grading `(γx₀,-γx₁)`. -/
def vectorGrade {M N : Type u} [AddCommGroup M] [AddCommGroup N] (γ : M →+ N) :
    (Fin 2 → M) →+ (Fin 2 → N) where
  toFun v := ![γ (v 0), -γ (v 1)]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp [map_add, add_comm]

@[simp] theorem vectorGrade_zero {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (γ : M →+ N) (v : Fin 2 → M) : vectorGrade γ v 0 = γ (v 0) := rfl

@[simp] theorem vectorGrade_one {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (γ : M →+ N) (v : Fin 2 → M) : vectorGrade γ v 1 = -γ (v 1) := rfl

/-- The matrix Morita induction functor on objects, with its actual grading. -/
abbrev liftObj (X : GradedModuleCat θ) : GradedModuleCat (matrixGrade θ) where
  V := ModuleCat.of (Matrix (Fin 2) (Fin 2) A) (Fin 2 → X.V)
  grade := vectorGrade X.grade
  grade_smul a v := by
    ext i
    fin_cases i <;>
      simp [vectorGrade, Matrix.Module.smul_def, Fin.sum_univ_two,
        X.grade_smul, map_add, smul_neg, neg_smul, add_comm]
  grade_sq v := by
    ext i
    fin_cases i <;> simp [vectorGrade, X.grade_sq]

def lift : GradedModuleCat θ ⥤ GradedModuleCat (matrixGrade θ) where
  obj := liftObj θ
  map {X Y} f :=
    ⟨(ModuleCat.toMatrixModCat A (Fin 2)).map f.hom, by
      intro v
      ext i
      fin_cases i
      · exact f.comm (v 0)
      · change f.hom (-X.grade (v 1)) = -Y.grade (f.hom (v 1))
        rw [map_neg, f.comm]⟩
  map_id X := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_comp _ _ _

local instance matrixCoefficientModule (M : ModuleCat (Matrix (Fin 2) (Fin 2) A)) :
    Module A M := Module.compHom M (Matrix.scalar (Fin 2))

local instance matrixCoefficientScalarTower (M : ModuleCat (Matrix (Fin 2) (Fin 2) A)) :
    IsScalarTower A (Matrix (Fin 2) (Fin 2) A) M :=
  MatrixModCat.isScalarTower_toModuleCat A M

private theorem grade_mem_corner (Y : GradedModuleCat (matrixGrade θ))
    (x : MatrixModCat.toModuleCatObj A Y.V (0 : Fin 2)) :
    Y.grade (x : Y.V) ∈ MatrixModCat.toModuleCatObj A Y.V (0 : Fin 2) := by
  rcases x.property with ⟨z, hz⟩
  refine ⟨Y.grade z, ?_⟩
  rw [← hz, Y.grade_smul, matrixGrade_corner]

/-- The invariant `E₀₀` corner carries the original coefficient grading. -/
abbrev reduceObj (Y : GradedModuleCat (matrixGrade θ)) : GradedModuleCat θ where
  V := ModuleCat.of A (MatrixModCat.toModuleCatObj A Y.V (0 : Fin 2))
  grade :=
    { toFun x := ⟨Y.grade (x : Y.V), grade_mem_corner θ Y x⟩
      map_zero' := by apply Subtype.ext; exact Y.grade.map_zero
      map_add' x y := by apply Subtype.ext; exact Y.grade.map_add _ _ }
  grade_smul a x := by
    apply Subtype.ext
    change Y.grade (Matrix.scalar (Fin 2) a • (x : Y.V)) =
      Matrix.scalar (Fin 2) (θ a) • Y.grade (x : Y.V)
    rw [Y.grade_smul, matrixGrade_scalar]
  grade_sq x := by apply Subtype.ext; exact Y.grade_sq _

def reduce : GradedModuleCat (matrixGrade θ) ⥤ GradedModuleCat θ where
  obj := reduceObj θ
  map {X Y} f :=
    ⟨(MatrixModCat.toModuleCat A (0 : Fin 2)).map f.hom, by
      intro x
      apply Subtype.ext
      exact f.comm (x : X.V)⟩
  map_id X := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by apply GradedModuleCat.Hom.ext; exact CategoryTheory.Functor.map_comp _ _ _

private def unitComponent (X : GradedModuleCat θ) :
    X ≅ (reduce θ).obj ((lift θ).obj X) :=
  GradedModuleCat.isoOfUnderlying
    ((ModuleCat.matrixEquivalence A (0 : Fin 2)).unitIso.app X.V) (by
      intro x
      apply Subtype.ext
      change (Pi.single (0 : Fin 2) (X.grade x) : Fin 2 → X.V) =
        vectorGrade X.grade (Pi.single (0 : Fin 2) x)
      ext i
      fin_cases i <;> simp [vectorGrade])

private def counitComponent (Y : GradedModuleCat (matrixGrade θ)) :
    (lift θ).obj ((reduce θ).obj Y) ≅ Y :=
  GradedModuleCat.isoOfUnderlying
    ((ModuleCat.matrixEquivalence A (0 : Fin 2)).counitIso.app Y.V) (by
      intro v
      change (∑ i : Fin 2, Matrix.single i (0 : Fin 2) (1 : A) •
          ((vectorGrade (reduceObj θ Y).grade v) i : Y.V)) =
        Y.grade (∑ i : Fin 2, Matrix.single i (0 : Fin 2) (1 : A) • (v i : Y.V))
      simp only [Fin.sum_univ_two, vectorGrade_zero, vectorGrade_one,
        map_add, Y.grade_smul, matrixGrade_corner, matrixGrade_lower]
      change Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : A) • Y.grade (v 0 : Y.V) +
          Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : A) • (-Y.grade (v 1 : Y.V)) =
        Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : A) • Y.grade (v 0 : Y.V) +
          (-Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : A)) • Y.grade (v 1 : Y.V)
      simp only [smul_neg, neg_smul])

private def unitIso : 𝟭 (GradedModuleCat θ) ≅ lift θ ⋙ reduce θ :=
  NatIso.ofComponents (unitComponent θ) (by
    intro X Y f
    apply GradedModuleCat.Hom.ext
    exact (ModuleCat.matrixEquivalence A (0 : Fin 2)).unitIso.hom.naturality f.hom)

private def counitIso : reduce θ ⋙ lift θ ≅ 𝟭 (GradedModuleCat (matrixGrade θ)) :=
  NatIso.ofComponents (counitComponent θ) (by
    intro X Y f
    apply GradedModuleCat.Hom.ext
    exact (ModuleCat.matrixEquivalence A (0 : Fin 2)).counitIso.hom.naturality f.hom)

/-- Matrix Morita equivalence with an arbitrary noncommutative coefficient
grading. Its functors and coherence isomorphisms are the native matrix Morita
ones, with their grading compatibility proved above. -/
def matrixEquivalence :
    GradedModuleCat θ ≌ GradedModuleCat (matrixGrade θ) where
  functor := lift θ
  inverse := reduce θ
  unitIso := unitIso θ
  counitIso := counitIso θ
  functor_unitIso_comp X := by
    apply GradedModuleCat.Hom.ext
    exact (ModuleCat.matrixEquivalence A (0 : Fin 2)).functor_unitIso_comp X.V

/-- The induction keeps the full matrix action, including noncommuting
coefficient entries. -/
theorem liftObj_smul (X : GradedModuleCat θ) (a : Matrix (Fin 2) (Fin 2) A)
    (v : (liftObj θ X).V) (i : Fin 2) :
    (a • v) i = a i 0 • v 0 + a i 1 • v 1 := by
  exact Fin.sum_univ_two _

/-- Every coefficient-linear operator intertwines the residual coefficient
action after induction, independently of its grading. -/
theorem mapMatrixModule_smul {X Y : GradedModuleCat θ} (D : X.V →ₗ[A] Y.V)
    (a : Matrix (Fin 2) (Fin 2) A) (v : (liftObj θ X).V) :
    D.mapMatrixModule (Fin 2) (a • v) = a • D.mapMatrixModule (Fin 2) v :=
  (D.mapMatrixModule (Fin 2)).map_smul a v

/-- Even coefficient-linear operators remain even under Morita induction. -/
theorem mapMatrixModule_even {X Y : GradedModuleCat θ} (D : X.V →ₗ[A] Y.V)
    (hD : ∀ x, D (X.grade x) = Y.grade (D x)) (v : (liftObj θ X).V) :
    D.mapMatrixModule (Fin 2) ((liftObj θ X).grade v) =
      (liftObj θ Y).grade (D.mapMatrixModule (Fin 2) v) := by
  ext i
  fin_cases i
  · exact hD (v 0)
  · change D (-X.grade (v 1)) = -Y.grade (D (v 1))
    rw [map_neg, hD]

/-- Odd coefficient-linear operators retain their anticommutation with the
module grading after induction. -/
theorem mapMatrixModule_odd {X Y : GradedModuleCat θ} (D : X.V →ₗ[A] Y.V)
    (hD : ∀ x, D (X.grade x) = -Y.grade (D x)) (v : (liftObj θ X).V) :
    D.mapMatrixModule (Fin 2) ((liftObj θ X).grade v) =
      -(liftObj θ Y).grade (D.mapMatrixModule (Fin 2) v) := by
  ext i
  fin_cases i
  · exact hD (v 0)
  · change D (-X.grade (v 1)) = -(-Y.grade (D (v 1)))
    rw [map_neg, hD]

/-- A coefficient-superlinear operator lifts with the head parity sign.
This retains supercommutation with arbitrary noncommuting coefficients. -/
def liftSemilinearOperator {X Y : GradedModuleCat θ}
    (D : X.V →ₛₗ[θ.toRingHom] Y.V) :
    (liftObj θ X).V →ₛₗ[(matrixGrade θ).toRingHom] (liftObj θ Y).V where
  toFun := vectorGrade D.toAddMonoidHom
  map_add' := (vectorGrade D.toAddMonoidHom).map_add
  map_smul' a v := by
    ext i
    fin_cases i <;>
      simp [vectorGrade, Matrix.Module.smul_def, Fin.sum_univ_two,
        D.map_smulₛₗ, map_add, smul_neg, neg_smul, add_comm]

/-- A superlinear matrix operator preserves the Morita corner because its
coefficient grading fixes `E₀₀`. The restricted map remains superlinear over
the full residual coefficient ring. -/
def reduceSemilinearOperator {Y Z : GradedModuleCat (matrixGrade θ)}
    (D : Y.V →ₛₗ[(matrixGrade θ).toRingHom] Z.V) :
    (reduceObj θ Y).V →ₛₗ[θ.toRingHom] (reduceObj θ Z).V where
  toFun x :=
    ⟨D (x : Y.V), by
      rcases x.property with ⟨y, hy⟩
      refine ⟨D y, ?_⟩
      rw [← hy, D.map_smulₛₗ, matrixGrade_corner]⟩
  map_add' x y := by apply Subtype.ext; exact D.map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    change D (Matrix.scalar (Fin 2) a • (x : Y.V)) =
      Matrix.scalar (Fin 2) (θ a) • D (x : Y.V)
    rw [D.map_smulₛₗ, matrixGrade_scalar]

/-- The actual Morita counit intertwines a superlinear operator with its
corner reduction and signed induction. This proves reconstruction of the
operator, rather than merely reconstruction of its underlying carrier. -/
theorem counit_intertwines_semilinear {Y Z : GradedModuleCat (matrixGrade θ)}
    (D : Y.V →ₛₗ[(matrixGrade θ).toRingHom] Z.V)
    (v : (liftObj θ (reduceObj θ Y)).V) :
    ((matrixEquivalence θ).counitIso.hom.app Z).hom
        (liftSemilinearOperator θ (reduceSemilinearOperator θ D) v) =
      D (((matrixEquivalence θ).counitIso.hom.app Y).hom v) := by
  change (∑ i : Fin 2, Matrix.single i (0 : Fin 2) (1 : A) •
      ((vectorGrade (reduceSemilinearOperator θ D).toAddMonoidHom v) i : Z.V)) =
    D (∑ i : Fin 2, Matrix.single i (0 : Fin 2) (1 : A) • (v i : Y.V))
  simp only [Fin.sum_univ_two, vectorGrade_zero, vectorGrade_one, map_add,
    D.map_smulₛₗ, matrixGrade_corner, matrixGrade_lower]
  change Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : A) • D (v 0 : Y.V) +
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : A) • (-D (v 1 : Y.V)) =
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : A) • D (v 0 : Y.V) +
      (-Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : A)) • D (v 1 : Y.V)
  simp only [smul_neg, neg_smul]

/-- The actual Morita unit also intertwines a coefficient-superlinear
operator with its signed induction and corner reduction. -/
theorem unit_intertwines_semilinear {X Y : GradedModuleCat θ}
    (D : X.V →ₛₗ[θ.toRingHom] Y.V) (x : X.V) :
    reduceSemilinearOperator θ (liftSemilinearOperator θ D)
        (((matrixEquivalence θ).unitIso.hom.app X).hom x) =
      ((matrixEquivalence θ).unitIso.hom.app Y).hom (D x) := by
  apply Subtype.ext
  change vectorGrade D.toAddMonoidHom (Pi.single (0 : Fin 2) x) =
    Pi.single (0 : Fin 2) (D x)
  ext i
  fin_cases i <;> simp [vectorGrade]

theorem liftSemilinearOperator_odd {X Y : GradedModuleCat θ}
    (D : X.V →ₛₗ[θ.toRingHom] Y.V)
    (hD : ∀ x, D (X.grade x) = -Y.grade (D x)) (v : (liftObj θ X).V) :
    liftSemilinearOperator θ D ((liftObj θ X).grade v) =
      -(liftObj θ Y).grade (liftSemilinearOperator θ D v) := by
  ext i
  fin_cases i
  · exact hD (v 0)
  · change -D (-X.grade (v 1)) = -(-Y.grade (-D (v 1)))
    rw [map_neg, hD, map_neg]

theorem reduceSemilinearOperator_odd {Y Z : GradedModuleCat (matrixGrade θ)}
    (D : Y.V →ₛₗ[(matrixGrade θ).toRingHom] Z.V)
    (hD : ∀ y, D (Y.grade y) = -Z.grade (D y)) (y : (reduceObj θ Y).V) :
    reduceSemilinearOperator θ D ((reduceObj θ Y).grade y) =
      -(reduceObj θ Z).grade (reduceSemilinearOperator θ D y) := by
  apply Subtype.ext
  exact hD (y : Y.V)

end InfoGeometry.OperatorAlgebra.GradedMatrixMorita
