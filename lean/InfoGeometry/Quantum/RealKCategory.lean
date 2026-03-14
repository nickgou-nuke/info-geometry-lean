import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# InfoGeometry.Quantum.RealKCategory

Categorical real/complex bridge via an internal square-minus-one operator.

`RealKVect` bundles a real vector space with a distinguished endomorphism
`K` satisfying `K^2 = -Id`. Morphisms are real-linear maps commuting with `K`.

This module provides a concrete first categorical layer:
- the category `RealKVect`;
- a derived complex action on each object from `K`;
- a functor `ModuleCat ℂ ⥤ RealKVect` (complex spaces as real spaces with `K := I•`).
-/

open CategoryTheory

universe u

namespace InfoGeometry.Quantum.RealKCategory

/-- Real vector spaces with an internal complex axis `K^2 = -Id`. -/
structure RealKVect where
  V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℝ V]
  K : V →ₗ[ℝ] V
  K_sq : K.comp K = -(LinearMap.id : V →ₗ[ℝ] V)

attribute [instance] RealKVect.instAddCommGroup RealKVect.instModule

instance : CoeSort RealKVect (Type u) := ⟨RealKVect.V⟩

namespace RealKVect

/-- Morphisms in `RealKVect`: real-linear maps commuting with `K`. -/
@[ext] structure Hom (X Y : RealKVect) where
  hom : X →ₗ[ℝ] Y
  comm : hom.comp X.K = Y.K.comp hom

instance (X Y : RealKVect) : CoeFun (Hom X Y) (fun _ => X → Y) := ⟨fun f => f.hom⟩

noncomputable instance : Category RealKVect where
  Hom X Y := Hom X Y
  id X :=
    { hom := LinearMap.id
      comm := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      comm := by
        calc
          (g.hom.comp f.hom).comp X.K
              = g.hom.comp (f.hom.comp X.K) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.K.comp f.hom) := by rw [f.comm]
          _ = (g.hom.comp Y.K).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.K.comp g.hom).comp f.hom := by rw [g.comm]
          _ = Z.K.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc] }

@[simp] lemma hom_id (X : RealKVect) : ((𝟙 X : X ⟶ X).hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : RealKVect} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).hom) = g.hom.comp f.hom := rfl

/-- Derived real action of a complex scalar through `K`. -/
noncomputable def complexSMul (X : RealKVect) (z : ℂ) (v : X) : X :=
  z.re • v + z.im • (X.K v)

/-- Derived complex module structure on a `RealKVect` object. -/
noncomputable def complexModule (X : RealKVect) : Module ℂ X where
  smul z v := complexSMul X z v
  one_smul v := by
    change ((1 : ℂ).re • v + (1 : ℂ).im • X.K v = v)
    simp [complexSMul]
  mul_smul z w v := by
    rcases z with ⟨a, b⟩
    rcases w with ⟨c, d⟩
    have hK2 : X.K (X.K v) = -v := by
      have h := congrArg (fun T : X →ₗ[ℝ] X => T v) X.K_sq
      simpa using h
    change ((a * c - b * d) • v + (a * d + b * c) • X.K v)
      = a • (c • v + d • X.K v) + b • X.K (c • v + d • X.K v)
    calc
      (a * c - b * d) • v + (a * d + b * c) • X.K v
          = (a * c + -1 • (b * d)) • v + ((a * d) • X.K v + (b * c) • X.K v) := by
              simp [sub_eq_add_neg, add_smul, smul_add, smul_smul, mul_assoc, mul_left_comm,
                mul_comm]
      _ = (a * c) • v + ((-1 : ℝ) • (b * d) • v + ((a * d) • X.K v + (b * c) • X.K v)) := by
            simp [add_smul, add_assoc, add_left_comm, add_comm]
      _ = a • (c • v + d • X.K v) + b • X.K (c • v + d • X.K v) := by
            simp [map_add, map_smul, hK2, smul_add, smul_smul, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm]
  smul_add z v w := by
    change z.re • (v + w) + z.im • X.K (v + w)
      = (z.re • v + z.im • X.K v) + (z.re • w + z.im • X.K w)
    simp [complexSMul, map_add, smul_add, add_assoc, add_left_comm, add_comm]
  smul_zero z := by
    change z.re • (0 : X) + z.im • X.K (0 : X) = 0
    simp [complexSMul]
  add_smul z w v := by
    rcases z with ⟨a, b⟩
    rcases w with ⟨c, d⟩
    change ((a + c) • v + (b + d) • X.K v)
      = (a • v + b • X.K v) + (c • v + d • X.K v)
    simp [complexSMul, add_smul, add_assoc, add_left_comm, add_comm]
  zero_smul v := by
    change ((0 : ℂ).re • v + (0 : ℂ).im • X.K v = 0)
    simp [complexSMul]

/-- `Complex.I` acts as the internal operator `K` under the derived action. -/
lemma complexI_smul_eq_K (X : RealKVect) (v : X) :
    letI : Module ℂ X := complexModule X
    (Complex.I : ℂ) • v = X.K v := by
  change (Complex.I.re • v + Complex.I.im • X.K v = X.K v)
  simp

/-- Convert a `RealKVect` object into a complex module object. -/
noncomputable def asComplexModule (X : RealKVect) : ModuleCat ℂ := by
  letI : Module ℂ X := complexModule X
  exact ModuleCat.of ℂ X

/-- Convert a `RealKVect` morphism into a complex-linear map on derived modules. -/
noncomputable def Hom.toComplexLinear {X Y : RealKVect} (f : X ⟶ Y) :
    asComplexModule X ⟶ asComplexModule Y := by
  letI : Module ℂ X := complexModule X
  letI : Module ℂ Y := complexModule Y
  refine ModuleCat.ofHom
    { toFun := f.hom
      map_add' := by simpa using f.hom.map_add
      map_smul' := ?_ }
  intro z x
  rcases z with ⟨a, b⟩
  have hcomm : f.hom (X.K x) = Y.K (f.hom x) := by
    exact congrArg (fun T : X →ₗ[ℝ] Y => T x) f.comm
  change f.hom (a • x + b • X.K x) = a • f.hom x + b • Y.K (f.hom x)
  simp [map_add, map_smul, hcomm]

/-- Backward functor: use the derived complex action from `K`. -/
noncomputable def realKToComplex : RealKVect ⥤ ModuleCat ℂ where
  obj X := asComplexModule X
  map {X Y} f := f.toComplexLinear
  map_id X := by
    rfl
  map_comp f g := by
    rfl

/-- Forward functor: forget to real and remember `K := (I • ·)`. -/
noncomputable def complexToRealK : ModuleCat ℂ ⥤ RealKVect where
  obj W :=
    { V := W
      K :=
        { toFun := fun v => (Complex.I : ℂ) • v
          map_add' := by simp
          map_smul' := by
            intro r v
            simpa using (smul_comm (Complex.I : ℂ) r v) }
      K_sq := by
        ext v
        change (Complex.I : ℂ) • ((Complex.I : ℂ) • v) = -v
        simp [smul_smul, Complex.I_mul_I] }
  map {W W'} f :=
    { hom := f.hom.restrictScalars ℝ
      comm := by
        ext v
        change f.hom ((Complex.I : ℂ) • v) = (Complex.I : ℂ) • f.hom v
        simpa using (f.hom.map_smul (Complex.I : ℂ) v) }
  map_id W := by
    rfl
  map_comp f g := by
    rfl

/- TODO:
Add `unitIsoComplexRealK`, `counitIsoComplexRealK`, and package
`ModuleCat ℂ ≌ RealKVect`.

The core functors `complexToRealK` and `realKToComplex` are implemented and
compile; remaining work is coercion-heavy instance alignment between bundled
module structures in unit/counit component linearity proofs.
-/

end RealKVect

end InfoGeometry.Quantum.RealKCategory
