import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation

/-!
# Exterior derivation induced by a `Cl(5,5)` bivector

The Clifford commutator action on vectors is already established in
`Cl55BivectorVectorRepresentation`. This file lifts that linear action from the
generators to the exterior algebra, and proves the ordinary Leibniz rule on the
whole carrier. The lift is constructed by the universal property of the
exterior algebra, using the trivial square-zero extension as the tangent
algebra.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation

open ExteriorAlgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.BivectorVectorRepresentation

private abbrev TangentAlgebra (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] :=
  TrivSqZeroExt (ExteriorAlgebra R V) (ExteriorAlgebra R V)

private def tangentGeneratorMap {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) :
    V →ₗ[R] TangentAlgebra R V :=
  LinearMap.prod (ExteriorAlgebra.ι R)
    ((ExteriorAlgebra.ι R).comp f)

private theorem tangentGeneratorMap_sq_zero {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) (v : V) :
    tangentGeneratorMap f v * tangentGeneratorMap f v = 0 := by
  apply TrivSqZeroExt.ext
  · simp [tangentGeneratorMap, ExteriorAlgebra.ι_sq_zero]
  · change ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R (f v) +
      ExteriorAlgebra.ι R (f v) * ExteriorAlgebra.ι R v = 0
    exact ExteriorAlgebra.ι_add_mul_swap v (f v)

private noncomputable def tangentLift {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) :
    ExteriorAlgebra R V →ₐ[R] TangentAlgebra R V :=
  ExteriorAlgebra.lift R ⟨tangentGeneratorMap f, tangentGeneratorMap_sq_zero f⟩

/-- The linear endomorphism of the exterior algebra induced by a linear map on
its degree-one generators. -/
noncomputable def liftExteriorDerivation {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  (TrivSqZeroExt.sndHom (ExteriorAlgebra R V) (ExteriorAlgebra R V)).restrictScalars R ∘ₗ
    (tangentLift f).toLinearMap

/-- On degree-one generators, the lifted map agrees with the prescribed
linear action. -/
theorem liftExteriorDerivation_ι {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) (v : V) :
    liftExteriorDerivation f (ExteriorAlgebra.ι R v) = ExteriorAlgebra.ι R (f v) := by
  simp [liftExteriorDerivation, tangentLift, tangentGeneratorMap]

private theorem tangentLift_fst {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) (x : ExteriorAlgebra R V) :
    (tangentLift f x).fst = x := by
  have h : (TrivSqZeroExt.fstHom R (ExteriorAlgebra R V)
      (ExteriorAlgebra R V)).comp (tangentLift f) = AlgHom.id R (ExteriorAlgebra R V) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [tangentLift, tangentGeneratorMap]
  exact congrArg (fun g : ExteriorAlgebra R V →ₐ[R] ExteriorAlgebra R V => g x) h
    |> by simpa using id

/-- The extension satisfies the ordinary (degree-zero) Leibniz rule on all
exterior-algebra elements. -/
theorem liftExteriorDerivation_leibniz {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (f : V →ₗ[R] V)
    (x y : ExteriorAlgebra R V) :
    liftExteriorDerivation f (x * y) =
      liftExteriorDerivation f x * y + x * liftExteriorDerivation f y := by
  change ((tangentLift f) (x * y)).snd =
    ((tangentLift f x).snd * y) + (x * (tangentLift f y).snd)
  rw [map_mul, TrivSqZeroExt.snd_mul, tangentLift_fst, tangentLift_fst]
  simp [mul_comm, add_comm]

/-- The degree-one action appearing in the Clifford commutator formula, bundled
as a linear endomorphism of `V55`. -/
noncomputable def bivectorVectorTransformLinear (u v : V55) : V55 →ₗ[ℝ] V55 where
  toFun := bivectorVectorTransform u v
  map_add' w₁ w₂ := by
    dsimp [bivectorVectorTransform]
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      add_smul, add_smul]
    abel
  map_smul' c w := by
    dsimp [bivectorVectorTransform]
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      smul_smul, smul_smul]
    rfl

local notation "Exterior55" => ExteriorAlgebra ℝ V55

/-- The exterior-algebra derivation induced by the action of a `Cl(5,5)`
bivector on vectors. -/
noncomputable def bivectorExteriorDerivation (u v : V55) :
    Exterior55 →ₗ[ℝ] Exterior55 :=
  liftExteriorDerivation (bivectorVectorTransformLinear u v)

/-- The lifted derivation agrees with the vector action on exterior
generators. -/
theorem bivectorExteriorDerivation_ι (u v w : V55) :
    bivectorExteriorDerivation u v (ExteriorAlgebra.ι ℝ w) =
      ExteriorAlgebra.ι ℝ (bivectorVectorTransform u v w) := by
  exact liftExteriorDerivation_ι (bivectorVectorTransformLinear u v) w

/-- The bivector-induced action is a derivation on the full exterior-algebra
carrier. -/
theorem bivectorExteriorDerivation_leibniz (u v : V55)
    (x y : Exterior55) :
    bivectorExteriorDerivation u v (x * y) =
      bivectorExteriorDerivation u v x * y + x * bivectorExteriorDerivation u v y := by
  exact liftExteriorDerivation_leibniz (bivectorVectorTransformLinear u v) x y

end InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation
