import InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.LogNilpotentMonoidalUnit

/-!
# Logarithmic tensor powers and adjacent checked-R slices

This file is the object/slice layer for the existing braid-group tower.
It introduces no braid presentation.  Given a logarithmic object `X` and a
certified checked-R automorphism of `X ⊗ X`, it builds the right-associated
tensor powers of `X` and inserts the checked-R at any adjacent pair.

Every slice is constructed as an isomorphism in `LogNilpotentModule`, so the
intertwining law for the total primitive nilpotent is part of the type.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentTensorPowerBraid

open CategoryTheory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalUnit

universe u

variable {𝕜 : Type u} [Field 𝕜]

/-- Right-associated tensor powers with the existing logarithmic tensor unit at
power zero.  Powers one and two reduce definitionally to `X` and `X ⊗ X`. -/
def tensorPowerObj (X : LogNilpotentModule.{u, u} 𝕜) : ℕ → LogNilpotentModule.{u, u} 𝕜
  | 0 => unitObject
  | 1 => X
  | n + 2 => LogNilpotentModule.tensorObj X (tensorPowerObj X (n + 1))

@[simp]
theorem tensorPowerObj_zero (X : LogNilpotentModule.{u, u} 𝕜) :
    tensorPowerObj X 0 = unitObject := rfl

@[simp]
theorem tensorPowerObj_one (X : LogNilpotentModule.{u, u} 𝕜) :
    tensorPowerObj X 1 = X := rfl

@[simp]
theorem tensorPowerObj_succ_succ (X : LogNilpotentModule.{u, u} 𝕜) (n : ℕ) :
    tensorPowerObj X (n + 2) =
      LogNilpotentModule.tensorObj X (tensorPowerObj X (n + 1)) := rfl

/-- Tensor product of logarithmic isomorphisms. -/
def tensorIso
    {X X' Y Y' : LogNilpotentModule.{u, u} 𝕜}
    (f : X ≅ X') (g : Y ≅ Y') :
    LogNilpotentModule.tensorObj X Y ≅
      LogNilpotentModule.tensorObj X' Y' where
  hom := LogNilpotentModule.tensorHom f.hom g.hom
  inv := LogNilpotentModule.tensorHom f.inv g.inv
  hom_inv_id := by
    rw [← LogNilpotentModule.tensorHom_comp, f.hom_inv_id, g.hom_inv_id]
    exact LogNilpotentModule.tensorHom_id X Y
  inv_hom_id := by
    rw [← LogNilpotentModule.tensorHom_comp, f.inv_hom_id, g.inv_hom_id]
    exact LogNilpotentModule.tensorHom_id X' Y'

@[simp]
theorem tensorIso_hom_tmul
    {X X' Y Y' : LogNilpotentModule.{u, u} 𝕜}
    (f : X ≅ X') (g : Y ≅ Y') (x : X.toLogEndModule.V)
    (y : Y.toLogEndModule.V) :
    (tensorIso f g).hom.hom (x ⊗ₜ[𝕜] y) =
      f.hom.hom x ⊗ₜ[𝕜] g.hom.hom y := by
  exact LogNilpotentModule.tensorHom_tmul f.hom g.hom x y

/-- Convert a self-isomorphism in the logarithmic category to the underlying
linear equivalence. -/
def isoToLinearEquiv {X : LogNilpotentModule.{u, u} 𝕜} (e : X ≅ X) : X ≃ₗ[𝕜] X := by
  apply LinearEquiv.ofLinear e.hom.hom e.inv.hom
  · have h := e.inv_hom_id
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f : X ⟶ X => f.hom x) h
    simpa only [LogNilpotentModule.hom_comp, LinearMap.comp_apply,
      LinearMap.id_apply] using hx
  · have h := e.hom_inv_id
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f : X ⟶ X => f.hom x) h
    simpa only [LogNilpotentModule.hom_comp, LinearMap.comp_apply,
      LinearMap.id_apply] using hx

@[simp]
theorem isoToLinearEquiv_apply
    {X : LogNilpotentModule.{u, u} 𝕜} (e : X ≅ X) (x : X) :
    isoToLinearEquiv e x = e.hom.hom x := rfl

/-- Insert an adjacent checked-R into a right-associated tensor power.

For a power `n+2` there are `n+1` adjacent generator positions.  Position zero
acts on the first two factors, transported through the associator; a successor
position tensors the corresponding tail action with the identity on the first
factor. -/
def braidGeneratorIso
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : CategoryTheory.Iso (LogNilpotentModule.tensorObj X X)
      (LogNilpotentModule.tensorObj X X)) :
    (n : ℕ) → Fin (n + 1) →
      CategoryTheory.Iso (tensorPowerObj X (n + 2)) (tensorPowerObj X (n + 2))
  | 0, _ => by simpa [tensorPowerObj] using R
  | n + 1, i =>
      Fin.cases
        ((LogNilpotentModule.associatorIso
            X X (tensorPowerObj X (n + 1))).symm.trans
          ((tensorIso R (Iso.refl (tensorPowerObj X (n + 1)))).trans
            (LogNilpotentModule.associatorIso
              X X (tensorPowerObj X (n + 1)))))
        (fun j => tensorIso (Iso.refl X) (braidGeneratorIso X R n j))
        i

/-- Underlying linear automorphism of an adjacent checked-R slice. -/
def braidGeneratorLinearEquiv
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : LogNilpotentModule.tensorObj X X ≅
      LogNilpotentModule.tensorObj X X)
    (n : ℕ) (i : Fin (n + 1)) :
    tensorPowerObj X (n + 2) ≃ₗ[𝕜] tensorPowerObj X (n + 2) :=
  isoToLinearEquiv (braidGeneratorIso X R n i)

/-- Every adjacent slice is, by construction, a genuine logarithmic
intertwiner for the total tensor-power nilpotent. -/
theorem braidGenerator_intertwines
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : LogNilpotentModule.tensorObj X X ≅
      LogNilpotentModule.tensorObj X X)
    (n : ℕ) (i : Fin (n + 1)) :
    (braidGeneratorIso X R n i).hom.hom.comp (tensorPowerObj X (n + 2)).N =
      (tensorPowerObj X (n + 2)).N.comp
        (braidGeneratorIso X R n i).hom.hom :=
  (braidGeneratorIso X R n i).hom.comm

/-- The unique generator on the two-fold tensor power is exactly the supplied
checked-R. -/
@[simp]
theorem braidGeneratorIso_two
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : LogNilpotentModule.tensorObj X X ≅
      LogNilpotentModule.tensorObj X X)
    (i : Fin 1) :
    braidGeneratorIso X R 0 i = R := by
  rfl

/-- On the three-fold tensor power, generator zero is the associator transport
of `R ⊗ id`. -/
theorem braidGeneratorIso_three_zero
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : LogNilpotentModule.tensorObj X X ≅
      LogNilpotentModule.tensorObj X X) :
    braidGeneratorIso X R 1 (0 : Fin 2) =
      (LogNilpotentModule.associatorIso X X X).symm.trans
        ((tensorIso R (Iso.refl X)).trans
          (LogNilpotentModule.associatorIso X X X)) := by
  rfl

/-- On the three-fold tensor power, generator one is `id ⊗ R`. -/
theorem braidGeneratorIso_three_one
    (X : LogNilpotentModule.{u, u} 𝕜)
    (R : LogNilpotentModule.tensorObj X X ≅
      LogNilpotentModule.tensorObj X X) :
    braidGeneratorIso X R 1 (1 : Fin 2) =
      tensorIso (Iso.refl X) R := by
  rfl

end InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
