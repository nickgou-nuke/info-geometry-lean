import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat

/-!
# Native ranges of finite-stage inverse-limit observations

For each finite-stage observable and each symbolic-latent orbit closure, this
owner packages the actual `Set.range` as a `TopCat` object.  The range map is
surjective by construction and factors the observation through the canonical
subtype inclusion.  No compactness or quotient identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev carrier :=
  (limit readoutDiagram).carrier

abbrev flow := scalarDilationSymbolicLatentFlow

variable [T2Space carrier]

abbrev stageObservationRange
    (ρ : carrier) (n : ℕ) (X : MatStage n) : Set ℝ :=
  Set.range (fun y : SymbolicLatentModularOrbitClosure flow ρ =>
    orbitClosureStageObservationTopCatHom ρ n X y)

def stageObservationRangeInclusionTopCatHom
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    TopCat.of (stageObservationRange ρ n X) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def stageObservationRangeMapTopCatHom
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    TopCat.of (SymbolicLatentModularOrbitClosure flow ρ) ⟶
      TopCat.of (stageObservationRange ρ n X) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨orbitClosureStageObservationTopCatHom ρ n X y, ⟨y, rfl⟩⟩
      continuous_toFun :=
        (orbitClosureStageObservationTopCatHom ρ n X).hom.continuous.subtype_mk
          (fun y => ⟨y, rfl⟩) }

@[simp] theorem stageObservationRangeMapTopCatHom_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n)
    (y : SymbolicLatentModularOrbitClosure flow ρ) :
    stageObservationRangeMapTopCatHom ρ n X y =
      ⟨orbitClosureStageObservationTopCatHom ρ n X y, ⟨y, rfl⟩⟩ := rfl

theorem stageObservationRangeMapTopCatHom_surjective
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    Function.Surjective (stageObservationRangeMapTopCatHom ρ n X) := by
  intro z
  rcases z.property with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  exact Subtype.ext hy

theorem stageObservationRange_factorization
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    stageObservationRangeMapTopCatHom ρ n X ≫
        stageObservationRangeInclusionTopCatHom ρ n X =
      orbitClosureStageObservationTopCatHom ρ n X := by
  ext y
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat

end
