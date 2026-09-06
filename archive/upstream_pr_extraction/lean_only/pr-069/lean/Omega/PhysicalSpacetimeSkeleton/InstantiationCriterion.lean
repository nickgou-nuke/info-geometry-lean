import Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate
import Omega.RecursiveAddressing.NullAsLocalSectionObstruction

namespace Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion

open Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate

/-- Concrete backend carriers for an acceptable physical-spacetime instantiation. -/
structure AcceptableInstantiation where
  Addr : Type
  Obj : Type
  Visible : Type
  Fiber : Addr → Set Obj
  NullReadout : Addr → Prop
  Obstructed : Addr → Prop
  witness : Addr
  R : Setoid Visible
  K : Visible → Visible → ℝ

/-- The local-global obstruction, kernelized positivity/invariance, and continuum witness produce
the physical-spacetime instantiation conclusions. -/
theorem paper_physical_spacetime_instantiation_criterion
    (I : AcceptableInstantiation)
    (localGlobalTrivial :
      ∀ {a : I.Addr}, (I.Fiber a).Nonempty → ¬ I.Obstructed a)
    (localGlobalNull :
      ∀ {a : I.Addr}, I.Fiber a = (∅ : Set I.Obj) → I.NullReadout a)
    (witnessObstructed : I.Obstructed I.witness)
    (hinv : ∀ {x x' y y'}, I.R.r x x' → I.R.r y y' → I.K x y = I.K x' y')
    (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → I.Visible) (a : ι → ℝ),
      0 ≤ quadraticEnergy I.K ψ a)
    (continuumLimit : Prop)
    (continuumWitness : continuumLimit) :
    (I.Fiber I.witness = (∅ : Set I.Obj) ∧ I.NullReadout I.witness) ∧
      (∀ {ι : Type} [Fintype ι] (ψ ψ' : ι → I.Visible) (a : ι → ℝ),
        (∀ i, I.R.r (ψ i) (ψ' i)) →
          quadraticEnergy I.K ψ a = quadraticEnergy I.K ψ' a ∧
            0 ≤ quadraticEnergy I.K ψ a) ∧
        continuumLimit := by
  refine ⟨?_, ?_, continuumWitness⟩
  · exact
      Omega.RecursiveAddressing.paper_null_as_h2_obstruction
        I.Fiber I.NullReadout I.Obstructed localGlobalTrivial localGlobalNull
        I.witness witnessObstructed
  · intro ι _ ψ ψ' a hrep
    exact
      paper_physical_spacetime_kernelization_template_package
        I.R I.K hinv hpsd ψ ψ' a hrep

end Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion
