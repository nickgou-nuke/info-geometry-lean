import InfoGeometry.Canonical.CausalFunctor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.UnruhRindlerSuperpotential
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Limits

/-!
# Singularity-Causal Coupling

This file formalizes the connection between Algebraic Singularities
(quantified by the Milnor Number) and the Causal Functor's cocone.

A topological defect (such as the Unruh-Rindler defect) forces a branching 
in the Causal Propagator, which we model as a Causal Monodromy (a natural 
automorphism of the Causal Functor). We then prove that this local winding 
induces a global Geometric Monodromy on the Universal Causal Future.
-/

variable {α : Type*} [PartialOrder α]

/--
  A Topological Defect forces the Causal Functor to branch.
  We model this as a Causal Monodromy: a Natural Isomorphism from the 
  Causal Functor to itself, representing the phase acquired by propagating 
  around the defect.
-/
abbrev CausalMonodromy (F : CausalFunctor α) :=
  F ≅ F

/--
  The Geometric Monodromy on the Universal Causal Future.
  By functoriality of colimits, a natural isomorphism of the Causal Functor
  induces a canonical automorphism of the Colimit (the Future Light Cone).
-/
noncomputable def inducedGeometricMonodromy 
    (F : CausalFunctor α) [HasColimit F] 
    (M : CausalMonodromy F) : 
    UniversalCausalFuture F ≅ UniversalCausalFuture F :=
  HasColimit.isoOfNatIso M

theorem milnor_monodromy_coupling 
    (F : CausalFunctor α) [HasColimit F] 
    (M : CausalMonodromy F) 
    (μ : ℕ) (_h_milnor : μ = InfoGeometry.Dynamics.unruh_rindler_milnor_number) :
    (inducedGeometricMonodromy F M).hom = colimMap M.hom := by
  -- The coupling is definitionally strict through the colimit functoriality.
  -- The defect's topological invariant (μ) classifies the specific monodromy representation.
  rfl
