import InfoGeometry.Epistemology.ArchetypeHomotopyFramework
import InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

/-!
# Presented paths act compatibly on module colimits

A presented directed path gives an order comparison when its graph maps to a
preorder.  For a sequence of modules, the canonical colimit inclusions identify
elements related by the corresponding diagram map.  The second theorem records
this fact for the existing logarithmic braid tensor-power colimit.

This bridge concerns elements of mathematical module carriers.  It does not
transport Lean declarations, proof terms, or meta-level audit records through a
colimit.
-/

noncomputable section

namespace InfoGeometry.Categorical.PresentedPathModuleColimitBridge

open CategoryTheory
open InfoGeometry.Epistemology.ArchetypeHomotopyFramework
open InfoGeometry.Spectral.Colimit.SequentialModule
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

universe u

/-- A presented path between stages, mapped monotonically into `ℕ`, identifies
the image of a stage element with the image of its transported element in the
categorical colimit of any sequential module diagram. -/
theorem presented_path_colimit_readback
    {R : Type u} [Ring R] {G : InfoGeometry.Topology.ChiralDigraph}
    (D : Diagram R)
    (P : InfoGeometry.Topology.DirectedPathPresentation G)
    (F : InfoGeometry.Topology.ChiralDigraphHom G (prerequisiteGraph ℕ))
    {a b : G.Vertex}
    (p : InfoGeometry.Topology.PresentedPathClass P a b)
    (x : D.obj (F.mapVertex a)) :
    (inclusion R (F.mapVertex b)).hom
        ((D.map (homOfLE (presentedPathClass_le F P p))).hom x) =
      (inclusion R (F.mapVertex a)).hom x := by
  have h := inclusion_naturality R (F := D)
    (presentedPathClass_le F P p)
  have hlinear := congrArg ModuleCat.Hom.hom h
  change (inclusion R (F.mapVertex b)).hom.comp
      (D.map (homOfLE (presentedPathClass_le F P p))).hom =
    (inclusion R (F.mapVertex a)).hom at hlinear
  exact LinearMap.congr_fun hlinear x

/-- The same path-to-colimit compatibility instantiated at the repository's
existing logarithmic braid tensor-power module colimit. -/
theorem presented_path_tensor_power_readback
    {G : InfoGeometry.Topology.ChiralDigraph}
    (P : InfoGeometry.Topology.DirectedPathPresentation G)
    (F : InfoGeometry.Topology.ChiralDigraphHom G (prerequisiteGraph ℕ))
    {a b : G.Vertex}
    (p : InfoGeometry.Topology.PresentedPathClass P a b)
    (x : standardTensorPowerModuleDiagram.obj (F.mapVertex a)) :
    (stageInclusion (F.mapVertex b)).hom
        ((standardTensorPowerModuleDiagram.map
          (homOfLE (presentedPathClass_le F P p))).hom x) =
      (stageInclusion (F.mapVertex a)).hom x := by
  exact presented_path_colimit_readback
    (R := ℂ) standardTensorPowerModuleDiagram P F p x

end InfoGeometry.Categorical.PresentedPathModuleColimitBridge

end
