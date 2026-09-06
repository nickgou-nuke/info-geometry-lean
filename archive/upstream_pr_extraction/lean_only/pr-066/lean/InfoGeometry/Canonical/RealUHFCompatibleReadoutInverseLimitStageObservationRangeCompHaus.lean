import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of finite-stage observation ranges

Under explicit compactness and Hausdorff hypotheses on the inverse-limit
carrier, the orbit closure is compact and every finite-stage observation has
compact range.  This owner packages that range and its surjective map in
`CompHaus`; it does not promote the full inverse limit to a compact object.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev carrier :=
  (limit readoutDiagram).carrier

abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def stageObservationRangeCompHaus
    (ρ : carrier) (n : ℕ) (X : MatStage n) : CompHaus := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure flow ρ) :=
    isCompact_iff_compactSpace.mp (flow.isCompact_orbitClosure ρ)
  letI : CompactSpace (stageObservationRange ρ n X) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range
        (orbitClosureStageObservationTopCatHom ρ n X).hom.continuous)
  exact CompHaus.of (stageObservationRange ρ n X)

noncomputable def stageObservationRangeCompHausHom
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    symbolicLatentModularOrbitClosureCompHaus flow ρ ⟶
      stageObservationRangeCompHaus ρ n X := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure flow ρ) :=
    isCompact_iff_compactSpace.mp (flow.isCompact_orbitClosure ρ)
  letI : CompactSpace (stageObservationRange ρ n X) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range
        (orbitClosureStageObservationTopCatHom ρ n X).hom.continuous)
  exact ⟨stageObservationRangeMapTopCatHom ρ n X⟩

theorem stageObservationRangeCompHausHom_forget
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    compHausToTop.map (stageObservationRangeCompHausHom ρ n X) =
      stageObservationRangeMapTopCatHom ρ n X := by
  rfl

theorem stageObservationRangeCompHausHom_surjective
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    Function.Surjective (stageObservationRangeCompHausHom ρ n X) := by
  intro z
  exact stageObservationRangeMapTopCatHom_surjective ρ n X z

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus

end
