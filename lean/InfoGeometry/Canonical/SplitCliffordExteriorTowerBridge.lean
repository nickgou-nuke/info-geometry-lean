import InfoGeometry.Algebra.SuperGrassmannianClifford
import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-!
# Exterior presentation of the canonical split Clifford tower

The exterior carrier in `SuperGrassmannianClifford` transports the split
Clifford stage maps. This file identifies those maps with the already-owned
Mathlib direct-system transition maps, so the exterior presentation does not
define a second tower or colimit.
-/

namespace InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge

open InfoGeometry.Algebra.SuperGrassmannianClifford
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- The exterior tower's Clifford map is exactly the transition map used by
the canonical split-Clifford direct system. -/
theorem stageCliffordMap_eq_canonicalStep (n : ℕ) :
    splitStageCliffordMap n = splitCliffordStep n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change splitStageCliffordMap n
      (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit n) v) =
    splitCliffordStep n
      (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit n) v)
  simp [splitStageCliffordMap, splitCliffordStep,
    GradedTensorProduct.includeRight_apply]
  rw [← splitCliffordTensorStep_tailFactor n v]
  simp only [AlgEquiv.symm_apply_apply]
  change CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))
      ((0, v) : InfoGeometry.CliffordTower.SplitSpace (n + 1)) =
    CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))
      (((0, 0), v) : InfoGeometry.CliffordTower.SplitSpace (n + 1))
  rfl

/-- Consequently, the exterior-stage map is the transport of the canonical
direct-system step through the Clifford/exterior equivalences. -/
theorem stageExteriorMap_eq_canonicalStepTransport (n : ℕ) :
    splitStageExteriorMap n =
      (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit (n + 1))).toLinearMap.comp
        ((splitCliffordStep n).toLinearMap.comp
          (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm.toLinearMap) := by
  simp [splitStageExteriorMap, stageCliffordMap_eq_canonicalStep]

end InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge
