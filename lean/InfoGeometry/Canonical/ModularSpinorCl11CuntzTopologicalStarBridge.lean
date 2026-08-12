import InfoGeometry.Canonical.ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
import InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1)-Cuntz topological star bridge

This file adds the next honest node after
`ModularSpinorCl11MarkovJonesTopologicalCyclicBridge`. The repository already owns:

* a modular-spinor / Cl(1,1) Markov-Jones cyclic transport bridge;
* a genuine continuous involution readout on the Cl(1,1)-Cuntz matrix colimit.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the Cuntz-side involution readout or proving exchange/KMS
compatibility with that involution. The theorem below records a genuine
stage-level consequence of the native involution and its inclusion readback.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

theorem topologicalStarReadout_inclusion_involutive
    (n : ℕ) (A : MatrixStage n) :
    topologicalStarReadout concreteData
        (topologicalStarReadout concreteData
          (topologicalInclusion concreteData n A)) =
      topologicalInclusion concreteData n A := by
  rw [topologicalStarReadout_inclusion, topologicalStarReadout_inclusion]
  simp

end

end InfoGeometry.Canonical
