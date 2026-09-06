import InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient
import InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction

/-!
# Coarse orbit quotient of the concrete ternary Coxeter boundary

This specializes the generic order-three quotient to the cyclic color action
already present in the Toeplitz--Cuntz triality boundary.  It is a coarse orbit
space; the transformation groupoid remains the owner of arrows and isotropy.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient

open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality
open InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient

abbrev CoxeterBoundaryOrbitSpace :=
  OrbitSpace coxeterBoundaryHomeomorph coxeterBoundaryHomeomorph_cube

def coxeterOrbitProjection :
    TernaryBoundary → CoxeterBoundaryOrbitSpace :=
  orbitProjection coxeterBoundaryHomeomorph coxeterBoundaryHomeomorph_cube

theorem continuous_coxeterOrbitProjection :
    Continuous coxeterOrbitProjection :=
  continuous_orbitProjection coxeterBoundaryHomeomorph
    coxeterBoundaryHomeomorph_cube

@[simp] theorem coxeterOrbitProjection_identifies_cycle
    (x : TernaryBoundary) :
    coxeterOrbitProjection (coxeterBoundaryHomeomorph x) =
      coxeterOrbitProjection x := by
  exact orbitProjection_apply coxeterBoundaryHomeomorph
    coxeterBoundaryHomeomorph_cube x

end InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
