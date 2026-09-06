import InfoGeometry.Projective.FiveGradedTopologicalInvariants

namespace InfoGeometry.Projective.Topology

open InfoGeometry.Projective.Closure

def concreteTopologicalInvariants2 : SpinTopologicalInvariants 2 :=
  concreteSpinTopologicalInvariants2

theorem concreteTopologicalInvariants2_trace_zero :
    Matrix.trace concreteTopologicalInvariants2.closure.moebiusParity = 0 := by
  exact concrete_pontryagin_trace_zero

theorem concreteTopologicalInvariants2_gw_zero :
    concreteTopologicalInvariants2.closure.gromovWittenIndex = 0 := by
  exact (gromovWittenIndex_zero_iff_trace_zero 2
    concreteTopologicalInvariants2).mpr concreteTopologicalInvariants2_trace_zero

theorem concreteTopologicalInvariants2_ribbon_twist :
    concreteTopologicalInvariants2.closure.moebiusParity *
        concreteTopologicalInvariants2.closure.moebiusParity =
      -concreteTopologicalInvariants2.closure.I := by
  exact ribbon_twist_eq_minus_id 2 concreteTopologicalInvariants2

theorem concreteTopologicalInvariants2_unobstructed :
    SpinStructureUnobstructed concreteTopologicalInvariants2 := by
  rfl

end InfoGeometry.Projective.Topology
