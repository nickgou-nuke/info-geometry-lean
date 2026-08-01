import InfoGeometry.External.Auto.NuclearPhononGenerators

/-!
Direct readback owner for the finite nuclear-generator facts.

The former AQL/Boolean graph and milestone status layer is not a mathematical
proof and is intentionally absent.
-/

namespace NuclearPhononMetriplecticBridge

theorem phonon_generator_readback :
    NuclearPhononGenerators.u6Dimension = 36 ∧
    NuclearPhononGenerators.sp6RDimension = 21 := by
  exact ⟨NuclearPhononGenerators.u6_dimension_eq_36,
    NuclearPhononGenerators.sp6R_dimension_eq_21⟩

theorem spring_stiffness_at_poincare_c1 :
    NuclearPhononGenerators.springStiffnessFromC1
      (NuclearPhononGenerators.poincareC1 3) = 9 := by
  norm_num [NuclearPhononGenerators.springStiffnessFromC1,
    NuclearPhononGenerators.poincareC1]

end NuclearPhononMetriplecticBridge
