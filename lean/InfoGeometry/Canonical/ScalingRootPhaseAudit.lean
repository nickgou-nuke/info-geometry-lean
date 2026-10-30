import InfoGeometry.Canonical.ThreeColorZornScalingObstruction
import InfoGeometry.Canonical.ZornRootUnipotentObstruction
import InfoGeometry.Algebra.RegularBimoduleWeylObstruction

/-!
Kernel dependencies of three obstruction replacements:
* reciprocal Zorn scaling preserves multiplication exactly at cubic roots of unity;
* root updates preserve the owner product because their quadratic defects vanish;
* a scalar phase forces noncommutation exactly when the phase is nontrivial
  and the operator product is nonzero.
These statements concern their respective native carriers; no identification
between the complex Zorn carrier and the operator-valued Zorn carrier is used.
-/

#print axioms InfoGeometry.Canonical.ThreeColorZornScalingObstruction.zornScale_multiplicative_iff
#print axioms InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.rootXYUpdate_mul_defect
#print axioms InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.rootXYUpdate_bijective
#print axioms InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.six_root_actions_are_derivations_and_updates_multiplicative
#print axioms InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.root_updates_group_commutator
#print axioms InfoGeometry.Algebra.RegularBimoduleWeylObstruction.phase_commute_iff
#print axioms InfoGeometry.Algebra.RegularBimoduleWeylObstruction.phase_noncommute_iff
#print axioms InfoGeometry.Algebra.RegularBimoduleWeylObstruction.matrix3_noncommutative
