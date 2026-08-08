import InfoGeometry.Dynamics.RapiditySpace
import InfoGeometry.Dynamics.RindlerWedge
import InfoGeometry.Clifford.ConformalReflection55
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import InfoGeometry.Canonical.ConformalSL2GeneratorBridge

/-!
# Conformal Rapidity Rosetta

Rosetta table for the rapidity, Rindler, inversion, Möbius, and adjoint lanes.

This file does not add new mathematics. It pins the existing owner surfaces to a
single named translation table so the SymPy property and the Lean owner theorems
share the same vocabulary.

| SymPy / geometric readout | Lean owner |
| --- | --- |
| rapidity composition | `Dynamics.RapiditySpace.rapidity_additive_composition` |
| rapidity logarithm shift | `Dynamics.RapiditySpace.log_coordinate_rapidity_shift` |
| Rindler time translation | `Dynamics.RindlerWedge.rindler_flow_is_time_translation` |
| Rindler proper distance | `Dynamics.RindlerWedge.rindler_flow_preserves_proper_distance` |
| conformal inversion generator | `Clifford.ConformalReflection55.J_sq`, `J_swap_origin`, `J_swap_infinity` |
| Möbius translation/inversion | `Clifford.DiscreteMoebiusGroup.moebius_T_action`, `moebius_S_action` |
| conformal `sl₂` readout | `Canonical.ConformalSL2GeneratorBridge.P`, `D`, `K` |
| ambient orthogonal label | `Canonical.ConformalSL2GeneratorBridge.ambient_group_is_O55` |

The intended physics dictionary is:

- rapidity boost `↔` additive hyperbolic flow;
- `log`/`exp` `↔` additive/multiplicative coordinate conversion;
- `J = u - v` `↔` conformal inversion / origin-infinity swap;
- `z ↦ -1 / z` `↔` projective Möbius inversion;
- `Op ↦ 1 / Op` only as a projective/inversion readout, not a literal algebraic inverse unless the operator is invertible.
-/

set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Canonical.ConformalRapidityRosetta

/-! ## Rapidities and Rindler flow -/

abbrev rapidity_additive_composition :=
  InfoGeometry.Dynamics.RapiditySpace.rapidity_additive_composition

abbrev rapidity_zero :=
  InfoGeometry.Dynamics.RapiditySpace.rapidity_zero

abbrev rapidity_mul_neg :=
  InfoGeometry.Dynamics.RapiditySpace.rapidity_mul_neg

abbrev rapidity_neg_mul :=
  InfoGeometry.Dynamics.RapiditySpace.rapidity_neg_mul

abbrev log_coordinate_rapidity_shift :=
  InfoGeometry.Dynamics.RapiditySpace.log_coordinate_rapidity_shift

abbrev rindler_flow_is_time_translation :=
  InfoGeometry.Dynamics.RindlerWedge.rindler_flow_is_time_translation

abbrev rindler_lightcone_product :=
  InfoGeometry.Dynamics.RindlerWedge.rindler_lightcone_product

abbrev rindler_flow_preserves_proper_distance :=
  InfoGeometry.Dynamics.RindlerWedge.rindler_flow_preserves_proper_distance

/-! ## Conformal inversion and projective readout -/

abbrev J_sq :=
  InfoGeometry.Clifford.ConformalReflection55.J_sq

abbrev J_swap_origin :=
  InfoGeometry.Clifford.ConformalReflection55.J_swap_origin

abbrev J_swap_infinity :=
  InfoGeometry.Clifford.ConformalReflection55.J_swap_infinity

abbrev J_mul_neg_J :=
  InfoGeometry.Clifford.ConformalReflection55.J_mul_neg_J

abbrev neg_J_mul_J :=
  InfoGeometry.Clifford.ConformalReflection55.neg_J_mul_J

abbrev moebius_T_action :=
  InfoGeometry.Clifford.DiscreteMoebiusGroup.moebius_T_action

abbrev moebius_S_action :=
  InfoGeometry.Clifford.DiscreteMoebiusGroup.moebius_S_action

/-! ## Conformal `sl₂` readout and ambient orthogonal label -/

abbrev P_sq_zero :=
  InfoGeometry.Canonical.ConformalSL2GeneratorBridge.P_sq_zero

abbrev K_sq_zero :=
  InfoGeometry.Canonical.ConformalSL2GeneratorBridge.K_sq_zero

abbrev comm_D_P :=
  InfoGeometry.Canonical.ConformalSL2GeneratorBridge.comm_D_P

abbrev comm_D_K :=
  InfoGeometry.Canonical.ConformalSL2GeneratorBridge.comm_D_K

abbrev comm_P_K :=
  InfoGeometry.Canonical.ConformalSL2GeneratorBridge.comm_P_K


end InfoGeometry.Canonical.ConformalRapidityRosetta
