/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Epistemology.ContinuousMERA

/-!
# Audit Companion: Continuous MERA (cMERA)

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Epistemology.ContinuousMERA`.
-/

open InfoGeometry.Epistemology.ContinuousMERA

#print axioms zCoord_pos
#print axioms uCoord_zCoord
#print axioms zCoord_uCoord
#print axioms poincare_metric_transform
#print axioms mra_projector_annihilation
#print axioms mra_projector_annihilation_rev
#print axioms mra_complement_idempotent
#print axioms unitary_preserves_identity
#print axioms circuit_interval_compose
#print axioms circuit_interval_inv
#print axioms circuit_interval_refl
#print axioms causal_cone_depth_eq_log_ratio
#print axioms causal_cone_depth_pos
#print axioms cmera_rt_pos
#print axioms cmera_rt_monotone
#print axioms cmera_rt_coincidence
#print axioms compile_continuous_mera
