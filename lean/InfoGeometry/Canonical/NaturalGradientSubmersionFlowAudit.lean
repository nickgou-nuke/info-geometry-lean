/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow

/-!
# Audit Companion: Natural Gradient Submersion Flow

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Canonical.NaturalGradientSubmersionFlow`.
-/

open InfoGeometry.Canonical.NaturalGradientSubmersionFlow

#print axioms para_projectors_sum_id
#print axioms para_projector_plus_idempotent
#print axioms para_projector_minus_idempotent
#print axioms para_projectors_annihilation_plus_minus
#print axioms para_projectors_annihilation_minus_plus
#print axioms paraComplexSubmersionSplit
#print axioms metric_ortho_VH
#print axioms natural_gradient_horizontal_isolation
#print axioms kernel_pinning_vanishing_drift
#print axioms kinetic_energy_fiber_collapse
#print axioms compile_natural_gradient_submersion_flow
