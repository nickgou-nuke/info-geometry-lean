/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Epistemology.RiemannianSubmersion

/-!
# Audit Companion: Riemannian Submersions & Chentsov Geometry

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Epistemology.RiemannianSubmersion`.
-/

open InfoGeometry.Epistemology.RiemannianSubmersion

#print axioms horizontal_of_vertical_zero
#print axioms vertical_of_horizontal_zero
#print axioms vertical_zero_of_horizontal_fixed
#print axioms metric_collapse_on_vertical_fiber
#print axioms oneill_curvature_augmented
#print axioms oneill_flat_ambient_curvature
#print axioms kernel_pinning_eliminates_confabulation
