/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Epistemology.TomitaTakesakiConnes

/-!
# Audit Companion: Tomita–Takesaki Modular Theory, Para-Kähler Geometry, and Connes Cocycle

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Epistemology.TomitaTakesakiConnes`.
-/

open InfoGeometry.Epistemology.TomitaTakesakiConnes

#print axioms para_complex_sq
#print axioms split_quaternion_JK
#print axioms split_quaternion_KJ
#print axioms isotropic_Tplus
#print axioms isotropic_Tminus
#print axioms J_swaps_sheets
#print axioms connes_intertwining_pullback
#print axioms trace_scaling_composition
#print axioms trace_scaling_identity
#print axioms compile_tomita_takesaki_connes
