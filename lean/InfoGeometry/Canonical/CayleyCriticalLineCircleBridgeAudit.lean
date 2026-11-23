/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Axiom audit for the Cayley critical-line radius criteria

The audited declarations express the signed unit-radius criterion and the two
open half-plane cases. The expected transitive axioms are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` only.
-/

#print axioms InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity_normSq_sub_one
#print axioms InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity_normSq_gt_one_iff
#print axioms InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity_normSq_lt_one_iff
