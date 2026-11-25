/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralSkewIncidence
import InfoGeometry.Twistor.DiracSpinorBrackets
import InfoGeometry.Canonical.DiracBipartitePairing
import InfoGeometry.OperatorAlgebra.DiracCoarseGraining

/-!
# Real Dirac incidence, finite bipartite pairings, and Schur transport

Public mathematical entry point for the four native owners. The separate
`DiracPlabicCoarseAudit` target imports this umbrella and checks all explicitly
named public declarations. Scope and proof assumptions are recorded in
`verification/dirac-plabic-coarse/THEOREM_CONTRACT.md`.
-/
