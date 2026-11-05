/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.SchurDefect
import InfoGeometry.OperatorAlgebra.SchurDefectExamples
import InfoGeometry.Canonical.MajoranaUHFJordanWignerInduction

/-!
# Peirce decomposition, defect transport, and finite Schur descent

This entrypoint reuses the existing noncommutative tetraktys and finite
defect-iteration owners, adds exact Schur defect transport and an admissible
reduction partial order, and exposes concrete noncommuting witnesses. The
existing Jordan-Wigner successor theorem is imported as a separate branch
with its explicit parity hypotheses. No theorem identifies Schur descent
with Clifford doubling, claims automatic defect repair, or assigns a physical
interpretation to the dependency or reduction orders.
-/
