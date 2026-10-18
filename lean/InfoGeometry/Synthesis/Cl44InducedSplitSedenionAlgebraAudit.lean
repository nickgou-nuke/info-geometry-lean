/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra

/-!
# Axiom Audit for `Cl44InducedSplitSedenionAlgebra`
-/

namespace InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebraAudit

open InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra

#check @idealSedenionMul
#check @idealSedenionConj
#check @idealSedenionNorm

#print axioms idealSedenionMul
#print axioms idealSedenionConj
#print axioms idealSedenionNorm

end InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebraAudit
