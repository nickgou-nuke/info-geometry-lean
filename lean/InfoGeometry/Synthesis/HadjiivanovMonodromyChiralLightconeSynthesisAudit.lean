/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

/-!
# Audit: `HadjiivanovMonodromyChiralLightconeSynthesis`

External `#check` audit verifying exported theorem and definition signatures for
`InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis`.
-/

namespace InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesisAudit

open InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

#check @chiral_ladder_ne_comm
#check @Splus_eq_jordanNilpotent
#check @chiralPeircePlus
#check @chiralPeirceMinus
#check @chiral_ladder_matrix_unit_resolution
#check @unipotentChiralShear
#check @unipotentChiralShear_mul_and_det

#print axioms chiral_ladder_matrix_unit_resolution
#print axioms unipotentChiralShear_mul_and_det

end InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesisAudit
