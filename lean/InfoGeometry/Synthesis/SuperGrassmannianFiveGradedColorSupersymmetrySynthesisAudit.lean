/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

/-!
# Axiom Audit for `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`
-/

namespace InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesisAudit

open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

#check @Z2Z2ColorGrade
#check @gradeGauge0
#check @gradeLepton
#check @gradeQuark
#check @gradeColorBoson
#check @z2z2Pairing
#check @z2z2KoszulSign
#check @z2z2_color_supersymmetry_sign_laws
#check @quarkAntiquarkOuter
#check @quarkAntiquarkTracelessSL3
#check @quarkAntiquarkDilatationTrace
#check @quarkAntiquarkTracelessSL3_trace_zero
#check @quarkAntiquarkToSL3
#check @gunaydin_gursey_g1_gm1_superbracket_closure
#check @embedPureQuarkZorn
#check @embedPureAntiQuarkZorn
#check @zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure
#check @oddSupercolorFull
#check @oddSupercolorFull_sq_closes_on_even_bosonic_socle
#check @superBerezinian23
#check @superTrace23
#check @leptonWeylScaleMatrix
#check @super_berezinian_gauge_invariance
#check @superSouriauMassieuPotential
#check @superSouriauMassieu_uv_cancellation_and_moment_readout

#print axioms z2z2_color_supersymmetry_sign_laws
#print axioms quarkAntiquarkTracelessSL3_trace_zero
#print axioms gunaydin_gursey_g1_gm1_superbracket_closure
#print axioms zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure
#print axioms oddSupercolorFull_sq_closes_on_even_bosonic_socle
#print axioms super_berezinian_gauge_invariance
#print axioms superSouriauMassieu_uv_cancellation_and_moment_readout

end InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesisAudit
