/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

/-!
# Audit: `MajoranaParaKahlerMaurerCartanSupercolorSynthesis`

Typecheck and signature audit for `InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis`.
-/

namespace InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis.Audit

open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

#check @paraKahler_majorana_car_ccr_chameleon
#check @majoranaPairPlus
#check @majoranaPairMinus
#check @r44Metric
#check @r44Symplectic
#check @four_majorana_pairs_car_ccr_chameleon
#check @FiveGradedMaurerCartanJet
#check @canonicalMaurerCartanJet
#check @canonicalMaurerCartanJet_ne_default
#check @mcCurvatureGradeM2
#check @mcCurvatureGradeM1
#check @mcCurvatureGrade0
#check @mcCurvatureGradeP1
#check @mcCurvatureGradeP2
#check @mcCurvatureTower
#check @mcCurvatureTower_flat_iff_source_laws
#check @canonicalMaurerCartanJet_flat
#check @colorGenJ12
#check @colorGenK13
#check @colorGenJ12_mul_colorGenK13_ne_comm
#check @evenColorTransform
#check @evenColorTransform_annihilates_lepton_singlet
#check @evenColorTransform_preserves_quark_antiquark_pairing
#check @oddSupercolorTransform
#check @oddSupercolorTransform_components
#check @hyperbolic_root_plus_ell_lightcone_condensation
#check @canonicalImaginaryUnitOctonion
#check @canonicalImaginaryUnitOctonion_spec

end InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis.Audit
