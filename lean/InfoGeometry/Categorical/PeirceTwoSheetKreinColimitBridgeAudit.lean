/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge

/-!
# Axiom audit for the Peirce two-sheet Krein colimit bridge.

These declarations expose the kernel axiom dependencies of the algebraic, categorical,
and concrete specialization results. They do not promote their interpretations beyond
the theorem statements in the owner module.
-/

open InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge

#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.genPhi_mul_self_eq_genV
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.genPhi_sq_eq_one_of_genV_eq_one
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.qgt_cycles_eq_peirce_corners_of_genV_eq_one
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.genPhi_conj_P_eq_compl
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.peirceKreinAction_square
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.peirceKreinStage_square
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.peirceKreinStage_exchanges_plus
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.peirceColimit_krein_involutive_and_sheet_exchange
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.sheetMatrix_genPhi_eq_fundamentalSymmetry
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.sheetMatrix_qgt_and_genV_identities
#print axioms InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge.hestenes_krein_peirce_colimit_master_bridge
