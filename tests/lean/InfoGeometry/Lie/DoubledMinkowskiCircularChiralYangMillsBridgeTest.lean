/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Meta.Trust

open Lean Elab Command InfoGeometry.Meta

namespace InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridgeTest

private def bridgeDecls : Array Name :=
  #[ ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.doubledMinkowski_krein_pauli_soldering_bridge
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.zornToKreinFrame_intertwines_chirality
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularCoordToKreinFrame_intertwines_sheetFlip
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylChannel_noncomm_sheet_blocks_witness
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSheet_tetraktys_table
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularGaugeConnection4_evalScalar
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularGaugeConnection4_yang_mills_bridge
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularCurvatureMat4_hilbertSchmidt_action
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularCurvatureMat4_vorticity_action_gap
   , ``InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularConnection_starColimit_transport ]

run_cmd do
  let policy := defaultPolicySnapshot
  let batch ← liftCoreM <| collectHardEvidenceBatch policy bridgeDecls
  for decl in bridgeDecls do
    let some ev := batch[decl]?
      | throwError "missing HardEvidence for {decl}"
    unless ev.forbiddenAxioms.isEmpty do
      throwError "forbidden axioms on {decl}: {ev.forbiddenAxioms}"
    if ev.hasSorryAx then
      throwError "unexpected sorryAx dependency on {decl}"
    if ev.unsafeLeakage then
      throwError "unexpected unsafeLeakage on {decl}"

end InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridgeTest
