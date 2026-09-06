import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.SuperMetriplectic.InverseBridge
import InfoGeometry.SuperMetriplectic.EntropyShadowBridge
import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Meta.Architecture

/-!
# SuperMetriplectic Triad Bridge

Small theorem-backed capstone bridge joining the conservative scalar chiral
closure packet to the existing scalar inverse-shadow and entropy-shadow bridges.

This file is intentionally conservative. It does not derive the scalar chiral
packet from the Schur/Drazin/entropy data. Instead it packages a triad together
with an explicit scalar chiral packet and records the compatibility equations
that identify the chiral translation/defect shadows with the Schur effective
metric and the Drazin defect projector.
-/

namespace InfoGeometry.SuperMetriplectic.TriadBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.AssociativeSuperBracket

/--
Conservative capstone packet joining:
- a scalar chiral odd-odd closure packet,
- a scalar Schur/Penrose/Drazin/body-entropy triad,
- and explicit compatibility equations between those scalar shadows.

Policy note: this bridge is a scalar readout surface only. It does not claim
that scalar shadows replace noncommuting operator dynamics.
-/
@[rep_depth transport]
structure DrazinPenroseSchurChiralTriadBridge where
  triad : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad
  chiral : InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure ℝ
  translationShadow_eq_effectiveEvenOnsager :
    chiral.translationShadow = triad.block.effectiveEvenOnsager
  defectShadow_eq_drazinDefectProjector :
    chiral.defectShadow = triad.block.drazinDefectProjector

/--
Readout-first alias for the scalar capstone packet.

This is naming-only (definitional) and keeps legacy theorem names intact.
-/
abbrev DrazinPenroseSchurChiralReadoutBridge := DrazinPenroseSchurChiralTriadBridge

namespace DrazinPenroseSchurChiralTriadBridge

/--
Scalar odd packet already certified to be compatible with a Schur/Drazin triad.

This narrows the previous raw constructor interface by packaging the odd data and
its closure witness into a dedicated scalar packet.
-/
@[rep_depth transport]
structure TriadCompatibleOddPacket where
  triad : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad
  QL : ℝ
  QR : ℝ
  gamma : ℝ
  oddOddClosure :
    anticommutator (QR - QL) (QR - QL)
      = gamma • triad.block.effectiveEvenOnsager + triad.block.drazinDefectProjector

namespace TriadCompatibleOddPacket

variable (P : TriadCompatibleOddPacket)

/-- The canonical scalar chiral closure carried by a triad-compatible odd packet. -/
@[rep_depth transport]
noncomputable def toChiralSuperchargeClosure :
    InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure ℝ where
  QL := P.QL
  QR := P.QR
  P := P.triad.block.effectiveEvenOnsager
  Z := P.triad.block.drazinDefectProjector
  gamma := P.gamma
  netOddOddClosure := P.oddOddClosure

@[rep_depth transport]
theorem toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager :
    (toChiralSuperchargeClosure P).translationShadow = P.triad.block.effectiveEvenOnsager := by
  rfl

/-- Readout-first restatement of the scalar translation-shadow compatibility. -/
@[rep_depth transport]
theorem toChiralSuperchargeClosure_translationReadout_eq_effectiveEvenOnsager :
    (toChiralSuperchargeClosure P).translationShadow = P.triad.block.effectiveEvenOnsager := by
  exact toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager P

@[rep_depth transport]
theorem toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector :
    (toChiralSuperchargeClosure P).defectShadow = P.triad.block.drazinDefectProjector := by
  rfl

/-- Readout-first restatement of the scalar defect-shadow compatibility. -/
@[rep_depth transport]
theorem toChiralSuperchargeClosure_defectReadout_eq_drazinDefectProjector :
    (toChiralSuperchargeClosure P).defectShadow = P.triad.block.drazinDefectProjector := by
  exact toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector P

end TriadCompatibleOddPacket

/--
Canonical scalar chiral closure built directly from triad-compatible odd data and
repo-owned scalar Schur/Drazin readouts.
-/
@[rep_depth transport]
noncomputable def chiralClosureOfTriadOddData
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure ℝ where
  QL := QL
  QR := QR
  P := T.block.effectiveEvenOnsager
  Z := T.block.drazinDefectProjector
  gamma := gamma
  netOddOddClosure := hClosure

@[rep_depth transport]
theorem chiralClosureOfTriadOddData_translationShadow_eq_effectiveEvenOnsager
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    (chiralClosureOfTriadOddData T QL QR gamma hClosure).translationShadow
      = T.block.effectiveEvenOnsager := by
  rfl

/-- Readout-first restatement of the scalar translation-shadow equality. -/
@[rep_depth transport]
theorem chiralClosureOfTriadOddData_translationReadout_eq_effectiveEvenOnsager
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    (chiralClosureOfTriadOddData T QL QR gamma hClosure).translationShadow
      = T.block.effectiveEvenOnsager := by
  exact chiralClosureOfTriadOddData_translationShadow_eq_effectiveEvenOnsager
    T QL QR gamma hClosure

@[rep_depth transport]
theorem chiralClosureOfTriadOddData_defectShadow_eq_drazinDefectProjector
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    (chiralClosureOfTriadOddData T QL QR gamma hClosure).defectShadow
      = T.block.drazinDefectProjector := by
  rfl

/-- Readout-first restatement of the scalar defect-shadow equality. -/
@[rep_depth transport]
theorem chiralClosureOfTriadOddData_defectReadout_eq_drazinDefectProjector
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    (chiralClosureOfTriadOddData T QL QR gamma hClosure).defectShadow
      = T.block.drazinDefectProjector := by
  exact chiralClosureOfTriadOddData_defectShadow_eq_drazinDefectProjector
    T QL QR gamma hClosure

/-- The packet-built closure is definitionally the raw triad-odd-data closure. -/
@[rep_depth transport]
theorem toChiralSuperchargeClosure_eq_chiralClosureOfTriadOddData
    (P : TriadCompatibleOddPacket) :
    P.toChiralSuperchargeClosure
      = chiralClosureOfTriadOddData P.triad P.QL P.QR P.gamma P.oddOddClosure := by
  rfl

@[rep_depth transport]
noncomputable def ofTriadCompatibleOddPacket
    (P : TriadCompatibleOddPacket) :
    DrazinPenroseSchurChiralTriadBridge where
  triad := P.triad
  chiral := P.toChiralSuperchargeClosure
  translationShadow_eq_effectiveEvenOnsager :=
    P.toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager
  defectShadow_eq_drazinDefectProjector :=
    P.toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector

/--
Capstone bridge constructor from triad-compatible odd data.

This removes the need to carry translation/defect compatibility as separate
fields: those shadows are now built directly from the triad block.
-/
@[rep_depth transport]
noncomputable def ofTriadOddData
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    DrazinPenroseSchurChiralTriadBridge where
  triad := T
  chiral := chiralClosureOfTriadOddData T QL QR gamma hClosure
  translationShadow_eq_effectiveEvenOnsager :=
    chiralClosureOfTriadOddData_translationShadow_eq_effectiveEvenOnsager T QL QR gamma hClosure
  defectShadow_eq_drazinDefectProjector :=
    chiralClosureOfTriadOddData_defectShadow_eq_drazinDefectProjector T QL QR gamma hClosure

/-- The raw odd-data constructor factors definitionally through the packaged odd packet. -/
@[rep_depth transport]
theorem ofTriadOddData_eq_ofTriadCompatibleOddPacket
    (T : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad)
    (QL QR : ℝ)
    (gamma : ℝ)
    (hClosure :
      anticommutator (QR - QL) (QR - QL)
        = gamma • T.block.effectiveEvenOnsager + T.block.drazinDefectProjector) :
    ofTriadOddData T QL QR gamma hClosure
      = ofTriadCompatibleOddPacket
          ({ triad := T
             QL := QL
             QR := QR
             gamma := gamma
             oddOddClosure := hClosure } : TriadCompatibleOddPacket) := by
  rfl

variable (B : DrazinPenroseSchurChiralTriadBridge)

/-- Hidden-block scalar chiral anomaly in repo-owned Moore-Penrose vocabulary. -/
@[rep_depth transport]
def hiddenBlockChiralAnomaly : ℝ :=
  MoorePenrose.chiralAnomaly B.triad.block.LΘΘ B.triad.block.drazin.aD B.triad.block.penrose.aPlus

/-- The carried chiral packet viewed as a public scalar readout closure interface. -/
@[rep_depth transport]
def toChiralSuperchargeClosure : InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure ℝ :=
  B.chiral

/-- Scalar translation readout exported by the capstone packet. -/
@[rep_depth transport]
def translationReadout : ℝ :=
  (toChiralSuperchargeClosure B).translationShadow

/-- Scalar defect readout exported by the capstone packet. -/
@[rep_depth transport]
def defectReadout : ℝ :=
  (toChiralSuperchargeClosure B).defectShadow

/-- The hidden scalar block carries a certified Moore-Penrose shadow witness. -/
@[rep_depth transport]
theorem hiddenBlock_hasMoorePenroseShadow :
    MoorePenrose.IsMoorePenroseInverse B.triad.block.LΘΘ B.triad.block.penrose.aPlus := by
  exact InfoGeometry.SuperMetriplectic.InverseBridge.hiddenBlock_hasMoorePenroseShadow B.triad.block

/-- The hidden scalar block carries a certified Drazin shadow witness. -/
@[rep_depth transport]
theorem hiddenBlock_hasDrazinShadow :
    Drazin.IsDrazinInverse B.triad.block.LΘΘ B.triad.block.drazin.aD B.triad.block.drazin.index := by
  exact InfoGeometry.SuperMetriplectic.InverseBridge.hiddenBlock_hasDrazinShadow B.triad.block

/-- Vanishing hidden-block projector mismatch kills the hidden scalar chiral anomaly. -/
@[rep_depth transport]
theorem hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero
    (hΔ : MoorePenrose.projectorMismatch B.triad.block.LΘΘ B.triad.block.drazin.aD B.triad.block.penrose.aPlus = 0) :
    hiddenBlockChiralAnomaly B = 0 := by
  simpa [hiddenBlockChiralAnomaly] using
    (InfoGeometry.SuperMetriplectic.EntropyShadowBridge.hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero
      B.triad.block hΔ)

/-- The scalar triad carries a coadjoint-leaf entropy split through the body packet. -/
@[rep_depth transport]
def toCoadjointLeafEntropySplit : InfoGeometry.SuperMetriplectic.CoadjointLeafEntropySplit :=
  InfoGeometry.SuperMetriplectic.EntropyShadowBridge.toCoadjointLeafEntropySplit B.triad.entropy

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction :
    (toCoadjointLeafEntropySplit B).totalEntropyChange = B.triad.entropy.production := by
  exact InfoGeometry.SuperMetriplectic.EntropyShadowBridge.toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction B.triad.entropy

/-- The carried chiral translation shadow is explicitly tied to the effective Schur metric. -/
@[rep_depth transport]
theorem toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager :
    (toChiralSuperchargeClosure B).translationShadow = B.triad.block.effectiveEvenOnsager := by
  exact B.translationShadow_eq_effectiveEvenOnsager

/-- Readout-first statement: scalar translation readout equals the effective Schur metric readout. -/
@[rep_depth transport]
theorem translationReadout_eq_effectiveEvenOnsager :
    B.translationReadout = B.triad.block.effectiveEvenOnsager := by
  simpa [translationReadout] using
    (toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager (B := B))

/-- The carried chiral defect shadow is explicitly tied to the Drazin defect projector. -/
@[rep_depth transport]
theorem toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector :
    (toChiralSuperchargeClosure B).defectShadow = B.triad.block.drazinDefectProjector := by
  exact B.defectShadow_eq_drazinDefectProjector

/-- Readout-first statement: scalar defect readout equals the Drazin defect-projector readout. -/
@[rep_depth transport]
theorem defectReadout_eq_drazinDefectProjector :
    B.defectReadout = B.triad.block.drazinDefectProjector := by
  simpa [defectReadout] using
    (toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector (B := B))

/--
Readout-seal theorem for this capstone interface.

This theorem records that exported scalar quantities are readouts tied to owned
scalar shadows; it does not assert replacement of noncommuting operator lanes.
-/
@[rep_depth transport]
theorem scalar_readout_seal :
    (B.translationReadout = B.triad.block.effectiveEvenOnsager)
      ∧ (B.defectReadout = B.triad.block.drazinDefectProjector) := by
  exact ⟨B.translationReadout_eq_effectiveEvenOnsager,
    B.defectReadout_eq_drazinDefectProjector⟩

/-- The effective metric is the Moore-Penrose stabilized Schur complement of the hidden block. -/
@[rep_depth transport]
theorem effective_metric_is_schur_complement :
    B.triad.entropy.effectiveOnsager
      = B.triad.block.LPP - B.triad.block.LPΘ * B.triad.block.penrose.aPlus * B.triad.block.LΘP := by
  exact InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad.effective_metric_is_schur_complement B.triad

end DrazinPenroseSchurChiralTriadBridge

end InfoGeometry.SuperMetriplectic.TriadBridge
