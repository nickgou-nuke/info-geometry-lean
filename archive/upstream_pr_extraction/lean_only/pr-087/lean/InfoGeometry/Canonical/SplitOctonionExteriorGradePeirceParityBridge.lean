import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

/-!
# Native exterior-grade / Peirce-parity intertwiner

The literal exterior algebra already carries Mathlib's grade involution, while
the `1+3+3+1` Peirce coordinate carrier carries `exteriorDegreeParity`.
This owner proves that they are the same involution under the established
basis-preserving linear equivalence.

The proof uses the actual Mathlib exterior basis.  No multiplicative
identification between exterior wedge multiplication and the nonassociative
Zorn product is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge

open InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev V3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3
abbrev CoordinateCarrier :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.SplitOctonionCoordinateCarrier
abbrev CoordinateEnd := Module.End ℝ CoordinateCarrier

/-- Grade involution on an explicit `n`-fold exterior product. -/
theorem exteriorGrade3_ιMulti (n : ℕ) (v : Fin n → V3) :
    exteriorGrade3 (ExteriorAlgebra.ιMulti ℝ n v) =
      ((-1 : ℝ) ^ n) • ExteriorAlgebra.ιMulti ℝ n v := by
  induction n with
  | zero =>
      simp [ExteriorAlgebra.ιMulti_zero_apply, exteriorGrade3]
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      change exteriorGrade3
          (exteriorWedge3 (v 0)
            (ExteriorAlgebra.ιMulti ℝ n (Matrix.vecTail v))) = _
      rw [exteriorGrade3_wedge, ih (Matrix.vecTail v), map_smul]
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      rw [pow_succ]
      module

/-- Mathlib's canonical exterior basis is diagonal for the grade involution,
with eigenvalue `(-1)^|s|`. -/
theorem exteriorGrade3_mathlibBasis (s : Finset (Fin 3)) :
    exteriorGrade3 (vBasis3.ExteriorAlgebra s) =
      ((-1 : ℝ) ^ s.card) • vBasis3.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  simpa [exteriorPower.ιMulti_family] using
    (exteriorGrade3_ιMulti s.card
      (vBasis3 ∘ Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.prodEquiv.symm s).2))

/-- The repository's collected exterior basis is Mathlib's canonical exterior
basis on the same `Finset (Fin 3)` index. -/
theorem exterior3BasisFinset_eq_mathlibBasis :
    exterior3BasisFinset = vBasis3.ExteriorAlgebra := by
  apply Module.Basis.ext
  intro s
  simp [exterior3BasisFinset, exterior3BasisSigma,
    Module.Basis.ExteriorAlgebra, degreeBasis3]

/-- The Peirce-reindexed exterior basis is the Mathlib exterior basis indexed
by the corresponding subset. -/
theorem exterior3PeirceBasis_eq_mathlibBasis (i : Fin 8) :
    exterior3PeirceBasis i = vBasis3.ExteriorAlgebra (peirceSubset i) := by
  rw [exterior3PeirceBasis, exterior3BasisFinset_eq_mathlibBasis]
  simp [peirceSubsetEquiv]

/-- Every Peirce basis vector has the expected exterior-grade eigenvalue. -/
theorem exteriorGrade3_peirceBasis (i : Fin 8) :
    exteriorGrade3 (exterior3PeirceBasis i) =
      ((-1 : ℝ) ^ exteriorDegree1331 i) • exterior3PeirceBasis i := by
  rw [exterior3PeirceBasis_eq_mathlibBasis, exteriorGrade3_mathlibBasis]
  rw [exteriorDegree1331_eq_card_peirceSubset]

/-- Coordinate degree parity has the same eigenvalue on every coordinate axis. -/
theorem exteriorDegreeParity_single (i : Fin 8) :
    exteriorDegreeParity (Pi.single i (1 : ℝ)) =
      ((-1 : ℝ) ^ exteriorDegree1331 i) • Pi.single i (1 : ℝ) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [exteriorDegreeParity, exteriorDegree1331, Pi.single_apply]

/-- Basis-level commuting square between literal exterior grade and Peirce
coordinate degree parity. -/
theorem exteriorGrade3_coordinate_intertwines_basis (i : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv
        (exteriorGrade3 (exterior3PeirceBasis i)) =
      exteriorDegreeParity
        (exterior3SplitOctonionCoordinateEquiv (exterior3PeirceBasis i)) := by
  rw [exteriorGrade3_peirceBasis, map_smul,
    exterior3SplitOctonionCoordinateEquiv_basis,
    exterior3SplitOctonionCoordinateEquiv_basis,
    exteriorDegreeParity_single]

/-- Full commuting theorem: Mathlib's grade involution transports exactly to
`exteriorDegreeParity` on the `1+3+3+1` Peirce coordinate carrier. -/
theorem exteriorGrade3_coordinate_intertwines (ψ : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorGrade3 ψ) =
      exteriorDegreeParity (exterior3SplitOctonionCoordinateEquiv ψ) := by
  let L : Exterior3 →ₗ[ℝ] CoordinateCarrier :=
    exterior3SplitOctonionCoordinateEquiv.toLinearMap.comp
      exteriorGrade3.toLinearMap
  let R : Exterior3 →ₗ[ℝ] CoordinateCarrier :=
    exteriorDegreeParity.comp exterior3SplitOctonionCoordinateEquiv.toLinearMap
  have hLR : L = R := by
    apply exterior3PeirceBasis.ext
    intro i
    simpa [L, R] using exteriorGrade3_coordinate_intertwines_basis i
  simpa [L, R] using congrArg (fun T : Exterior3 →ₗ[ℝ] CoordinateCarrier => T ψ) hLR

/-- Conjugating the literal exterior grade through the established coordinate
equivalence gives exactly the existing Peirce degree-parity operator. -/
noncomputable def transportedExteriorGrade : CoordinateEnd :=
  exterior3SplitOctonionCoordinateEquiv.toLinearMap.comp
    (exteriorGrade3.toLinearMap.comp
      exterior3SplitOctonionCoordinateEquiv.symm.toLinearMap)

theorem transportedExteriorGrade_eq_exteriorDegreeParity :
    transportedExteriorGrade = exteriorDegreeParity := by
  apply LinearMap.ext
  intro x
  change exterior3SplitOctonionCoordinateEquiv
      (exteriorGrade3 (exterior3SplitOctonionCoordinateEquiv.symm x)) =
    exteriorDegreeParity x
  rw [exteriorGrade3_coordinate_intertwines,
    exterior3SplitOctonionCoordinateEquiv.apply_symm_apply]

/-- Exterior degree parity commutes with the independent Peirce sheet parity. -/
theorem transportedExteriorGrade_commutes_sheetParity :
    transportedExteriorGrade * peirceSheetParity =
      peirceSheetParity * transportedExteriorGrade := by
  rw [transportedExteriorGrade_eq_exteriorDegreeParity]
  exact peirceParities_commute.symm

/-- The four joint character projectors are simultaneous eigenspaces of the
transported Mathlib exterior-grade involution. -/
theorem transportedExteriorGrade_character_projector_packet :
    transportedExteriorGrade * projectorPP = projectorPP ∧
    transportedExteriorGrade * projectorPM = -projectorPM ∧
    transportedExteriorGrade * projectorMP = projectorMP ∧
    transportedExteriorGrade * projectorMM = -projectorMM := by
  rw [transportedExteriorGrade_eq_exteriorDegreeParity]
  exact ⟨degreeParity_projectorPP, degreeParity_projectorPM,
    degreeParity_projectorMP, degreeParity_projectorMM⟩

end InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
