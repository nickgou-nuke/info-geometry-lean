import InfoGeometry.Canonical.HexagonalSixRootTiling
import InfoGeometry.Canonical.SplitOctonionSixSectorFin3

namespace InfoGeometry.Canonical

open HexagonalSixRootTiling

noncomputable section

/-!
# Hexagonal labels as split-octonion off-diagonal channels

The finite hexagonal labels and the six Zorn channels use different sheet
index types.  This owner supplies the explicit equivalence between them and
transports the already proved channel range without identifying the
associative matrix operator algebra with the split-octonion product.
-/

def hexSheetFin2 : HexSheet ≃ Fin 2 where
  toFun
    | .positive => 0
    | .negative => 1
  invFun
    | 0 => .positive
    | 1 => .negative
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    fin_cases s <;> rfl

def hexIndexSixSector (n : HexIndex) : ChiralZornCarrier :=
  let p := sheetColorEquiv n
  sixSectorBasisFin3 (hexSheetFin2 p.1) p.2

theorem hexIndexSixSector_eq_sheetColor (n : HexIndex) :
    hexIndexSixSector n =
      sixSectorBasisFin3
        (hexSheetFin2 (sheetColorEquiv n).1) (sheetColorEquiv n).2 := by
  rfl

theorem hexIndexSixSector_injective :
    Function.Injective hexIndexSixSector := by
  intro m n h
  have hp :
      (hexSheetFin2 (sheetColorEquiv m).1, (sheetColorEquiv m).2) =
        (hexSheetFin2 (sheetColorEquiv n).1, (sheetColorEquiv n).2) := by
    exact sixSectorBasisFin3_injective h
  have hs : (sheetColorEquiv m).1 = (sheetColorEquiv n).1 := by
    exact hexSheetFin2.injective
      (congrArg (fun p : Fin 2 × Fin 3 => p.1) hp)
  have hc : (sheetColorEquiv m).2 = (sheetColorEquiv n).2 :=
    congrArg (fun p : Fin 2 × Fin 3 => p.2) hp
  apply sheetColorEquiv.injective
  exact Prod.ext hs hc

theorem hexIndexSixSector_range :
    Set.range hexIndexSixSector =
      Set.range (fun p : Fin 2 × Fin 3 =>
        sixSectorBasisFin3 p.1 p.2) := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(hexSheetFin2 (sheetColorEquiv n).1, (sheetColorEquiv n).2), rfl⟩
  · rintro ⟨⟨s, c⟩, rfl⟩
    let n := sheetColorEquiv.symm (hexSheetFin2.symm s, c)
    refine ⟨n, ?_⟩
    simp [n, hexIndexSixSector]

end
end InfoGeometry.Canonical
