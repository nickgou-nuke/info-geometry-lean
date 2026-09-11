import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Topology.WallpaperRepresentations

namespace InfoGeometry.Topology
open InfoGeometry.Topology

/-- Wallpaper representation row data structure -/
structure WallpaperRepresentationRow where
  lattice : WallpaperLattice
  pointGroup : WallpaperPointGroup
  pointGroupOrder : ℕ
  oneDimensional : ℕ
  twoDimensional : ℕ
  irrepTotal : ℕ
  deriving Repr, DecidableEq

/-- Build a complete representation row from a wallpaper group. -/
def representationRow (g : WallpaperGroup) : WallpaperRepresentationRow :=
  let P := pointGroupKind g
  let profile := pointGroupIrrepProfile P
  {
    lattice := latticeKind g
    pointGroup := P
    pointGroupOrder := pointGroupOrder P
    oneDimensional := profile.oneDimensional
    twoDimensional := profile.twoDimensional
    irrepTotal := profile.total
  }

theorem representationRow_fields (g : WallpaperGroup) :
    (representationRow g).lattice = latticeKind g ∧
    (representationRow g).pointGroup = pointGroupKind g ∧
    (representationRow g).pointGroupOrder = point_group_order g ∧
    (representationRow g).irrepTotal = gamma_irrep_count g := by
  cases g <;> decide

def allRows : List (WallpaperGroup × WallpaperRepresentationRow) :=
  [(.p1, representationRow .p1), (.p2, representationRow .p2), (.pm, representationRow .pm),
   (.pg, representationRow .pg), (.cm, representationRow .cm), (.pmm, representationRow .pmm),
   (.pmg, representationRow .pmg), (.pgg, representationRow .pgg), (.cmm, representationRow .cmm),
   (.p4, representationRow .p4), (.p4m, representationRow .p4m), (.p4g, representationRow .p4g),
   (.p3, representationRow .p3), (.p3m1, representationRow .p3m1), (.p31m, representationRow .p31m),
   (.p6, representationRow .p6), (.p6m, representationRow .p6m)]

theorem allRows_length : allRows.length = 17 := by decide

theorem p6m_row : representationRow .p6m =
    { lattice := .hexagonal, pointGroup := .D6, pointGroupOrder := 12,
      oneDimensional := 4, twoDimensional := 2, irrepTotal := 6 } := by rfl

theorem p4m_row : representationRow .p4m =
    { lattice := .square, pointGroup := .D4, pointGroupOrder := 8,
      oneDimensional := 4, twoDimensional := 1, irrepTotal := 5 } := by rfl

/-- Character table entries as exact rational / cyclotomic expressions encoded as strings for each point group.
--   Each inner list is a conjugacy class column, each outer list is an irrep row.
--   Expressions use: 1, -1, 2, -2, i, -i, w3, w3², z6, z6², z6⁴, z6⁵ -/
def pointGroupCharacterTable (P : WallpaperPointGroup) : List (List String) :=
  match P with
  | .C1 => [["1"]]
  | .C2 => [["1", "1"], ["1", "-1"]]
  | .D1 => [["1", "1"], ["1", "-1"]]
  | .V4 => [["1", "1", "1", "1"], ["1", "1", "-1", "-1"], ["1", "-1", "1", "-1"], ["1", "-1", "-1", "1"]]
  | .C4 => [["1", "1", "1", "1"], ["1", "i", "-1", "-i"], ["1", "-1", "1", "-1"], ["1", "-i", "-1", "i"]]
  | .D4 => [["1", "1", "1", "1", "1"], ["1", "1", "1", "-1", "-1"], ["1", "1", "-1", "1", "-1"], ["1", "1", "-1", "-1", "1"], ["2", "-2", "0", "0", "0"]]
  | .C3 => [["1", "1", "1"], ["1", "w3", "w3²"], ["1", "w3²", "w3"]]
  | .D3 => [["1", "1", "1"], ["1", "1", "-1"], ["2", "-1", "0"]]
  | .C6 => [["1", "1", "1", "1", "1", "1"], ["1", "z6", "z6²", "-1", "z6⁴", "z6⁵"], ["1", "z6²", "z6⁴", "1", "z6²", "z6⁴"], ["1", "-1", "1", "-1", "1", "-1"], ["1", "z6⁴", "z6²", "1", "z6⁴", "z6²"], ["1", "z6⁵", "z6⁴", "-1", "z6²", "z6"]]
  | .D6 => [["1", "1", "1", "1", "1", "1"], ["1", "1", "1", "1", "-1", "-1"], ["1", "-1", "-1", "1", "1", "-1"], ["1", "-1", "-1", "1", "-1", "1"], ["2", "-2", "1", "-1", "0", "0"], ["2", "2", "-1", "-1", "0", "0"]]

/-- Character table row count equals number of irreps. -/
theorem pointGroupCharacterTable_row_count (P : WallpaperPointGroup) :
    (pointGroupCharacterTable P).length = (pointGroupIrrepProfile P).total := by
  cases P <;> decide

/-- Character table column count equals number of conjugacy classes. -/
theorem pointGroupCharacterTable_col_count (P : WallpaperPointGroup) :
    ((pointGroupCharacterTable P).headD []).length = (pointGroupClassLabels P).length := by
  cases P <;> decide

end InfoGeometry.Topology
