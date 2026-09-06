import InfoGeometry.Canonical.PeircePositiveCellImage

namespace InfoGeometry.Canonical

/-! Coordinate boundary strata for the finite Peirce-positive chart. -/

inductive PeirceBoundaryCoordinate
  | a00 | a01 | a10 | a11
  deriving DecidableEq, Fintype

def peirceBoundaryValue
    (b : PeirceBoundaryCoordinate)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  match b with
  | .a00 => M 0 0
  | .a01 => M 0 1
  | .a10 => M 1 0
  | .a11 => M 1 1

def peirceBoundaryLocus (b : PeirceBoundaryCoordinate) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | peirceBoundaryValue b M = 0}

def peircePositiveBoundaryCell (b : PeirceBoundaryCoordinate) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peircePositiveChannelCell ∩ peirceBoundaryLocus b

end InfoGeometry.Canonical
