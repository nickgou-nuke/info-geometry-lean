import Mathlib
import InfoGeometry.Canonical.PeircePositiveBoundary

namespace InfoGeometry.Canonical

/-!
  A theorem-honest local residue socket for a Peirce boundary coordinate.

  This is deliberately scalar: it records a local defining parameter and a
  regular factor.  It is not yet a differential form or a canonical-form
  theorem.
-/

structure PeirceBoundaryResidueSocket
    (b : PeirceBoundaryCoordinate)
    (path : ℝ → Matrix (Fin 2) (Fin 2) ℝ) where
  regularPart : ℝ → ℝ
  regularPart_continuousAt_zero : ContinuousAt regularPart 0
  factorization : ∀ t,
    peirceBoundaryValue b (path t) = t * regularPart t

def PeirceBoundaryResidue
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (socket : PeirceBoundaryResidueSocket b path) : ℝ :=
  socket.regularPart 0

def peirceBoundaryCoordinatePath
    (b : PeirceBoundaryCoordinate) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  match b with
  | .a00 => ![![t, 1], ![1, 1]]
  | .a01 => ![![1, t], ![1, 1]]
  | .a10 => ![![1, 1], ![t, 1]]
  | .a11 => ![![1, 1], ![1, t]]

theorem peirceBoundaryCoordinatePath_value
    (b : PeirceBoundaryCoordinate) (t : ℝ) :
    peirceBoundaryValue b (peirceBoundaryCoordinatePath b t) = t := by
  fin_cases b <;> rfl

noncomputable def peirceCoordinateResidueSocket
    (b : PeirceBoundaryCoordinate) :
    PeirceBoundaryResidueSocket b
      (peirceBoundaryCoordinatePath b) where
  regularPart := fun _ => 1
  regularPart_continuousAt_zero := continuous_const.continuousAt
  factorization := by
    intro t
    rw [peirceBoundaryCoordinatePath_value]
    ring

theorem peirceCoordinateResidueSocket_residue
    (b : PeirceBoundaryCoordinate) :
    PeirceBoundaryResidue (peirceCoordinateResidueSocket b) = 1 := by
  rfl

theorem peirceBoundaryResidue_quotient_eq_regularPart
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (socket : PeirceBoundaryResidueSocket b path)
    {t : ℝ} (ht : t ≠ 0) :
    peirceBoundaryValue b (path t) / t = socket.regularPart t := by
  rw [socket.factorization]
  field_simp

theorem peirceBoundaryResidue_regularPart_tendsto
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (socket : PeirceBoundaryResidueSocket b path) :
    Filter.Tendsto socket.regularPart (_root_.nhds 0)
      (_root_.nhds (PeirceBoundaryResidue socket)) := by
  simpa [PeirceBoundaryResidue] using
    socket.regularPart_continuousAt_zero

end InfoGeometry.Canonical
