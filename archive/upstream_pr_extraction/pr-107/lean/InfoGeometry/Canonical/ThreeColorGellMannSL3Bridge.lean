import InfoGeometry.Physics.ThreeColorSL3MatrixConjugation
import InfoGeometry.Physics.GellMannSU3

/-!
# Three-color Gell-Mann / `SL₃` bridge

This file packages a few concrete Gell-Mann commutator relations under the
existing `SL₃` conjugation transport theorem.  It does not introduce a new
representation: it reuses the matrix conjugation owner and the explicit
generator identities already proved in the physics layer.
-/

namespace InfoGeometry.Canonical.ThreeColorGellMannSL3Bridge

noncomputable section

open Matrix
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Physics.ThreeColorSL3MatrixConjugation

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev SL3C := Matrix.SpecialLinearGroup (Fin 3) ℂ

theorem sl3ConjAct_gl1_gl2_commutator (g : SL3C) :
    sl3ConjAct g (gl1 * gl2 - gl2 * gl1) =
      (2 * Complex.I) • sl3ConjAct g gl3 := by
  calc
    sl3ConjAct g (gl1 * gl2 - gl2 * gl1)
        = sl3ConjAct g gl1 * sl3ConjAct g gl2 -
            sl3ConjAct g gl2 * sl3ConjAct g gl1 := by
              rw [sl3ConjAct_commutator]
    _ = (2 * Complex.I) • sl3ConjAct g gl3 := by
      simpa [gl1_comm_gl2] using
        (sl3ConjAct_transport g gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2)

theorem sl3ConjAct_gl1_gl3_commutator (g : SL3C) :
    sl3ConjAct g (gl1 * gl3 - gl3 * gl1) =
      (-2 * Complex.I) • sl3ConjAct g gl2 := by
  calc
    sl3ConjAct g (gl1 * gl3 - gl3 * gl1)
        = sl3ConjAct g gl1 * sl3ConjAct g gl3 -
            sl3ConjAct g gl3 * sl3ConjAct g gl1 := by
              rw [sl3ConjAct_commutator]
    _ = (-2 * Complex.I) • sl3ConjAct g gl2 := by
      simpa [gl1_comm_gl3] using
        (sl3ConjAct_transport g gl1 gl3 gl2 (-2 * Complex.I) gl1_comm_gl3)

theorem sl3ConjAct_gl4_gl8_commutator (g : SL3C) :
    sl3ConjAct g (gl4 * gl8 - gl8 * gl4) =
      (-3 * Complex.I) • sl3ConjAct g gl5 := by
  calc
    sl3ConjAct g (gl4 * gl8 - gl8 * gl4)
        = sl3ConjAct g gl4 * sl3ConjAct g gl8 -
            sl3ConjAct g gl8 * sl3ConjAct g gl4 := by
              rw [sl3ConjAct_commutator]
    _ = (-3 * Complex.I) • sl3ConjAct g gl5 := by
      simpa [gl4_comm_gl8] using
        (sl3ConjAct_transport g gl4 gl8 gl5 (-3 * Complex.I) gl4_comm_gl8)

end

end InfoGeometry.Canonical.ThreeColorGellMannSL3Bridge
