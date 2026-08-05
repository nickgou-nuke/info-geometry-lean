import Mathlib
import InfoGeometry.Topology.ProjectiveBoundaryAction

namespace InfoGeometry.Topology

/-!
# Determinant-one matrix actions on the projective boundary

The construction is written with the explicit 2-by-2 determinant.  This keeps
the preservation proof elementary and makes the required invertibility
hypothesis visible.
-/

def det2 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

@[ext]
structure SL2BoundaryMatrix (R : Type*) [CommRing R] where
  matrix : Matrix (Fin 2) (Fin 2) R
  det_eq_one : det2 matrix = 1

def SL2BoundaryMatrix.applyPair
    {R : Type*} [CommRing R]
    (M : SL2BoundaryMatrix R) (p : UnimodularPair R) :
    UnimodularPair R := by
    refine ⟨(M.matrix 0 0 * p.fst + M.matrix 0 1 * p.snd,
      M.matrix 1 0 * p.fst + M.matrix 1 1 * p.snd), ?_⟩
    rcases p.unimodular with ⟨a, b, hp⟩
    refine ⟨a * M.matrix 1 1 - b * M.matrix 1 0,
      -a * M.matrix 0 1 + b * M.matrix 0 0, ?_⟩
    calc
      (a * M.matrix 1 1 - b * M.matrix 1 0) *
            (M.matrix 0 0 * p.fst + M.matrix 0 1 * p.snd) +
          (-a * M.matrix 0 1 + b * M.matrix 0 0) *
            (M.matrix 1 0 * p.fst + M.matrix 1 1 * p.snd) =
          (a * p.fst + b * p.snd) * det2 M.matrix := by
            simp [det2]
            ring
      _ = 1 := by rw [hp, M.det_eq_one]; simp

def SL2BoundaryMatrix.toProjectiveAction
    {R : Type*} [CommRing R]
    (M : SL2BoundaryMatrix R) : ProjectiveBoundaryAction R where
  toPair := M.applyPair
  respects_units := by
    intro p q hpq
    rcases hpq with ⟨u, hfst, hsnd⟩
    refine ⟨u, ?_, ?_⟩
    · dsimp [SL2BoundaryMatrix.applyPair]
      change M.matrix 0 0 * q.fst + M.matrix 0 1 * q.snd =
        (u : R) * (M.matrix 0 0 * p.fst + M.matrix 0 1 * p.snd)
      rw [hfst, hsnd]
      ring
    · dsimp [SL2BoundaryMatrix.applyPair]
      change M.matrix 1 0 * q.fst + M.matrix 1 1 * q.snd =
        (u : R) * (M.matrix 1 0 * p.fst + M.matrix 1 1 * p.snd)
      rw [hfst, hsnd]
      ring

def SL2BoundaryMatrix.onBoundary
    {R : Type*} [CommRing R]
    (M : SL2BoundaryMatrix R) :
    ProjectiveBoundary R → ProjectiveBoundary R :=
  M.toProjectiveAction.onBoundary

@[simp] theorem SL2BoundaryMatrix.onBoundary_mk
    {R : Type*} [CommRing R]
    (M : SL2BoundaryMatrix R) (p : UnimodularPair R) :
    M.onBoundary (projectiveBoundaryMk p) =
      projectiveBoundaryMk (M.applyPair p) := rfl

end InfoGeometry.Topology
