import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ProjectiveBoundarySL2Action

namespace InfoGeometry.Topology

/-!
# Composition of determinant-one boundary blocks
-/

theorem det2_mul
    {R : Type*} [CommRing R]
    (M N : Matrix (Fin 2) (Fin 2) R) :
    det2 (M * N) = det2 M * det2 N := by
  simp [det2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

def SL2BoundaryMatrix.mul
    {R : Type*} [CommRing R]
    (M N : SL2BoundaryMatrix R) : SL2BoundaryMatrix R where
  matrix := M.matrix * N.matrix
  det_eq_one := by
    rw [det2_mul, M.det_eq_one, N.det_eq_one]
    simp

theorem SL2BoundaryMatrix.mul_applyPair
    {R : Type*} [CommRing R]
    (M N : SL2BoundaryMatrix R) (p : UnimodularPair R) :
    (M.mul N).applyPair p = M.applyPair (N.applyPair p) := by
  ext <;> dsimp [SL2BoundaryMatrix.mul, SL2BoundaryMatrix.applyPair]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem SL2BoundaryMatrix.mul_onBoundary
    {R : Type*} [CommRing R]
    (M N : SL2BoundaryMatrix R) (p : ProjectiveBoundary R) :
    (M.mul N).onBoundary p =
      M.onBoundary (N.onBoundary p) := by
  refine Quotient.inductionOn p ?_
  intro q
  simpa [SL2BoundaryMatrix.onBoundary_mk] using
    congrArg projectiveBoundaryMk (M.mul_applyPair N q)

end InfoGeometry.Topology
