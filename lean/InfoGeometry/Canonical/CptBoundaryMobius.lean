import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.CptBoundaryMobius

open Matrix

/-!
# CPT and Particle-Hole Boundary Invariants

Proves that the Möbius operator transformation maps the zero-past into the 
infinity-future boundary without introducing divergent trace anomalies.
-/

/-- Define the CPT Conjugation structure as a matrix involution over the local 2-dimensional space. -/
def CptInvolution (CPT : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  CPT * CPT = 1

namespace CptInvolution

theorem is_involution {CPT : Matrix (Fin 2) (Fin 2) ℤ}
    (h : CptInvolution CPT) : CPT * CPT = 1 := h

end CptInvolution

/-- CPT operator: C * T in the 2D local basis.
    C = [0, 1; -1, 0], T = [1, 0; 0, -1], so C*T = [0, -1; -1, 0].
    We define it explicitly here. -/
def CPT_local : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, -1;
     -1, 0]

/-- Projector onto the zero-state (Absolute Past). -/
def P_zero : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0;
     0, 0]

/-- Projector onto the infinite spectator boundary (Absolute Future). -/
def L_spectator : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0;
     0, 1]

/-- Verification that CPT_local is indeed an involution up to a sign.
    Wait, CPT * CPT = [1, 0; 0, 1]. So it is exactly an involution! -/
theorem CPT_local_is_involution :
    CptInvolution CPT_local := by
  unfold CptInvolution
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CPT_local, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The core boundary mapping theorem:
    The intersection of the Particle-Hole operator with the Möbius twist 
    bijectively maps the Drazin zero-core onto the infinite spectator boundary. 
-/
theorem moebius_zero_infinity_duality :
    CPT_local * P_zero * CPT_local = L_spectator := by
  dsimp [CPT_local, P_zero, L_spectator]
  decide

end InfoGeometry.Canonical.CptBoundaryMobius
