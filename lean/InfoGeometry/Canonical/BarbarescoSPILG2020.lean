import Mathlib.Tactic

/-!
# Barbaresco SPIGL 2020: finite Souriau--Casimir property layer

This file extracts theorem-safe algebraic content from
`Barbaresco-SPILG2020.pdf`:

* infinitesimal adjoint action `ad_X Y = [X,Y] = XY - YX`;
* KKS/Souriau bilinear form `B_F(X,Y)=⟪F,[X,Y]⟫`;
* alternating and cocycle/Jacobi identities for this finite model;
* the Massieu/Fisher finite-difference identity for `Φ(β)=β²/2`.

It intentionally does **not** claim the analytic/global statements of the
slides: no global coadjoint-orbit theorem, no measure-theoretic Gibbs state,
and no differentiable Lie-group construction.  Those remain interfaces for owner
files with the needed hypotheses.
-/

namespace InfoGeometry
namespace Canonical
namespace BarbarescoSPILG2020

abbrev M2Q := Matrix (Fin 2) (Fin 2) ℚ

def commutator (A B : M2Q) : M2Q := A * B - B * A

def trace2 (A : M2Q) : ℚ := A 0 0 + A 1 1

def tracePairing (F X : M2Q) : ℚ := trace2 (F * X)

/-- Finite KKS/Souriau form: `B_F(X,Y)=⟪F,[X,Y]⟫`. -/
def kksForm (F X Y : M2Q) : ℚ := tracePairing F (commutator X Y)

/-- Souriau two-cocycle in the finite matrix model. -/
def souriauTheta (F X Y : M2Q) : ℚ := kksForm F X Y

@[simp] theorem commutator_apply (A B : M2Q) (i j : Fin 2) :
    commutator A B i j = (A * B) i j - (B * A) i j :=
  rfl

theorem commutator_self (A : M2Q) : commutator A A = 0 := by
  ext i j
  simp [commutator]

theorem commutator_skew (A B : M2Q) : commutator A B = - commutator B A := by
  ext i j
  simp [commutator]

/-- Matrix commutators satisfy Jacobi: the infinitesimal Lie-algebra law in the slides. -/
theorem commutator_jacobi (A B C : M2Q) :
    commutator A (commutator B C) +
      commutator B (commutator C A) +
      commutator C (commutator A B) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem kks_alternating (F X : M2Q) : kksForm F X X = 0 := by
  simp [kksForm, tracePairing, trace2, commutator_self]

theorem kks_skew (F X Y : M2Q) : kksForm F X Y = - kksForm F Y X := by
  simp [kksForm, tracePairing, trace2, commutator, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem souriauTheta_eq_kks (F X Y : M2Q) :
    souriauTheta F X Y = kksForm F X Y :=
  rfl

/-- The finite Souriau cocycle equation is Jacobi after pairing with `F`. -/
theorem souriau_cocycle_jacobi (F X Y Z : M2Q) :
    souriauTheta F X (commutator Y Z) +
      souriauTheta F Y (commutator Z X) +
      souriauTheta F Z (commutator X Y) = 0 := by
  simp [souriauTheta, kksForm, tracePairing, trace2, commutator,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Algebraic Massieu potential `Φ(β)=β²/2`. -/
def massieu (β : ℚ) : ℚ := β ^ 2 / 2

/-- Algebraic entropy-affine Legendre readout `βQ-S(Q)` with `S(Q)=cQ`. -/
def affineEntropy (c Q : ℚ) : ℚ := c * Q

def legendreReadout (β c Q : ℚ) : ℚ := β * Q - affineEntropy c Q

theorem legendreReadout_eq_zero_on_dual_line (c Q : ℚ) :
    legendreReadout c c Q = 0 := by
  simp [legendreReadout, affineEntropy]

/-- Exact finite-difference Hessian property for Souriau/Fisher capacity. -/
theorem massieu_centered_second_difference (β : ℚ) :
    massieu (β + 1) - 2 * massieu β + massieu (β - 1) = 1 := by
  simp [massieu]
  ring

theorem property (F X Y Z : M2Q) :
    commutator X Y = - commutator Y X ∧
      (commutator X (commutator Y Z) +
        commutator Y (commutator Z X) +
        commutator Z (commutator X Y) = 0) ∧
      kksForm F X X = 0 ∧
      (souriauTheta F X (commutator Y Z) +
        souriauTheta F Y (commutator Z X) +
        souriauTheta F Z (commutator X Y) = 0) ∧
      (massieu (0 + 1) - 2 * massieu 0 + massieu (0 - 1) = 1) := by
  exact ⟨commutator_skew X Y,
    commutator_jacobi X Y Z,
    kks_alternating F X,
    souriau_cocycle_jacobi F X Y Z,
    massieu_centered_second_difference 0⟩

end BarbarescoSPILG2020
end Canonical
end InfoGeometry
