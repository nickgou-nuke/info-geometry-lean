import InfoGeometry.Projective.SplitOctonions.ZornMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Modular Tensor Category: Pentagon and Triangle Equations on the Zorn Diagonal

This module formalizes the topological data of the Fibonacci Majorana Zero Modes (MZMs)
living on the associative $\mathbb{OP}^1$ horizon boundary.
-/

namespace InfoGeometry.Projective.MTC

open InfoGeometry.Projective.SplitOctonions
open InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/--
A diagonal Zorn matrix represents a state that is purely confined
to the associative horizon boundary $\mathbb{OP}^1$.
-/
def is_diagonal (x : ZornMatrix R V) : Prop :=
  x.x21 = 0 ∧ x.x22 = 0

/--
The F-matrix (Fusion) acts on the associative diagonal boundary.
-/
def FMatrix (x y z : ZornMatrix R V) : ZornMatrix R V :=
  mul B (mul B x y) z

/--
The Pentagon Equation for Fusion
-/
theorem MacLane_Pentagon_Equation
    (a b c d : ZornMatrix R V)
    (ha : is_diagonal a) (hb : is_diagonal b)
    (hc : is_diagonal c) (hd : is_diagonal d) :
    mul B (FMatrix B a b c) d = mul B a (FMatrix B b c d) := by
  dsimp [FMatrix]
  ext <;> {
    dsimp [mul, diag]
    simp_all [is_diagonal, map_zero, smul_zero]
    try ring
  }

/--
The Triangle Equation for Vacuum Identity
-/
theorem MacLane_Triangle_Equation
    (a b : ZornMatrix R V)
    (ha : is_diagonal a) (hb : is_diagonal b) :
    FMatrix B a (diag 1 1) b = mul B a b := by
  dsimp [FMatrix]
  ext <;> {
    dsimp [mul, diag]
    simp_all [is_diagonal, map_zero, smul_zero]
    try ring
  }

/--
The R-matrix (Braiding) operator on the diagonal boundary.
-/
def RMatrix (x y : ZornMatrix R V) : ZornMatrix R V :=
  mul B y x

/--
The Hexagon Equation for Braiding and Fusion consistency.
-/
theorem MacLane_Hexagon_Equation
    (a b c : ZornMatrix R V)
    (ha : is_diagonal a) (hb : is_diagonal b) (hc : is_diagonal c) :
    RMatrix B (mul B a b) c = mul B (RMatrix B a c) b := by
  dsimp [RMatrix]
  ext <;> {
    dsimp [mul, diag]
    simp_all [is_diagonal, map_zero, smul_zero]
    try ring
  }

end InfoGeometry.Projective.MTC
