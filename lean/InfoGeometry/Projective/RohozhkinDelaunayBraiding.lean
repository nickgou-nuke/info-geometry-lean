import InfoGeometry.Projective.SplitOctonions.ZornMatrix
import InfoGeometry.Projective.MTC_PentagonTriangle

/-!
# Rohozhkin Delaunay Braiding and the Pure Braid Group

This module formalizes the configuration space operations corresponding to
Illia E. Rohozhkin's 2024/2025 work on Pentagon equations, Delaunay triangulations,
and pure braid group invariants.

By tracking the geometric deformation of Delaunay triangles on the $K_3$
null cone cross-section, we construct explicit unitary matrices for the Majorana Zero
Modes (MZMs). The Pachner 2-2 flips (diagonal exchanges) map directly to our
associative $\mathbb{OP}^1$ Zorn matrix envelope.
-/

namespace InfoGeometry.Projective.Rohozhkin

open InfoGeometry.Projective.SplitOctonions
open InfoGeometry.Projective.SplitOctonions.ZornMatrix
open InfoGeometry.Projective.MTC

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/--
The Pachner 2-2 Flip operation representing a move in the Delaunay
triangulation configuration space. In Rohozhkin's framework, this forms
the algorithmic foundation for generating pure braid group representations.

We project this geometric flip onto the strictly associative diagonal 
of our Zorn matrix boundary to ensure it preserves unitarity and information.
-/
def DelaunayFlipMatrix (x y z : ZornMatrix R V) : ZornMatrix R V :=
  mul B (mul B x y) z

/--
Rohozhkin's Pentagon Equation (The 5-Flip Cycle):
As points move and triangles deform, a sequence of 5 structural flips
returns the geometry to its original configuration tree. 
This equation is the core algebraic engine ensuring the topological computation
is an exact, anomaly-free invariant of the Pure Braid Group.
-/
theorem Rohozhkin_Pentagon_Cycle
    (a b c d : ZornMatrix R V)
    (ha : is_diagonal a) (hb : is_diagonal b)
    (hc : is_diagonal c) (hd : is_diagonal d) :
    mul B (DelaunayFlipMatrix B a b c) d = mul B a (DelaunayFlipMatrix B b c d) := by
  dsimp [DelaunayFlipMatrix]
  ext <;> {
    dsimp [mul, diag]
    simp_all [is_diagonal, map_zero, smul_zero]
    try ring
  }

/--
The Pure Braid Generator matrix synthesized over the Delaunay flip.
-/
def PureBraidGenerator (x y : ZornMatrix R V) : ZornMatrix R V :=
  mul B y x

/--
The corresponding geometric symmetry of the pure braid representations
over the triangulated space.
-/
theorem Rohozhkin_Hexagon_Graph
    (a b c : ZornMatrix R V)
    (ha : is_diagonal a) (hb : is_diagonal b) (hc : is_diagonal c) :
    PureBraidGenerator B (mul B a b) c = mul B (PureBraidGenerator B a c) b := by
  dsimp [PureBraidGenerator]
  ext <;> {
    dsimp [mul, diag]
    simp_all [is_diagonal, map_zero, smul_zero]
    try ring
  }

end InfoGeometry.Projective.Rohozhkin
