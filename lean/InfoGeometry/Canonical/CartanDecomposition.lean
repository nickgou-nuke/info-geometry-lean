import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical.CartanDecomposition

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R] [StarRing R]

/-!
# Information Cartan Decomposition

This module formalizes the splitting of belief updates into symmetric (compact)
and antisymmetric (non-compact) generators, driven by the discrepancy between
geometric and spectral information.
-/

/-- 
The Information Cartan Triple.
Pairs a degenerate information operator with its two canonical regularizations.
-/
structure InformationCartanTriple (R : Type*) [Ring R] [StarRing R] where
  A    : R
  A_D  : R
  A_MP : R

namespace InformationCartanTriple

variable (T : InformationCartanTriple R)

/-! ### 1. Chiral Operators (Gradings) -/

/-- 
The Geometric Chiral Operator (Geometric Grading).
Γ_G = P_R - P_L = A*A⁺ - A⁺*A.
Captures the 'Metric Orientation' of the belief manifold.
-/
def GammaG : R := 
  (IsMoorePenroseInverse.rightProjector T.A T.A_MP) - (IsMoorePenroseInverse.leftProjector T.A T.A_MP)

/-- 
The Spectral Chiral Operator (Spectral Grading).
Γ_S = 2*P_D - 1.
Captures the 'Algebraic Orientation' of the belief manifold.
-/
def GammaS : R := 
  2 * (IsDrazinInverse.projection T.A T.A_D) - 1

/-- 
Theorem: The commutator of the Geometric and Spectral Gradings is 
directly proportional to the Chiral Anomaly.
[Γ_G, Γ_S] = 2 [Γ_G, P_D].
-/
theorem grading_commutator_anomaly :
    T.GammaG * T.GammaS - T.GammaS * T.GammaG = 2 * (T.GammaG * (IsDrazinInverse.projection T.A T.A_D) - (IsDrazinInverse.projection T.A T.A_D) * T.GammaG) := by
  unfold GammaS
  noncomm_ring

/-! ### 2. The Cartan Splitting 𝔨 ⊕ 𝔭 -/

/-- 
The Compact (Rotational) Component.
Belief updates X that commute with the Geometric Grading Γ_G.
These preserve the 'Information Chirality'.
-/
def IsCompact (X : R) : Prop := X * T.GammaG = T.GammaG * X

/-- 
The Non-Compact (Boost) Component.
Belief updates X that anti-commute with the Geometric Grading Γ_G.
These drive the 'Information Scale' flow.
-/
def IsNonCompact (X : R) : Prop := X * T.GammaG = - (T.GammaG * X)

/-- 
Theorem: In a Normal belief manifold (ε = 0), the Spectral Projector 
is purely compact.
-/
theorem spectral_proj_is_compact_of_normal
    (h_gamma : T.GammaG = 0) :
    IsCompact T (IsDrazinInverse.projection T.A T.A_D) := by
  simp [IsCompact, h_gamma]

end InformationCartanTriple

end InfoGeometry.Canonical.CartanDecomposition
