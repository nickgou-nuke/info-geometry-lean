import InfoGeometry.Arithmetic.RiemannHypothesis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RHEquivalence
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Arithmetic.SpectralDistance
import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Analysis.BregmanMonodromyBridge
import DAG.ChiralDiracAnticommutation
import DAG.AffineProjectiveClosure
import DAG.GraphHodge
import DAG.HarmonicKMS
import DAG.MatrixRepresentation
import DAG.GradedBottInclusion

/-!
# Millennium arithmetic ledger — no RH proof

This module is an import-compatible ledger for arithmetic ingredients that may
be relevant to the repository's Hestenes--Krein/categorical-colimit RH
reformulations.  It does **not** prove the Riemann Hypothesis, a colimit zeta
identification, or a Möbius growth bound.
-/

open Complex

namespace InfoGeometry.Arithmetic

/-- Kernel fact: the Dikin envelope is positive for positive input. -/
example (t : ℝ) (ht : 0 < t) :
    0 < InfoGeometry.Analysis.BregmanAnalyticBound.dikinOmega t :=
  RHEquivalence.dikinOmega_pos t ht

/-- Kernel fact: the Liouville function flips sign after multiplication by a
prime under the hypotheses of the arithmetic owner. -/
example (p n : ℕ+) (hp : Nat.Prime (p.val)) :
    BostConnesSystem.liouville (p * n) = - BostConnesSystem.liouville n :=
  BostConnesSystem.liouville_prime_mul p n hp n.property

end InfoGeometry.Arithmetic
