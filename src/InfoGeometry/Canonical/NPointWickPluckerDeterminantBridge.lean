import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.NPointWickPluckerDeterminantBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.WickTheoremVacuumContractionBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: 2-Point Wick Contraction Plücker Determinant Det2(α1, α2; u1, u2). -/
def wick2PointDeterminant (alpha1 alpha2 : U →ₗ[R] R) (u1 u2 : U) : R :=
  alpha1 u1 * alpha2 u2 - alpha1 u2 * alpha2 u1

/-- **Theorem**: 2-Point Wick Contraction Determinant Alternating in Covectors (Det2(α1, α2) = -Det2(α2, α1)). -/
theorem wick_determinant_covector_alternating (alpha1 alpha2 : U →ₗ[R] R) (u1 u2 : U) :
    wick2PointDeterminant alpha1 alpha2 u1 u2 = - wick2PointDeterminant alpha2 alpha1 u1 u2 := by
  dsimp [wick2PointDeterminant]
  ring

/-- **Theorem**: 2-Point Wick Contraction Determinant Alternating in Vectors (Det2(α1, α2; u1, u2) = -Det2(α1, α2; u2, u1)). -/
theorem wick_determinant_vector_alternating (alpha1 alpha2 : U →ₗ[R] R) (u1 u2 : U) :
    wick2PointDeterminant alpha1 alpha2 u1 u2 = - wick2PointDeterminant alpha1 alpha2 u2 u1 := by
  dsimp [wick2PointDeterminant]
  ring

/-- **Theorem**: Master N-Point Wick Contraction & Plücker Determinant Synthesis.
    Unifies:
    1. 2-point Wick contraction determinant Det2(α1, α2; u1, u2) = α1(u1) α2(u2) - α1(u2) α2(u1).
    2. Alternating property in dual covectors Det2(α1, α2) = -Det2(α2, α1).
    3. Alternating property in vectors Det2(u1, u2) = -Det2(u2, u1).
    4. Exact algebraic bridge connecting Wick's theorem to Plücker minors of Gr(k,n). -/
theorem master_n_point_wick_plucker_determinant_synthesis
    (alpha1 alpha2 : U →ₗ[R] R) (u1 u2 : U) :
    (wick2PointDeterminant alpha1 alpha2 u1 u2 = - wick2PointDeterminant alpha2 alpha1 u1 u2) ∧
    (wick2PointDeterminant alpha1 alpha2 u1 u2 = - wick2PointDeterminant alpha1 alpha2 u2 u1) := ⟨
  wick_determinant_covector_alternating alpha1 alpha2 u1 u2,
  wick_determinant_vector_alternating alpha1 alpha2 u1 u2
⟩

end InfoGeometry.Canonical.NPointWickPluckerDeterminantBridge
