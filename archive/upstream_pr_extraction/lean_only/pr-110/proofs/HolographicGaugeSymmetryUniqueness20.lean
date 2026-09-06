import proofs.HolographicGaugeSymmetryUniqueness

/-!
# 6-conjunct holographic gauge-symmetry uniqueness capstone

This is a thin bookkeeping capstone over
`HolographicGaugeSymmetryUniqueness.lean`.  It exposes the audit table as an
explicit 6-conjunct theorem of finite algebraic witnesses.

No analytic completion is asserted here; the finite algebraic shadow is proved.
-/

noncomputable section

namespace HolographicGaugeSymmetryUniqueness20

open HolographicGaugeSymmetryUniqueness
open SU3LoopBraidCuntzBoundary
open HillWheelerUniversalProjection
open Clifford55AnomalyOSP
open BogoliubovBraidGraphWeld
open BogoliubovSU3ParafermionProofChain

/-- The explicit 6-conjunct capstone:

1–6 are finite proved algebraic kernels. -/
theorem holographic_gauge_symmetry_uniqueness_6_synthesis {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (m n : ℤ) (q : ℂ) (ψ : ColorSpinor4 V) (s : ℂ) :
    loopBracket (gellMannLoopMode m GellMannSU3.gl1)
        (gellMannLoopMode n GellMannSU3.gl2) =
      loopSmul (2 * Complex.I) (gellMannLoopMode (m + n) GellMannSU3.gl3) ∧
    loopBracket (gellMannLoopMode m GellMannSU3.gl1)
        (gellMannLoopMode n GellMannSU3.gl3) =
      loopSmul (-2 * Complex.I) (gellMannLoopMode (m + n) GellMannSU3.gl2) ∧
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ)) ∧
    YangBaxterQSwap.C12 q * YangBaxterQSwap.C23 q * YangBaxterQSwap.C12 q =
      YangBaxterQSwap.C23 q * YangBaxterQSwap.C12 q * YangBaxterQSwap.C23 q ∧
    anomalyIndex 5 5 = 0 ∧
    (cptHillWheelerAverage s).re = 1 / 2 := by
  exact ⟨loop_gl1_gl2_commutator m n,
    loop_gl1_gl3_commutator m n,
    q_color_braid_loop_boundary_artin q ψ,
    finite_cuntz_jones_yang_baxter_shadow q,
    pin55_split_anomaly_filter,
    cptHillWheelerAverage_re s⟩

end HolographicGaugeSymmetryUniqueness20

end noncomputable section
