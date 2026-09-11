import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.SUNLoopBraidCuntzBoundary
import InfoGeometry.External.Auto.BogoliubovBraidGraphWeld
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Clifford.Clifford55AnomalyOSP

/-!
# Finite holographic gauge-symmetry bridge

This file packages only the available finite algebraic content.  It does not
define a completed loop group, a Cuntz--Jones theorem, a conformal net, or an
analytic CPT theorem.

The three concrete lanes are:

* matrix loop modes, with the Gell-Mann commutator transported to mode sums;
* q-clocked color braids and the explicit 8-by-8 Yang--Baxter matrix;
* the arithmetic split-signature readout `5 - 5 = 0`.

The final midpoint lemma is an elementary complex conjugation identity.  It is
not a spectral or analytic CPT assertion.
-/

noncomputable section

namespace InfoGeometry.Canonical.HolographicGaugeSymmetryFiniteBridge

open InfoGeometry.Physics.GellMannSU3
open SUNLoopBraidCuntzBoundary
open BogoliubovBraidGraphWeld
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Clifford.Clifford55AnomalyOSP
open InfoGeometry.Topology.AlgebraicCuntzQuotient

abbrev SU3LoopMode := SUNLoopMode 3

def su3LoopMode (m : ℤ) (A : Matrix (Fin 3) (Fin 3) ℂ) : SU3LoopMode :=
  matrixLoopMode m A

theorem su3_loop_gl1_gl2 (m n : ℤ) :
    loopBracket (su3LoopMode m gl1) (su3LoopMode n gl2) =
      loopSmul (2 * Complex.I) (su3LoopMode (m + n) gl3) := by
  exact loopBracket_of_commutator m n gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2

theorem su3_loop_gl1_gl3 (m n : ℤ) :
    loopBracket (su3LoopMode m gl1) (su3LoopMode n gl3) =
      loopSmul (-2 * Complex.I) (su3LoopMode (m + n) gl2) := by
  exact loopBracket_of_commutator m n gl1 gl3 gl2 (-2 * Complex.I) gl1_comm_gl3

theorem su3_loop_gl2_gl3 (m n : ℤ) :
    loopBracket (su3LoopMode m gl2) (su3LoopMode n gl3) =
      loopSmul (2 * Complex.I) (su3LoopMode (m + n) gl1) := by
  exact loopBracket_of_commutator m n gl2 gl3 gl1 (2 * Complex.I) gl2_comm_gl3

theorem q_color_artin {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (ψ : ColorSpinor4 V) :
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ)) := by
  exact qColorBraid4_artin q ψ

theorem q_swap_yang_baxter (q : ℂ) :
    InfoGeometry.Physics.YangBaxterQSwap.C12 q *
        InfoGeometry.Physics.YangBaxterQSwap.C23 q *
        InfoGeometry.Physics.YangBaxterQSwap.C12 q =
      InfoGeometry.Physics.YangBaxterQSwap.C23 q *
        InfoGeometry.Physics.YangBaxterQSwap.C12 q *
        InfoGeometry.Physics.YangBaxterQSwap.C23 q := by
  exact InfoGeometry.Physics.YangBaxterQSwap.yang_baxter_relation q

theorem split_anomaly_index_zero : anomalyIndex 5 5 = 0 := by
  exact anomalyIndex_55_zero

/-- The elementary conjugation midpoint used as a finite real-part readout. -/
def conjugationMidpoint (s : ℂ) : ℂ :=
  (s + (1 - star s)) / 2

theorem conjugationMidpoint_re (s : ℂ) :
    (conjugationMidpoint s).re = 1 / 2 := by
  simp [conjugationMidpoint, div_eq_mul_inv]

structure FiniteHolographicGaugeData : Prop where
  loop_gl1_gl2 : ∀ m n : ℤ,
    loopBracket (su3LoopMode m gl1) (su3LoopMode n gl2) =
      loopSmul (2 * Complex.I) (su3LoopMode (m + n) gl3)
  loop_gl1_gl3 : ∀ m n : ℤ,
    loopBracket (su3LoopMode m gl1) (su3LoopMode n gl3) =
      loopSmul (-2 * Complex.I) (su3LoopMode (m + n) gl2)
  q_artin : ∀ {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (ψ : ColorSpinor4 V),
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ))
  ybe : ∀ q : ℂ,
    InfoGeometry.Physics.YangBaxterQSwap.C12 q *
        InfoGeometry.Physics.YangBaxterQSwap.C23 q *
        InfoGeometry.Physics.YangBaxterQSwap.C12 q =
      InfoGeometry.Physics.YangBaxterQSwap.C23 q *
        InfoGeometry.Physics.YangBaxterQSwap.C12 q *
        InfoGeometry.Physics.YangBaxterQSwap.C23 q
  anomaly : anomalyIndex 5 5 = 0

theorem finite_holographic_gauge_data :
    FiniteHolographicGaugeData := by
  refine ⟨su3_loop_gl1_gl2, su3_loop_gl1_gl3, ?_, q_swap_yang_baxter,
    split_anomaly_index_zero⟩
  intro V _ _ q ψ
  exact q_color_artin q ψ

end InfoGeometry.Canonical.HolographicGaugeSymmetryFiniteBridge

end noncomputable section
