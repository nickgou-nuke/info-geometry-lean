import InfoGeometry.Categorical.FibonacciFiveChannelAssociator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciPentagonVertexAssociator
import InfoGeometry.Canonical.FibonacciPentagonEquationBridge

/-!
# Concrete golden-ratio normalization of the Fibonacci associator

This file supplies the standard real positive Fibonacci parameters to the
existing complex-valued five-channel associator.  It does not claim the
pentagon word equality; it closes only the scalar normalization needed by the
nontrivial `F` block.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonGoldenNormalization

open InfoGeometry.Categorical.FibonacciFiveChannelAssociator
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier
open InfoGeometry.Categorical.FibonacciPentagonVertexAssociator
open FibonacciPentagonEquationBridge

noncomputable def goldenTau : ℂ :=
  Complex.ofReal (1 / goldenRatio)

noncomputable def goldenS : ℂ :=
  Complex.ofReal (1 / Real.sqrt goldenRatio)

theorem goldenTau_sq_add_goldenTau :
    goldenTau ^ 2 + goldenTau = 1 := by
  rw [goldenTau, ← Complex.ofReal_pow, ← Complex.ofReal_add]
  congr 1
  exact golden_ratio_inverse_sum_identity

theorem goldenS_sq :
    goldenS ^ 2 = goldenTau := by
  rw [goldenS, goldenTau, ← Complex.ofReal_pow]
  congr 1
  have hpos : 0 < goldenRatio := by
    dsimp [goldenRatio]
    positivity
  have hsqrt : (Real.sqrt goldenRatio) ^ 2 = goldenRatio :=
    Real.sq_sqrt (le_of_lt hpos)
  rw [div_pow, hsqrt]
  ring

theorem golden_fiveChannelAssociator_involutive :
    fiveChannelAssociatorMatrix goldenTau goldenS *
        fiveChannelAssociatorMatrix goldenTau goldenS = 1 :=
  fiveChannelAssociatorMatrix_sq goldenTau goldenS
    goldenS_sq goldenTau_sq_add_goldenTau

theorem golden_formalVertexAssociator_comp_inverse
    (v w : PentagonVertex) :
    (formalVertexAssociator w v goldenTau goldenS).comp
        (formalVertexAssociator v w goldenTau goldenS) = LinearMap.id := by
  exact formalVertexAssociator_comp_inverse v w goldenTau goldenS
    goldenS_sq goldenTau_sq_add_goldenTau

theorem golden_formalVertexAssociator_inverse_comp
    (v w : PentagonVertex) :
    (formalVertexAssociator v w goldenTau goldenS).comp
        (formalVertexAssociator w v goldenTau goldenS) = LinearMap.id := by
  exact formalVertexAssociator_inverse_comp v w goldenTau goldenS
    goldenS_sq goldenTau_sq_add_goldenTau

end InfoGeometry.Categorical.FibonacciPentagonGoldenNormalization
