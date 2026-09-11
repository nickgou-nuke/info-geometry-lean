import InfoGeometry.Analysis.BipolarMobiusPunctureEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Convex.BipolarLogitBarrierDuality
import InfoGeometry.Canonical.BipolarSquareRootSpinorialDescent
import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import InfoGeometry.NCG.BipolarCayleyBerezinianRealization

/-!
# Pristine intrinsic terminology for the bipolar coordinate

This capstone records the exact mathematical replacements for several names
that were superimposed in the informal synthesis.

* `q(s)=s/(1-s)` is a Möbius equivalence between punctured affine charts. It
  is not declared to be the universal covering of the thrice-punctured sphere.
* `log x - log(1-x)` is the odd logit coordinate, whereas
  `-log x - log(1-x)` is the even two-sided logarithmic barrier.
* the half-weight construction defines a square-root cover with central deck
  sign. This is a spinorial descent mechanism, not a definition of physical
  angular momentum or a tangent-bundle spin structure.
* the informal Berezinian/coth formula becomes a theorem only after specifying
  the explicit `1|1` diagonal supermatrix `diag(1+q,1-q)`.
* the Schwarzian, contour, operator-connection, Poisson, and GENERIC owners
  remain independent layers. No twistor transform, hyper-para-Kaehler
  structure, modular-lambda uniformization, BdG model, or optimal-transport
  dynamics is inferred merely from sharing notation.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarIntrinsicTerminologyPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarMobiusPunctureEquiv
open InfoGeometry.Convex.BipolarLogitBarrierDuality
open InfoGeometry.Canonical.BipolarSquareRootSpinorialDescent
open InfoGeometry.NCG.BipolarCayleyBerezinianRealization

/-- The exact finite coordinate statement replacing the overstrong word
"uniformization" in the elementary bipolar layer. -/
theorem pristine_mobius_coordinate_core
    (s : SourcePoint) (z : TargetPoint) :
    inverseCrossRatio01 (crossRatio01 (s : ℂ)) = (s : ℂ) ∧
      crossRatio01 (inverseCrossRatio01 (z : ℂ)) = (z : ℂ) :=
  bipolar_mobius_puncture_equiv_packet s z

/-- The exact distinction between the odd logarithmic coordinate and the even
interval barrier. -/
theorem pristine_logit_barrier_core (t : ℝ) :
    logitCoordinate (1 / 2 : ℝ) = 0 ∧
      logitGradient (1 / 2 : ℝ) = 4 ∧
      intervalBarrierGradient (1 / 2 : ℝ) = 0 ∧
      intervalBarrierHessian (1 / 2 : ℝ) = 8 ∧
      logitCoordinate (logistic t) = t ∧
      intervalBarrier (logistic t) =
        2 * Real.log (1 + Real.exp t) - t :=
  bipolar_logit_barrier_duality_packet t

/-- The exact finite statement called monodromy-induced spinoriality: the
fundamental half-weight changes sign under the deck involution, but conjugated
matrix observables descend. -/
theorem pristine_spinorial_descent_core
    (p : SquareRootPoint) (ψ : Spinor2) (X : Matrix2C) :
    deck (deck p) = p ∧
      deck p ≠ p ∧
      Matrix.det (squareRootCartanLift p) = 1 ∧
      squareRootCartanLift (deck p) = -squareRootCartanLift p ∧
      fundamentalAction (deck p) ψ = -fundamentalAction p ψ ∧
      observableAction (deck p) X = observableAction p X :=
  bipolar_square_root_spinorial_descent_packet p ψ X

/-- The exact finite statement replacing the undefined slogan
`-coth(W/2)=Ber(D)`: the block `D` and its invertibility condition are explicit. -/
theorem pristine_berezinian_realization_core
    {s : ℂ} (hs : s ∈ punctured01)
    (hcrit : 1 - 2 * s ≠ 0) :
    negCothHalfExp (bipolarLog s) =
        superCayleyBerezinian (crossRatio01 s) ∧
      superCayleyBerezinian (crossRatio01 s) =
        (1 - 2 * s)⁻¹ :=
  bipolar_cayley_berezinian_packet hs hcrit

/-- Combined intrinsic correction packet. -/
theorem bipolar_intrinsic_terminology_pristine_chain
    (s : SourcePoint) (z : TargetPoint) (t : ℝ)
    (p : SquareRootPoint) (ψ : Spinor2) (X : Matrix2C) :
    (inverseCrossRatio01 (crossRatio01 (s : ℂ)) = (s : ℂ) ∧
      crossRatio01 (inverseCrossRatio01 (z : ℂ)) = (z : ℂ)) ∧
    (logitCoordinate (1 / 2 : ℝ) = 0 ∧
      logitGradient (1 / 2 : ℝ) = 4 ∧
      intervalBarrierGradient (1 / 2 : ℝ) = 0 ∧
      intervalBarrierHessian (1 / 2 : ℝ) = 8 ∧
      logitCoordinate (logistic t) = t) ∧
    (deck (deck p) = p ∧
      deck p ≠ p ∧
      squareRootCartanLift (deck p) = -squareRootCartanLift p ∧
      fundamentalAction (deck p) ψ = -fundamentalAction p ψ ∧
      observableAction (deck p) X = observableAction p X) := by
  refine ⟨pristine_mobius_coordinate_core s z, ?_, ?_⟩
  · exact ⟨logitCoordinate_half, logitGradient_half,
      intervalBarrierGradient_half, intervalBarrierHessian_half,
      logitCoordinate_logistic t⟩
  · exact ⟨deck_involutive p, deck_ne_self p,
      squareRootCartanLift_deck p, fundamentalAction_deck p ψ,
      observableAction_deck p X⟩

end InfoGeometry.Canonical.BipolarIntrinsicTerminologyPristineChain

