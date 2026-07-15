import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperatorInner

/-!
# Kernel and faithfulness of the finite-support GNS representation

This continues the finite Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  The represented left action forgets exactly the
coordinates outside the active support, equivalently the finite null/zero-inner
subspace.  With full support the representation is faithful.
-/

noncomputable section

namespace GNSFiniteSupportOperatorKernel

open GNSFiniteSupport
open GNSFiniteSupportOperator
open GNSFiniteSupportOperatorInner

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Equality of represented bounded operators implies equality on the cyclic vector. -/
theorem liftOp_eq_implies_cyclic_eq (a b : Alg n)
    (h : liftOp p a = liftOp p b) :
    liftOp p a (omegaVec p) = liftOp p b (omegaVec p) := by
  rw [h]

/-- Equality of represented operators is equivalent to equality of restrictions. -/
theorem liftOp_eq_iff_restrict_eq (a b : Alg n) :
    liftOp p a = liftOp p b ↔ restrict p a = restrict p b := by
  constructor
  · intro h
    have hc := liftOp_eq_implies_cyclic_eq p a b h
    rwa [liftOp_omegaVec_eq_restrict, liftOp_omegaVec_eq_restrict] at hc
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    funext i
    have hi := congrFun h i
    simp [restrict] at hi
    change a i.1 * x i = b i.1 * x i
    rw [hi]

/-- The zero represented operator is equivalent to nullity on active support. -/
theorem liftOp_eq_zero_iff_null (a : Alg n) :
    liftOp p a = 0 ↔ nullSubspace p a := by
  constructor
  · intro h i
    have hc := congrFun (congrArg (fun T : GNS p →L[ℂ] GNS p => T (omegaVec p)) h) i
    simpa [liftOp_apply, omegaVec] using hc
  · intro hnull
    apply ContinuousLinearMap.ext
    intro x
    funext i
    simp [liftOp_apply, hnull i]

/-- With full support, the finite-support GNS representation is faithful. -/
theorem liftOp_faithful_of_full_support
    (hfull : ∀ i : Fin n, p i) (a b : Alg n)
    (h : liftOp p a = liftOp p b) :
    a = b := by
  have hres : restrict p a = restrict p b := (liftOp_eq_iff_restrict_eq p a b).1 h
  funext i
  have hi := congrFun hres ⟨i, hfull i⟩
  simpa [restrict] using hi

/-- With full support, only the zero element is represented by the zero operator. -/
theorem liftOp_zero_faithful_of_full_support
    (hfull : ∀ i : Fin n, p i) (a : Alg n)
    (h : liftOp p a = 0) :
    a = 0 := by
  have hzero : liftOp p a = liftOp p (0 : Alg n) := by
    apply ContinuousLinearMap.ext
    intro x
    funext i
    have hz := congrFun (congrArg (fun T : GNS p →L[ℂ] GNS p => T x) h) i
    simpa [liftOp_apply] using hz
  exact liftOp_faithful_of_full_support p hfull a 0 hzero

end GNSFiniteSupportOperatorKernel
