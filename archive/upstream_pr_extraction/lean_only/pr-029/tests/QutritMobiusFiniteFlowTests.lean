import InfoGeometry.Quantum.QutritMobiusFiniteFlowClassification

open InfoGeometry.Quantum.QutritMobiusFiniteFlowClassification

#check ellipticMatrixFlow_closedForm
#check parabolicMatrixFlow_closedForm
#check hyperbolicMatrixFlow_closedForm
#check ellipticFinite_isElliptic
#check parabolicFinite_isParabolic
#check hyperbolicFinite_isHyperbolic
#check traceSq_eq_of_matrixConjugate

example (t : ℝ) (z : ℂ) :
    (parabolicTransform t).eval (some z) = some (z + (t : ℂ)) :=
  parabolicTransform_eval_some t z

example (t : ℝ) (z : ℂ) :
    (hyperbolicTransform t).eval (some z) = some ((Real.exp (2 * t) : ℂ) * z) :=
  hyperbolicTransform_eval_some t z

example {s t : ℝ} (hs : Real.sin s ≠ 0) (ht : t ≠ 0) :
    ¬ MatrixConjugate (ellipticFinite s) (hyperbolicFinite t) :=
  ellipticFinite_not_conjugate_hyperbolicFinite hs ht
