import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.SplitOctonions.ZornLogVolume
import InfoGeometry.RegularizedKL

namespace InfoGeometry.Probability

abbrev ThermodynamicBase :=
  InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.ThermodynamicBase

structure ZornStatisticalVariety where
  carrier : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct
  det_pos : 0 < InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ carrier

abbrev base (M : ZornStatisticalVariety) : ThermodynamicBase :=
  InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.projectToBase M.carrier

noncomputable def zornLogBarrier (M : ZornStatisticalVariety) : ℝ :=
  - Real.log (base M).det

abbrev ProbabilityMeasureVariety (α : Type*) := PositiveMeasure α ℝ

@[simp] theorem base_det_eq (M : ZornStatisticalVariety) :
    (base M).det = InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ M.carrier :=
  rfl

@[simp] theorem zornLogBarrier_eq (M : ZornStatisticalVariety) :
    zornLogBarrier M = - Real.log (base M).det :=
  rfl

@[simp] theorem regularizedPMF_strictly_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
    0 < InfoGeometry.RegularizedKL.regularizedPMF count ε hε x := by
  simpa using
    (InfoGeometry.RegularizedKL.regularizedPMF_strictly_pos count ε hε x)

@[simp] theorem regularizedGeneralizedKL_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ InfoGeometry.RegularizedKL.regularizedGeneralizedKL countP countQ ε hε := by
  simpa using
    (InfoGeometry.RegularizedKL.regularizedGeneralizedKL_nonneg countP countQ ε hε)

@[simp] theorem sum_regularizedPMF_eq_one
    {α : Type*} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∑ x : α, InfoGeometry.RegularizedKL.regularizedPMF count ε hε x = 1 := by
  simpa using
    (InfoGeometry.RegularizedKL.sum_regularizedPMF_eq_one count ε hε)

@[simp] theorem regularized_kl_is_safe
    {α : Type*} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
    0 < (InfoGeometry.RegularizedKL.regularizedPMF countP ε hε x) /
        (InfoGeometry.RegularizedKL.regularizedPMF countQ ε hε x) := by
  simpa using
    (InfoGeometry.RegularizedKL.regularized_kl_is_safe countP countQ ε hε x)

end InfoGeometry.Probability
