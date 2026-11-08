import InfoGeometry.KK.Product
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.CompactOperatorBridge
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Finite-dimensional base space for concrete KK test models. -/
abbrev FinModelE (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Doubled finite-dimensional carrier with canonical Krein and grading instances. -/
abbrev FinModelH (n : ℕ) : Type := HilbertDoubled (FinModelE n)

variable (n : ℕ)

/-- Canonical split Cl(1,1) action on the doubled finite-dimensional carrier. -/
noncomputable def finModelCl11Action :
    InfoGeometry.Quantum.RealSplitCl11Action (FinModelH n) :=
  InfoGeometry.Quantum.RealSplitCl11Action.ofContinuousLinearEquiv
    (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := FinModelE n))
    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := FinModelE n))

/-- Concrete bounded Kasparov cycle test model on the doubled finite-dimensional carrier. -/
noncomputable def trivialKasparovCycle : KasparovCycle ℝ ℝ (FinModelH n) where
  cl11 := finModelCl11Action n
  π := Algebra.ofId ℝ (EndH (FinModelH n))
  ρ := Algebra.ofId ℝ (EndH (FinModelH n))
  π_even := by
    intro a
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := FinModelH n) (a • KreinGradedModule.gradeCLM (H := FinModelH n) x) = a • x
    rw [map_smul]
    congr 1
    exact (KreinGradedModule.grade_invol (H := FinModelH n) x)
  ρ_even := by
    intro b
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := FinModelH n) (b • KreinGradedModule.gradeCLM (H := FinModelH n) x) = b • x
    rw [map_smul]
    congr 1
    exact (KreinGradedModule.grade_invol (H := FinModelH n) x)
  F := 0
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    simp
  F_skewAdj := by
    simp [KreinSpace.IsKreinSkewAdjoint]
  F_sq_one_compact := by
    simpa using (isCompactEnd_of_finiteDimensional
      (H := FinModelH n) (A := (-(1 : EndH (FinModelH n)))))
  comm_compact := by
    intro a
    simpa using (isCompactEnd_zero (H := FinModelH n))
  superComm_eps_compact := by
    simp
    exact isCompactEnd_zero (H := FinModelH n)
  superComm_J_compact := by
    simp
    exact isCompactEnd_zero (H := FinModelH n)

/-- End-to-end concrete product packaging for the trivial finite-dimensional test cycle. -/
noncomputable def trivialKasparovProductData :
    KasparovProductData
      ℝ ℝ ℝ
      (FinModelH n) (FinModelH n) (FinModelH n)
      (trivialKasparovCycle n) (trivialKasparovCycle n) :=
  trivialKasparovCycle n

@[simp] lemma trivialKasparovProductData_F :
    (trivialKasparovProductData n).F = 0 := rfl

end InfoGeometry.KK
