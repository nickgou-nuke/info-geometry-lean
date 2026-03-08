import InfoGeometry.KK.Product
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Finite-dimensional base space for concrete KK test models. -/
abbrev FinModelE (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Doubled finite-dimensional carrier with canonical Krein and grading instances. -/
abbrev FinModelH (n : ℕ) : Type := HilbertDoubled (FinModelE n)

variable (n : ℕ)

/-- Trivial compactness predicate used for interface-level finite-dimensional tests. -/
instance instCompactLikeTrueFinModel :
    CompactLike (K := fun _ : EndH (FinModelH n) => True) where
  zero_mem := trivial
  add_mem := by
    intro A B hA hB
    trivial
  smul_mem := by
    intro r A hA
    trivial

/-- Concrete bounded Kasparov cycle test model on the doubled finite-dimensional carrier. -/
noncomputable def trivialKasparovCycle : KasparovCycle ℝ ℝ (FinModelH n) where
  π := Algebra.ofId ℝ (EndH (FinModelH n))
  ρ := Algebra.ofId ℝ (EndH (FinModelH n))
  F := 0
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    simp
  F_skewAdj := by
    simp [KreinSpace.IsKreinSkewAdjoint]
  K := fun _ => True
  compactLike := instCompactLikeTrueFinModel n
  F_sq_one_compact := trivial
  comm_compact := by
    intro a
    trivial

/-- End-to-end concrete product packaging for the trivial finite-dimensional test cycle. -/
noncomputable def trivialKasparovProductData :
    KasparovProductData
      ℝ ℝ ℝ
      (FinModelH n) (FinModelH n) (FinModelH n)
      (trivialKasparovCycle n) (trivialKasparovCycle n) where
  out := trivialKasparovCycle n

@[simp] lemma trivialKasparovProductData_out_F :
    (trivialKasparovProductData n).out.F = 0 := rfl

end InfoGeometry.KK
