/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Analysis.CliffordWaveletTransform
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Riemannian.CartanMetric

/-!
# Algebraic core for the `Cl(3,1)` Clifford-wavelet transform

This owner grounds the algebraic part of Ansari--Lakshmi Gorty,
"Analysis of Clifford-wavelet transform in `Cl(3,1)`",
DOI `10.56827/SEAJMMS.2024.2002.22`, in the repository's existing
`Cl(3,1)` grade-projection and Clifford-wavelet owners.

Scope: only finite algebraic/invertibility consequences are proved here.
The paper's integral Fourier formula, Plancherel identity, admissibility
constant, weak inversion, reproducing kernel, examples, and Dirac/Klein--Gordon
applications remain explicit open analytic debts; they are not asserted.
-/

noncomputable section

namespace InfoGeometry.Analysis.Cl31WaveletAlgebraicCore

open InfoGeometry.Analysis.CliffordWaveletTransform
open InfoGeometry.Clifford.GradedGraceContraction

/-- Paper (2.4): the five-grade decomposition of a `Cl(3,1)` multivector. -/
theorem cl31_grade_decomposition (x : Cl31) :
    (∑ k ∈ Finset.range 5, cliffordGradeProj Q31 k x) = x := by
  simpa using (cliffordGradeProj_sum_range_apply (Q := Q31) x)

/-- Paper (2.4) scalar channel: grade zero is the Clifford scalar trace. -/
theorem cl31_scalar_projection_eq_algebraMap_hTrace (x : Cl31) :
    cliffordGradeProj Q31 0 x =
      algebraMap ℝ Cl31 (InfoGeometry.Riemannian.hTrace_cl Q31 x) := by
  exact cliffordGradeProj_zero_eq_algebraMap_hTrace Q31 x

/-- Paper (2.4) vector channel: grade one contains the embedded vectors. -/
theorem cl31_vector_projection_ι (v : Fin 4 → ℝ) :
    cliffordGradeProj Q31 1 (CliffordAlgebra.ι Q31 v) =
      CliffordAlgebra.ι Q31 v := by
  exact cliffordGradeProj_one_ι Q31 v

/-- A two-sided reconstruction makes the analysis map injective. -/
theorem waveletTransform_injective_of_admissible
    (W : CliffordWaveletModel) (hAdm : W.admissible) :
    Function.Injective W.waveletTransform :=
  hAdm.injective

/-- A two-sided reconstruction is surjective when analysis is a left inverse. -/
theorem reconstruction_surjective_of_admissible
    (W : CliffordWaveletModel) (hAdm : W.admissible) :
    Function.Surjective W.reconstruction :=
  hAdm.surjective

/-- A reproducing kernel makes reconstruction injective. -/
theorem reconstruction_injective_of_reproducing
    (W : CliffordWaveletModel) (hRep : W.reproducingKernel) :
    Function.Injective W.reconstruction :=
  hRep.injective

/-- A reproducing kernel makes the analysis map surjective. -/
theorem waveletTransform_surjective_of_reproducing
    (W : CliffordWaveletModel) (hRep : W.reproducingKernel) :
    Function.Surjective W.waveletTransform :=
  hRep.surjective

/-- The paper's inversion formula needs both reconstruction laws at the
abstract model level: analysis is bijective once reconstruction is its
two-sided inverse. -/
theorem waveletTransform_bijective_of_admissible_reproducing
    (W : CliffordWaveletModel) (hAdm : W.admissible)
    (hRep : W.reproducingKernel) :
    Function.Bijective W.waveletTransform :=
  ⟨waveletTransform_injective_of_admissible W hAdm,
    waveletTransform_surjective_of_reproducing W hRep⟩

end InfoGeometry.Analysis.Cl31WaveletAlgebraicCore
