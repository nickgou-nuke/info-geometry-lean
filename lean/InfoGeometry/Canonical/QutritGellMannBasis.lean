import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.QutritGates

/-!
# The real Gell--Mann coordinates of a qutrit

The eight displayed Gell--Mann directions are linearly independent and expand
every traceless Hermitian qutrit matrix.  Hence they span the whole real
`tracelessHermitian` carrier, whose real dimension is eight.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Quantum.Qutrit

theorem gellMann_linearIndependent :
    LinearIndependent ℝ gellMann := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hM : ∑ k, g k • (gellMann k : QutritMatrix) = 0 :=
    congrArg Subtype.val hg
  have h01 := congrArg (fun M : QutritMatrix => M 0 1) hM
  have h10 := congrArg (fun M : QutritMatrix => M 1 0) hM
  have h02 := congrArg (fun M : QutritMatrix => M 0 2) hM
  have h20 := congrArg (fun M : QutritMatrix => M 2 0) hM
  have h12 := congrArg (fun M : QutritMatrix => M 1 2) hM
  have h21 := congrArg (fun M : QutritMatrix => M 2 1) hM
  have h00 := congrArg (fun M : QutritMatrix => M 0 0) hM
  have h11 := congrArg (fun M : QutritMatrix => M 1 1) hM
  have h22 := congrArg (fun M : QutritMatrix => M 2 2) hM
  have h22r := congrArg Complex.re h22
  simp [gellMann, symmetricGellMann, antisymmetricGellMann,
    symmetricUnit, antisymmetricUnit, diagonalGellMann3, diagonalGellMann8,
    diagonalUnit, matrixUnit, Fin.sum_univ_succ] at h01 h10 h02 h20 h12 h21 h00 h11 h22r
  have h01r := congrArg Complex.re h01
  have h01i := congrArg Complex.im h01
  have h02r := congrArg Complex.re h02
  have h02i := congrArg Complex.im h02
  have h12r := congrArg Complex.re h12
  have h12i := congrArg Complex.im h12
  have h00r := congrArg Complex.re h00
  have h11r := congrArg Complex.re h11
  norm_num at h01r h01i h02r h02i h12r h12i h00r h11r h22r
  fin_cases i
  · exact h01r
  · exact h01i
  · have hg2 : g 2 = 0 := by linarith [h22r, h00r]
    simpa using hg2
  · exact h02r
  · exact h02i
  · exact h12r
  · exact h12i
  · exact h22r

theorem gellMann_span_finrank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range gellMann)) = 8 :=
  finrank_span_eq_card gellMann_linearIndependent

noncomputable def gellMannTracelessCoefficient
    (H : tracelessHermitian) : Fin 8 → ℝ := ![
  ((H : QutritMatrix) 0 1).re,
  -((H : QutritMatrix) 0 1).im,
  (((H : QutritMatrix) 0 0).re - ((H : QutritMatrix) 1 1).re) / 2,
  ((H : QutritMatrix) 0 2).re,
  -((H : QutritMatrix) 0 2).im,
  ((H : QutritMatrix) 1 2).re,
  -((H : QutritMatrix) 1 2).im,
  (((H : QutritMatrix) 0 0).re + ((H : QutritMatrix) 1 1).re) *
    Real.sqrt 3 / 2
]

set_option maxHeartbeats 5000000 in
theorem gellMann_traceless_expansion (H : tracelessHermitian) :
    ∑ k : Fin 8, gellMannTracelessCoefficient H k • gellMann k = H := by
  apply Subtype.ext
  ext i j
  have hherm : (H : QutritMatrix)ᴴ = H := H.property.1
  have htr : Matrix.trace (H : QutritMatrix) = 0 := H.property.2
  have hherm' : Matrix.IsHermitian (H : QutritMatrix) := hherm
  have h01 := hherm'.apply 0 1
  have h02 := hherm'.apply 0 2
  have h12 := hherm'.apply 1 2
  have h01r := congrArg Complex.re h01
  have h01i := congrArg Complex.im h01
  have h02r := congrArg Complex.re h02
  have h02i := congrArg Complex.im h02
  have h12r := congrArg Complex.re h12
  have h12i := congrArg Complex.im h12
  have h01r' : ((H : QutritMatrix) 1 0).re = ((H : QutritMatrix) 0 1).re := by
    simpa [Complex.star_def] using h01r
  have h01i' : -((H : QutritMatrix) 1 0).im = ((H : QutritMatrix) 0 1).im := by
    simpa [Complex.star_def] using h01i
  have h02r' : ((H : QutritMatrix) 2 0).re = ((H : QutritMatrix) 0 2).re := by
    simpa [Complex.star_def] using h02r
  have h02i' : -((H : QutritMatrix) 2 0).im = ((H : QutritMatrix) 0 2).im := by
    simpa [Complex.star_def] using h02i
  have h12r' : ((H : QutritMatrix) 2 1).re = ((H : QutritMatrix) 1 2).re := by
    simpa [Complex.star_def] using h12r
  have h12i' : -((H : QutritMatrix) 2 1).im = ((H : QutritMatrix) 1 2).im := by
    simpa [Complex.star_def] using h12i
  have htrace := congrArg Complex.re htr
  have h00i := congrArg Complex.im (hherm'.apply 0 0)
  have h11i := congrArg Complex.im (hherm'.apply 1 1)
  have h22i := congrArg Complex.im (hherm'.apply 2 2)
  have h00eq : -((H : QutritMatrix) 0 0).im = ((H : QutritMatrix) 0 0).im := by
    simpa [Complex.star_def] using h00i
  have h11eq : -((H : QutritMatrix) 1 1).im = ((H : QutritMatrix) 1 1).im := by
    simpa [Complex.star_def] using h11i
  have h22eq : -((H : QutritMatrix) 2 2).im = ((H : QutritMatrix) 2 2).im := by
    simpa [Complex.star_def] using h22i
  have h00im : ((H : QutritMatrix) 0 0).im = 0 := by
    linarith [h00eq]
  have h11im : ((H : QutritMatrix) 1 1).im = 0 := by
    linarith [h11eq]
  have h22im : ((H : QutritMatrix) 2 2).im = 0 := by
    linarith [h22eq]
  have htrace' : ((H : QutritMatrix) 0 0).re +
      ((H : QutritMatrix) 1 1).re + ((H : QutritMatrix) 2 2).re = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three] using htrace
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  fin_cases i <;> fin_cases j
  all_goals
    apply Complex.ext <;>
      simp [gellMannTracelessCoefficient, gellMann, symmetricGellMann,
        antisymmetricGellMann, symmetricUnit, antisymmetricUnit,
        diagonalGellMann3, diagonalGellMann8, diagonalUnit, matrixUnit,
        Fin.sum_univ_succ, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.trace, Fin.sum_univ_three]
  all_goals try field_simp [hsqrt]
  all_goals try rw [hsqrt_sq]
  all_goals
    nlinarith [hsqrt_sq, htrace', h00im, h11im, h22im,
      h01r', h01i', h02r', h02i', h12r', h12i']

theorem gellMann_span_eq_top :
    Submodule.span ℝ (Set.range gellMann) = ⊤ := by
  apply top_unique
  rintro H hH
  rw [← gellMann_traceless_expansion H]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨k, rfl⟩

theorem tracelessHermitian_finrank :
    Module.finrank ℝ tracelessHermitian = 8 := by
  have h := gellMann_span_finrank
  rw [gellMann_span_eq_top] at h
  simpa using h

end InfoGeometry.Quantum.Qutrit
end noncomputable section
