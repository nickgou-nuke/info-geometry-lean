import InfoGeometry.Canonical.ActualEntireCenteredXiBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge

/-!
# The actual zero-free loci for the completed xi readouts

This owner supplies the open domains on which the existing logarithmic
derivative readouts can later be treated as differential forms.  It proves
only openness and reflection invariance of the actual loci; no de Rham class,
closedness, contour period, or global zero-divisor theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireCenteredXiBridge

def entireRiemannXiZeroFreeLocus : Set ℂ :=
  {s | entireRiemannXi s ≠ 0}

@[simp] theorem mem_entireRiemannXiZeroFreeLocus (s : ℂ) :
    s ∈ entireRiemannXiZeroFreeLocus ↔ entireRiemannXi s ≠ 0 := Iff.rfl

theorem entireRiemannXi_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    entireRiemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  rw [entireRiemannXi_eq_riemannXi hs0 hs1]
  exact InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi_ne_zero_of_one_lt_re hs

theorem entireRiemannXi_ne_zero_of_re_lt_zero
    {s : ℂ} (hs : s.re < 0) :
    entireRiemannXi s ≠ 0 := by
  have hs_ref : 1 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  intro hzero
  have hzero_ref : entireRiemannXi (1 - s) = 0 := by
    rw [entireRiemannXi_one_sub]
    exact hzero
  exact entireRiemannXi_ne_zero_of_one_lt_re hs_ref hzero_ref

theorem entireRiemannXi_zero_mem_closed_critical_strip
    {s : ℂ} (hs : entireRiemannXi s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    exact entireRiemannXi_ne_zero_of_re_lt_zero (lt_of_not_ge h) hs
  · by_contra h
    exact entireRiemannXi_ne_zero_of_one_lt_re (lt_of_not_ge h) hs

theorem isOpen_entireRiemannXiZeroFreeLocus :
    IsOpen entireRiemannXiZeroFreeLocus := by
  change IsOpen (entireRiemannXi ⁻¹' ({0}ᶜ))
  exact isOpen_compl_singleton.preimage
    differentiable_entireRiemannXi.continuous

theorem entireRiemannXiZeroFree_reflection
    {s : ℂ} (hs : s ∈ entireRiemannXiZeroFreeLocus) :
    1 - s ∈ entireRiemannXiZeroFreeLocus := by
  intro hzero
  apply hs
  rw [← entireRiemannXi_one_sub s, hzero]

theorem entireRiemannXiZeroFree_reflection_iff (s : ℂ) :
    1 - s ∈ entireRiemannXiZeroFreeLocus ↔
      s ∈ entireRiemannXiZeroFreeLocus := by
  constructor
  · intro hs
    have h := entireRiemannXiZeroFree_reflection
      (s := 1 - s) hs
    simpa using h
  · exact entireRiemannXiZeroFree_reflection

theorem entireRiemannXiZeroFree_conjugation_iff (s : ℂ) :
    star s ∈ entireRiemannXiZeroFreeLocus ↔
      s ∈ entireRiemannXiZeroFreeLocus := by
  change entireRiemannXi (star s) ≠ 0 ↔ entireRiemannXi s ≠ 0
  rw [← entireRiemannXi_conj s]
  simp

theorem entireRiemannXiZeroFree_criticalLine_even (t : ℝ) :
    ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ∈
        entireRiemannXiZeroFreeLocus ↔
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ∈
        entireRiemannXiZeroFreeLocus := by
  change
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ≠ 0 ↔
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0
  rw [entireRiemannXi_criticalLine_even]

def actualEntireCenteredXiZeroFreeLocus : Set ℂ :=
  {z | actualEntireCenteredXi z ≠ 0}

@[simp] theorem mem_actualEntireCenteredXiZeroFreeLocus (z : ℂ) :
    z ∈ actualEntireCenteredXiZeroFreeLocus ↔
      actualEntireCenteredXi z ≠ 0 := Iff.rfl

theorem isOpen_actualEntireCenteredXiZeroFreeLocus :
    IsOpen actualEntireCenteredXiZeroFreeLocus := by
  change IsOpen (actualEntireCenteredXi ⁻¹' ({0}ᶜ))
  have hcont : Continuous actualEntireCenteredXi := by
    unfold actualEntireCenteredXi
    exact differentiable_entireRiemannXi.continuous.comp
      (continuous_const.add continuous_id)
  exact isOpen_compl_singleton.preimage
    hcont

theorem actualEntireCenteredXiZeroFree_neg_iff (z : ℂ) :
    -z ∈ actualEntireCenteredXiZeroFreeLocus ↔
      z ∈ actualEntireCenteredXiZeroFreeLocus := by
  change actualEntireCenteredXi (-z) ≠ 0 ↔
    actualEntireCenteredXi z ≠ 0
  rw [actualEntireCenteredXi_even z]

end InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
