import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Canonical.ActualEntireCenteredXiBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
import InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
import InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge

/-!
# Zero-locus symmetries of the actual entire completed xi representative

This owner transports the already-proved reflection and Schwarz identities to
the predicate that the actual entire representative vanishes.  It does not
introduce zero multiplicities, an enumeration of zeros, or any RH statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiZeroLocusSymmetryBridge

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Canonical.ActualEntireCenteredXiBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge

def entireRiemannXiZeroLocus : Set ℂ :=
  {s | entireRiemannXi s = 0}

@[simp] theorem mem_entireRiemannXiZeroLocus (s : ℂ) :
    s ∈ entireRiemannXiZeroLocus ↔ entireRiemannXi s = 0 := Iff.rfl

theorem entireRiemannXiZeroLocus_subset_closed_critical_strip :
    entireRiemannXiZeroLocus ⊆
      {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1} := by
  intro s hs
  exact entireRiemannXi_zero_mem_closed_critical_strip hs

theorem mem_entireRiemannXiZeroLocus_iff_riemannXi_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s ∈ entireRiemannXiZeroLocus ↔
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s = 0 := by
  rw [mem_entireRiemannXiZeroLocus,
    entireRiemannXi_eq_riemannXi hs0 hs1]

theorem isClosed_entireRiemannXiZeroLocus :
    IsClosed entireRiemannXiZeroLocus := by
  change IsClosed (entireRiemannXi ⁻¹' ({0} : Set ℂ))
  exact isClosed_singleton.preimage differentiable_entireRiemannXi.continuous

theorem entireRiemannXi_zero_one_sub_iff (s : ℂ) :
    entireRiemannXi (1 - s) = 0 ↔ entireRiemannXi s = 0 := by
  rw [entireRiemannXi_one_sub]

theorem entireRiemannXi_zero_conj_iff (s : ℂ) :
    entireRiemannXi (star s) = 0 ↔ entireRiemannXi s = 0 := by
  rw [← entireRiemannXi_conj]
  simp

theorem entireRiemannXi_zero_antiunitary_iff (s : ℂ) :
    entireRiemannXi (1 - star s) = 0 ↔ entireRiemannXi s = 0 := by
  rw [entireRiemannXi_one_sub, ← entireRiemannXi_conj]
  simp

theorem actualEntireCenteredXi_zero_neg_iff (z : ℂ) :
    actualEntireCenteredXi (-z) = 0 ↔
      actualEntireCenteredXi z = 0 := by
  rw [actualEntireCenteredXi_even]

theorem actualEntireCenteredXi_zero_conj_iff (z : ℂ) :
    actualEntireCenteredXi (star z) = 0 ↔
      actualEntireCenteredXi z = 0 := by
  change entireRiemannXi ((1 / 2 : ℂ) + star z) = 0 ↔
    entireRiemannXi ((1 / 2 : ℂ) + z) = 0
  have harg :
      star ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + star z := by
    simp
  rw [← harg, ← entireRiemannXi_conj]
  simp

def actualEntireCenteredXiZeroLocus : Set ℂ :=
  {z | actualEntireCenteredXi z = 0}

@[simp] theorem mem_actualEntireCenteredXiZeroLocus (z : ℂ) :
    z ∈ actualEntireCenteredXiZeroLocus ↔
      actualEntireCenteredXi z = 0 := Iff.rfl

theorem actualEntireCenteredXiZeroLocus_subset_closed_centered_strip :
    actualEntireCenteredXiZeroLocus ⊆
      {z : ℂ | -(1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 1 / 2} := by
  intro z hz
  change entireRiemannXi ((1 / 2 : ℂ) + z) = 0 at hz
  have hstrip := entireRiemannXi_zero_mem_closed_critical_strip hz
  norm_num [Complex.add_re] at hstrip
  constructor <;> dsimp at hstrip ⊢ <;> linarith [hstrip.1, hstrip.2]

theorem isClosed_actualEntireCenteredXiZeroLocus :
    IsClosed actualEntireCenteredXiZeroLocus := by
  change IsClosed (actualEntireCenteredXi ⁻¹' ({0} : Set ℂ))
  have hcont : Continuous actualEntireCenteredXi := by
    unfold actualEntireCenteredXi
    exact differentiable_entireRiemannXi.continuous.comp
      (continuous_const.add continuous_id)
  exact isClosed_singleton.preimage hcont

theorem actualEntireCenteredXiZeroLocus_neg_iff (z : ℂ) :
    -z ∈ actualEntireCenteredXiZeroLocus ↔
      z ∈ actualEntireCenteredXiZeroLocus := by
  change actualEntireCenteredXi (-z) = 0 ↔
    actualEntireCenteredXi z = 0
  exact actualEntireCenteredXi_zero_neg_iff z

theorem actualEntireCenteredXiZeroLocus_conj_iff (z : ℂ) :
    star z ∈ actualEntireCenteredXiZeroLocus ↔
      z ∈ actualEntireCenteredXiZeroLocus := by
  change actualEntireCenteredXi (star z) = 0 ↔
    actualEntireCenteredXi z = 0
  exact actualEntireCenteredXi_zero_conj_iff z

def actualEntireRiemannXiCriticalZeroLocus : Set ℝ :=
  {t | entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0}

@[simp] theorem mem_actualEntireRiemannXiCriticalZeroLocus (t : ℝ) :
    t ∈ actualEntireRiemannXiCriticalZeroLocus ↔
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 := Iff.rfl

theorem isClosed_actualEntireRiemannXiCriticalZeroLocus :
    IsClosed actualEntireRiemannXiCriticalZeroLocus := by
  change IsClosed ((fun t : ℝ =>
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) ⁻¹' ({0} : Set ℂ))
  have hline : Continuous (fun t : ℝ =>
      (1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  exact isClosed_singleton.preimage
    (differentiable_entireRiemannXi.continuous.comp hline)

theorem actualEntireRiemannXiCriticalZeroLocus_neg_iff (t : ℝ) :
    -t ∈ actualEntireRiemannXiCriticalZeroLocus ↔
      t ∈ actualEntireRiemannXiCriticalZeroLocus := by
  change entireRiemannXi ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) = 0 ↔
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0
  have harg :
      (1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        1 - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    norm_num
    ring
  rw [harg]
  exact entireRiemannXi_zero_one_sub_iff _

theorem actualEntireRiemannXiCriticalZeroLocus_iff_realReadout_zero (t : ℝ) :
    t ∈ actualEntireRiemannXiCriticalZeroLocus ↔
      criticalLineRealReadout entireRiemannXi t = 0 := by
  change entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 ↔ _
  exact (criticalLineRealReadout_zero_iff_xi_zero entireRiemannXi
    actualEntireRiemannXiFunctionDatum t).symm

end InfoGeometry.Canonical.ActualEntireRiemannXiZeroLocusSymmetryBridge
