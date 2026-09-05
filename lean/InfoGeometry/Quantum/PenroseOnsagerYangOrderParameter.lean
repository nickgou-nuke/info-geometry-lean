import InfoGeometry.Quantum.PenroseOnsagerYangOccupationSpectrum
import Mathlib

/-!
# Finite condensate kernels and order-parameter normalization

For a finite complex mode `chi`, the intrinsic rank-one condensate kernel is

  `K(i,j) = chi(i) * conj (chi(j))`.

This file proves positivity, Hermiticity, the trace formula, invariance under a
global unit-modulus scalar, and the Penrose--Onsager--Yang normalization

  `Phi = sqrt(N0) chi`,  `||Phi||^2 = N0`

for a normalized mode. It also builds finite positive spectral kernels from
arbitrary nonnegative occupations. No spontaneous-symmetry-breaking
expectation value or microscopic pairing Hamiltonian is used.
-/

noncomputable section

namespace InfoGeometry.Quantum.PenroseOnsagerYang

open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Finite complex mode space. -/
abbrev Mode (ι : Type*) := ι → ℂ

/-- Squared norm of a finite complex mode. -/
def modeNormSq (ψ : Mode ι) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

/-- A normalized finite mode. -/
def IsNormalizedMode (ψ : Mode ι) : Prop :=
  modeNormSq ψ = 1

/-- Rank-one kernel associated with a finite complex mode. -/
def rankOneKernel (ψ : Mode ι) : Matrix ι ι ℂ :=
  fun i j => ψ i * Complex.conj (ψ j)

/-- Every mode kernel is positive semidefinite. -/
theorem rankOneKernel_posSemidef (ψ : Mode ι) :
    (rankOneKernel ψ).PosSemidef := by
  let C : Matrix ι Unit ℂ := fun i _ => ψ i
  have hC : C * Cᴴ = rankOneKernel ψ := by
    ext i j
    simp [C, rankOneKernel, Matrix.mul_apply]
  rw [← hC]
  exact Matrix.posSemidef_self_mul_conjTranspose C

/-- Every mode kernel is Hermitian. -/
theorem rankOneKernel_isHermitian (ψ : Mode ι) :
    (rankOneKernel ψ).IsHermitian :=
  (rankOneKernel_posSemidef ψ).isHermitian

/-- The trace of a rank-one kernel is the squared norm of its defining mode. -/
theorem trace_rankOneKernel_eq_modeNormSq (ψ : Mode ι) :
    Matrix.trace (rankOneKernel ψ) = (modeNormSq ψ : ℂ) := by
  classical
  simp [Matrix.trace, rankOneKernel, modeNormSq, Complex.mul_conj]

/-- Pointwise multiplication of a mode by one complex scalar. -/
def scalarAction (u : ℂ) (ψ : Mode ι) : Mode ι :=
  fun i => u * ψ i

/-- Scaling a mode scales its rank-one kernel by `u * conj u`. -/
theorem rankOneKernel_scalarAction (u : ℂ) (ψ : Mode ι) :
    rankOneKernel (scalarAction u ψ) =
      (u * Complex.conj u) • rankOneKernel ψ := by
  ext i j
  change
    (u * ψ i) * Complex.conj (u * ψ j) =
      (u * Complex.conj u) * (ψ i * Complex.conj (ψ j))
  simp only [map_mul]
  ring

/-- A global unit-modulus scalar is invisible to the condensate kernel. -/
theorem rankOneKernel_globalPhase_invariant
    {u : ℂ} (hu : u * Complex.conj u = 1)
    (ψ : Mode ι) :
    rankOneKernel (scalarAction u ψ) = rankOneKernel ψ := by
  rw [rankOneKernel_scalarAction, hu, one_smul]

/-- Squared norm under scalar multiplication. -/
theorem modeNormSq_scalarAction (u : ℂ) (ψ : Mode ι) :
    modeNormSq (scalarAction u ψ) =
      Complex.normSq u * modeNormSq ψ := by
  classical
  unfold modeNormSq scalarAction
  calc
    ∑ i, Complex.normSq (u * ψ i)
        = ∑ i, Complex.normSq u * Complex.normSq (ψ i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Complex.normSq_mul]
    _ = Complex.normSq u * ∑ i, Complex.normSq (ψ i) := by
          rw [Finset.mul_sum]

/-- Finite Penrose--Onsager--Yang order parameter `Phi = sqrt(N0) chi`. -/
def orderParameter (N0 : ℝ) (χ : Mode ι) : Mode ι :=
  scalarAction (Real.sqrt N0 : ℂ) χ

/-- The order-parameter mass equals the condensate occupation for a normalized
mode and a nonnegative occupation number. -/
theorem modeNormSq_orderParameter
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ) :
    modeNormSq (orderParameter N0 χ) = N0 := by
  unfold orderParameter
  rw [modeNormSq_scalarAction]
  change modeNormSq χ = 1 at hχ
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt hN0, hχ, mul_one]

/-- The condensate kernel of `sqrt(N0) chi` is `N0 |chi><chi|`. -/
theorem rankOneKernel_orderParameter
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    (χ : Mode ι) :
    rankOneKernel (orderParameter N0 χ) =
      (N0 : ℂ) • rankOneKernel χ := by
  unfold orderParameter
  rw [rankOneKernel_scalarAction]
  have hscalar :
      (Real.sqrt N0 : ℂ) * Complex.conj (Real.sqrt N0 : ℂ) =
        (N0 : ℂ) := by
    calc
      (Real.sqrt N0 : ℂ) * Complex.conj (Real.sqrt N0 : ℂ)
          = ((Real.sqrt N0 * Real.sqrt N0 : ℝ) : ℂ) := by simp
      _ = (N0 : ℂ) := by rw [Real.mul_self_sqrt hN0]
  rw [hscalar]

/-- Trace form of the order-parameter normalization. -/
theorem trace_orderParameterKernel
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ) :
    Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) := by
  rw [trace_rankOneKernel_eq_modeNormSq,
    modeNormSq_orderParameter hN0 hχ]

/-! ## Finite spectral kernels -/

/-- Finite positive kernel assembled from nonnegative occupation numbers and
normalized or unnormalized modes. -/
def spectralKernel
    (occupation : κ → ℝ) (mode : κ → Mode ι) : Matrix ι ι ℂ :=
  ∑ k, rankOneKernel (orderParameter (occupation k) (mode k))

/-- A finite spectral kernel is positive semidefinite, independently of mode
orthogonality. -/
theorem spectralKernel_posSemidef
    (occupation : κ → ℝ) (mode : κ → Mode ι) :
    (spectralKernel occupation mode).PosSemidef := by
  classical
  unfold spectralKernel
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty =>
      simpa using
        (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Matrix.PosSemidef.add (rankOneKernel_posSemidef _) ih

/-- For nonnegative occupations and normalized modes, the trace of the
spectral kernel is the total occupation. -/
theorem trace_spectralKernel
    (occupation : κ → ℝ)
    (hoccupation : ∀ k, 0 ≤ occupation k)
    (mode : κ → Mode ι)
    (hmode : ∀ k, IsNormalizedMode (mode k)) :
    Matrix.trace (spectralKernel occupation mode) =
      ∑ k, (occupation k : ℂ) := by
  classical
  unfold spectralKernel
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [trace_orderParameterKernel (hoccupation k) (hmode k)]

/-- Compact finite condensate-kernel packet. -/
theorem condensate_kernel_packet
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ)
    {u : ℂ} (hu : u * Complex.conj u = 1) :
    (rankOneKernel χ).PosSemidef ∧
      (rankOneKernel χ).IsHermitian ∧
      modeNormSq (orderParameter N0 χ) = N0 ∧
      Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) ∧
      rankOneKernel (scalarAction u χ) = rankOneKernel χ := by
  exact ⟨rankOneKernel_posSemidef χ, rankOneKernel_isHermitian χ,
    modeNormSq_orderParameter hN0 hχ,
    trace_orderParameterKernel hN0 hχ,
    rankOneKernel_globalPhase_invariant hu χ⟩

end InfoGeometry.Quantum.PenroseOnsagerYang
