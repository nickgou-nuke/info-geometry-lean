import Mathlib.Tactic
import InfoGeometry.External.Auto.KanCayley

noncomputable section

open Matrix Complex
open InfoGeometry.Canonical.Cayley

namespace InfoGeometry.GrandUnification.TraceSeparation

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Traceful (scalar) sector in Pauli decomposition:
`g ↦ (tr g / 2) · I`. -/
def traceSector (g : M2C) : M2C :=
  (g.trace / 2) • (1 : M2C)

/-- Traceless sector: `g - (tr g / 2)I`. -/
def tracelessSector (g : M2C) : M2C :=
  g - traceSector g

/-- `tr((tr g / 2)·I) = tr g` for `2×2` matrices. -/
theorem traceSector_trace (g : M2C) :
    Matrix.trace (traceSector g) = g.trace := by
  simp [traceSector, Matrix.trace_smul]

/-- `tr(g - (tr g / 2)I) = 0` on `2×2`. -/
theorem tracelessSector_trace (g : M2C) :
    Matrix.trace (tracelessSector g) = 0 := by
  simp [tracelessSector, traceSector]

/-- Exact split into traceful + traceless components. -/
theorem trace_decomposition (g : M2C) :
    g = traceSector g + tracelessSector g := by
  simp [tracelessSector]

/-- Traceless projector is idempotent. -/
theorem tracelessSector_idem (g : M2C) :
    tracelessSector (tracelessSector g) = tracelessSector g := by
  simp [tracelessSector, traceSector]

/-- Concrete decomposition package on a single matrix. -/
structure SL2Decomposition (g : M2C) where
  tracePart : M2C
  tracelessPart : M2C
  hTraceless : Matrix.trace tracelessPart = 0
  hSplit : g = tracePart + tracelessPart

/-- Canonical decomposition for any `g`. -/
noncomputable def sl2_canonical_decomposition (g : M2C) :
    SL2Decomposition g := by
  refine ⟨traceSector g, tracelessSector g, tracelessSector_trace g, ?_⟩
  simp [traceSector, tracelessSector]

/-- `log(trace-free)` bridge helper used in the Flow Matching step. -/
lemma trace_zero_of_exp_one_of_im_zero {z : ℂ} (hz : Complex.exp z = 1)
    (hzI : z.im = 0) : z = 0 := by
  rcases Complex.exp_eq_one_iff.mp hz with ⟨n, hz⟩
  have him0 : (n : ℝ) * (2 * Real.pi) = 0 := by
    have him := congrArg Complex.im hz
    simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hzI, mul_assoc, mul_comm, mul_left_comm] using him
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have hnR : (n : ℝ) = 0 := (mul_eq_zero.mp him0).resolve_right hpi
  have hn : (n : ℤ) = 0 := by exact_mod_cast hnR
  calc
    z = (n : ℂ) * (2 * Real.pi * Complex.I) := hz
    _ = 0 := by simp [hn]

/-- Abstract log-bridge for the matrix Lie-type step. -/
class LogTraceModel where
  log : M2C → M2C
  det_eq_exp_trace : ∀ g : M2C, g.det = Complex.exp (Matrix.trace (log g))
  trace_im_zero : ∀ g : M2C, (Matrix.trace (log g)).im = 0

/-- Self-closed logarithmic map on `det=1` sector: trace vanishes. -/
theorem log_map_selfclosed (g : M2C) [h1 : Fact (g.det = 1)] (L : LogTraceModel) :
    Matrix.trace (L.log g) = 0 := by
  have hz1 : Complex.exp (Matrix.trace (L.log g)) = 1 := by
    simpa [h1.out] using (L.det_eq_exp_trace g).symm

  exact trace_zero_of_exp_one_of_im_zero hz1 (L.trace_im_zero g)

/-- As a corollary, the abstract logarithm lands in traceless sector for `SL(2,ℂ)`. -/
theorem log_map_lands_in_traceless (g : M2C) [Fact (g.det = 1)] (L : LogTraceModel) :
    tracelessSector (L.log g) = L.log g := by
  have ht : Matrix.trace (L.log g) = 0 := log_map_selfclosed (g := g) (L := L)
  simp [tracelessSector, traceSector, ht]

/-- The K·A·N product has explicit `traceless` and `traceful` trace components. -/
theorem kan_trace_split (θ : ℝ) (β : ℝ) (z : ℂ) :
    let g : M2C := KPart θ * APart β * NPart z
    Matrix.trace (tracelessSector g) = 0 ∧
      Matrix.trace (traceSector g) = g.trace := by
  intro g
  exact ⟨tracelessSector_trace g, traceSector_trace g⟩

end InfoGeometry.GrandUnification.TraceSeparation
