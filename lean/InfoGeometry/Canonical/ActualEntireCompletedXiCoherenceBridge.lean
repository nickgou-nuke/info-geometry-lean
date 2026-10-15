import InfoGeometry.Canonical.ActualCompletedXiDatumBridge
import InfoGeometry.Canonical.ActualCenteredXiDataBridge
import InfoGeometry.Canonical.ActualEntireCenteredXiBridge
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge

/-!
# Coherence of the two actual completed-Xi readouts

`riemannXi` is the regular meromorphic readout, while `entireRiemannXi` is
the pole-removed entire representative.  Mathlib identifies them away from
the exceptional points `0` and `1`; this owner records that identification in
the centered and uncentered actual datum surfaces.  No global definitional
equality, zero-factorization, or RH statement is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireCompletedXiCoherenceBridge

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.ActualCenteredXiDataBridge
open InfoGeometry.Canonical.ActualEntireCenteredXiBridge
open InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge

def actualEntireCompletedXiDatum :
    CompletedXiDatum entireRiemannXi where
  func_eq := entireRiemannXi_one_sub
  schwarz := fun s => (entireRiemannXi_conj s).symm

theorem actualEntireCompletedXiDatum_norm_v4 (s : ℂ) :
    (Complex.normSq (entireRiemannXi (1 - s)) =
        Complex.normSq (entireRiemannXi s)) ∧
    (Complex.normSq (entireRiemannXi (star s)) =
        Complex.normSq (entireRiemannXi s)) ∧
    (Complex.normSq (entireRiemannXi (1 - star s)) =
        Complex.normSq (entireRiemannXi s)) := by
  exact xi_norm_v4_invariance entireRiemannXi actualEntireCompletedXiDatum s

def actualCenteredXiRegularLocus : Set ℂ :=
  {z | ((1 / 2 : ℂ) + z ≠ 0) ∧ ((1 / 2 : ℂ) + z ≠ 1)}

@[simp] theorem mem_actualCenteredXiRegularLocus (z : ℂ) :
    z ∈ actualCenteredXiRegularLocus ↔
      ((1 / 2 : ℂ) + z ≠ 0) ∧ ((1 / 2 : ℂ) + z ≠ 1) :=
  Iff.rfl

theorem actualEntireCenteredXiData_lambda_eq_actualCompletedXiDatum
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    actualEntireCenteredXiData.lambda s = riemannXi s := by
  rw [actualEntireCenteredXiData_lambda]
  exact entireRiemannXi_eq_riemannXi hs0 hs1

theorem actualEntireCenteredXiData_xi_eq_actualCenteredXiData
    {z : ℂ} (hz : z ∈ actualCenteredXiRegularLocus) :
    actualEntireCenteredXiData.xi z = actualCenteredXiData.xi z := by
  rw [actualEntireCenteredXiData_xi, actualCenteredXiData_xi,
    actualEntireCenteredXi_apply]
  exact entireRiemannXi_eq_riemannXi hz.1 hz.2

theorem actualEntireCenteredXiData_xi_eq_actualCenteredXiData_iff
    {z : ℂ} (hz : z ∈ actualCenteredXiRegularLocus) :
    actualEntireCenteredXiData.xi z = actualCenteredXiData.xi z ∧
      actualCenteredXiData.xi z = actualEntireCenteredXiData.xi z := by
  exact ⟨actualEntireCenteredXiData_xi_eq_actualCenteredXiData hz,
    (actualEntireCenteredXiData_xi_eq_actualCenteredXiData hz).symm⟩

end InfoGeometry.Canonical.ActualEntireCompletedXiCoherenceBridge
