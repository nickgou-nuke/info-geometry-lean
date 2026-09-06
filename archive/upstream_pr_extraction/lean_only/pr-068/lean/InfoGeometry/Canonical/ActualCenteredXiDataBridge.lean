import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge
import InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge

/-!
# Concrete centered `CompletedXiData` realization

This file instantiates the small affine-coordinate wrapper with Mathlib's
concrete completed `riemannXi`.  The only analytic input is the existing
functional equation `riemannXi_one_sub`; no RH or spectral assertion is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualCenteredXiDataBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge
open InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge

/-! ## Generic transport from the completed-Xi symmetry datum -/

/-- Center an arbitrary completed-Xi symmetry datum in the affine coordinate
`z = s - 1/2`.  This is a structural transport, not an analytic realization. -/
def centeredXiDataOfCompletedDatum
    {lambda : ℂ → ℂ} (_h : CompletedXiDatum lambda) : CompletedXiData where
  lambda := lambda
  xi := fun z => lambda ((1 / 2 : ℂ) + z)
  xi_def := by intro z; rfl

@[simp] theorem centeredXiDataOfCompletedDatum_lambda
    {lambda : ℂ → ℂ} (_h : CompletedXiDatum lambda) (s : ℂ) :
    (centeredXiDataOfCompletedDatum _h).lambda s = lambda s := rfl

@[simp] theorem centeredXiDataOfCompletedDatum_xi
    {lambda : ℂ → ℂ} (_h : CompletedXiDatum lambda) (z : ℂ) :
    (centeredXiDataOfCompletedDatum _h).xi z =
      lambda ((1 / 2 : ℂ) + z) := rfl

theorem centeredXiDataOfCompletedDatum_even
    {lambda : ℂ → ℂ} (h : CompletedXiDatum lambda) (z : ℂ) :
    (centeredXiDataOfCompletedDatum h).xi z =
      (centeredXiDataOfCompletedDatum h).xi (-z) := by
  have href :
      1 - ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + (-z) := by
    ring
  have hsym := h.func_eq ((1 / 2 : ℂ) + z)
  rw [href] at hsym
  exact hsym.symm

/-- The centered wrapper whose affine readout is the actual `riemannXi`. -/
def actualCenteredXiData : CompletedXiData where
  lambda := riemannXi
  xi := fun z => riemannXi ((1 / 2 : ℂ) + z)
  xi_def := by intro z; rfl

@[simp] theorem actualCenteredXiData_xi (z : ℂ) :
    actualCenteredXiData.xi z = riemannXi ((1 / 2 : ℂ) + z) := rfl

@[simp] theorem actualCenteredXiData_lambda (s : ℂ) :
    actualCenteredXiData.lambda s = riemannXi s := rfl

/-- The concrete centered `riemannXi` is even in the affine coordinate. -/
theorem actualCenteredXiData_even (z : ℂ) :
    actualCenteredXiData.xi z = actualCenteredXiData.xi (-z) := by
  dsimp [actualCenteredXiData]
  have href : (1 / 2 : ℂ) - z = 1 - ((1 / 2 : ℂ) + z) := by ring
  rw [show (1 / 2 : ℂ) + -z = 1 / 2 - z by ring, href]
  exact (riemannXi_one_sub ((1 / 2 : ℂ) + z)).symm

/-- The actual centered `riemannXi` also satisfies Schwarz conjugation. -/
theorem actualCenteredXiData_conj (z : ℂ) :
    actualCenteredXiData.xi (star z) =
      star (actualCenteredXiData.xi z) := by
  dsimp [actualCenteredXiData]
  have h := actualRiemannXi_conj ((1 / 2 : ℂ) + z)
  simpa using h

end InfoGeometry.Canonical.ActualCenteredXiDataBridge
