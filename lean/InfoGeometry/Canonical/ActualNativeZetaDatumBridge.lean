import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Canonical.NativeMathlibZetaConnectionBridge
import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

/-!
# Actual native zeta/Xi datum

This file realizes the abstract `NativeZetaDatum` with Mathlib's concrete
`riemannZeta` and `riemannXi`.  Every field is discharged by an existing
analytic owner: the completed-zeta reflection theorem, the concrete Mellin
Schwarz theorem, and the zero equivalence in the open critical strip.

No zero-free region, Riemann hypothesis, Hardy-Z factorization, or colimit
construction is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualNativeZetaDatumBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
open InfoGeometry.Canonical.MasterRH
open InfoGeometry.Canonical.NativeZeta
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

def actualNativeZetaDatum : NativeZetaDatum where
  zeta := riemannZeta
  xi := riemannXi
  h_xi_reflect := riemannXi_one_sub
  h_xi_conj := actualXiSchwarzHypothesis_concrete
  h_strip_zero_equiv := by
    intro s hs
    exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip hs.1 hs.2).symm

@[simp] theorem actualNativeZetaDatum_zeta (s : ℂ) :
    actualNativeZetaDatum.zeta s = riemannZeta s := rfl

@[simp] theorem actualNativeZetaDatum_xi (s : ℂ) :
    actualNativeZetaDatum.xi s = riemannXi s := rfl

theorem actualNativeZetaDatum_reflection (s : ℂ) :
    actualNativeZetaDatum.xi (1 - s) = actualNativeZetaDatum.xi s := by
  exact riemannXi_one_sub s

theorem actualNativeZetaDatum_conjugation (s : ℂ) :
    actualNativeZetaDatum.xi (star s) = star (actualNativeZetaDatum.xi s) := by
  exact actualXiSchwarzHypothesis_concrete s

theorem actualNativeZetaDatum_strip_zero_equivalence
    {s : ℂ} (hs : s ∈ criticalStrip) :
    actualNativeZetaDatum.zeta s = 0 ↔ actualNativeZetaDatum.xi s = 0 := by
  exact actualNativeZetaDatum.h_strip_zero_equiv s hs

end InfoGeometry.Canonical.ActualNativeZetaDatumBridge
