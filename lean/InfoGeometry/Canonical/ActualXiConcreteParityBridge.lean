import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ActualXiHardyZRealizationBridge

/-!
# Concrete `riemannXi` parity interface

This owner connects the concrete centered `riemannXi` readout to the generic
`ConcreteXiFunctions` interface.  The parameterized constructor retains the
Schwarz interface for reuse; the concrete constructor below discharges it
from the proved Mellin-kernel conjugation theorem. Functional reflection and
all parity readouts are discharged by the existing concrete owners.

No Hardy-Z normalization, zero-set identification, or Riemann-hypothesis claim
is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualXiConcreteParityBridge

open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.CompletedZetaV4Character
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Topology.ActualXiHardyZRealization

/-- The generic parity interface realized by the centered Mathlib `riemannXi`.
The parameterized form accepts the reusable Schwarz interface; its concrete
instance is defined below from the upstream proof.
-/
def actualConcreteXiFunctions
    (hSchwarz : ActualXiSchwarzHypothesis) : ConcreteXiFunctions where
  A := centeredRiemannXiReal
  B := centeredRiemannXiImag
  schwarz_re := by
    intro u tau
    exact (actualXiSymmetryDatum hSchwarz).schwarz_A u tau
  schwarz_im := by
    intro u tau
    exact (actualXiSymmetryDatum hSchwarz).schwarz_B u tau
  func_re := by
    intro u tau
    exact (actualXiSymmetryDatum hSchwarz).parity_A u tau
  func_im := by
    intro u tau
    exact (actualXiSymmetryDatum hSchwarz).parity_B u tau

/-- The concrete parity interface, now instantiated by the proved Mathlib
Schwarz identity rather than by a supplied hypothesis. -/
def actualConcreteXiFunctions_concrete : ConcreteXiFunctions :=
  actualConcreteXiFunctions actualXiSchwarzHypothesis_concrete

@[simp] theorem actualConcreteXiFunctions_A
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    (actualConcreteXiFunctions hSchwarz).A u tau = centeredRiemannXiReal u tau := rfl

@[simp] theorem actualConcreteXiFunctions_B
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    (actualConcreteXiFunctions hSchwarz).B u tau = centeredRiemannXiImag u tau := rfl

theorem actualConcreteXiFunctions_critical_imag_zero
    (hSchwarz : ActualXiSchwarzHypothesis) (tau : ℝ) :
    centeredRiemannXiImag 0 tau = 0 := by
  simpa [actualConcreteXiFunctions, centeredRiemannXiImag] using
    (concrete_xi_critical_reality (actualConcreteXiFunctions hSchwarz) tau)

theorem actualConcreteXiFunctions_critical_real
    (hSchwarz : ActualXiSchwarzHypothesis) (tau : ℝ) :
    centeredRiemannXi 0 tau =
      (centeredRiemannXiReal 0 tau : ℂ) := by
  exact actualXiSymmetryDatum_criticalLine_real hSchwarz tau

/-!
The preceding identity gives an actual real-valued critical-line readout.  The
following zero theorem is deliberately stated for that readout, rather than
calling it the classical Hardy `Z` function: no independent Riemann--Siegel
phase normalization is assumed here.
-/

theorem centeredRiemannXiReal_zero_iff
    (hSchwarz : ActualXiSchwarzHypothesis) (tau : ℝ) :
    centeredRiemannXiReal 0 tau = 0 ↔
      centeredRiemannXi 0 tau = 0 := by
  rw [← Complex.ofReal_eq_zero]
  rw [actualXiSymmetryDatum_criticalLine_real hSchwarz tau]

theorem centeredRiemannXiReal_zero_iff_riemannXi_zero
    (hSchwarz : ActualXiSchwarzHypothesis) (tau : ℝ) :
    centeredRiemannXiReal 0 tau = 0 ↔
      riemannXi ((1 / 2 : ℂ) + Complex.I * tau) = 0 := by
  simpa [centeredRiemannXi] using
    centeredRiemannXiReal_zero_iff hSchwarz tau

theorem centeredRiemannXiReal_zero_iff_riemannXi_zero_concrete
    (tau : ℝ) :
    centeredRiemannXiReal 0 tau = 0 ↔
      riemannXi ((1 / 2 : ℂ) + Complex.I * tau) = 0 :=
  centeredRiemannXiReal_zero_iff_riemannXi_zero
    actualXiSchwarzHypothesis_concrete tau

theorem actual_concrete_xi_parity_packet
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    centeredRiemannXiReal (-u) (-tau) = centeredRiemannXiReal u tau ∧
    centeredRiemannXiImag (-u) (-tau) = centeredRiemannXiImag u tau ∧
    centeredRiemannXiReal u (-tau) = centeredRiemannXiReal u tau ∧
    centeredRiemannXiImag u (-tau) = - centeredRiemannXiImag u tau := by
  let D := actualConcreteXiFunctions hSchwarz
  exact ⟨D.func_re u tau, D.func_im u tau,
    D.schwarz_re u tau, D.schwarz_im u tau⟩

end InfoGeometry.Canonical.ActualXiConcreteParityBridge
