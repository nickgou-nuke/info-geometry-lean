import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Canonical.CompletedZetaV4CharacterBridge

/-!
# Concrete centered `riemannXi` readout

This file is the realization dock between Mathlib's concrete `riemannXi` and
the abstract `XiSymmetryDatum`.  The reflection `s ↦ 1 - s` is discharged by
the existing completed-zeta functional equation.  Schwarz conjugation is
discharged by the concrete Mellin-kernel proof in
`ActualRiemannXiSchwarzBridge`.

No claim about the Riemann hypothesis or zeros is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Canonical.CompletedZetaV4Character

/-- The centered complex `riemannXi` readout at `u + I * tau`. -/
def centeredRiemannXi (u tau : ℝ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + u + Complex.I * tau)

/-- Real part of the concrete centered `riemannXi` readout. -/
def centeredRiemannXiReal (u tau : ℝ) : ℝ :=
  (centeredRiemannXi u tau).re

/-- Imaginary part of the concrete centered `riemannXi` readout. -/
def centeredRiemannXiImag (u tau : ℝ) : ℝ :=
  (centeredRiemannXi u tau).im

/-! The centered readout is the existing symmetry-adapted `riemannXi`
readout on the embedded real coordinates. -/
theorem centeredRiemannXi_eq_symmetryAdaptedXi (u tau : ℝ) :
    centeredRiemannXi u tau =
      symmetryAdaptedXi ((u : ℂ) + Complex.I * (tau : ℂ)) := by
  unfold centeredRiemannXi symmetryAdaptedXi fromSymmetryAdapted
  congr 1
  ring

/-- The concrete Schwarz-reflection statement needed by the datum constructor. -/
def ActualXiSchwarzHypothesis : Prop :=
  ∀ s : ℂ, riemannXi (star s) = star (riemannXi s)

/--
The corresponding Schwarz statement at the completed-zeta level.  It remains
an interface predicate for reusable conditional constructors; the concrete
instance below is proved upstream.
-/
def ActualCompletedXiSchwarzHypothesis : Prop :=
  ∀ s : ℂ, completedRiemannZeta (star s) =
    star (completedRiemannZeta s)

theorem riemannXi_schwarz_of_completed
    (hSchwarz : ActualCompletedXiSchwarzHypothesis) (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := by
  unfold riemannXi
  rw [hSchwarz]
  simp

theorem actualXiSchwarzHypothesis_of_completed
    (hSchwarz : ActualCompletedXiSchwarzHypothesis) :
    ActualXiSchwarzHypothesis := by
  intro s
  exact riemannXi_schwarz_of_completed hSchwarz s

theorem centeredRiemannXi_neg (u tau : ℝ) :
    centeredRiemannXi (-u) (-tau) = centeredRiemannXi u tau := by
  unfold centeredRiemannXi
  have hu : ((-u : ℝ) : ℂ) = -(u : ℂ) := by norm_num
  have ht : ((-tau : ℝ) : ℂ) = -(tau : ℂ) := by norm_num
  rw [hu, ht]
  calc
    riemannXi ((1 / 2 : ℂ) + (-u : ℂ) + Complex.I * (-tau : ℂ)) =
        riemannXi (1 - ((1 / 2 : ℂ) + (u : ℂ) + Complex.I * (tau : ℂ))) := by
      congr 1
      ring
    _ = riemannXi ((1 / 2 : ℂ) + (u : ℂ) + Complex.I * (tau : ℂ)) :=
      riemannXi_one_sub _

theorem centeredRiemannXi_schwarz
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    centeredRiemannXi u (-tau) = star (centeredRiemannXi u tau) := by
  unfold centeredRiemannXi
  have ht : ((-tau : ℝ) : ℂ) = -(tau : ℂ) := by norm_num
  rw [ht]
  have harg :
      (1 / 2 : ℂ) + (u : ℂ) + Complex.I * (-tau : ℂ) =
        star ((1 / 2 : ℂ) + (u : ℂ) + Complex.I * (tau : ℂ)) := by
    apply Complex.ext <;> simp
  rw [harg, hSchwarz]

/--
The concrete centered `riemannXi` readout forms the existing symmetry datum
once Schwarz conjugation is supplied.  The only non-definitional input is
the explicit `ActualXiSchwarzHypothesis`.
-/
def actualXiSymmetryDatum
    (hSchwarz : ActualXiSchwarzHypothesis) : XiSymmetryDatum where
  A := centeredRiemannXiReal
  B := centeredRiemannXiImag
  parity_A u tau := by
    exact congrArg Complex.re (centeredRiemannXi_neg u tau)
  parity_B u tau := by
    exact congrArg Complex.im (centeredRiemannXi_neg u tau)
  schwarz_A u tau := by
    simpa using congrArg Complex.re (centeredRiemannXi_schwarz hSchwarz u tau)
  schwarz_B u tau := by
    have h := congrArg Complex.im (centeredRiemannXi_schwarz hSchwarz u tau)
    simpa using h

/--
Direct concrete constructor from the completed-zeta Schwarz boundary.  This
is the preferred entry point when the upstream analytic owner supplies
conjugation for `completedRiemannZeta`.
-/
def actualXiSymmetryDatum_of_completed
    (hSchwarz : ActualCompletedXiSchwarzHypothesis) : XiSymmetryDatum :=
  actualXiSymmetryDatum (actualXiSchwarzHypothesis_of_completed hSchwarz)

/--
Concrete constructor for Mathlib's completed Riemann readout.  The Schwarz
identity is proved upstream from conjugation of the real Mellin kernel; no
Schwarz hypothesis is supplied at this boundary.
-/
def actualXiSchwarzHypothesis_concrete : ActualXiSchwarzHypothesis :=
  actualXiSchwarzHypothesis_of_completed
    (by
      intro s
      exact actualCompletedRiemannZetaSchwarz s)

def actualXiSymmetryDatum_concrete : XiSymmetryDatum :=
  actualXiSymmetryDatum actualXiSchwarzHypothesis_concrete

@[simp] theorem actualXiSymmetryDatum_A
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    (actualXiSymmetryDatum hSchwarz).A u tau = centeredRiemannXiReal u tau := rfl

@[simp] theorem actualXiSymmetryDatum_B
    (hSchwarz : ActualXiSchwarzHypothesis) (u tau : ℝ) :
    (actualXiSymmetryDatum hSchwarz).B u tau = centeredRiemannXiImag u tau := rfl

theorem actualXiSymmetryDatum_criticalLine_real
    (hSchwarz : ActualXiSchwarzHypothesis) (tau : ℝ) :
    centeredRiemannXi 0 tau =
      (centeredRiemannXiReal 0 tau : ℂ) := by
  simpa [actualXiSymmetryDatum, centeredRiemannXiReal,
    centeredRiemannXiImag] using
    (xi_strictly_real_on_critical_line (actualXiSymmetryDatum hSchwarz) tau)

/-- Critical-line reality for the concrete Mathlib instance, with no
external Schwarz hypothesis at the call site. -/
theorem actualXiSymmetryDatum_concrete_criticalLine_real (tau : ℝ) :
    centeredRiemannXi 0 tau =
      (centeredRiemannXiReal 0 tau : ℂ) :=
  actualXiSymmetryDatum_criticalLine_real actualXiSchwarzHypothesis_concrete tau

end InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
