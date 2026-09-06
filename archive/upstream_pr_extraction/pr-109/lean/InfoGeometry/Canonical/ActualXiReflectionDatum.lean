import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Concrete reflection datum for the completed Riemann `xi` readout

This owner records the unconditional reflection law supplied by Mathlib.
Schwarz conjugation is intentionally not included: the current Mathlib
surface provides the functional equation `s ↦ 1 - s`, but no corresponding
conjugation theorem for `completedRiemannZeta`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualXiReflectionDatum

open InfoGeometry.Arithmetic.RiemannZetaEquivalences

structure XiReflectionDatum where
  Xi : ℂ → ℂ
  reflection : ∀ s : ℂ, Xi (1 - s) = Xi s

def actualRiemannXiReflectionDatum : XiReflectionDatum where
  Xi := riemannXi
  reflection := riemannXi_one_sub

@[simp] theorem actualRiemannXiReflectionDatum_Xi (s : ℂ) :
    actualRiemannXiReflectionDatum.Xi s = riemannXi s := rfl

theorem actualRiemannXiReflectionDatum_reflection (s : ℂ) :
    actualRiemannXiReflectionDatum.Xi (1 - s) =
      actualRiemannXiReflectionDatum.Xi s := by
  exact riemannXi_one_sub s

end InfoGeometry.Canonical.ActualXiReflectionDatum
