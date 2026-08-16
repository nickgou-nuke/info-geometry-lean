import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Section24

/-!
# Section 25: revised quaternionic extension finite repair

The source revises Section 24 by weakening the Clifford-embedding claim and by
adding a trace/conjugation explanation for the reality of the proposed
vielbein.  This file formalizes only the theorem-safe finite part:

* the same Hamilton multiplication, norm, metric symmetry, and torsion
  antisymmetry facts already closed in Section 24;
* a scalar version of the revised reality argument with an explicit conjugacy
  premise `B = conj A`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The finite quaternion algebra and tensor antisymmetry corridor is inherited
from Section 24.  In addition, for complex scalars `A,B`, if `B` is the complex
conjugate of `A`, then `i/2 * (A-B)` has zero imaginary part, hence is a real
complex number in this finite scalar model.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The scalar reality readout depends on the explicit premise
`B = starRingEnd ℂ A`, standing in for the trace/conjugation relation that the
source text assumes.

#### BUCKET 3: OPEN CLOSURE DEBT
No full Clifford algebra embedding theorem, trace theorem for the advertised
gamma representation, vacuum expectation value, smooth derivative, spin
connection, curvature/torsion decomposition, inverse-vielbein field equation,
or self-consistency loop is claimed here.
-/

noncomputable section

namespace Section25

abbrev Quat := Section24.Quat

/--
Finite scalar shadow of the revised vielbein reality expression
`(i/2) (A-B)`.
-/
def scalarRealityReadout (A B : ℂ) : ℂ :=
  Complex.I / 2 * (A - B)

/--
If the second scalar is the conjugate of the first, the revised finite readout
is real-valued as a complex number.
-/
theorem scalarRealityReadout_im_zero
    (A B : ℂ) (hB : B = starRingEnd ℂ A) :
    (scalarRealityReadout A B).im = 0 := by
  subst B
  simp [scalarRealityReadout]

/-- Quaternion norm scalar identity reused in the revised statement. -/
theorem revised_quaternion_norm_scalar (Q : Quat) :
    Section8.Quat.conj Q * Q = Section8.Quat.scalar (Section8.Quat.normSq Q) :=
  Section24.quaternion_norm_scalar Q

/-- Finite metric symmetry reused in the revised statement. -/
theorem revised_quaternion_metric_symmetric
    (e : Fin 4 → Fin 4 → ℝ) (mu nu : Fin 4) :
    Section22.quaternionInducedMetric e mu nu =
      Section22.quaternionInducedMetric e nu mu :=
  Section24.quaternion_metric_symmetric e mu nu

/-- Finite torsion shadow antisymmetry reused in the revised statement. -/
theorem revised_torsionCommutatorShadow_antisymmetric
    (kappa : ℂ) (B : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (lam mu nu : Fin 4) :
    Section24.torsionCommutatorShadow kappa B lam nu mu =
      -Section24.torsionCommutatorShadow kappa B lam mu nu :=
  Section24.torsionCommutatorShadow_antisymmetric kappa B lam mu nu

end Section25
