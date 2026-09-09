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

theorem section25_capstone :
    (∀ A B : ℂ, B = starRingEnd ℂ A →
      (scalarRealityReadout A B).im = 0) ∧
    (∀ Q : Quat,
      Section8.Quat.conj Q * Q =
        Section8.Quat.scalar (Section8.Quat.normSq Q)) ∧
    (Section8.Quat.qi * Section8.Quat.qi = -(1 : Quat)
      ∧ Section8.Quat.qj * Section8.Quat.qj = -(1 : Quat)
      ∧ Section8.Quat.qk * Section8.Quat.qk = -(1 : Quat)
      ∧ Section8.Quat.qi * Section8.Quat.qj = Section8.Quat.qk
      ∧ Section8.Quat.qj * Section8.Quat.qk = Section8.Quat.qi
      ∧ Section8.Quat.qk * Section8.Quat.qi = Section8.Quat.qj
      ∧ (Section8.Quat.qi * Section8.Quat.qj) * Section8.Quat.qk =
        -(1 : Quat)) ∧
    (∀ e : Fin 4 → Fin 4 → ℝ, ∀ mu nu : Fin 4,
      Section22.quaternionInducedMetric e mu nu =
        Section22.quaternionInducedMetric e nu mu) ∧
    (∀ kappa : ℂ, ∀ B : Fin 4 → Fin 4 → Fin 4 → ℂ,
      ∀ lam mu nu : Fin 4,
        Section24.torsionCommutatorShadow kappa B lam nu mu =
          -Section24.torsionCommutatorShadow kappa B lam mu nu) := by
  exact ⟨scalarRealityReadout_im_zero, Section24.quaternion_norm_scalar,
    Section24.hamilton_basis_with_triple, Section24.quaternion_metric_symmetric,
    Section24.torsionCommutatorShadow_antisymmetric⟩

end Section25
