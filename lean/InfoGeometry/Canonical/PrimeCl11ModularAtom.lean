import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.Cl11ModularAtom
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimeHurwitzLimit

/-!
# InfoGeometry.Canonical.PrimeCl11ModularAtom

Prime-local `Cl(1,1)` modular atom and CPT wavelet witness surface.

This file formalizes the theorem-safe algebraic core of the proposed prime
atom:

* a local `Cl(1,1)`-style atom with generators `c` and `d`;
* the Möbius parity element `c * d` and its involutive square;
* a continuous CPT symmetry packet;
* a Laplace--Mellin wavelet witness packet that keeps the CPT/Lee--Yang
  interface explicit.

It does not prove any prime-to-`xi` convergence theorem, Lee--Yang stability,
or RH.
-/

noncomputable section

namespace PrimeCl11ModularAtom

open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeHurwitzLimit

section Core

variable {A : Type*}
variable [Ring A]

/-- Local `Cl(1,1)`-style prime atom. -/
@[rep_depth operator]
structure Cl11Atom (A : Type*) [Ring A] where
  c : A
  d : A
  c_sq : c * c = 1
  d_sq : d * d = -1
  anticomm : c * d + d * c = 0

namespace Cl11Atom

variable (atom : Cl11Atom A)

/-- The local Möbius parity (pseudo-scalar). -/
@[rep_depth operator]
def mobiusParity : A :=
  atom.c * atom.d

/-- The local Möbius parity squares to `1`. -/
@[rep_depth operator]
theorem mobiusParity_sq_eq_one :
    (mobiusParity atom) * (mobiusParity atom) = 1 := by
  have hdc : atom.d * atom.c = -(atom.c * atom.d) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using atom.anticomm
  calc
    (mobiusParity atom) * (mobiusParity atom)
        = atom.c * (atom.d * atom.c) * atom.d := by
            simp [mobiusParity, mul_assoc]
    _ = atom.c * (-(atom.c * atom.d)) * atom.d := by
          rw [hdc]
    _ = - (atom.c * (atom.c * atom.d) * atom.d) := by
          simp [mul_assoc]
    _ = - (((atom.c * atom.c) * atom.d) * atom.d) := by
          simp [mul_assoc]
    _ = - ((atom.c * atom.c) * (atom.d * atom.d)) := by
          simp [mul_assoc]
    _ = - ((1 : A) * (-1)) := by
          rw [atom.c_sq, atom.d_sq]
    _ = 1 := by
          simp

end Cl11Atom

end Core

--------------------------------------------------------------------------------
-- CPT symmetry and Laplace--Mellin wavelet transform
--------------------------------------------------------------------------------

/-- Continuous CPT symmetry packet. -/
@[rep_depth operator]
structure ContinuousCPTSymmetry where
  s_inversion : ℂ → ℂ
  z_inversion : ℂ → ℂ

/-- Canonical continuous CPT symmetry: `s ↦ 1 - s`, `z ↦ z⁻¹`. -/
@[rep_depth operator]
def canonicalContinuousCPTSymmetry : ContinuousCPTSymmetry :=
  { s_inversion := fun s => 1 - s
    z_inversion := fun z => z⁻¹ }

/--
Laplace--Mellin discrete Hurwitz wavelet witness.

The wavelet packet is deliberately witness-gated: paraunitarity is recorded as
an analytic invariant, but the prime-to-`xi` convergence statement is not
claimed here.
-/
@[rep_depth operator]
structure LaplaceMellinWaveletTransform
    (Ξ : CompletedXiZeroPredicate) where
  approximants : LeeYangApproximants
  cptSymmetry : ContinuousCPTSymmetry

  /-- CPT preservation at the level of Lee--Yang zero sets. -/
  cpt_preservation :
    ∀ N z, z ≠ 0 →
      (approximants.Z N z = 0 ↔ approximants.Z N (z⁻¹) = 0)

  /-- Paraunitary boundedness / energy preservation witness. -/
  paraunitary_boundedness : Prop


/--
CPT invariance transfers a finite zero to the reciprocal point.

This is the exact theorem-safe statement stored by the wavelet packet.
-/
@[rep_depth operator]
theorem cpt_invariance_forces_reciprocal_zeros
    {Ξ : CompletedXiZeroPredicate}
    (WT : LaplaceMellinWaveletTransform Ξ)
    (N : ℕ) (z : ℂ) (hz_zero : WT.approximants.Z N z = 0)
    (hz_neq : z ≠ 0) :
    WT.approximants.Z N (z⁻¹) = 0 := by
  exact (WT.cpt_preservation N z hz_neq).mp hz_zero

end PrimeCl11ModularAtom
