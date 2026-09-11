/-
InfoGeometry/Algebraic/SplitCliffordCarrier.lean

Split Clifford carrier and rotor target for `Cl(n,n)`.
No complex imports.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import InfoGeometry.Algebraic.CartanCocycle
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Algebraic.SplitSignature

/-- The canonical vector injection into the split Clifford algebra. -/
def splitCliffordVector (n : ℕ) :
    SplitModule n →ₗ[ℝ] Cl_nn n :=
  CliffordAlgebra.ι (splitQuadraticForm n)

@[simp]
theorem splitCliffordVector_sq
    {n : ℕ} (v : SplitModule n) :
    splitCliffordVector n v * splitCliffordVector n v =
      algebraMap ℝ (Cl_nn n) (splitQuadraticForm n v) := by
  simp [splitCliffordVector]

@[simp]
theorem splitClifford_posBasis_sq
    {n : ℕ} (i : Fin n) :
    splitCliffordVector n (splitBasisVector (Sum.inl i)) *
        splitCliffordVector n (splitBasisVector (Sum.inl i)) =
      algebraMap ℝ (Cl_nn n) 1 := by
  rw [splitCliffordVector_sq, splitQuadraticForm_posBasisVector]

@[simp]
theorem splitClifford_negBasis_sq
    {n : ℕ} (i : Fin n) :
    splitCliffordVector n (splitBasisVector (Sum.inr i)) *
        splitCliffordVector n (splitBasisVector (Sum.inr i)) =
      algebraMap ℝ (Cl_nn n) (-1) := by
  rw [splitCliffordVector_sq, splitQuadraticForm_negBasisVector]

/--
The real spin group associated to the split Clifford algebra.

This is the canonical rotor target attached to `Cl(n,n)`.
-/
abbrev SplitSpinGroup (n : ℕ) : Type :=
  spinGroup (splitQuadraticForm n)

instance (n : ℕ) : Group (SplitSpinGroup n) :=
  inferInstance

/--
Orientation and volume data for a chosen split Clifford basis.

The pseudoscalar depends on the basis/orientation convention, so it is kept
as explicit data rather than baked into the carrier.
-/
structure SplitVolumeData (n : ℕ) where
  volume : Cl_nn n
  volume_sq_one : volume * volume = 1

/-- Positive chiral projector once split volume data is supplied. -/
noncomputable def chiralProjectorPlus
    {n : ℕ}
    (Ω : SplitVolumeData n) :
    Cl_nn n :=
  ((1 : ℝ) / 2) • (1 + Ω.volume)

/-- Negative chiral projector once split volume data is supplied. -/
noncomputable def chiralProjectorMinus
    {n : ℕ}
    (Ω : SplitVolumeData n) :
    Cl_nn n :=
  ((1 : ℝ) / 2) • (1 - Ω.volume)

/--
Split-signature rotor cocycle.

This is the higher-rank analogue of the modular Berry cocycle, with target
`SplitSpinGroup n`.
-/
abbrev SplitRotorCocycle
    (n : ℕ)
    (Γ X : Type*)
    [Group Γ] [MulAction Γ X] :=
  InfoGeometry.Algebraic.Cartan.CartanRotorCocycle Γ X (SplitSpinGroup n)

/-- Stabilizer anomaly extraction for the split Clifford rotor cocycle. -/
def splitStabilizerAnomaly
    {n : ℕ}
    {G X : Type*}
    [Group G] [MulAction G X]
    (C : SplitRotorCocycle n G X)
    (x : X) :
    MulAction.stabilizer G x →* SplitSpinGroup n :=
  C.stabilizerHom x (MulAction.stabilizer G x) (fun _ hg => hg)

end InfoGeometry.Algebraic.SplitSignature
