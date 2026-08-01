import Mathlib.Tactic
import InfoGeometry.External.Auto.ZetaSpectralBridge

noncomputable section

namespace InfoGeometry.Quantum.MellinHeatKernelBridge

open Complex
open scoped BigOperators

/--
Finite Mellin bridge data.

This is intentionally conservative: `mellin` is an abstract transform on a
finite modeled heat object `F`, with only the finite additivity and atom
evaluation properties required by the bridge theorem.
-/
structure FiniteMellinModel (F : Type*) [AddCommMonoid F] (ι : Type*) [Fintype ι] where
  mellin : F → ℂ → ℂ
  gamma : ℂ → ℂ
  heatAtom : ι → F
  spectralAtom : ι → ℂ → ℂ
  finite_additivity :
    ∀ s : ℂ, mellin (∑ i : ι, heatAtom i) s = ∑ i : ι, mellin (heatAtom i) s
  atom_eval :
    ∀ (i : ι) (s : ℂ), mellin (heatAtom i) s = gamma s * spectralAtom i s

variable {F ι : Type*} [AddCommMonoid F] [Fintype ι]

/--
Finite heat-kernel-to-spectral-sum Mellin bridge.

If the transform is additive on the finite heat trace and each heat atom has
Mellin value `Γ(s) * spectralAtom_i(s)`, then the finite heat trace transforms
to `Γ(s)` times the finite spectral sum.
-/
theorem finite_mellin_heat_trace_bridge (M : FiniteMellinModel F ι) (s : ℂ) :
    M.mellin (∑ i : ι, M.heatAtom i) s =
      M.gamma s * ∑ i : ι, M.spectralAtom i s := by
  rw [M.finite_additivity]
  calc
    (∑ i : ι, M.mellin (M.heatAtom i) s)
        = ∑ i : ι, M.gamma s * M.spectralAtom i s := by
            apply Finset.sum_congr rfl
            intro i _
            exact M.atom_eval i s
    _ = M.gamma s * ∑ i : ι, M.spectralAtom i s := by
            rw [Finset.mul_sum]

/--
Finite Primon spectral atom using logarithmic energies.

For index `i`, the modeled spectral contribution is
`exp (-s * log(i+1))`, the finite-stage analogue of `(i+1)^(-s)`.
-/
def primonSpectralAtom {n : ℕ} (i : Fin (n + 1)) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (Real.log ((i.1 + 1 : ℕ) : ℝ) : ℂ)))

/--
Specialized finite-stage statement for Primon-style logarithmic weights.

The theorem is still assumption-explicit: it does not define the improper
Mellin integral.  It packages the exact finite consequence of the atom formula.
-/
theorem finite_primon_mellin_bridge
    {F : Type*} [AddCommMonoid F] (n : ℕ)
    (M : FiniteMellinModel F (Fin (n + 1)))
    (hAtom : ∀ (i : Fin (n + 1)) (s : ℂ),
      M.spectralAtom i s = primonSpectralAtom i s)
    (s : ℂ) :
    M.mellin (∑ i : Fin (n + 1), M.heatAtom i) s =
      M.gamma s * ∑ i : Fin (n + 1), primonSpectralAtom i s := by
  rw [finite_mellin_heat_trace_bridge M s]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hAtom i s

/-- The abstract Mellin atom used here is the same atom used by `ZetaSpectralBridge`. -/
theorem primonSpectralAtom_eq_gammaNormalizedMellinMode {n : ℕ}
    (i : Fin (n + 1)) (s : ℂ) :
    primonSpectralAtom i s =
      InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode
        s (i.1 + 1 : ℝ) := by
  unfold primonSpectralAtom
  unfold InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode
  congr 1
  norm_num

/--
The finite spectral sum produced by the abstract heat-kernel Mellin bridge is
exactly the finite Mellin trace used by `ZetaSpectralBridge`.
-/
theorem finite_primon_spectral_sum_eq_zeta_mellin_trace (n : ℕ) (s : ℂ) :
    (∑ i : Fin (n + 1), primonSpectralAtom i s) =
      InfoGeometry.Quantum.ZetaSpectralBridge.finitePrimonMellinTrace n s := by
  unfold InfoGeometry.Quantum.ZetaSpectralBridge.finitePrimonMellinTrace
  apply Finset.sum_congr rfl
  intro i _
  exact primonSpectralAtom_eq_gammaNormalizedMellinMode i s

end InfoGeometry.Quantum.MellinHeatKernelBridge
