import Mathlib
import InfoGeometry.Physics.SupergradedCuntzBdG
/-!
# Majorana → Primon Spectral Bridge

The self-adjoint Majorana operator `γ₁` generates the positive Cuntz-BdG
Hamiltonian `H_atom = γ₁²`, already proved in `SupergradedCuntzBdG`. This file
bundles those theorems with the CPT spectral involution `s ↦ 1 - s̄` whose
unique fixed locus is `Re(s) = 1/2` — the critical line.

The theorem-honest boundary is important: `H_atom`/the Primon Hamiltonian is
the arithmetic thermodynamic generator, not the Hilbert–Pólya zero operator.
This finite algebraic file does not assert a Hilbert–Pólya/RH theorem.

No omitted proof holes.
-/

namespace MajoranaPrimonSpectralBridge

open SupergradedCuntzBdG
open scoped ComplexConjugate

/-- CPT spectral involution: `s ↦ 1 - s̄`. The critical line `Re(s)=1/2`
is the unique fixed locus of this map. -/
def cptSpectralMap (s : ℂ) : ℂ := 1 - conj s

/-- The critical line `Re(s) = 1/2` is the fixed point set of the CPT involution. -/
theorem cpt_fixed_point_iff_critical_line (s : ℂ) :
    cptSpectralMap s = s ↔ s.re = 1/2 := by
  constructor
  · intro h; have h' := congrArg Complex.re h
    simp [cptSpectralMap, Complex.sub_re, Complex.one_re, Complex.conj_re] at h'; linarith
  · intro h; apply Complex.ext
    · simp [cptSpectralMap, Complex.sub_re, Complex.one_re, Complex.conj_re, h]; ring
    · simp [cptSpectralMap, Complex.sub_im, Complex.one_im, Complex.conj_im]

/-- The Majorana-Primon Spectral Bridge:
1. γ₁ is self-adjoint (proved in `SupergradedCuntzBdG`)
2. γ₁² = H_atom (proved in `SupergradedCuntzBdG`)
3. CPT involution fixes exactly the critical line Re(s)=1/2 (proved above) -/
theorem majorana_primon_spectral_bridge {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (s : ℂ) :
    (star (bdgMajoranaPlus i) = bdgMajoranaPlus i) ∧
    (bdgMajoranaPlus i * bdgMajoranaPlus i = hamiltonianAtom i) ∧
    (cptSpectralMap s = s ↔ s.re = 1/2) := by
  refine ⟨star_bdgMajoranaPlus i,
    bdgMajoranaPlus_sq_eq_hamiltonianAtom i,
    cpt_fixed_point_iff_critical_line s⟩

end MajoranaPrimonSpectralBridge
