import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Projective Simplex Foundation

This module establishes the canonical link between projective geometry and 
information theory. The probability simplex is implemented as a specific 
gauge-fixing section of the projectivization of the positive cone.

Mathematical Hierarchy:
1. Carrier Space (Vector Space V)
2. Unnormalized States (Positive Cone interior)
3. Projective State Space (ℙ ℝ V)
4. Normalized Distributions (stdSimplex via gauge-fixing)
-/

namespace InfoGeometry.Canonical

open LinearAlgebra
open scoped LinearAlgebra.Projectivization

/-- Every normalized distribution in the standard simplex defines a unique projective state. -/
noncomputable def fromStdSimplex {ι : Type*} [Fintype ι] (f : stdSimplex ℝ ι) : ℙ ℝ (ι → ℝ) :=
  let v : ι → ℝ := f.1
  let hv : v ≠ 0 := by
    intro h
    have hsum := f.2.2
    have h_zero_sum : ∑ i, v i = 0 := by
      rw [h]
      simp
    rw [h_zero_sum] at hsum
    exact zero_ne_one hsum
  Projectivization.mk ℝ v hv

/-- Choice of a normalized representative from a projective ray (Gauge Fixing). -/
noncomputable def gaugeFix {ι : Type*} [Fintype ι] (p : ℙ ℝ (ι → ℝ)) (h_mass : ∑ i, p.rep i ≠ 0) :
    { f : ι → ℝ // ∑ i, f i = 1 } :=
  let v : ι → ℝ := p.rep
  ⟨(∑ i, v i)⁻¹ • v, by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ h_mass⟩

end InfoGeometry.Canonical
