/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import Mathlib.Analysis.Matrix.Order

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Passing positivity from cutoff kernels to their pointwise limit

The cutoff parameter can range over an arbitrary nontrivial filter. The test-label set
can be infinite. Native `Matrix.PosSemidef` tests every finitely supported coefficient
vector and includes Hermitian symmetry. Closedness of this cone therefore passes all
finite Gram inequalities, and Hermitian symmetry, to an entrywise limit.

The analytic convergence and the cutoff positivity are hypotheses. This theorem does
not infer reflection positivity from a renormalization estimate or identify kernels
at different cutoffs by exact isometries.
-/

@[expose] public section

open Filter
open scoped Topology ComplexOrder MatrixOrder

namespace CoreLean.PositiveKernel

variable {X I : Type*} {l : Filter I} [l.NeBot]

/-- Eventual positive semidefiniteness survives pointwise convergence of complex kernels. -/
theorem posSemidef_of_tendsto
    {cutoff : I → Matrix X X ℂ} {K : Matrix X X ℂ}
    (hpos : ∀ᶠ i in l, (cutoff i).PosSemidef)
    (hlim : ∀ x y, Tendsto (fun i => cutoff i x y) l (𝓝 (K x y))) :
    K.PosSemidef := by
  have hK : Tendsto cutoff l (𝓝 K) :=
    tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => hlim x y
  have hnonneg : ∀ᶠ i in l, (0 : Matrix X X ℂ) ≤ cutoff i :=
    hpos.mono fun _ hi => Matrix.nonneg_iff_posSemidef.mpr hi
  exact Matrix.nonneg_iff_posSemidef.mp (ge_of_tendsto hK hnonneg)

end CoreLean.PositiveKernel
