/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Null eigenspaces of a split anti-isometry

If an involution $K$ acts as a *split anti-isometry* of a bilinear form,
$g(Kx, Ky) = -g(x, y)$, then on the subspace it fixes pointwise one gets

$$g(x,x) = g(Kx, Kx) = -g(x,x) \;\Longrightarrow\; 2\,g(x,x) = 0 .$$

This is the algebraic reason the primal and covector sheets must be **null**: they are the
eigenspaces of such a $K$, so the form cannot give them an internal length. This module
formalizes the general statement over an arbitrary commutative ring and pins down exactly
where the familiar conclusion stops being available.

**The honest boundary.** The derivable conclusion is `2 * g x x = 0`, *not* `g x x = 0`. Over a
ring with $2$-torsion these differ: in $\mathbb{Z}/6$ one has $2 \neq 0$ yet $2\cdot 3 = 0$.
A sufficient condition for `g x x = 0` is `NoZeroDivisors` together with
`2 ≠ 0` (`sheet_self_zero_of_two_ne`), as in a field of characteristic other
than two. The exact uniform condition is absence of two-torsion; see
`FixedPairingTorsionBoundary`. That is why the real
para-Kähler carrier is clean and why the general statement is not stronger than it is here.

Note the conclusion is about the *fixed* eigenspace. For the para-Kähler form
$g((u,\alpha),(u',\alpha')) = \langle u,\alpha'\rangle + \langle \alpha,u'\rangle$ the
self-metric of a general $(u,\alpha)$ is $2\langle u,\alpha\rangle$, which is zero only on the
null cone $\langle u,\alpha\rangle = 0$ — see `SplitOctonionParaKahlerNullCone` for that
instance and `isOnNullCone_iff_vec3Dot_zero`.
-/

namespace InfoGeometry.Canonical.NullEigenspace

/-- **Null eigenspaces: the sheet metrics vanish.** If `K` is an involution acting as a *split
anti-isometry* of a bilinear form, then on the subspace it fixes pointwise every self-pairing
satisfies `2 g(x,x) = 0` — and hence `g(x,x) = 0` whenever `2` is invertible.

This is the algebraic core of the conditional isotropy claim for fixed directions: the anti-isometry `g(Kx,Ky) = -g(x,y)` and the involution `K² = id` together force
`g(x,x) = g(Kx,Kx) = -g(x,x)`.

The output is deliberately `2 * g x x = 0` and not `g x x = 0`, because the inference from the
former to the latter fails over a general commutative ring with `2`-torsion. That is the
precise boundary of the necessity argument, made explicit in
`sheet_self_zero_of_two_ne`. -/
theorem sheet_self_double_zero {F ι : Type*} [CommRing F]
    (g : ι → ι → F) (K : ι → ι)
    (hanti : ∀ x y, g (K x) (K y) = -g x y)
    (hfix : ∀ x, K x = x) (x : ι) :
    2 * g x x = 0 := by
  have h1 : g x x = -g x x := by
    have h := hanti x x
    rw [hfix x] at h
    exact h
  calc 2 * g x x = g x x + g x x := by ring
    _ = g x x + (-g x x) := by rw [← h1]
    _ = 0 := by simp

theorem sheet_self_zero_of_two_ne {F ι : Type*} [CommRing F] [NoZeroDivisors F]
    (g : ι → ι → F) (K : ι → ι)
    (hanti : ∀ x y, g (K x) (K y) = -g x y)
    (hfix : ∀ x, K x = x) (x : ι) (h2 : (2 : F) ≠ 0) :
    g x x = 0 := by
  have h := sheet_self_double_zero g K hanti hfix x
  exact (mul_eq_zero.mp h).resolve_left h2

/-- **Cross terms vanish too**, under symmetry: for two fixed directions `g(x,y) = -g(y,x)`,
so `2 g(x,y) = 0`. After cancellation this gives isotropy; maximal isotropy
requires separate hypotheses. Symmetry is retained for compatibility here,
but the localized theorem in `FixedPairingTorsionBoundary` does not need it. -/
theorem sheet_cross_double_zero {F ι : Type*} [CommRing F]
    (g : ι → ι → F) (K : ι → ι)
    (hsymm : ∀ x y, g x y = g y x)
    (hanti : ∀ x y, g (K x) (K y) = -g x y)
    (hfix : ∀ x, K x = x) (x y : ι) :
    2 * g x y = 0 := by
  have h1 : g y x = -g y x := by
    have h := hanti y x
    rw [hfix x, hfix y] at h
    exact h
  calc 2 * g x y = 2 * g y x := by rw [hsymm x y]
    _ = g y x + g y x := by ring
    _ = g y x + (-g y x) := by rw [← h1]
    _ = 0 := by ring

end InfoGeometry.Canonical.NullEigenspace
