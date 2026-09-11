import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-!
# InfoGeometry.Canonical.LeeYangAsanoMobiusNative

Native algebraic closure for the nondegenerate Asano root-map layer.

Closed here:
* the Möbius root map algebra;
* the inverse root map algebra;
* no common numerator/denominator zero in the nondegenerate branch;
* image-of-complement constraints forced by two-variable zero-freeness.

Not closed here:
* the final Riemann-sphere/topological lemma that turns these local facts into
  `z ∈ -K₁K₂`;
* repeated contraction;
* Grace/Ruelle characterization.

No witness packets.
No `sorry`.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeStep

open Set
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
Variable-swap identity for the two-variable affine Asano polynomial.
-/
@[rep_depth operator]
theorem asanoPhi_swap_vars
    (A B C D z₁ z₂ : ℂ) :
    asanoPhi A B C D z₁ z₂ =
      asanoPhi A C B D z₂ z₁ := by
  unfold asanoPhi
  ring

/--
In the nondegenerate branch, numerator and denominator of the root map cannot
vanish simultaneously.
-/
@[rep_depth operator]
theorem asano_nondegenerate_no_common_num_den
    {A B C D z : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hden : C + D * z = 0) :
    A + B * z ≠ 0 := by
  intro hnum
  have hzero : A * D - B * C = 0 := by
    calc
      A * D - B * C
          = D * (A + B * z) - B * (C + D * z) := by
              ring
      _ = D * 0 - B * 0 := by
              rw [hnum, hden]
      _ = 0 := by
              ring
  exact hNondeg hzero

/--
Swapped version: in the inverse root map, numerator and denominator cannot
vanish simultaneously.
-/
@[rep_depth operator]
theorem asano_nondegenerate_no_common_num_den_swapped
    {A B C D w : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hden : B + D * w = 0) :
    A + C * w ≠ 0 := by
  have hNondeg' : A * D - C * B ≠ 0 := by
    intro h
    apply hNondeg
    calc
      A * D - B * C = A * D - C * B := by ring
      _ = 0 := h
  exact asano_nondegenerate_no_common_num_den
    (A := A) (B := C) (C := B) (D := D) (z := w)
    hNondeg' hden

/--
The root map is forced into `K₂` whenever the first coordinate lies outside
`K₁` and the denominator is nonzero.

This is a direct kernel proof from two-variable zero-freeness.
-/
@[rep_depth operator]
theorem asanoRootMap_mem_K₂_of_z₁_not_mem_K₁
    {K₁ K₂ : Set ℂ}
    {A B C D z₁ : ℂ}
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hz₁ : z₁ ∉ K₁)
    (hden : C + D * z₁ ≠ 0) :
    asanoRootMap A B C D z₁ ∈ K₂ := by
  by_contra hnot
  have hzero : asanoPhi A B C D z₁ (asanoRootMap A B C D z₁) = 0 :=
    asanoPhi_rootMap_zero hden
  exact (hPhi z₁ (asanoRootMap A B C D z₁) hz₁ hnot) hzero

/--
The inverse root map of the affine equation, solved for `z₁` in terms of `z₂`.
-/
@[rep_depth operator]
def asanoInvRootMap (A B C D w : ℂ) : ℂ :=
  -((A + C * w) / (B + D * w))

/--
The inverse root map also zeros the original Asano polynomial.
-/
@[rep_depth operator]
theorem asanoPhi_invRootMap_zero
    {A B C D w : ℂ}
    (hden : B + D * w ≠ 0) :
    asanoPhi A B C D (asanoInvRootMap A B C D w) w = 0 := by
  have hroot :
      asanoPhi A C B D w (asanoRootMap A C B D w) = 0 :=
    asanoPhi_rootMap_zero (A := A) (B := C) (C := B) (D := D)
      (z1 := w) hden
  have hroot' :
      asanoPhi A C B D w (asanoInvRootMap A B C D w) = 0 := by
    simpa [asanoInvRootMap, asanoRootMap] using hroot
  have hswap :
      asanoPhi A B C D (asanoInvRootMap A B C D w) w =
        asanoPhi A C B D w (asanoInvRootMap A B C D w) := by
    unfold asanoPhi
    ring
  rw [hswap]
  exact hroot'

/--
The inverse root map is forced into `K₁` whenever the second coordinate lies
outside `K₂` and the inverse denominator is nonzero.
-/
@[rep_depth operator]
theorem asanoInvRootMap_mem_K₁_of_z₂_not_mem_K₂
    {K₁ K₂ : Set ℂ}
    {A B C D w : ℂ}
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hw : w ∉ K₂)
    (hden : B + D * w ≠ 0) :
    asanoInvRootMap A B C D w ∈ K₁ := by
  by_contra hnot
  have hzero :
      asanoPhi A B C D (asanoInvRootMap A B C D w) w = 0 :=
    asanoPhi_invRootMap_zero hden
  exact (hPhi (asanoInvRootMap A B C D w) w hnot hw) hzero

/--
If `w` is the root map value of `z`, then the original polynomial vanishes.
-/
@[rep_depth operator]
theorem asanoPhi_zero_of_eq_rootMap
    {A B C D z w : ℂ}
    (hden : C + D * z ≠ 0)
    (hw : w = asanoRootMap A B C D z) :
    asanoPhi A B C D z w = 0 := by
  rw [hw]
  exact asanoPhi_rootMap_zero hden

/--
If `w = rootMap z`, then, assuming the inverse denominator is nonzero, `z` is
the inverse root map of `w`.
-/
@[rep_depth operator]
theorem z_eq_asanoInvRootMap_of_eq_rootMap
    {A B C D z w : ℂ}
    (hdenz : C + D * z ≠ 0)
    (hdenw : B + D * w ≠ 0)
    (hw : w = asanoRootMap A B C D z) :
    z = asanoInvRootMap A B C D w := by
  have hzero₁ : asanoPhi A B C D z w = 0 :=
    asanoPhi_zero_of_eq_rootMap hdenz hw
  have hzero₂ : asanoPhi A C B D w z = 0 := by
    simpa [asanoPhi_swap_vars] using hzero₁
  have hsol :
      z = asanoRootMap A C B D w :=
    z₂_eq_asanoRootMap_of_asanoPhi_eq_zero
      (A := A) (B := C) (C := B) (D := D)
      (z1 := w) (z2 := z) hdenw hzero₂
  simpa [asanoInvRootMap, asanoRootMap] using hsol

/--
If `w = rootMap z`, then, in the nondegenerate branch, the inverse denominator
is nonzero.
-/
@[rep_depth operator]
theorem inverse_den_ne_of_eq_rootMap_nondegenerate
    {A B C D z w : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hdenz : C + D * z ≠ 0)
    (hw : w = asanoRootMap A B C D z) :
    B + D * w ≠ 0 := by
  intro hdenw
  have hzero₁ : asanoPhi A B C D z w = 0 :=
    asanoPhi_zero_of_eq_rootMap hdenz hw
  have hzero₂ : asanoPhi A C B D w z = 0 := by
    simpa [asanoPhi_swap_vars] using hzero₁
  have hnumw : A + C * w = 0 := by
    have hlin : A + C * w + (B + D * w) * z = 0 := by
      calc
        A + C * w + (B + D * w) * z = asanoPhi A C B D w z := by
          unfold asanoPhi
          ring
        _ = 0 := hzero₂
    rw [hdenw] at hlin
    simpa using hlin
  exact
    (asano_nondegenerate_no_common_num_den_swapped
      (A := A) (B := B) (C := C) (D := D) (w := w)
      hNondeg hdenw) hnumw

/--
Nondegenerate root map is locally invertible on its natural domain.
-/
@[rep_depth operator]
theorem rootMap_left_inverse_nondegenerate
    {A B C D z : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hdenz : C + D * z ≠ 0) :
    asanoInvRootMap A B C D (asanoRootMap A B C D z) = z := by
  let w := asanoRootMap A B C D z
  have hw : w = asanoRootMap A B C D z := rfl
  have hdenw : B + D * w ≠ 0 :=
    inverse_den_ne_of_eq_rootMap_nondegenerate
      (A := A) (B := B) (C := C) (D := D)
      (z := z) (w := w) hNondeg hdenz hw
  have hzinv :
      z = asanoInvRootMap A B C D w :=
    z_eq_asanoInvRootMap_of_eq_rootMap
      (A := A) (B := B) (C := C) (D := D)
      (z := z) (w := w) hdenz hdenw hw
  exact hzinv.symm

/--
Nondegenerate inverse root map is locally inverted by the root map.
-/
@[rep_depth operator]
theorem invRootMap_left_inverse_nondegenerate
    {A B C D w : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hdenw : B + D * w ≠ 0) :
    asanoRootMap A B C D (asanoInvRootMap A B C D w) = w := by
  let z := asanoInvRootMap A B C D w
  have hzero : asanoPhi A B C D z w = 0 :=
    asanoPhi_invRootMap_zero (A := A) (B := B) (C := C) (D := D)
      (w := w) hdenw
  have hdenz : C + D * z ≠ 0 := by
    intro hdenz
    have hnumz : A + B * z = 0 := by
      have hlin : A + B * z + (C + D * z) * w = 0 := by
        calc
          A + B * z + (C + D * z) * w = asanoPhi A B C D z w := by
            unfold asanoPhi
            ring
          _ = 0 := hzero
      rw [hdenz] at hlin
      simpa using hlin
    exact
      (asano_nondegenerate_no_common_num_den
        (A := A) (B := B) (C := C) (D := D) (z := z)
        hNondeg hdenz) hnumz
  have hwsol :
      w = asanoRootMap A B C D z :=
    z₂_eq_asanoRootMap_of_asanoPhi_eq_zero
      (A := A) (B := B) (C := C) (D := D)
      (z1 := z) (z2 := w) hdenz hzero
  exact hwsol.symm

end InfoGeometry.Canonical.LeeYangAsanoNativeStep
