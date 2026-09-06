/-
InfoGeometry/Automorphic/ZetaPotentialSign.lean

Abstract arithmetic and Jordan potential barriers.

This module does not commit to Mathlib's concrete `riemannZeta`.
Instead it defines the interface needed to compare:

  Φ_J(X) = -log |N(X)|

with

  Φ_L(s) = -log |L(s)|.

A later bridge file can instantiate the arithmetic side using Mathlib's
`riemannZeta`, Dirichlet L-functions, or completed L-functions.
-/

import Mathlib.Tactic
import InfoGeometry.Automorphic.SiegelResonance

noncomputable section

namespace InfoGeometry.Automorphic.ZetaPotentialSign

universe uX uS

/-! ## 1. Geometric/Jordan barrier datum -/

/--
A positive Jordan norm/barrier datum.

The intended model is a cubic or determinant-like invariant `N(X)`, with
`jordanNorm X = |N(X)|` on the admissible region.
-/
structure JordanBarrierDatum (X : Type uX) where
  /-- Region where the logarithmic barrier is meaningful. -/
  admissible : X → Prop
  /-- Positive scalar norm/readout, morally `|N(X)|`. -/
  jordanNorm : X → ℝ
  /-- Strict positivity on the admissible region. -/
  jordanNorm_pos :
    ∀ x : X, admissible x → 0 < jordanNorm x

namespace JordanBarrierDatum

variable {X : Type uX}
variable (J : JordanBarrierDatum X)

/--
The geometric Jordan pseudo-barrier:

`Φ_J(X) = -log |N(X)|`.
-/
def potential (x : X) : ℝ :=
  - Real.log (J.jordanNorm x)

theorem potential_nonnegative_iff_norm_le_one
    {x : X} (hx : J.admissible x) :
    0 ≤ J.potential x ↔ J.jordanNorm x ≤ 1 := by
  have hpos : 0 < J.jordanNorm x := J.jordanNorm_pos x hx
  constructor
  · intro h
    change 0 ≤ -Real.log (J.jordanNorm x) at h
    by_contra hnot
    have hgt : 1 < J.jordanNorm x := lt_of_not_ge hnot
    have hlog : 0 < Real.log (J.jordanNorm x) := Real.log_pos hgt
    linarith
  · intro hle
    exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt hpos) hle)

@[simp]
theorem potential_eq_zero_of_norm_eq_one
    {x : X}
    (h : J.jordanNorm x = 1) :
    J.potential x = 0 := by
  simp [potential, h]

theorem potential_eq_zero_iff_norm_eq_one
    {x : X} (hx : J.admissible x) :
    J.potential x = 0 ↔ J.jordanNorm x = 1 := by
  have hpos : 0 < J.jordanNorm x := J.jordanNorm_pos x hx
  constructor
  · intro h
    have hlog : Real.log (J.jordanNorm x) = 0 := by
      simpa [potential] using neg_eq_zero.mp h
    rcases (Real.log_eq_zero).mp hlog with hzero | hone | hneg
    · exact (ne_of_gt hpos hzero).elim
    · exact hone
    · linarith
  · exact potential_eq_zero_of_norm_eq_one J

end JordanBarrierDatum

/-! ## 2. Abstract Euler/L-function barrier datum -/

/--
Abstract Euler-product or L-function datum.

This is deliberately not specialized to the Riemann zeta function. It can model
`ζ`, Dirichlet `L`-functions, completed `L`-functions, finite Euler products,
or regularized automorphic `L`-functions.
-/
structure EulerProductDatum (S : Type uS) where
  /-- Region where the logarithmic potential is meaningful. -/
  admissible : S → Prop
  /-- The complex-valued arithmetic function. -/
  value : S → ℂ
  /-- Positive real amplitude, usually `‖value s‖`. -/
  absValue : S → ℝ
  /-- Nonvanishing of the complex value on the admissible region. -/
  value_nonzero :
    ∀ s : S, admissible s → value s ≠ 0
  /-- Strict positivity of the amplitude on the admissible region. -/
  absValue_pos :
    ∀ s : S, admissible s → 0 < absValue s
  /-- Compatibility with the complex norm. -/
  absValue_eq_norm :
    ∀ s : S, admissible s → absValue s = ‖value s‖
  /--
  Local Euler factor readout.

  The input is an integer index; concrete instances may restrict this to primes
  using an additional predicate. No Euler-product law is implied by this
  field; such a law belongs to `HasEulerProduct`/`EulerProductData` below.
  -/
  localFactor : ℕ → S → ℂ

namespace EulerProductDatum

variable {S : Type uS}
variable (L : EulerProductDatum S)

/--
The arithmetic divisor barrier / prime surprisal potential:

`Φ_L(s) = -log |L(s)|`.
-/
def potential (s : S) : ℝ :=
  - Real.log (L.absValue s)

theorem potential_nonnegative_iff_absValue_le_one
    {s : S} (hs : L.admissible s) :
    0 ≤ L.potential s ↔ L.absValue s ≤ 1 := by
  have hpos : 0 < L.absValue s := L.absValue_pos s hs
  constructor
  · intro h
    change 0 ≤ -Real.log (L.absValue s) at h
    by_contra hnot
    have hgt : 1 < L.absValue s := lt_of_not_ge hnot
    have hlog : 0 < Real.log (L.absValue s) := Real.log_pos hgt
    linarith
  · intro hle
    exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt hpos) hle)

@[simp]
theorem potential_eq_zero_of_absValue_eq_one
    {s : S}
    (h : L.absValue s = 1) :
    L.potential s = 0 := by
  simp [potential, h]

theorem potential_eq_zero_iff_absValue_eq_one
    {s : S} (hs : L.admissible s) :
    L.potential s = 0 ↔ L.absValue s = 1 := by
  have hpos : 0 < L.absValue s := L.absValue_pos s hs
  constructor
  · intro h
    have hlog : Real.log (L.absValue s) = 0 := by
      simpa [potential] using neg_eq_zero.mp h
    rcases (Real.log_eq_zero).mp hlog with hzero | hone | hneg
    · exact (ne_of_gt hpos hzero).elim
    · exact hone
    · linarith
  · exact potential_eq_zero_of_absValue_eq_one L

end EulerProductDatum

/-! ## 3. Potential sign calibration -/

/--
Sign calibration for the arithmetic potential.

This should not be hard-coded as a theorem of every Euler-product datum. It
depends on the chosen normalization of `absValue`.
-/
structure PotentialSignCalibration
    {S : Type uS}
    (L : EulerProductDatum S) where
  /-- Nonnegative potential corresponds to amplitude at most one. -/
  potential_nonnegative_iff_absValue_le_one :
    ∀ s : S, L.admissible s →
      0 ≤ L.potential s ↔ L.absValue s ≤ 1
  /-- Zero potential corresponds to unit amplitude. -/
  potential_zero_iff_absValue_eq_one :
    ∀ s : S, L.admissible s →
      L.potential s = 0 ↔ L.absValue s = 1

/-! ## 4. Jordan/arithmetic correspondence -/

/--
A correspondence between a Jordan barrier and an arithmetic L-potential.

This is the formal version of the slogan

`Φ_J(X) = Φ_L(s)`

under a spectral/arithmetic map `X ↦ s`.
-/
structure ZetaJordanPotentialCorrespondence
    {X : Type uX}
    {S : Type uS}
    (J : JordanBarrierDatum X)
    (L : EulerProductDatum S) where
  /-- Spectral/arithmetic parameter extracted from a geometric state. -/
  toSpectral : X → S
  /-- Admissible Jordan states map to admissible arithmetic parameters. -/
  maps_admissible :
    ∀ x : X, J.admissible x → L.admissible (toSpectral x)
  /--
  The key amplitude matching law:

  `|L(s(X))| = |N(X)|`.
  -/
  norm_match :
    ∀ x : X, J.admissible x →
      L.absValue (toSpectral x) = J.jordanNorm x

namespace ZetaJordanPotentialCorrespondence

variable {X : Type uX}
variable {S : Type uS}
variable {J : JordanBarrierDatum X}
variable {L : EulerProductDatum S}

/--
The geometric and arithmetic potentials agree under the correspondence.
-/
theorem potentials_match
    (C : ZetaJordanPotentialCorrespondence J L)
    {x : X}
    (hx : J.admissible x) :
    L.potential (C.toSpectral x) = J.potential x := by
  simp [
    EulerProductDatum.potential,
    JordanBarrierDatum.potential,
    C.norm_match x hx
  ]

theorem potential_zero_iff
    (C : ZetaJordanPotentialCorrespondence J L)
    {x : X} (hx : J.admissible x) :
    L.potential (C.toSpectral x) = 0 ↔ J.potential x = 0 := by
  rw [C.potentials_match hx]

theorem potential_nonnegative_iff
    (C : ZetaJordanPotentialCorrespondence J L)
    {x : X} (hx : J.admissible x) :
    0 ≤ L.potential (C.toSpectral x) ↔ 0 ≤ J.potential x := by
  rw [C.potentials_match hx]

end ZetaJordanPotentialCorrespondence

/-! ## 5. Owner targets -/

end InfoGeometry.Automorphic.ZetaPotentialSign
