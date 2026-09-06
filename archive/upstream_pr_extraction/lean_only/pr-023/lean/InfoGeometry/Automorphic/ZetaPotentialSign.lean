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

import Mathlib
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

@[simp]
theorem potential_eq_zero_of_norm_eq_one
    {x : X}
    (h : J.jordanNorm x = 1) :
    J.potential x = 0 := by
  simp [potential, h]

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
  Local Euler factor placeholder.

  The input is an integer index; concrete instances may restrict this to primes
  using an additional predicate.
  -/
  localFactor : ℕ → S → ℂ
  /--
  The product/Dirichlet-series law.

  This is intentionally a `Prop` field, because convergence domains and
  regularization choices differ between zeta, Dirichlet `L`-functions, and
  automorphic `L`-functions.
  -/
  eulerProductLaw : Prop

namespace EulerProductDatum

variable {S : Type uS}
variable (L : EulerProductDatum S)

/--
The arithmetic divisor barrier / prime surprisal potential:

`Φ_L(s) = -log |L(s)|`.
-/
def potential (s : S) : ℝ :=
  - Real.log (L.absValue s)

@[simp]
theorem potential_eq_zero_of_absValue_eq_one
    {s : S}
    (h : L.absValue s = 1) :
    L.potential s = 0 := by
  simp [potential, h]

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

end ZetaJordanPotentialCorrespondence

/-! ## 5. Owner targets -/

/--
Owner target for constructing a calibrated arithmetic zeta/L-potential.
-/
def ArithmeticPotentialOwnerTarget
    (S : Type uS) : Prop :=
  ∃ L : EulerProductDatum S,
    Nonempty (PotentialSignCalibration L)

/--
Owner target for matching a geometric Jordan barrier to an arithmetic
Euler/L-function potential.
-/
def ZetaJordanCorrespondenceOwnerTarget
    (X : Type uX)
    (S : Type uS) : Prop :=
  ∃ (J : JordanBarrierDatum X)
    (L : EulerProductDatum S),
      Nonempty (ZetaJordanPotentialCorrespondence J L)

end InfoGeometry.Automorphic.ZetaPotentialSign
