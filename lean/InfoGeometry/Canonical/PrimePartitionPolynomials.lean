import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimeHurwitzLimit

/-!
# InfoGeometry.Canonical.PrimePartitionPolynomials

Finite prime-chain partition functions.

This module bridges the finite ferromagnetic prime-chain Hamiltonian to the
Lee--Yang interface used by `PrimeHurwitzLimit`.

The arithmetic local fugacities have logarithmic weights, so the natural
finite readout is a generalized Dirichlet/quasi-polynomial in the shifted
complex field `w`, not an ordinary polynomial in one variable.  The ordinary
polynomial projection is still available below as a coarse global fugacity
readout, but the Hurwitz handoff uses the generalized Lee--Yang witness.

The generalized Lee--Yang theorem remains a witness.  This file proves the
algebraic handoff: once that witness and the chosen Cayley/global projection are
supplied, the finite prime-chain partition functions yield the
`LeeYangApproximants` required by the Hurwitz limit layer.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimePartitionPolynomials

open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeHurwitzLimit

variable {N : ℕ}

/-- Spin configurations for a finite prime chain. `true` is the occupied/up state. -/
@[rep_depth thermo]
abbrev SpinConfig
    (N : ℕ) :=
  Fin N → Bool

/-- Real Ising sign readout for Boolean spins. -/
@[rep_depth thermo]
def spinSign
    (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp]
theorem spinSign_true :
    spinSign true = 1 := by
  simp [spinSign]

@[simp]
theorem spinSign_false :
    spinSign false = -1 := by
  simp [spinSign]

/-- Number of occupied/up spins, used as the global fugacity exponent. -/
@[rep_depth thermo]
def occupiedCount
    (σ : SpinConfig N) : ℕ :=
  ∑ i : Fin N, if σ i then 1 else 0

/--
Interaction energy readout in the ferromagnetic Ising convention.

This keeps only the interaction part. External-field/fugacity data are
introduced by the polynomial exponent.
-/
@[rep_depth thermo]
def interactionEnergy
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (σ : SpinConfig N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    D.spinCoupling lam i j * spinSign (σ i) * spinSign (σ j)

/-- Boltzmann weight of a spin configuration, using the interaction readout. -/
@[rep_depth thermo]
def configurationWeight
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (σ : SpinConfig N) : ℝ :=
  Real.exp (interactionEnergy D lam σ)

/-- Configuration weights are strictly positive. -/
@[rep_depth thermo]
theorem configurationWeight_pos
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (σ : SpinConfig N) :
    0 < configurationWeight D lam σ := by
  unfold configurationWeight
  exact Real.exp_pos _

/-! ## Generalized arithmetic fugacity readout -/

/-- Weighted spin sum controlling the arithmetic external field. -/
@[rep_depth thermo]
def weightedSpinSum
    (D : FinitePrimeChainData N)
    (σ : SpinConfig N) : ℝ :=
  ∑ i : Fin N, D.ell i * spinSign (σ i)

/--
Generalized finite partition function in the shifted field `w`.

The local arithmetic fugacity is encoded through
`exp((w / 2) * ∑ᵢ ellᵢ σᵢ)`.  Since the `ellᵢ = log pᵢ` are real weights, this
is not represented as a natural-power polynomial in one global variable.
-/
@[rep_depth thermo]
def generalizedPartitionFunction
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (w : ℂ) : ℂ :=
  ∑ σ : SpinConfig N,
    ((configurationWeight D lam σ : ℝ) : ℂ) *
      Complex.exp ((((weightedSpinSum D σ : ℝ) : ℂ) * w) / 2)

/--
Witness for the generalized Lee--Yang theorem in the arithmetic weighted-field
coordinate.

For the prime-chain application, a zero of the generalized partition function
forces the shifted field to lie on the imaginary axis, `w.re = 0`.  The
Asano/Grace/Suzuki--Fisher proof is deliberately not reimplemented here.
-/
@[rep_depth thermo]
structure GeneralizedLeeYangWitness where
  imaginary_axis_theorem :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
      0 < lam →
        ∀ w : ℂ, generalizedPartitionFunction D lam w = 0 →
          w.re = 0

namespace GeneralizedLeeYangWitness

/-- Re-export of the supplied generalized Lee--Yang axis law. -/
@[rep_depth thermo]
theorem zeros_on_imaginary_axis
    (GLY : GeneralizedLeeYangWitness)
    (D : FinitePrimeChainData N)
    {lam : ℝ}
    (hLam : 0 < lam)
    (w : ℂ)
    (hz : generalizedPartitionFunction D lam w = 0) :
    w.re = 0 :=
  GLY.imaginary_axis_theorem D hLam w hz

end GeneralizedLeeYangWitness

/--
Projection witness from a global Hurwitz/Cayley coordinate `z` to the shifted
arithmetic field `w`.

This is where the chosen coordinate chart records that `w.re = 0` maps to the
Lee--Yang unit circle in the `z` variable consumed by `PrimeHurwitzLimit`.
-/
@[rep_depth thermo]
structure GeneralizedLeeYangProjectionWitness where
  wOfZ : ℂ → ℂ
  imaginary_axis_to_unit :
    ∀ z : ℂ, (wOfZ z).re = 0 → OnUnitCircle z

/--
Finite-volume generalized prime-chain family feeding the Hurwitz layer.

`D N` supplies the finite prime chain, `lam N` its positive coupling scale, `P`
the projection from Hurwitz coordinate to shifted field, and `R` a nonvanishing
renormalization readout.
-/
@[rep_depth thermo]
structure GeneralizedPrimePartitionFamily where
  D :
    (N : ℕ) → FinitePrimeChainData N
  lam :
    ℕ → ℝ
  lam_pos :
    ∀ N : ℕ, 0 < lam N
  projection :
    GeneralizedLeeYangProjectionWitness
  R :
    ℕ → ℂ → ℂ
  R_nonzero :
    ∀ N : ℕ, ∀ z : ℂ, R N z ≠ 0

namespace GeneralizedPrimePartitionFamily

/-- Generalized finite partition-function readout in the Hurwitz coordinate. -/
@[rep_depth thermo]
def Z
    (F : GeneralizedPrimePartitionFamily)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  generalizedPartitionFunction (F.D N) (F.lam N) (F.projection.wOfZ z)

/--
Construct the Hurwitz approximant family from generalized finite prime
partition functions and a generalized Lee--Yang witness.
-/
@[rep_depth thermo]
def toLeeYangApproximants
    (F : GeneralizedPrimePartitionFamily)
    (GLY : GeneralizedLeeYangWitness) :
    LeeYangApproximants where
  Z := F.Z
  R := F.R
  lee_yang := by
    intro N z hz
    have hAxis :
        (F.projection.wOfZ z).re = 0 :=
      GLY.zeros_on_imaginary_axis (F.D N) (F.lam_pos N)
        (F.projection.wOfZ z) hz
    exact F.projection.imaginary_axis_to_unit z hAxis
  renorm_nonzero :=
    F.R_nonzero

/-- The constructed approximants preserve the family renormalization. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_R
    (F : GeneralizedPrimePartitionFamily)
    (GLY : GeneralizedLeeYangWitness) :
    (F.toLeeYangApproximants GLY).R = F.R := rfl

/-- The constructed approximants use the generalized partition readout. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_Z
    (F : GeneralizedPrimePartitionFamily)
    (GLY : GeneralizedLeeYangWitness)
    (N : ℕ)
    (z : ℂ) :
    (F.toLeeYangApproximants GLY).Z N z =
      generalizedPartitionFunction (F.D N) (F.lam N) (F.projection.wOfZ z) := rfl

/-- The constructed Hurwitz approximants satisfy the finite Lee--Yang law. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_leeYang
    (F : GeneralizedPrimePartitionFamily)
    (GLY : GeneralizedLeeYangWitness)
    (N : ℕ)
    (z : ℂ)
    (hz : (F.toLeeYangApproximants GLY).Z N z = 0) :
    OnUnitCircle z :=
  (F.toLeeYangApproximants GLY).lee_yang N z hz

end GeneralizedPrimePartitionFamily

/-! ## Coarse ordinary-polynomial projection -/

/--
Finite global-fugacity Lee--Yang partition polynomial.

This is a coarse ordinary polynomial projection.  It is useful for interfaces
that require `Polynomial ℂ`, but the arithmetic weighted fugacity lane above is
the honest prime-chain readout.
-/
@[rep_depth thermo]
def partitionPolynomial
    (D : FinitePrimeChainData N)
    (lam : ℝ) : Polynomial ℂ :=
  ∑ σ : SpinConfig N,
    Polynomial.C ((configurationWeight D lam σ : ℝ) : ℂ) *
      Polynomial.X ^ occupiedCount σ

/-- The corresponding partition function is polynomial evaluation. -/
@[rep_depth thermo]
def partitionFunction
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (z : ℂ) : ℂ :=
  (partitionPolynomial D lam).eval z

/-- The partition function is evaluation of the partition polynomial. -/
@[rep_depth thermo]
theorem partitionFunction_eq_eval
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (z : ℂ) :
    partitionFunction D lam z = (partitionPolynomial D lam).eval z := rfl

/--
Witness for the finite Lee--Yang theorem applied to the prime-chain partition
polynomial.

The ordinary polynomial Lee--Yang theorem is not proved here. A later
Asano/Grace-style formalization can replace this witness.
-/
@[rep_depth thermo]
structure LeeYangPolynomialWitness where
  circle_theorem :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
      0 ≤ lam →
        ∀ z : ℂ, (partitionPolynomial D lam).IsRoot z →
          OnUnitCircle z

namespace LeeYangPolynomialWitness

/-- Re-export of the supplied Lee--Yang circle law for a finite prime chain. -/
@[rep_depth thermo]
theorem roots_on_circle
    (LY : LeeYangPolynomialWitness)
    (D : FinitePrimeChainData N)
    {lam : ℝ}
    (hLam : 0 ≤ lam)
    (z : ℂ)
    (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z :=
  LY.circle_theorem D hLam z hz

end LeeYangPolynomialWitness

/--
Finite-volume prime-chain family feeding the Hurwitz layer.

This is the coarse polynomial projection lane.  The generalized arithmetic
fugacity lane is represented by `GeneralizedPrimePartitionFamily`.
-/
@[rep_depth thermo]
structure PrimePartitionPolynomialFamily where
  D :
    (N : ℕ) → FinitePrimeChainData N
  lam :
    ℕ → ℝ
  lam_nonneg :
    ∀ N : ℕ, 0 ≤ lam N
  R :
    ℕ → ℂ → ℂ
  R_nonzero :
    ∀ N : ℕ, ∀ z : ℂ, R N z ≠ 0

namespace PrimePartitionPolynomialFamily

/-- Polynomial at finite volume `N`. -/
@[rep_depth thermo]
def Zpoly
    (F : PrimePartitionPolynomialFamily)
    (N : ℕ) : Polynomial ℂ :=
  partitionPolynomial (F.D N) (F.lam N)

/-- Function readout at finite volume `N`. -/
@[rep_depth thermo]
def Z
    (F : PrimePartitionPolynomialFamily)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (F.Zpoly N).eval z

/-- Root of the function readout is root of the polynomial readout. -/
@[rep_depth thermo]
theorem isRoot_of_Z_eq_zero
    (F : PrimePartitionPolynomialFamily)
    (N : ℕ)
    (z : ℂ)
    (hz : F.Z N z = 0) :
    (F.Zpoly N).IsRoot z := by
  exact hz

/--
Construct the Hurwitz approximant family from finite prime partition
polynomials and a Lee--Yang witness.
-/
@[rep_depth thermo]
def toLeeYangApproximants
    (F : PrimePartitionPolynomialFamily)
    (LY : LeeYangPolynomialWitness) :
    LeeYangApproximants where
  Z := F.Z
  R := F.R
  lee_yang := by
    intro N z hz
    exact LY.roots_on_circle (F.D N) (F.lam_nonneg N) z
      (F.isRoot_of_Z_eq_zero N z hz)
  renorm_nonzero :=
    F.R_nonzero

/-- The constructed approximants preserve the family renormalization. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_R
    (F : PrimePartitionPolynomialFamily)
    (LY : LeeYangPolynomialWitness) :
    (F.toLeeYangApproximants LY).R = F.R := rfl

/-- The constructed approximants use the partition-polynomial evaluation. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_Z
    (F : PrimePartitionPolynomialFamily)
    (LY : LeeYangPolynomialWitness)
    (N : ℕ)
    (z : ℂ) :
    (F.toLeeYangApproximants LY).Z N z = (F.Zpoly N).eval z := rfl

/-- The constructed Hurwitz approximants satisfy the finite Lee--Yang law. -/
@[rep_depth thermo]
theorem toLeeYangApproximants_leeYang
    (F : PrimePartitionPolynomialFamily)
    (LY : LeeYangPolynomialWitness)
    (N : ℕ)
    (z : ℂ)
    (hz : (F.toLeeYangApproximants LY).Z N z = 0) :
    OnUnitCircle z :=
  (F.toLeeYangApproximants LY).lee_yang N z hz

end PrimePartitionPolynomialFamily

/--
Witness for matching a global fugacity polynomial to a more refined local
arithmetic fugacity model.

This is where a later file can state and prove how local readouts such as
`pᵢ^{-(s-1/2)}` are projected to a one-variable Lee--Yang fugacity.
-/
@[rep_depth thermo]
structure LocalFugacityProjectionWitness
    (N : ℕ)
    (D : FinitePrimeChainData N) where
  localFugacity :
    Fin N → ℂ → ℂ
  globalFugacity :
    ℂ → ℂ
  projection_law : Prop
  projection_certificate :
    projection_law
  preserves_unit_circle_law : Prop
  preserves_unit_circle_certificate :
    preserves_unit_circle_law

namespace LocalFugacityProjectionWitness

/-- Re-export of the supplied local-to-global projection law. -/
@[rep_depth thermo]
theorem projection
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D) :
    W.projection_law :=
  W.projection_certificate

/-- Re-export of the supplied unit-circle preservation law. -/
@[rep_depth thermo]
theorem preserves_unit_circle
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D) :
    W.preserves_unit_circle_law :=
  W.preserves_unit_circle_certificate

end LocalFugacityProjectionWitness

end InfoGeometry.Canonical.PrimePartitionPolynomials
