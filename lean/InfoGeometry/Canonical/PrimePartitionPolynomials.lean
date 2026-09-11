import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimeHurwitzLimit

/-!
# InfoGeometry.Canonical.PrimePartitionPolynomials

Finite prime-chain partition functions and the Lee--Yang interface.

This module bridges the finite ferromagnetic prime-chain Hamiltonian to the
Lee--Yang interface.

The key point is that the Lee--Yang theorem is multivariate before it is
single-variable.  We therefore construct the finite partition function as a
function of local fugacities

`y : Fin N → ℂ`

rather than using the non-polynomial expression `z^(log pᵢ)`.

The Riemann/Mellin pullback is a separate witness layer:

`yᵢ(s) = exp (-(s - 1/2) log pᵢ)`.

No RH theorem is asserted here.
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

/-! ## Multivariate local-fugacity readout -/

/-- Centered occupation bit: `true` is occupied/up, `false` is empty/down. -/
@[rep_depth thermo]
def centeredBit
    (b : Bool) : ℝ :=
  if b then (1 / 2 : ℝ) else -(1 / 2 : ℝ)

@[simp]
theorem centeredBit_true :
    centeredBit true = (1 / 2 : ℝ) := by
  simp [centeredBit]

@[simp]
theorem centeredBit_false :
    centeredBit false = -(1 / 2 : ℝ) := by
  simp [centeredBit]

/-- Centered logarithmic magnetization, odd under particle-hole reversal. -/
@[rep_depth thermo]
def centeredLogMagnetization
    (D : FinitePrimeChainData N)
    (k : SpinConfig N) : ℝ :=
  ∑ i : Fin N, D.ell i * centeredBit (k i)

/--
Ferromagnetic Hopfield/Curie--Weiss weight in occupation variables.

The Boltzmann exponent contains `+ λ A(k)^2`, equivalently the Hamiltonian
contains `- λ A(k)^2`.
-/
@[rep_depth thermo]
def hopfieldInteractionWeight
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (k : SpinConfig N) : ℝ :=
  Real.exp (lam * (centeredLogMagnetization D k)^2)

/-- Hopfield interaction weights are strictly positive. -/
@[rep_depth thermo]
theorem hopfieldInteractionWeight_pos
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (k : SpinConfig N) :
    0 < hopfieldInteractionWeight D lam k := by
  unfold hopfieldInteractionWeight
  exact Real.exp_pos _

/--
Multivariate finite prime-chain partition function.

`Z(y₁,...,y_N) = ∑ₖ W(k) ∏_{i : kᵢ = 1} yᵢ`.

This is multi-affine in the local fugacities `yᵢ` and avoids any expression of
the form `z^(log pᵢ)`.
-/
@[rep_depth thermo]
def multiPartition
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (y : Fin N → ℂ) : ℂ :=
  ∑ k : SpinConfig N,
    ((hopfieldInteractionWeight D lam k : ℝ) : ℂ) *
      ∏ i : Fin N, if k i then y i else 1

/--
Multivariate Lee--Yang zero-free witness.

Instead of asserting the full Asano/Ruelle contraction theorem in this file, we
store exactly the consequence needed:

* no zeros when all local fugacities are inside the unit disk;
* no zeros when all local fugacities are outside the unit disk.
-/
@[rep_depth thermo]
def LeeYangPolydiscWitness : Prop :=
  (∀ {N : ℕ}
    (D : FinitePrimeChainData N)
    (lam : ℝ),
    0 < lam →
    ∀ y : Fin N → ℂ,
      (∀ i : Fin N, InUnitDisk (y i)) →
      multiPartition D lam y ≠ 0) ∧
  (∀ {N : ℕ}
    (D : FinitePrimeChainData N)
    (lam : ℝ),
    0 < lam →
    ∀ y : Fin N → ℂ,
      (∀ i : Fin N, OutsideUnitDisk (y i)) →
      multiPartition D lam y ≠ 0)

/--
Pullback from the Riemann/Mellin variable into local Lee--Yang fugacities.

The intended concrete model is

`field s = s - 1/2` and
`localFugacity s i = exp (-(field s) * ellᵢ)`.

The exponential estimates are stored as witness fields so this bridge does not
accumulate complex-analysis proof debt.
-/
@[rep_depth thermo]
structure RiemannFieldPullback
    (D : FinitePrimeChainData N) where
  field :
    ℂ → ℂ
  localFugacity :
    ℂ → Fin N → ℂ
  /-- Right half-plane in the shifted field sends every local fugacity inside. -/
  re_pos_inner :
    ∀ s : ℂ, 0 < (field s).re →
      ∀ i : Fin N, InUnitDisk (localFugacity s i)
  /-- Left half-plane in the shifted field sends every local fugacity outside. -/
  re_neg_outer :
    ∀ s : ℂ, (field s).re < 0 →
      ∀ i : Fin N, OutsideUnitDisk (localFugacity s i)
  /-- The imaginary axis of the shifted field is the Riemann critical line. -/
  critical_of_field_re_zero :
    ∀ s : ℂ, (field s).re = 0 →
      s.re = (1 / 2 : ℝ)

/-- The pulled-back one-parameter partition function. -/
@[rep_depth thermo]
def pulledPartition
    (D : FinitePrimeChainData N)
    (lam : ℝ)
    (F : RiemannFieldPullback D)
    (s : ℂ) : ℂ :=
  multiPartition D lam (F.localFugacity s)

/--
Lee--Yang zero-free theorem after Riemann pullback.

If the pulled partition function vanishes, the shifted field must lie on the
imaginary axis.
-/
@[bridge_target_tag, rep_depth thermo]
theorem zero_implies_field_re_zero
    (D : FinitePrimeChainData N)
    (LY : LeeYangPolydiscWitness)
    (lam : ℝ)
    (hLam : 0 < lam)
    (F : RiemannFieldPullback D)
    (s : ℂ)
    (hz : pulledPartition D lam F s = 0) :
    (F.field s).re = 0 := by
  by_cases hneg : (F.field s).re < 0
  · have hzne : multiPartition D lam (F.localFugacity s) ≠ 0 :=
      LY.2 D lam hLam (F.localFugacity s) (F.re_neg_outer s hneg)
    exact False.elim (hzne (by simpa [pulledPartition] using hz))
  · by_cases hpos : 0 < (F.field s).re
    · have hzne : multiPartition D lam (F.localFugacity s) ≠ 0 :=
        LY.1 D lam hLam (F.localFugacity s) (F.re_pos_inner s hpos)
      exact False.elim (hzne (by simpa [pulledPartition] using hz))
    · linarith

/-- Under the supplied pullback chart, a zero of the finite pulled partition has
real coordinate `1/2`.  This is a chart-local Lee--Yang readout, not a theorem
about Riemann zeta zeros. -/
@[bridge_target_tag, rep_depth thermo]
theorem zero_implies_critical_line
    (D : FinitePrimeChainData N)
    (LY : LeeYangPolydiscWitness)
    (lam : ℝ)
    (hLam : 0 < lam)
    (F : RiemannFieldPullback D)
    (s : ℂ)
    (hz : pulledPartition D lam F s = 0) :
    s.re = (1 / 2 : ℝ) :=
  F.critical_of_field_re_zero s
    (zero_implies_field_re_zero D LY lam hLam F s hz)

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
def LeeYangPolynomialWitness : Prop :=
  ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
    0 ≤ lam →
      ∀ z : ℂ, (partitionPolynomial D lam).IsRoot z →
        OnUnitCircle z

namespace LeeYangPolynomialWitness

/-- Re-export of the supplied Lee--Yang circle law for a finite prime chain. -/
@[bridge_target_tag, rep_depth thermo]
theorem roots_on_circle
    (LY : LeeYangPolynomialWitness)
    (D : FinitePrimeChainData N)
    {lam : ℝ}
    (hLam : 0 ≤ lam)
    (z : ℂ)
    (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z :=
  LY D hLam z hz

end LeeYangPolynomialWitness

/--
Finite-volume prime-chain family feeding the Hurwitz layer.

This is the coarse polynomial projection lane.  The generalized arithmetic
fugacity lane is represented by `multiPartition` and `RiemannFieldPullback`.
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
    exact LeeYangPolynomialWitness.roots_on_circle LY (F.D N) (F.lam_nonneg N) z
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
  projection_eq_product :
    ∀ z : ℂ, globalFugacity z = ∏ i : Fin N, localFugacity i z
  preserves_unit_circle :
    ∀ z : ℂ, OnUnitCircle z →
      OnUnitCircle (globalFugacity z) ∧
        ∀ i : Fin N, OnUnitCircle (localFugacity i z)

namespace LocalFugacityProjectionWitness

/-- Re-export of the supplied local-to-global projection law. -/
@[rep_depth thermo]
theorem projection_eq_product_holds
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D)
    (z : ℂ) :
    W.globalFugacity z = ∏ i : Fin N, W.localFugacity i z :=
  W.projection_eq_product z

/-- Re-export of the supplied unit-circle preservation law. -/
@[rep_depth thermo]
theorem global_preserves_unit_circle
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D)
    (z : ℂ)
    (hz : OnUnitCircle z) :
    OnUnitCircle (W.globalFugacity z) :=
  (W.preserves_unit_circle z hz).1

/-- The supplied unit-circle preservation law holds. -/
@[rep_depth thermo]
theorem local_preserves_unit_circle
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D)
    (z : ℂ)
    (hz : OnUnitCircle z)
    (i : Fin N) :
    OnUnitCircle (W.localFugacity i z) :=
  (W.preserves_unit_circle z hz).2 i

end LocalFugacityProjectionWitness

end InfoGeometry.Canonical.PrimePartitionPolynomials
