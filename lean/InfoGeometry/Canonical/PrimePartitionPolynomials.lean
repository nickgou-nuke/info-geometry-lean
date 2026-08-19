import InfoGeometry.Meta.Architecture
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

The Riemann/Mellin pullback is a separate property layer:

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
Multivariate Lee--Yang zero-free property.

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

The exponential estimates are stored as property fields so this bridge does not
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

/-- Canonical explicit realization of `RiemannFieldPullback` using complex exponential arithmetic. -/
noncomputable def canonicalRiemannFieldPullback (D : FinitePrimeChainData N) :
    RiemannFieldPullback D where
  field s := s - (1 / 2 : ℂ)
  localFugacity s i := Complex.exp (-(s - (1 / 2 : ℂ)) * (D.ell i : ℂ))
  re_pos_inner := by
    intro s hpos i
    change Complex.normSq (Complex.exp (-(s - (1 / 2 : ℂ)) * (D.ell i : ℂ))) < 1
    have h_re : (-(s - (1 / 2 : ℂ)) * (D.ell i : ℂ)).re = -(s - (1 / 2 : ℂ)).re * D.ell i := by
      simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
                 Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, h_re]
    have h_prod_neg : -(s - (1 / 2 : ℂ)).re * D.ell i < 0 := by
      have h1 : -(s - (1 / 2 : ℂ)).re < 0 := by linarith
      have h2 : 0 < D.ell i := D.ell_pos i
      nlinarith
    have hexp : Real.exp (-(s - (1 / 2 : ℂ)).re * D.ell i) < 1 := by
      have hlt : Real.exp (-(s - (1 / 2 : ℂ)).re * D.ell i) < Real.exp 0 :=
        Real.exp_lt_exp.mpr h_prod_neg
      rw [Real.exp_zero] at hlt
      exact hlt
    have hexp_pos : 0 ≤ Real.exp (-(s - (1 / 2 : ℂ)).re * D.ell i) := (Real.exp_pos _).le
    nlinarith
  re_neg_outer := by
    intro s hneg i
    change 1 < Complex.normSq (Complex.exp (-(s - (1 / 2 : ℂ)) * (D.ell i : ℂ)))
    have h_re : (-(s - (1 / 2 : ℂ)) * (D.ell i : ℂ)).re = -(s - (1 / 2 : ℂ)).re * D.ell i := by
      simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
                 Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, h_re]
    have h_prod_pos : 0 < -(s - (1 / 2 : ℂ)).re * D.ell i := by
      have h1 : 0 < -(s - (1 / 2 : ℂ)).re := by linarith
      have h2 : 0 < D.ell i := D.ell_pos i
      nlinarith
    have hexp : 1 < Real.exp (-(s - (1 / 2 : ℂ)).re * D.ell i) := by
      have hlt : Real.exp 0 < Real.exp (-(s - (1 / 2 : ℂ)).re * D.ell i) :=
        Real.exp_lt_exp.mpr h_prod_pos
      rw [Real.exp_zero] at hlt
      exact hlt
    nlinarith
  critical_of_field_re_zero := by
    intro s hzero
    have hre : (s - (1 / 2 : ℂ)).re = s.re - 1 / 2 := by
      simp only [Complex.sub_re]
      norm_num
    have hf : (s - (1 / 2 : ℂ)).re = 0 := hzero
    linarith

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
@[rep_depth thermo]
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
@[rep_depth thermo]
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

/-! ## One-site Lee--Yang closure -/

private theorem oneSite_hopfieldWeight_eq
    (D : FinitePrimeChainData 1)
    (lam : ℝ)
    (σ : SpinConfig 1) :
    hopfieldInteractionWeight D lam σ =
      hopfieldInteractionWeight D lam (fun _ => false) := by
  have hσ : σ 0 = true ∨ σ 0 = false := by
    cases h : σ 0 <;> simp [h]
  rcases hσ with hσ | hσ
  · have hfun : σ = (fun _ => true) := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact hσ
    subst σ
    simp [hopfieldInteractionWeight, centeredLogMagnetization, centeredBit,
      Fin.sum_univ_succ]
  · have hfun : σ = (fun _ => false) := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact hσ
    subst σ
    rfl

private theorem oneSite_configurationWeight_eq_one
    (D : FinitePrimeChainData 1)
    (lam : ℝ)
    (σ : SpinConfig 1) :
    configurationWeight D lam σ = 1 := by
  unfold configurationWeight interactionEnergy
  simp [D.spinCoupling_self, Fin.sum_univ_succ]

theorem oneSite_partitionPolynomial_eq
    (D : FinitePrimeChainData 1)
    (lam : ℝ) :
    partitionPolynomial D lam =
      Polynomial.X + 1 := by
  classical
  let e : (SpinConfig 1) ≃ Bool := Equiv.funUnique (Fin 1) Bool
  unfold partitionPolynomial
  calc
    (∑ σ : SpinConfig 1,
      Polynomial.C ((configurationWeight D lam σ : ℝ) : ℂ) *
        Polynomial.X ^ occupiedCount σ) =
        ∑ b : Bool, Polynomial.X ^ (if b then 1 else 0) := by
      apply Fintype.sum_equiv e
      intro σ
      have hweight := oneSite_configurationWeight_eq_one D lam σ
      have hocc : occupiedCount σ = if e σ then 1 else 0 := by
        by_cases h : σ 0 = true
        · have hfun : σ = (fun _ => true) := by
            funext i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            exact h
          subst σ
          simp [occupiedCount, e]
        · have h' : σ 0 = false := Bool.eq_false_of_not_eq_true h
          have hfun : σ = (fun _ => false) := by
            funext i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            exact h'
          subst σ
          simp [occupiedCount, e]
      rw [hweight, hocc]
      simp
    _ = Polynomial.X + 1 := by
      simp [Polynomial.C_mul, mul_add, add_mul, mul_one, one_mul]

theorem oneSite_partitionPolynomial_root_on_leeYangCircle
    (D : FinitePrimeChainData 1)
    (lam : ℝ)
    (z : ℂ)
    (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z := by
  have hpoly := oneSite_partitionPolynomial_eq D lam
  have hw :
      (1 : ℂ) ≠ 0 := by
    norm_num
  have hfactor :
      (1 : ℂ) * ((Polynomial.X + 1).eval z) = 0 := by
    rw [hpoly] at hz
    simpa [Polynomial.eval_mul] using hz
  have hlinear : (Polynomial.X + 1).eval z = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hw
  have hzneg : z = -1 := by
    have hlinear' : z + 1 = 0 := by
      simpa [Polynomial.eval_add, Polynomial.eval_X] using hlinear
    linear_combination hlinear'
  rw [hzneg]
  simp [OnUnitCircle, Complex.normSq]

/-! The one-site polynomial supplies a concrete finite Lee--Yang witness.
This closes only the `N = 1` case; the general Asano/Grace contraction remains
represented by `LeeYangPolynomialWitness` below. -/
theorem oneSite_leeYang_polynomial_witness
    (D : FinitePrimeChainData 1)
    {lam : ℝ}
    (_hLam : 0 ≤ lam)
    (z : ℂ)
    (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z := by
  exact oneSite_partitionPolynomial_root_on_leeYangCircle D lam z hz

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
Asano/Grace-style formalization can replace this property.
-/
@[rep_depth thermo]
def LeeYangPolynomialWitness : Prop :=
  ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
    0 ≤ lam →
      ∀ z : ℂ, (partitionPolynomial D lam).IsRoot z →
        OnUnitCircle z

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
polynomials and a Lee--Yang property.
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
    exact LY (F.D N) (F.lam_nonneg N) z (F.isRoot_of_Z_eq_zero N z hz)
  renorm_nonzero :=
    F.R_nonzero

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

@[rep_depth thermo]
theorem global_preserves_unit_circle_of_local
    {N : ℕ}
    {D : FinitePrimeChainData N}
    (W : LocalFugacityProjectionWitness N D)
    (z : ℂ)
    (hlocal : ∀ i : Fin N, OnUnitCircle (W.localFugacity i z)) :
    OnUnitCircle (W.globalFugacity z) := by
  classical
  rw [W.projection_eq_product z]
  exact onUnitCircle_finset_prod Finset.univ
    (fun i => W.localFugacity i z) (fun i _ => hlocal i)

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
