/-
InfoGeometry/Geometry/SpectralDivisors.lean

Spectral divisors, residues, winding charges, and topological index readouts.

This module keeps analytic residue extraction proof-bearing:

* inverse branches carry left/right inverse proofs;
* phase normalizers carry injectivity of the integer period lattice;
* winding is a region-dependent readout;
* divisor charge is computed from an explicit finite divisor counter;
* index is tied directly to the winding datum, hence to the boundary residue.
-/

import Mathlib
import InfoGeometry.Geometry.BilingualAnalyticity

noncomputable section

namespace InfoGeometry.Geometry.SpectralDivisors

open InfoGeometry.Geometry.BilingualAnalyticity

/-! ## 1. Spectral divisors -/

/-- A point is a spectral divisor of `F` when `F z` is not invertible. -/
def IsSpectralDivisor
    {Point Value : Type*}
    [Monoid Value]
    (F : Point → Value)
    (z : Point) : Prop :=
  ¬ IsUnit (F z)

/-! ## 1A. Divisors from noncommutative Cauchy kernels -/

/--
A kernel spectral divisor is an admissibility failure of the noncommutative
Cauchy kernel.

This is the resolvent-pole language: the pair `(ζ,z)` lies on the spectral
divisor exactly when the supplied kernel is not admissible there.
-/
def IsKernelSpectralDivisor
    {Param Point Value : Type*}
    [Ring Value]
    (K : NoncommutativeCauchyKernel Param Point Value)
    (ζ : Param)
    (z : Point) : Prop :=
  ¬ K.IsAdmissible ζ z

/-- The difference function associated to a Cauchy kernel. -/
def kernelDiffFunction
    {Param Point Value : Type*}
    [Ring Value]
    (K : NoncommutativeCauchyKernel Param Point Value) :
    Param × Point → Value :=
  fun p => K.diff p.1 p.2

namespace NoncommutativeCauchyKernel

variable {Param Point Value : Type*} [Ring Value]
variable (K : NoncommutativeCauchyKernel Param Point Value)

/--
On admissible pairs, the kernel proves that the difference element is a unit.
-/
theorem isUnit_diff_of_admissible
    {ζ : Param}
    {z : Point}
    (h : K.IsAdmissible ζ z) :
    IsUnit (K.diff ζ z) := by
  refine
    ⟨
      { val := K.diff ζ z
        inv := K.kernel ζ z
        val_inv := K.left_inverse ζ z h
        inv_val := K.right_inverse ζ z h },
      rfl
    ⟩

/-- Admissible pairs are not kernel spectral divisors. -/
theorem not_kernelSpectralDivisor_of_admissible
    {ζ : Param}
    {z : Point}
    (h : K.IsAdmissible ζ z) :
    ¬ IsKernelSpectralDivisor K ζ z := by
  intro hdiv
  exact hdiv h

/-- Being off the kernel divisor is exactly admissibility. -/
theorem admissible_of_not_kernelSpectralDivisor
    {ζ : Param}
    {z : Point}
    (h : ¬ IsKernelSpectralDivisor K ζ z) :
    K.IsAdmissible ζ z := by
  by_contra hadm
  exact h hadm

/-- Off the kernel divisor, the difference times the kernel is `1`. -/
theorem diff_mul_kernel_of_not_kernelSpectralDivisor
    {ζ : Param}
    {z : Point}
    (h : ¬ IsKernelSpectralDivisor K ζ z) :
    K.diff ζ z * K.kernel ζ z = 1 :=
  K.left_inverse ζ z (admissible_of_not_kernelSpectralDivisor K h)

/-- Off the kernel divisor, the kernel times the difference is `1`. -/
theorem kernel_mul_diff_of_not_kernelSpectralDivisor
    {ζ : Param}
    {z : Point}
    (h : ¬ IsKernelSpectralDivisor K ζ z) :
    K.kernel ζ z * K.diff ζ z = 1 :=
  K.right_inverse ζ z (admissible_of_not_kernelSpectralDivisor K h)

/--
Admissible pairs are not spectral divisors of the kernel difference function.
-/
theorem not_spectralDivisor_kernelDiff_of_admissible
    {ζ : Param}
    {z : Point}
    (h : K.IsAdmissible ζ z) :
    ¬ IsSpectralDivisor (kernelDiffFunction K) (ζ, z) := by
  intro hdiv
  exact hdiv (isUnit_diff_of_admissible K h)

/--
If the kernel difference is a spectral divisor, then the pair is a kernel
spectral divisor.
-/
theorem kernelSpectralDivisor_of_spectralDivisor_kernelDiff
    {ζ : Param}
    {z : Point}
    (h : IsSpectralDivisor (kernelDiffFunction K) (ζ, z)) :
    IsKernelSpectralDivisor K ζ z := by
  intro hadm
  exact h (isUnit_diff_of_admissible K hadm)

end NoncommutativeCauchyKernel

/--
Completeness certificate for a noncommutative Cauchy kernel.

The kernel itself proves `admissible → invertible difference`.  This extra
certificate is exactly the converse: every invertible difference lies in the
admissible resolvent domain.  Only with this certificate do admissibility
failure and ordinary spectral-divisor failure coincide.
-/
structure KernelAdmissibilityComplete
    {Param Point Value : Type*}
    [Ring Value]
    (K : NoncommutativeCauchyKernel Param Point Value) where
  /-- Invertibility of the difference implies admissibility of the kernel. -/
  admissible_of_isUnit_diff :
    ∀ ζ z,
      IsUnit (K.diff ζ z) →
        K.IsAdmissible ζ z

namespace KernelAdmissibilityComplete

variable {Param Point Value : Type*} [Ring Value]
variable {K : NoncommutativeCauchyKernel Param Point Value}

/--
With a completeness certificate, kernel spectral divisors are exactly spectral
divisors of the difference function.
-/
theorem kernelSpectralDivisor_iff_spectralDivisor_kernelDiff
    (complete : KernelAdmissibilityComplete K)
    (ζ : Param)
    (z : Point) :
    IsKernelSpectralDivisor K ζ z
      ↔ IsSpectralDivisor (kernelDiffFunction K) (ζ, z) := by
  constructor
  · intro hdiv hunit
    rcases complete with ⟨hcomplete⟩
    exact hdiv (hcomplete ζ z hunit)
  · intro hdiv hadm
    apply hdiv
    refine
      ⟨
        { val := K.diff ζ z
          inv := K.kernel ζ z
          val_inv := K.left_inverse ζ z hadm
          inv_val := K.right_inverse ζ z hadm },
        rfl
      ⟩

/--
Off the ordinary spectral divisor of the difference function, the kernel pair
is admissible.
-/
theorem admissible_of_not_spectralDivisor_kernelDiff
    (complete : KernelAdmissibilityComplete K)
    {ζ : Param}
    {z : Point}
    (h : ¬ IsSpectralDivisor (kernelDiffFunction K) (ζ, z)) :
    K.IsAdmissible ζ z := by
  rcases complete with ⟨hcomplete⟩
  apply hcomplete
  by_contra hunit
  exact h hunit

end KernelAdmissibilityComplete

/--
Spectral divisor data.

`multiplicity z` is the local integer multiplicity / divisor order.
-/
structure SpectralDivisorDatum
    (Point Value : Type*)
    [Monoid Value] where
  /-- The spectral function/operator family. -/
  F : Point → Value
  /-- Local divisor multiplicity. -/
  multiplicity : Point → ℤ
  /-- Off the divisor locus, multiplicity is zero. -/
  multiplicity_zero_off_divisor :
    ∀ z : Point,
      ¬ IsSpectralDivisor F z →
        multiplicity z = 0

namespace SpectralDivisorDatum

variable {Point Value : Type*}
variable [Monoid Value]
variable (D : SpectralDivisorDatum Point Value)

/-- The divisor locus of the spectral datum. -/
def divisorLocus : Set Point :=
  {z : Point | IsSpectralDivisor D.F z}

/-- If a point is outside the divisor locus, its multiplicity is zero. -/
theorem multiplicity_eq_zero_of_not_mem_divisorLocus
    {z : Point}
    (hz : z ∉ D.divisorLocus) :
    D.multiplicity z = 0 :=
  D.multiplicity_zero_off_divisor z
    (by
      simpa [divisorLocus] using hz)

end SpectralDivisorDatum

/-! ## 2. Logarithmic derivative forms -/

/--
Logarithmic derivative data for an invertible branch of a function.

The inverse branch carries left and right inverse proofs.
-/
structure LogDerivativeDatum
    {X Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [Ring Value] [Algebra ℝ Value]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Value)
    (F : X → Value) where
  /-- Local inverse branch of `F`. -/
  invF : X → Value
  /-- Pointwise Cauchy/phase analyticity of `F`. -/
  analytic :
    ∀ x : X, CauchyAnalyticAt Kdom Ktar F x
  /-- Left inverse branch law: `F⁻¹ F = 1`. -/
  left_inverse_branch :
    ∀ x : X, invF x * F x = 1
  /-- Right inverse branch law: `F F⁻¹ = 1`. -/
  right_inverse_branch :
    ∀ x : X, F x * invF x = 1

namespace LogDerivativeDatum

variable
    {X Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [Ring Value] [Algebra ℝ Value]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Value}
    {F : X → Value}

variable (L : LogDerivativeDatum Kdom Ktar F)

/-- The inverse branch proves that `F x` is a unit. -/
theorem isUnit_F
    (L : LogDerivativeDatum Kdom Ktar F)
    (x : X) :
    IsUnit (F x) := by
  rcases L with ⟨invF, _analytic, left_inverse_branch, right_inverse_branch⟩
  refine
    ⟨
      { val := F x
        inv := invF x
        val_inv := right_inverse_branch x
        inv_val := left_inverse_branch x },
      rfl
    ⟩

/-- An invertible branch excludes spectral divisors. -/
theorem not_spectralDivisor_F
    (L : LogDerivativeDatum Kdom Ktar F)
    (x : X) :
    ¬ IsSpectralDivisor F x := by
  intro h
  exact h (isUnit_F L x)

/--
A divisor datum whose function is this branch has zero multiplicity at every
point of the branch.
-/
theorem multiplicity_zero_for_branch
    (L : LogDerivativeDatum Kdom Ktar F)
    (D : SpectralDivisorDatum X Value)
    (hD : D.F = F)
    (x : X) :
    D.multiplicity x = 0 := by
  apply D.multiplicity_zero_off_divisor x
  intro hdiv
  exact not_spectralDivisor_F L x
    (by
      simpa [hD] using hdiv)

/-- Left logarithmic derivative form: `F⁻¹ dF`. -/
def leftLogDerivativeForm :
    LogDerivativeDatum Kdom Ktar F →
    OperatorOneForm X X Value :=
  fun L =>
  fun x v =>
    match L with
    | ⟨invF, analytic, _left_inverse_branch, _right_inverse_branch⟩ =>
        invF x * (analytic x).deriv v

/-- Right logarithmic derivative form: `dF F⁻¹`. -/
def rightLogDerivativeForm :
    LogDerivativeDatum Kdom Ktar F →
    OperatorOneForm X X Value :=
  fun L =>
  fun x v =>
    match L with
    | ⟨invF, analytic, _left_inverse_branch, _right_inverse_branch⟩ =>
        (analytic x).deriv v * invF x

end LogDerivativeDatum

/-! ## 3. Phase-period normalizer -/

/--
A phase-period normalizer for residue extraction.

The constructive field is faithfulness of the integer period lattice:
`n ↦ n • phasePeriod`.
-/
structure PhaseResidueNormalizer
    (Value : Type*)
    [AddCommGroup Value] [Module ℝ Value] where
  /-- Full phase period used to normalize the residue. -/
  phasePeriod : Value
  /-- Integer multiples of the phase period are faithfully represented. -/
  integer_period_injective :
    Function.Injective
      (fun n : ℤ => (n : ℝ) • phasePeriod)

namespace PhaseResidueNormalizer

variable {Value : Type*}
variable [AddCommGroup Value] [Module ℝ Value]
variable (N : PhaseResidueNormalizer Value)

/-- Integer period equality is equivalent to equality of winding integers. -/
theorem integer_period_eq_iff
    (m n : ℤ) :
    (m : ℝ) • N.phasePeriod = (n : ℝ) • N.phasePeriod
      ↔ m = n := by
  constructor
  · intro h
    exact N.integer_period_injective h
  · intro h
    rw [h]

/-- An integer multiple of the phase period vanishes iff the integer is zero. -/
theorem integer_period_zero_iff
    (n : ℤ) :
    (n : ℝ) • N.phasePeriod = 0 ↔ n = 0 := by
  constructor
  · intro h
    apply N.integer_period_injective
    simpa using h
  · intro h
    rw [h]
    simp

/-- Nonzero integer winding gives a nonzero period multiple. -/
theorem integer_period_ne_zero_of_ne_zero
    {n : ℤ}
    (hn : n ≠ 0) :
    (n : ℝ) • N.phasePeriod ≠ 0 := by
  intro h
  exact hn ((N.integer_period_zero_iff n).mp h)

end PhaseResidueNormalizer

/-! ## 3A. Scalar complex phase-period normalizer -/

/--
The classical scalar complex residue normalizer.

The phase period is `2πi`, represented as a value-level period element in `ℂ`.
The integer-period faithfulness is proved constructively by reading out the
imaginary component.
-/
def scalarComplexPhaseResidueNormalizer :
    PhaseResidueNormalizer ℂ where
  phasePeriod := (2 * Real.pi : ℝ) • Complex.I
  integer_period_injective := by
    intro m n h
    have him := congrArg Complex.im h
    simpa using him

namespace scalarComplexPhaseResidueNormalizer

/-- The scalar complex phase period is `2πi`. -/
theorem phasePeriod_eq :
    scalarComplexPhaseResidueNormalizer.phasePeriod =
      (2 * Real.pi : ℝ) • Complex.I :=
  rfl

/-- Integer multiples of the scalar complex phase period are faithful. -/
theorem integerPeriod_injective :
    Function.Injective
      (fun n : ℤ =>
        (n : ℝ) • scalarComplexPhaseResidueNormalizer.phasePeriod) :=
  scalarComplexPhaseResidueNormalizer.integer_period_injective

end scalarComplexPhaseResidueNormalizer

/-! ## 4. Winding number from residue -/

/--
A winding-number datum extracted from a boundary integral.

`winding Ω` is the integer charge enclosed by the region/contour `Ω`.
-/
structure WindingNumberDatum
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value) where
  /-- Integer winding/monodromy/charge readout for a region. -/
  winding : Region → ℤ
  /-- Residue law: `∮ ω = winding(Ω) • phasePeriod`. -/
  residue_law :
    ∀ Ω : Region,
      I.boundaryIntegral Ω ω =
        (winding Ω : ℝ) • N.phasePeriod

namespace WindingNumberDatum

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}

variable (W : WindingNumberDatum I N ω)

/-- The residue law as a theorem accessor. -/
theorem boundaryIntegral_eq
    (Ω : Region) :
    I.boundaryIntegral Ω ω =
      (W.winding Ω : ℝ) • N.phasePeriod :=
  W.residue_law Ω

/-- If the winding number is zero, the boundary integral vanishes. -/
theorem boundaryIntegral_eq_zero_of_winding_zero
    {Ω : Region}
    (hΩ : W.winding Ω = 0) :
    I.boundaryIntegral Ω ω = 0 := by
  rw [W.residue_law Ω, hΩ]
  simp

/--
A zero boundary integral forces zero winding, because the phase-period lattice
is injective.
-/
theorem winding_eq_zero_of_boundaryIntegral_eq_zero
    {Ω : Region}
    (hΩ : I.boundaryIntegral Ω ω = 0) :
    W.winding Ω = 0 := by
  apply N.integer_period_injective
  change (W.winding Ω : ℝ) • N.phasePeriod = ((0 : ℤ) : ℝ) • N.phasePeriod
  rw [← W.residue_law Ω, hΩ]
  simp

/-- Boundary integral vanishes iff winding vanishes. -/
theorem boundaryIntegral_eq_zero_iff
    {Ω : Region} :
    I.boundaryIntegral Ω ω = 0 ↔ W.winding Ω = 0 := by
  constructor
  · intro h
    exact W.winding_eq_zero_of_boundaryIntegral_eq_zero h
  · intro h
    exact W.boundaryIntegral_eq_zero_of_winding_zero h

/-- Nonzero winding gives a nonzero boundary integral. -/
theorem boundaryIntegral_ne_zero_of_winding_ne_zero
    {Ω : Region}
    (hΩ : W.winding Ω ≠ 0) :
    I.boundaryIntegral Ω ω ≠ 0 := by
  intro hzero
  exact hΩ (W.winding_eq_zero_of_boundaryIntegral_eq_zero hzero)

/-- Nonzero boundary integral gives nonzero winding. -/
theorem winding_ne_zero_of_boundaryIntegral_ne_zero
    {Ω : Region}
    (hΩ : I.boundaryIntegral Ω ω ≠ 0) :
    W.winding Ω ≠ 0 := by
  intro hzero
  exact hΩ (W.boundaryIntegral_eq_zero_of_winding_zero hzero)

/-- Boundary integral is nonzero iff winding is nonzero. -/
theorem boundaryIntegral_ne_zero_iff
    {Ω : Region} :
    I.boundaryIntegral Ω ω ≠ 0 ↔ W.winding Ω ≠ 0 := by
  constructor
  · intro h
    exact W.winding_ne_zero_of_boundaryIntegral_ne_zero h
  · intro h
    exact W.boundaryIntegral_ne_zero_of_winding_ne_zero h

/-- Equal boundary residues force equal winding numbers. -/
theorem winding_eq_of_boundaryIntegral_eq
    {Ω₁ Ω₂ : Region}
    (hΩ :
      I.boundaryIntegral Ω₁ ω =
        I.boundaryIntegral Ω₂ ω) :
    W.winding Ω₁ = W.winding Ω₂ := by
  apply N.integer_period_injective
  change (W.winding Ω₁ : ℝ) • N.phasePeriod =
    (W.winding Ω₂ : ℝ) • N.phasePeriod
  rw [← W.residue_law Ω₁, ← W.residue_law Ω₂]
  exact hΩ

/-- Boundary residues are equal iff the winding numbers are equal. -/
theorem boundaryIntegral_eq_iff_winding_eq
    (Ω₁ Ω₂ : Region) :
    I.boundaryIntegral Ω₁ ω =
        I.boundaryIntegral Ω₂ ω
      ↔ W.winding Ω₁ = W.winding Ω₂ := by
  constructor
  · intro h
    exact W.winding_eq_of_boundaryIntegral_eq h
  · intro h
    rw [W.residue_law Ω₁, W.residue_law Ω₂, h]

/-- Regions with the same certified winding have the same boundary residue. -/
theorem boundaryIntegral_eq_of_winding_eq
    {Ω₁ Ω₂ : Region}
    (hΩ : W.winding Ω₁ = W.winding Ω₂) :
    I.boundaryIntegral Ω₁ ω =
      I.boundaryIntegral Ω₂ ω :=
  (W.boundaryIntegral_eq_iff_winding_eq Ω₁ Ω₂).mpr hΩ

end WindingNumberDatum

/-! ## 5. Explicit finite divisor counting -/

/--
A finite divisor counter for a region.

The enclosed divisor charge is computed by summing the multiplicities of an
explicit finite list of enclosed divisor points.
-/
structure FiniteDivisorCounter
    (Region Point Value : Type*)
    [Monoid Value]
    (D : SpectralDivisorDatum Point Value) where
  /-- Finite list of divisor points enclosed by a region. -/
  enclosedDivisors : Region → List Point

namespace FiniteDivisorCounter

variable {Region Point Value : Type*}
variable [Monoid Value]
variable {D : SpectralDivisorDatum Point Value}

/-- The enclosed divisor multiplicity is the finite sum of local multiplicities. -/
def enclosedMultiplicity
    (C : FiniteDivisorCounter Region Point Value D)
    (Ω : Region) : ℤ :=
  (List.map D.multiplicity (C.enclosedDivisors Ω)).sum

/-- The enclosed multiplicity is definitionally the list sum. -/
theorem enclosedMultiplicity_eq_sum
    (C : FiniteDivisorCounter Region Point Value D)
    (Ω : Region) :
    C.enclosedMultiplicity Ω =
      (List.map D.multiplicity (C.enclosedDivisors Ω)).sum :=
  rfl

end FiniteDivisorCounter

/-! ## 6. Divisor-to-winding calibration -/

/--
Calibration connecting divisor multiplicities to winding readouts.

The divisor count is explicitly computed from a finite counter.  The remaining
proof field is the actual argument-principle equality.
-/
structure DivisorWindingCalibration
    {Region Point Tangent Value : Type*}
    [Monoid Value]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (D : SpectralDivisorDatum Point Value)
    (W : WindingNumberDatum I N ω) where
  /-- Explicit finite divisor counter. -/
  counter :
    FiniteDivisorCounter Region Point Value D
  /-- Winding equals the finite enclosed divisor multiplicity. -/
  winding_eq_enclosedMultiplicity :
    ∀ Ω : Region,
      W.winding Ω =
        FiniteDivisorCounter.enclosedMultiplicity counter Ω

namespace DivisorWindingCalibration

variable
    {Region Point Tangent Value : Type*}
    [Monoid Value]
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {D : SpectralDivisorDatum Point Value}
    {W : WindingNumberDatum I N ω}

variable (C : DivisorWindingCalibration I N ω D W)

/-- The enclosed divisor multiplicity computed by the calibration. -/
def enclosedMultiplicity
    (Ω : Region) : ℤ :=
  FiniteDivisorCounter.enclosedMultiplicity C.counter Ω

/--
The enclosed multiplicity is the explicit finite sum of divisor
multiplicities.
-/
theorem enclosedMultiplicity_eq_sum
    (Ω : Region) :
    C.enclosedMultiplicity Ω =
      (List.map D.multiplicity (C.counter.enclosedDivisors Ω)).sum :=
  rfl

/-- The winding number is the enclosed divisor count. -/
theorem winding_is_divisor_count
    (Ω : Region) :
    W.winding Ω = C.enclosedMultiplicity Ω :=
  C.winding_eq_enclosedMultiplicity Ω

/-- Residue law rewritten directly in terms of the divisor count. -/
theorem boundaryIntegral_eq_divisor_count_period
    (Ω : Region) :
    I.boundaryIntegral Ω ω =
      (C.enclosedMultiplicity Ω : ℝ) • N.phasePeriod := by
  calc
    I.boundaryIntegral Ω ω =
        (W.winding Ω : ℝ) • N.phasePeriod :=
      W.residue_law Ω
    _ = (C.enclosedMultiplicity Ω : ℝ) • N.phasePeriod := by
      rw [C.winding_is_divisor_count Ω]

/-- Boundary residue vanishes iff the enclosed divisor count is zero. -/
theorem boundaryIntegral_eq_zero_iff_enclosedMultiplicity_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω ω = 0
      ↔ C.enclosedMultiplicity Ω = 0 := by
  constructor
  · intro h
    have hW :
        W.winding Ω = 0 :=
      W.winding_eq_zero_of_boundaryIntegral_eq_zero h
    rw [C.winding_is_divisor_count Ω] at hW
    exact hW
  · intro h
    apply W.boundaryIntegral_eq_zero_of_winding_zero
    rw [C.winding_is_divisor_count Ω]
    exact h

/-- Boundary residue is nonzero iff the enclosed divisor count is nonzero. -/
theorem boundaryIntegral_ne_zero_iff_enclosedMultiplicity_ne_zero
    (Ω : Region) :
    I.boundaryIntegral Ω ω ≠ 0
      ↔ C.enclosedMultiplicity Ω ≠ 0 := by
  constructor
  · intro hB hM
    exact hB
      ((C.boundaryIntegral_eq_zero_iff_enclosedMultiplicity_eq_zero Ω).mpr hM)
  · intro hM hB
    exact hM
      ((C.boundaryIntegral_eq_zero_iff_enclosedMultiplicity_eq_zero Ω).mp hB)

end DivisorWindingCalibration

/-! ## 7. Topological index / K-homology pairing socket -/

/--
A topological index datum extracted from a concrete winding datum.

This does not carry an independent `winding : Region → ℤ`; the winding is the
one already extracted from the residue law.
-/
structure TopologicalIndexDatum
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (W : WindingNumberDatum I N ω)
    (Cycle : Type*) where
  /-- Region/contour associated to a cycle. -/
  regionOf : Cycle → Region
  /-- Integer index of a cycle. -/
  index : Cycle → ℤ
  /-- Spectral-flow readout for cycles. -/
  spectralFlow : Cycle → ℤ
  /-- Index equals winding of the associated region. -/
  index_eq_winding :
    ∀ c : Cycle,
      index c = W.winding (regionOf c)
  /-- Index equals spectral flow. -/
  index_eq_spectralFlow :
    ∀ c : Cycle,
      index c = spectralFlow c

namespace TopologicalIndexDatum

variable
    {Region Point Tangent Value Cycle : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}

variable (T : TopologicalIndexDatum I N ω W Cycle)

/-- The topological index is the residue winding. -/
theorem index_is_winding
    (c : Cycle) :
    T.index c = W.winding (T.regionOf c) :=
  T.index_eq_winding c

/-- The topological index is spectral flow. -/
theorem index_is_spectralFlow
    (c : Cycle) :
    T.index c = T.spectralFlow c :=
  T.index_eq_spectralFlow c

/-- Winding equals spectral flow through the common index. -/
theorem winding_eq_spectralFlow
    (c : Cycle) :
    W.winding (T.regionOf c) = T.spectralFlow c := by
  rw [← T.index_eq_winding c]
  exact T.index_eq_spectralFlow c

/-- Boundary residue equals index times the phase period. -/
theorem boundaryIntegral_eq_index_period
    (c : Cycle) :
    I.boundaryIntegral (T.regionOf c) ω =
      (T.index c : ℝ) • N.phasePeriod := by
  calc
    I.boundaryIntegral (T.regionOf c) ω =
        (W.winding (T.regionOf c) : ℝ) • N.phasePeriod :=
      W.residue_law (T.regionOf c)
    _ = (T.index c : ℝ) • N.phasePeriod := by
      rw [← T.index_eq_winding c]

/-- Boundary residue equals spectral flow times the phase period. -/
theorem boundaryIntegral_eq_spectralFlow_period
    (c : Cycle) :
    I.boundaryIntegral (T.regionOf c) ω =
      (T.spectralFlow c : ℝ) • N.phasePeriod := by
  calc
    I.boundaryIntegral (T.regionOf c) ω =
        (T.index c : ℝ) • N.phasePeriod :=
      T.boundaryIntegral_eq_index_period c
    _ = (T.spectralFlow c : ℝ) • N.phasePeriod := by
      rw [T.index_eq_spectralFlow c]

/-- Index vanishes iff the associated boundary residue vanishes. -/
theorem index_eq_zero_iff_boundaryIntegral_eq_zero
    (c : Cycle) :
    T.index c = 0
      ↔ I.boundaryIntegral (T.regionOf c) ω = 0 := by
  constructor
  · intro hIndex
    apply W.boundaryIntegral_eq_zero_of_winding_zero
    rw [← T.index_eq_winding c]
    exact hIndex
  · intro hBoundary
    rw [T.index_eq_winding c]
    exact W.winding_eq_zero_of_boundaryIntegral_eq_zero hBoundary

/-- Boundary residue is nonzero iff the associated index is nonzero. -/
theorem boundaryIntegral_ne_zero_iff_index_ne_zero
    (c : Cycle) :
    I.boundaryIntegral (T.regionOf c) ω ≠ 0
      ↔ T.index c ≠ 0 := by
  constructor
  · intro hBoundary hIndex
    exact hBoundary
      ((T.index_eq_zero_iff_boundaryIntegral_eq_zero c).mp hIndex)
  · intro hIndex hBoundary
    exact hIndex
      ((T.index_eq_zero_iff_boundaryIntegral_eq_zero c).mpr hBoundary)

/-- Boundary residue is nonzero iff spectral flow is nonzero. -/
theorem boundaryIntegral_ne_zero_iff_spectralFlow_ne_zero
    (c : Cycle) :
    I.boundaryIntegral (T.regionOf c) ω ≠ 0
      ↔ T.spectralFlow c ≠ 0 := by
  rw [← T.index_eq_spectralFlow c]
  exact T.boundaryIntegral_ne_zero_iff_index_ne_zero c

end TopologicalIndexDatum

/-! ## 8. Spectral function calibration -/

/--
A spectral function calibration.

The divisor datum is explicitly tied to the spectral function by equality.
-/
structure SpectralFunctionCalibration
    (State Point Value : Type*)
    [Monoid Value] where
  /-- Spectral/scattering/Fredholm/L-function readout. -/
  spectralFunction : State → Point → Value
  /-- Divisor datum associated to each state. -/
  divisorDatum : State → SpectralDivisorDatum Point Value
  /-- The divisor datum is attached to the stated spectral function. -/
  divisorDatum_F :
    ∀ s : State,
      (divisorDatum s).F = spectralFunction s

namespace SpectralFunctionCalibration

variable {State Point Value : Type*}
variable [Monoid Value]
variable (C : SpectralFunctionCalibration State Point Value)

/-- The divisor datum for a state uses the calibrated spectral function. -/
theorem divisorDatum_function_eq
    (s : State) :
    (C.divisorDatum s).F = C.spectralFunction s :=
  C.divisorDatum_F s

/--
The divisor locus of the stored divisor datum is the spectral divisor set of
the calibrated spectral function.
-/
theorem divisorLocus_eq_spectralDivisorSet
    (s : State) :
    (C.divisorDatum s).divisorLocus =
      {z : Point | IsSpectralDivisor (C.spectralFunction s) z} := by
  ext z
  simp [SpectralDivisorDatum.divisorLocus, C.divisorDatum_F s]

/-- Off the spectral divisor set, the calibrated multiplicity is zero. -/
theorem multiplicity_zero_off_spectral_divisor
    (s : State)
    {z : Point}
    (hz : ¬ IsSpectralDivisor (C.spectralFunction s) z) :
    (C.divisorDatum s).multiplicity z = 0 :=
  (C.divisorDatum s).multiplicity_zero_off_divisor z
    (by
      simpa [C.divisorDatum_F s] using hz)

end SpectralFunctionCalibration

end InfoGeometry.Geometry.SpectralDivisors
