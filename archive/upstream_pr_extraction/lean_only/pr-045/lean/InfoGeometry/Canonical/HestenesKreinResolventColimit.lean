import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Finite symmetrized resolvents on the Hestenes--Krein colimit

This owner translates the finite part of the resolvent/twin-wave interface into
the real Hestenes--Krein language.  The resolvent is a finite rational kernel,
and all colimit statements are finite-sum readout identities.  No infinite
resolvent series, Hadamard product, spectral measure, heat kernel, or Burgers
equation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinResolventColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein
open scoped BigOperators

variable {C : HestenesKreinCone}

/-! ## Finite two-sided resolvent kernel -/

def symmetricResolventKernel (z eigenvalue : ℝ) : ℝ :=
  (z - eigenvalue)⁻¹ + (z + eigenvalue)⁻¹

theorem symmetricResolventKernel_eq_two_mul
    {z eigenvalue : ℝ} (hzminus : z - eigenvalue ≠ 0)
    (hzplus : z + eigenvalue ≠ 0) :
    symmetricResolventKernel z eigenvalue =
      2 * z / (z ^ 2 - eigenvalue ^ 2) := by
  unfold symmetricResolventKernel
  have hden : z ^ 2 - eigenvalue ^ 2 ≠ 0 := by
    have hfactor : (z - eigenvalue) * (z + eigenvalue) =
        z ^ 2 - eigenvalue ^ 2 := by ring
    rw [← hfactor]
    exact mul_ne_zero hzminus hzplus
  field_simp [hzminus, hzplus, hden]
  ring

/-- The finite two-pole numerator identity behind the diagonal `2 × 2` Jost
resolvent.  It is stated separately from the quotient form so it remains
valid as the algebraic bridge to a determinant factor. -/
theorem symmetricResolventKernel_mul_poleProduct
    {z eigenvalue : ℝ} (hzminus : z - eigenvalue ≠ 0)
    (hzplus : z + eigenvalue ≠ 0) :
    (z - eigenvalue) * (z + eigenvalue) *
        symmetricResolventKernel z eigenvalue = 2 * z := by
  unfold symmetricResolventKernel
  field_simp [hzminus, hzplus]
  ring

theorem symmetricResolventKernel_eq_zero_iff
    {z eigenvalue : ℝ} (hzminus : z - eigenvalue ≠ 0)
    (hzplus : z + eigenvalue ≠ 0) :
    symmetricResolventKernel z eigenvalue = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    have hnum : (z - eigenvalue) * (z + eigenvalue) *
        symmetricResolventKernel z eigenvalue = 2 * z :=
      symmetricResolventKernel_mul_poleProduct hzminus hzplus
    rw [hzero] at hnum
    linarith
  · intro hz
    subst z
    unfold symmetricResolventKernel
    have heigenvalue : eigenvalue ≠ 0 := by
      intro heigenvalue
      apply hzminus
      simp [heigenvalue]
    field_simp [heigenvalue]
    ring

theorem symmetricResolventKernel_neg
    {z eigenvalue : ℝ} (hzminus : z - eigenvalue ≠ 0)
    (hzplus : z + eigenvalue ≠ 0) :
    symmetricResolventKernel (-z) eigenvalue =
      -symmetricResolventKernel z eigenvalue := by
  unfold symmetricResolventKernel
  have hnegminus : -z - eigenvalue ≠ 0 := by
    intro h
    apply hzplus
    linarith
  have hnegplus : -z + eigenvalue ≠ 0 := by
    intro h
    apply hzminus
    linarith
  field_simp [hzminus, hzplus, hnegminus, hnegplus]
  ring

theorem symmetricResolventKernel_zero
    {eigenvalue : ℝ} (heigenvalue : eigenvalue ≠ 0) :
    symmetricResolventKernel 0 eigenvalue = 0 := by
  unfold symmetricResolventKernel
  field_simp [heigenvalue]
  ring

def symmetricResolventSum
    {ι : Type*} (marks : Finset ι) (z : ℝ) (spectrum : ι → ℝ) : ℝ :=
  marks.sum (fun i => symmetricResolventKernel z (spectrum i))

theorem symmetricResolventSum_neg
    {ι : Type*} (marks : Finset ι) (z : ℝ) (spectrum : ι → ℝ)
    (hnonzero : ∀ i ∈ marks,
      z - spectrum i ≠ 0 ∧ z + spectrum i ≠ 0) :
    symmetricResolventSum marks (-z) spectrum =
      -symmetricResolventSum marks z spectrum := by
  unfold symmetricResolventSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [symmetricResolventKernel_neg
    (hnonzero i hi).1 (hnonzero i hi).2]

theorem symmetricResolventSum_zero
    {ι : Type*} (marks : Finset ι) (spectrum : ι → ℝ)
    (hnonzero : ∀ i ∈ marks, spectrum i ≠ 0) :
    symmetricResolventSum marks 0 spectrum = 0 := by
  unfold symmetricResolventSum
  apply Finset.sum_eq_zero
  intro i hi
  exact symmetricResolventKernel_zero (hnonzero i hi)

/-! ## Native twin-wave parity identities -/

def twinEven (t y : ℝ) : ℝ :=
  Real.cos (t * y) + Real.cos (-(t * y))

def twinOdd (t y : ℝ) : ℝ :=
  Real.sin (t * y) - Real.sin (-(t * y))

theorem twinEven_eq_two_cos (t y : ℝ) :
    twinEven t y = 2 * Real.cos (t * y) := by
  unfold twinEven
  rw [Real.cos_neg]
  ring

theorem twinOdd_eq_two_sin (t y : ℝ) :
    twinOdd t y = 2 * Real.sin (t * y) := by
  unfold twinOdd
  rw [Real.sin_neg]
  ring

theorem twinEven_zero (y : ℝ) :
    twinEven 0 y = 2 := by
  rw [twinEven_eq_two_cos]
  simp

theorem twinOdd_zero (y : ℝ) :
    twinOdd 0 y = 0 := by
  rw [twinOdd_eq_two_sin]
  simp

/-! ## Finite resolvent readout through the colimit -/

def stageResolventSum
    {ι : Type*} (marks : Finset ι) (z : ℝ)
    (spectrum : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  symmetricResolventSum marks z (fun i => spectrum n i x)

def limitResolventSum
    {ι : Type*} (marks : Finset ι) (z : ℝ)
    (spectrum : ι → DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  symmetricResolventSum marks z (fun i => spectrum i x)

theorem stageResolventSum_eq_limitResolventSum
    {ι : Type*} (marks : Finset ι) (z : ℝ)
    (stageSpectrum : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (limitSpectrum : ι → DoubledSpace C.LimitBase → ℝ)
    (hSpectrum : ∀ n i x,
      stageSpectrum n i x = limitSpectrum i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageResolventSum marks z stageSpectrum n x =
      limitResolventSum marks z limitSpectrum (C.ι n x) := by
  unfold stageResolventSum limitResolventSum symmetricResolventSum
  apply Finset.sum_congr rfl
  intro i hi
  change symmetricResolventKernel z (stageSpectrum n i x) =
    symmetricResolventKernel z (limitSpectrum i (C.ι n x))
  rw [hSpectrum n i x]

theorem stageResolventSum_bondIterate
    {ι : Type*} (marks : Finset ι) (z : ℝ)
    (stageSpectrum : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (limitSpectrum : ι → DoubledSpace C.LimitBase → ℝ)
    (hSpectrum : ∀ n i x,
      stageSpectrum n i x = limitSpectrum i (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageResolventSum marks z stageSpectrum (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageResolventSum marks z stageSpectrum n x := by
  rw [stageResolventSum_eq_limitResolventSum marks z stageSpectrum
      limitSpectrum hSpectrum (n + m),
    stageResolventSum_eq_limitResolventSum marks z stageSpectrum
      limitSpectrum hSpectrum n]
  unfold limitResolventSum symmetricResolventSum
  apply Finset.sum_congr rfl
  intro i hi
  change symmetricResolventKernel z
      (limitSpectrum i (C.ι (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x))) =
    symmetricResolventKernel z (limitSpectrum i (C.ι n x))
  have hι := C.toFilteredPhaseCone.ι_bondIterate_apply n m x
  change C.ι (n + m)
      (C.toFilteredPhaseCone.bondIterate n m x) = C.ι n x at hι
  rw [hι]

end InfoGeometry.Canonical.HestenesKreinResolventColimit

end noncomputable section
