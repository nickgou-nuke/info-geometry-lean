/-
InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean

KL-style projective relative entropy sockets for finite primitive and
von-Mangoldt projective densities.

This module does not prove a KL/Jensen/Gibbs inequality, the Erdős primitive
set theorem, the prime number theorem, or an analytic statement about `ζ`.
It defines finite readouts and packages nonnegativity/strict-positivity/zero
claims as explicit witness data.
-/

import InfoGeometry.Arithmetic.ProjectiveEntropy

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectiveRelativeEntropy

open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature
open InfoGeometry.Arithmetic.ProjectiveEntropy

/-! ## 1. Finite KL-style projective readouts -/

/--
Unnormalized KL-style scalar readout.

`projectiveKL p q = p * log (p / q)`.
No positivity theorem is asserted here; positivity depends on the model
hypotheses supplied by a witness.
-/
def projectiveKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q)

/--
KL-style readout comparing a primitive projective density against a finite
von-Mangoldt / prime projective density.
-/
def primitiveToPrimeProjectiveKL
    (candidate reference : Finset ℕ) (u : ℝ) : ℝ :=
  projectiveKL
    (primitiveInvertedPartitionDensity candidate u)
    (arithmeticPrimeInvertedPartitionDensity reference u)

/--
The opposite orientation: finite von-Mangoldt / prime projective density
against the primitive projective density.
-/
def primeToPrimitiveProjectiveKL
    (candidate reference : Finset ℕ) (u : ℝ) : ℝ :=
  projectiveKL
    (arithmeticPrimeInvertedPartitionDensity reference u)
    (primitiveInvertedPartitionDensity candidate u)

/-- Unfolding of the primitive-to-prime KL-style readout. -/
theorem primitiveToPrimeProjectiveKL_eq
    (candidate reference : Finset ℕ) (u : ℝ) :
    primitiveToPrimeProjectiveKL candidate reference u =
      primitiveInvertedPartitionDensity candidate u *
        Real.log
          (primitiveInvertedPartitionDensity candidate u /
            arithmeticPrimeInvertedPartitionDensity reference u) :=
  rfl

/-- Unfolding of the prime-to-primitive KL-style readout. -/
theorem primeToPrimitiveProjectiveKL_eq
    (candidate reference : Finset ℕ) (u : ℝ) :
    primeToPrimitiveProjectiveKL candidate reference u =
      arithmeticPrimeInvertedPartitionDensity reference u *
        Real.log
          (arithmeticPrimeInvertedPartitionDensity reference u /
            primitiveInvertedPartitionDensity candidate u) :=
  rfl

/-! ## 2. Proof-carrying KL witness -/

/--
Witness that a model readout realizes a chosen projective KL orientation.

`candidate_ne_reference` is intentionally supplied as a proposition rather
than hard-wired to equality of finsets.  Some models may quotient or calibrate
candidate/reference supports before making the strict-positivity claim.
-/
structure ProjectiveKLWitness
    (candidate reference : Finset ℕ) where
  /-- Model-specific KL-style readout on compact projective temperature. -/
  klReadout : ℝ → ℝ

  /-- Calibration to the primitive-to-prime finite KL-style expression. -/
  kl_eq_primitiveToPrime :
    ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      klReadout u = primitiveToPrimeProjectiveKL candidate reference u

  /-- Optional nonnegativity certificate supplied by the model/proof. -/
  kl_nonneg :
    ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      0 ≤ klReadout u

  /--
  Model-specific condition saying the candidate is not the reference state.
  This is a proposition because the reference may be quotient-calibrated.
  -/
  candidate_ne_reference : Prop

  /-- Strict positivity away from the reference state, supplied as witness data. -/
  kl_pos_of_ne_reference :
    candidate_ne_reference →
      ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
        0 < klReadout u

  /-- Optional zero law at the reference state, supplied as witness data. -/
  kl_zero_of_reference :
    ¬ candidate_ne_reference →
      ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
        klReadout u = 0

namespace ProjectiveKLWitness

variable {candidate reference : Finset ℕ}
variable (W : ProjectiveKLWitness candidate reference)

/-- Re-export the supplied KL calibration law. -/
theorem readout_eq_primitiveToPrime
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    W.klReadout u =
      primitiveToPrimeProjectiveKL candidate reference u :=
  W.kl_eq_primitiveToPrime u hu

/-- Re-export the supplied nonnegativity law. -/
theorem readout_nonneg
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ W.klReadout u :=
  W.kl_nonneg u hu

/-- Re-export strict positivity away from the supplied reference state. -/
theorem readout_pos_of_ne_reference
    (hne : W.candidate_ne_reference)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 < W.klReadout u :=
  W.kl_pos_of_ne_reference hne u hu

/-- Re-export the supplied zero law at the reference state. -/
theorem readout_eq_zero_of_reference
    (href : ¬ W.candidate_ne_reference)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    W.klReadout u = 0 :=
  W.kl_zero_of_reference href u hu

end ProjectiveKLWitness

/-! ## 3. Integrated compact-sector witness -/

/--
Proof-carrying integrated KL-style readout over the compact projective
temperature sector `(0, 1)`.

The integral equality and nonnegativity are supplied as data to avoid importing
general KL/Jensen/substitution proof obligations into this sidecar.
-/
structure IntegratedProjectiveKLWitness
    (candidate reference : Finset ℕ) where
  /-- Pointwise KL witness. -/
  pointwise : ProjectiveKLWitness candidate reference

  /-- Integrated compact-sector KL readout. -/
  integratedKL : ℝ

  /-- Supplied integral calibration for the pointwise readout. -/
  integrated_eq :
    integratedKL =
      ∫ u : ℝ in Set.Ioo 0 1, pointwise.klReadout u

  /-- Supplied nonnegativity of the integrated readout. -/
  integrated_nonneg :
    0 ≤ integratedKL

  /-- Supplied strict positivity away from the reference state. -/
  integrated_pos_of_ne_reference :
    pointwise.candidate_ne_reference → 0 < integratedKL

namespace IntegratedProjectiveKLWitness

variable {candidate reference : Finset ℕ}
variable (W : IntegratedProjectiveKLWitness candidate reference)

/-- Re-export the supplied integrated calibration law. -/
theorem integrated_eq_integral :
    W.integratedKL =
      ∫ u : ℝ in Set.Ioo 0 1, W.pointwise.klReadout u :=
  W.integrated_eq

/-- Re-export the supplied integrated nonnegativity law. -/
theorem integratedKL_nonneg :
    0 ≤ W.integratedKL :=
  W.integrated_nonneg

/-- Re-export strict positivity away from the supplied reference state. -/
theorem integratedKL_pos_of_ne_reference
    (hne : W.pointwise.candidate_ne_reference) :
    0 < W.integratedKL :=
  W.integrated_pos_of_ne_reference hne

end IntegratedProjectiveKLWitness

/-! ## 4. State-space calibration -/

/--
State-space calibration for projective KL readouts.

This is the socket through which a JKO/Souriau/geometric solver can attach its
own readout to the finite arithmetic projective KL witness.
-/
structure ProjectiveKLCalibration
    (State : Type*) where
  /-- Encode a candidate/reference pair as a model state. -/
  stateOfPair : Finset ℕ → Finset ℕ → State

  /-- Model-specific pointwise KL readout. -/
  klReadout : State → ℝ → ℝ

  /-- Model-specific integrated KL readout. -/
  integratedKLReadout : State → ℝ

  /-- Supplied integrated KL witness for each pair. -/
  witnessOfPair :
    ∀ candidate reference : Finset ℕ,
      IntegratedProjectiveKLWitness candidate reference

  /-- Pointwise state readout agrees with the supplied witness. -/
  pointwise_eq_sorry :
    ∀ candidate reference : Finset ℕ,
    ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      klReadout (stateOfPair candidate reference) u =
        (witnessOfPair candidate reference).pointwise.klReadout u

  /-- Integrated state readout agrees with the supplied witness. -/
  integrated_eq_sorry :
    ∀ candidate reference : Finset ℕ,
      integratedKLReadout (stateOfPair candidate reference) =
        (witnessOfPair candidate reference).integratedKL

namespace ProjectiveKLCalibration

variable {State : Type*}
variable (C : ProjectiveKLCalibration State)

/-- Calibrated pointwise KL readout equals the finite primitive-to-prime expression. -/
theorem pointwise_eq_primitiveToPrime
    (candidate reference : Finset ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.klReadout (C.stateOfPair candidate reference) u =
      primitiveToPrimeProjectiveKL candidate reference u := by
  rw [C.pointwise_eq_sorry candidate reference u hu]
  exact (C.witnessOfPair candidate reference).pointwise.readout_eq_primitiveToPrime hu

/-- Calibrated pointwise KL readout is nonnegative. -/
theorem pointwise_nonneg
    (candidate reference : Finset ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ C.klReadout (C.stateOfPair candidate reference) u := by
  rw [C.pointwise_eq_sorry candidate reference u hu]
  exact (C.witnessOfPair candidate reference).pointwise.readout_nonneg hu

/-- Calibrated integrated KL readout is nonnegative. -/
theorem integrated_nonneg
    (candidate reference : Finset ℕ) :
    0 ≤ C.integratedKLReadout (C.stateOfPair candidate reference) := by
  rw [C.integrated_eq_sorry candidate reference]
  exact (C.witnessOfPair candidate reference).integratedKL_nonneg

/-- Calibrated integrated KL is strictly positive away from the supplied reference state. -/
theorem integrated_pos_of_ne_reference
    (candidate reference : Finset ℕ)
    (hne : (C.witnessOfPair candidate reference).pointwise.candidate_ne_reference) :
    0 < C.integratedKLReadout (C.stateOfPair candidate reference) := by
  rw [C.integrated_eq_sorry candidate reference]
  exact (C.witnessOfPair candidate reference).integratedKL_pos_of_ne_reference hne

end ProjectiveKLCalibration

end InfoGeometry.Arithmetic.ProjectiveRelativeEntropy

