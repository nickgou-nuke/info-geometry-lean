import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter
import InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-!
# InfoGeometry.Arithmetic.PrimonSplitChiralFiniteCutoff

Finite-cutoff chiral primon thermodynamics on the split basis.

This file keeps the finite model explicit:

* the prime cutoff is the existing finite prime set `{p ≤ Λ | prime p}`;
* each chiral sector gets its own finite partition/readout;
* the split-complex observables are stored in the idempotent basis used by
  `SplitChiralPolarizationBasis`.

The CFT / infinite-prime interpretation is not asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimonSplitChiralFiniteCutoff

open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter

/-- Prime energy `E_p = log p`. -/
def primeEnergy (p : ℕ) : ℝ :=
  Real.log p

/-- A finite prime cutoff, reused from the finite primon character lane. -/
def primeCutoff (Λ : ℕ) : Finset ℕ :=
  PrimonMajoranaWittenCharacter.primeCutoff Λ

/-- Chiral fermionic mode weight `exp(ν - β log p)`. -/
def chiralModeWeight (β ν : ℝ) (p : ℕ) : ℝ :=
  Real.exp (ν - β * primeEnergy p)

lemma chiralModeWeight_pos (β ν : ℝ) (p : ℕ) :
    0 < chiralModeWeight β ν p := by
  unfold chiralModeWeight
  exact Real.exp_pos _

/-- Left chiral finite partition on a prime cutoff. -/
def chiralPartitionLeft (Λ : ℕ) (β ν : ℝ) : ℝ :=
  Finset.prod (primeCutoff Λ) (fun p => 1 + chiralModeWeight β ν p)

lemma chiralPartitionLeft_pos (Λ : ℕ) (β ν : ℝ) :
    0 < chiralPartitionLeft Λ β ν := by
  unfold chiralPartitionLeft
  exact Finset.prod_pos (fun p _hp =>
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (chiralModeWeight_pos β ν p)))

lemma chiralPartitionLeft_ne_zero (Λ : ℕ) (β ν : ℝ) :
    chiralPartitionLeft Λ β ν ≠ 0 :=
  (chiralPartitionLeft_pos Λ β ν).ne'

/-- Right chiral finite partition on a prime cutoff. -/
def chiralPartitionRight (Λ : ℕ) (β ν : ℝ) : ℝ :=
  Finset.prod (primeCutoff Λ) (fun p => 1 + chiralModeWeight β ν p)

lemma chiralPartitionRight_pos (Λ : ℕ) (β ν : ℝ) :
    0 < chiralPartitionRight Λ β ν := by
  unfold chiralPartitionRight
  exact Finset.prod_pos (fun p _hp =>
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (chiralModeWeight_pos β ν p)))

lemma chiralPartitionRight_ne_zero (Λ : ℕ) (β ν : ℝ) :
    chiralPartitionRight Λ β ν ≠ 0 :=
  (chiralPartitionRight_pos Λ β ν).ne'

/-- Split chiral finite partition in the idempotent basis. -/
def chiralPartition (Λ : ℕ) (βL νL βR νR : ℝ) : ChiralScalar :=
  reconstruct
    (chiralPartitionLeft Λ βL νL)
    (chiralPartitionRight Λ βR νR)

/-- Left chiral Massieu potential `Φ₊ = log Z₊`. -/
def chiralMassieuLeft (Λ : ℕ) (β ν : ℝ) : ℝ :=
  Real.log (chiralPartitionLeft Λ β ν)

/-- Right chiral Massieu potential `Φ₋ = log Z₋`. -/
def chiralMassieuRight (Λ : ℕ) (β ν : ℝ) : ℝ :=
  Real.log (chiralPartitionRight Λ β ν)

/-- Split chiral Massieu potential. -/
def chiralMassieu (Λ : ℕ) (βL νL βR νR : ℝ) : ChiralScalar :=
  reconstruct
    (chiralMassieuLeft Λ βL νL)
    (chiralMassieuRight Λ βR νR)

/-- Left chiral free energy `F₊ = -log Z₊`. -/
def chiralFreeEnergyLeft (Λ : ℕ) (β ν : ℝ) : ℝ :=
  -Real.log (chiralPartitionLeft Λ β ν)

/-- Right chiral free energy `F₋ = -log Z₋`. -/
def chiralFreeEnergyRight (Λ : ℕ) (β ν : ℝ) : ℝ :=
  -Real.log (chiralPartitionRight Λ β ν)

/-- Split chiral free energy. -/
def chiralFreeEnergy (Λ : ℕ) (βL νL βR νR : ℝ) : ChiralScalar :=
  reconstruct
    (chiralFreeEnergyLeft Λ βL νL)
    (chiralFreeEnergyRight Λ βR νR)

@[simp]
theorem leftPart_chiralPartition
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    leftPart (chiralPartition Λ βL νL βR νR) =
      chiralPartitionLeft Λ βL νL := by
  rfl

@[simp]
theorem rightPart_chiralPartition
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    rightPart (chiralPartition Λ βL νL βR νR) =
      chiralPartitionRight Λ βR νR := by
  rfl

@[simp]
theorem reconstruct_chiralPartition
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    reconstruct
      (leftPart (chiralPartition Λ βL νL βR νR))
      (rightPart (chiralPartition Λ βL νL βR νR)) =
    chiralPartition Λ βL νL βR νR := by
  simp [chiralPartition]

@[simp]
theorem leftPart_chiralMassieu
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    leftPart (chiralMassieu Λ βL νL βR νR) =
      chiralMassieuLeft Λ βL νL := by
  rfl

@[simp]
theorem rightPart_chiralMassieu
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    rightPart (chiralMassieu Λ βL νL βR νR) =
      chiralMassieuRight Λ βR νR := by
  rfl

@[simp]
theorem reconstruct_chiralMassieu
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    reconstruct
      (leftPart (chiralMassieu Λ βL νL βR νR))
      (rightPart (chiralMassieu Λ βL νL βR νR)) =
    chiralMassieu Λ βL νL βR νR := by
  simp [chiralMassieu]

@[simp]
theorem leftPart_chiralFreeEnergy
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    leftPart (chiralFreeEnergy Λ βL νL βR νR) =
      chiralFreeEnergyLeft Λ βL νL := by
  rfl

@[simp]
theorem rightPart_chiralFreeEnergy
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    rightPart (chiralFreeEnergy Λ βL νL βR νR) =
      chiralFreeEnergyRight Λ βR νR := by
  rfl

@[simp]
theorem reconstruct_chiralFreeEnergy
    (Λ : ℕ) (βL νL βR νR : ℝ) :
    reconstruct
      (leftPart (chiralFreeEnergy Λ βL νL βR νR))
      (rightPart (chiralFreeEnergy Λ βL νL βR νR)) =
    chiralFreeEnergy Λ βL νL βR νR := by
  simp [chiralFreeEnergy]

end InfoGeometry.Arithmetic.PrimonSplitChiralFiniteCutoff
