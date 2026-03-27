import InfoGeometry.Basic
import InfoGeometry.Canonical.InformationCalculus
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.MaxEnt.JaynesInfoStatMech

open scoped BigOperators

/-!
# Relative Surprisal Operator Lift

Thin first-quantization bridge for pointwise information quantities on finite
carriers.

This file does not introduce new modular or thermodynamic ontology. It only
packages existing owner surfaces already present in the repo:

- diagonal observables as the finite first-quantization of pointwise scalars,
- pointwise surprisal and entropy on the normalized slice,
- relative modular potential / relative surprisal on positive rays and count
  rays,
- the scalar mean relative modular Hamiltonian and its Tomita-Takesaki-style
  operator lift,
- the existing partition/log-partition derivative theorems specialized to that
  lifted operator.
-/

namespace InfoGeometry.Canonical.RelativeSurprisalOperatorLift

open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section FirstQuantization

variable {n : ℕ} [Nonempty (Fin n)]

/-- First quantization of a pointwise observable as a diagonal operator. -/
def firstQuantize (a : DiagObservable n) : FinMat n :=
  diagMatrix a

omit [Nonempty (Fin n)] in
@[simp] theorem firstQuantize_apply_diag (a : DiagObservable n) (i : Fin n) :
    firstQuantize a i i = a i := by
  simp [firstQuantize, diagMatrix]

omit [Nonempty (Fin n)] in
@[simp] theorem firstQuantize_apply_offdiag
    (a : DiagObservable n) {i j : Fin n} (hij : i ≠ j) :
    firstQuantize a i j = 0 := by
  simp [firstQuantize, diagMatrix, hij]

omit [Nonempty (Fin n)] in
theorem firstQuantize_add (a b : DiagObservable n) :
    firstQuantize (fun i => a i + b i) = firstQuantize a + firstQuantize b := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [firstQuantize, diagMatrix]
  · simp [firstQuantize, diagMatrix, hij]

omit [Nonempty (Fin n)] in
theorem firstQuantize_smul (c : ℝ) (a : DiagObservable n) :
    firstQuantize (fun i => c * a i) = c • firstQuantize a := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [firstQuantize, diagMatrix]
  · simp [firstQuantize, diagMatrix, hij]

omit [Nonempty (Fin n)] in
theorem firstQuantize_const_eq_smul_one (c : ℝ) :
    firstQuantize (n := n) (fun _ => c) = c • (1 : FinMat n) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [firstQuantize, diagMatrix]
  · simp [firstQuantize, diagMatrix, hij]

end FirstQuantization

section Normalized

variable {n : ℕ} [Nonempty (Fin n)]

/-- Diagonal density matrix associated to a finite probability law. -/
noncomputable def densityMatrixOfFinProb (p : InfoGeometry.FinProb (Fin n)) : FinMat n :=
  firstQuantize (n := n) (fun i => (p i).toReal)

/-- First-quantized pointwise log-density. -/
noncomputable def logDensityOperator (p : InfoGeometry.FinProb (Fin n)) : FinMat n :=
  firstQuantize (n := n) (fun i => InfoGeometry.log_density p i)

/-- First-quantized pointwise surprisal operator. -/
noncomputable def surprisalOperator (p : InfoGeometry.FinProb (Fin n)) : FinMat n :=
  firstQuantize (n := n) (fun i => InfoGeometry.surprisal p i)

/-- Diagonal expectation against a finite probability law. -/
noncomputable def diagonalExpectation
    (p : InfoGeometry.FinProb (Fin n)) (A : FinMat n) : ℝ :=
  ∑ i, (p i).toReal * A i i

omit [Nonempty (Fin n)] in
@[simp] theorem densityMatrixOfFinProb_diag
    (p : InfoGeometry.FinProb (Fin n)) (i : Fin n) :
    densityMatrixOfFinProb p i i = (p i).toReal := by
  simp [densityMatrixOfFinProb, firstQuantize, diagMatrix]

omit [Nonempty (Fin n)] in
@[simp] theorem densityMatrixOfFinProb_offdiag
    (p : InfoGeometry.FinProb (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    densityMatrixOfFinProb p i j = 0 := by
  simp [densityMatrixOfFinProb, firstQuantize, diagMatrix, hij]

omit [Nonempty (Fin n)] in
@[simp] theorem logDensityOperator_diag
    (p : InfoGeometry.FinProb (Fin n)) (i : Fin n) :
    logDensityOperator p i i = InfoGeometry.log_density p i := by
  simp [logDensityOperator, firstQuantize, diagMatrix]

omit [Nonempty (Fin n)] in
@[simp] theorem surprisalOperator_diag
    (p : InfoGeometry.FinProb (Fin n)) (i : Fin n) :
    surprisalOperator p i i = InfoGeometry.surprisal p i := by
  simp [surprisalOperator, firstQuantize, diagMatrix]

omit [Nonempty (Fin n)] in
@[simp] theorem diagonalExpectation_firstQuantize
    (p : InfoGeometry.FinProb (Fin n)) (a : DiagObservable n) :
    diagonalExpectation p (firstQuantize (n := n) a) = ∑ i, (p i).toReal * a i := by
  unfold diagonalExpectation firstQuantize diagMatrix
  simp

/-- Shannon entropy is the expectation of the first-quantized surprisal operator. -/
theorem entropy_eq_diagonalExpectation_surprisalOperator
    (p : InfoGeometry.FinProb (Fin n)) :
    InfoGeometry.entropy p = diagonalExpectation p (surprisalOperator (n := n) p) := by
  unfold InfoGeometry.entropy InfoGeometry.expectation diagonalExpectation surprisalOperator
  simp [firstQuantize, diagMatrix]

end Normalized

section PositiveRay

variable {n : ℕ} [Nonempty (Fin n)]

/-- First-quantized log-density of a positive ray. -/
noncomputable def rayLogDensityOperator
    (q : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n)
    (fun i => InfoGeometry.Canonical.PositiveRayCore.logDensity (α := Fin n) q i)

/-- First-quantized modular potential of a positive ray. -/
noncomputable def modularPotentialOperator
    (q : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n)
    (fun i => InfoGeometry.Canonical.PositiveRayCore.modularPotential (α := Fin n) q i)

/-- First-quantized relative log-density between positive rays. -/
noncomputable def relativeLogDensityOperator
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n)
    (fun i => InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i)

/-- First-quantized relative modular potential / relative surprisal operator. -/
noncomputable def relativeModularPotentialOperator
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n)
    (fun i => InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential (α := Fin n) q q0 i)

@[simp] theorem rayLogDensityOperator_diag
    (q : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) (i : Fin n) :
    rayLogDensityOperator (n := n) q i i =
      InfoGeometry.Canonical.PositiveRayCore.logDensity (α := Fin n) q i := by
  rw [rayLogDensityOperator, firstQuantize_apply_diag]

@[simp] theorem relativeLogDensityOperator_diag
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) (i : Fin n) :
    relativeLogDensityOperator (n := n) q q0 i i =
      InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i := by
  rw [relativeLogDensityOperator, firstQuantize_apply_diag]

@[simp] theorem relativeModularPotentialOperator_diag
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) (i : Fin n) :
    relativeModularPotentialOperator (n := n) q q0 i i =
      InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential (α := Fin n) q q0 i := by
  rw [relativeModularPotentialOperator, firstQuantize_apply_diag]

/-- The first-quantized relative log-density is the difference of log-density operators. -/
theorem relativeLogDensityOperator_eq_logDensityOperator_sub
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) :
    relativeLogDensityOperator (n := n) q q0 =
      rayLogDensityOperator (n := n) q - rayLogDensityOperator (n := n) q0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeLogDensityOperator_diag]
    change InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i =
      rayLogDensityOperator (n := n) q i i - rayLogDensityOperator (n := n) q0 i i
    rw [rayLogDensityOperator_diag, rayLogDensityOperator_diag]
    exact InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_eq_logDensity_sub_logDensity
      (q := q) (q0 := q0) (a := i)
  · have hq : rayLogDensityOperator (n := n) q i j = 0 := by
      rw [rayLogDensityOperator, firstQuantize_apply_offdiag (hij := hij)]
    have hq0 : rayLogDensityOperator (n := n) q0 i j = 0 := by
      rw [rayLogDensityOperator, firstQuantize_apply_offdiag (hij := hij)]
    rw [relativeLogDensityOperator, firstQuantize_apply_offdiag (hij := hij)]
    change 0 = rayLogDensityOperator (n := n) q i j - rayLogDensityOperator (n := n) q0 i j
    rw [hq, hq0]
    ring

/-- The first-quantized relative modular potential is the base-to-state log-density difference. -/
theorem relativeModularPotentialOperator_eq_logDensity_base_sub
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) :
    relativeModularPotentialOperator (n := n) q q0 =
      rayLogDensityOperator (n := n) q0 - rayLogDensityOperator (n := n) q := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeModularPotentialOperator_diag]
    change InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential (α := Fin n) q q0 i =
      rayLogDensityOperator (n := n) q0 i i - rayLogDensityOperator (n := n) q i i
    rw [rayLogDensityOperator_diag, rayLogDensityOperator_diag]
    exact InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_eq_logDensity_base_sub_logDensity
      (q := q) (q0 := q0) (a := i)
  · have hq0 : rayLogDensityOperator (n := n) q0 i j = 0 := by
      rw [rayLogDensityOperator, firstQuantize_apply_offdiag (hij := hij)]
    have hq : rayLogDensityOperator (n := n) q i j = 0 := by
      rw [rayLogDensityOperator, firstQuantize_apply_offdiag (hij := hij)]
    rw [relativeModularPotentialOperator, firstQuantize_apply_offdiag (hij := hij)]
    change 0 = rayLogDensityOperator (n := n) q0 i j - rayLogDensityOperator (n := n) q i j
    rw [hq0, hq]
    ring

end PositiveRay

section CountLift

variable {n : ℕ} [Nonempty (Fin n)]

/-- First-quantized raw relative count log-density. -/
noncomputable def relativeCountLogDensityOperator
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n) : FinMat n :=
  firstQuantize (n := n)
    (fun i => InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity n counts ref i)

/-- First-quantized raw relative modular potential from count ratios. -/
noncomputable def relativeCountModularPotentialOperator
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n) : FinMat n :=
  firstQuantize (n := n)
    (fun i => -InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity n counts ref i)

/-- Arithmetic mean of the diagonal of a finite operator. -/
noncomputable def diagonalAverage (A : FinMat n) : ℝ :=
  (n : ℝ)⁻¹ * diagonalMass A

omit [Nonempty (Fin n)] in
@[simp] theorem diagonalAverage_firstQuantize
    (a : DiagObservable n) :
    diagonalAverage (n := n) (firstQuantize (n := n) a) = (n : ℝ)⁻¹ * ∑ i, a i := by
  unfold diagonalAverage diagonalMass firstQuantize diagMatrix
  simp

/-- Count-ray relative modular potential lifts to a diagonal operator plus a scalar gauge shift. -/
theorem relativeModularPotentialOperator_countRay_eq_raw_add_massShift
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    relativeModularPotentialOperator (n := n)
        (InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
        (InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
      = relativeCountModularPotentialOperator (n := n) counts ref
        + Real.log
            (InfoGeometry.Canonical.RelativePotentialCountBridge.countMass counts hcounts /
              InfoGeometry.Canonical.RelativePotentialCountBridge.countMass ref href) •
            (1 : FinMat n) := by
  let c : ℝ := Real.log
    (InfoGeometry.Canonical.RelativePotentialCountBridge.countMass counts hcounts /
      InfoGeometry.Canonical.RelativePotentialCountBridge.countMass ref href)
  have hfun :
      (fun i =>
        InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential (α := Fin n)
          (InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
          (InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href) i)
        = (fun i =>
            -InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity n counts ref i + c) := by
    funext i
    dsimp [c]
    rw [InfoGeometry.Canonical.RelativePotentialCountBridge.relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_add_massShift]
  rw [relativeModularPotentialOperator, hfun]
  rw [firstQuantize_add, firstQuantize_const_eq_smul_one]
  rfl

/-- The scalar relative modular Hamiltonian is the diagonal average of the lifted raw modular potential. -/
theorem relativeModularHamiltonian_eq_diagonalAverage_rawLift
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n) :
    InfoGeometry.Canonical.RelativePotentialCountBridge.relativeModularHamiltonian n
        (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity n counts ref)
      = diagonalAverage (n := n) (relativeCountModularPotentialOperator (n := n) counts ref) := by
  unfold InfoGeometry.Canonical.RelativePotentialCountBridge.relativeModularHamiltonian
  unfold InfoGeometry.Canonical.RelativePotentialCountBridge.relativeLogDensityMean
  unfold diagonalAverage diagonalMass
  simp [relativeCountModularPotentialOperator, firstQuantize, diagMatrix,
    InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity]

/-- The Tomita-Takesaki-style operator is the averaged relative surprisal times `Id`. -/
theorem relativeTomitaTakesakiOp_eq_diagonalAverage_rawLift_smul_id
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n) :
    InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n
        (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity n counts ref)
      = diagonalAverage (n := n) (relativeCountModularPotentialOperator (n := n) counts ref) •
          ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace (RouterAmplitude n)) := by
  unfold InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp
  exact congrArg
    (fun c : ℝ => c • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace (RouterAmplitude n)))
    (relativeModularHamiltonian_eq_diagonalAverage_rawLift (n := n)
      (counts := counts) (ref := ref))

end CountLift

section SpectralTaylor

variable {n : ℕ} [Nonempty (Fin n)]

local notation "EndRA" => EndH (RouterAmplitude n)

noncomputable local instance : NormedRing EndRA := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndRA := inferInstance
noncomputable local instance : NormedSpace ℝ EndRA := inferInstance
local instance : IsTopologicalRing EndRA := inferInstance
local instance : CompleteSpace EndRA := inferInstance

/-- First-order spectral/Taylor law for the lifted relative Tomita-Takesaki operator. -/
theorem hasDerivAt_informationPartitionFunction_zero_relativeTomitaTakesakiOp
    (ω : EndRA →L[ℝ] ℝ) (ρ : Fin n → ℝ) :
    HasDerivAt
      (fun τ : ℝ =>
        informationPartitionFunction ω
          (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ) τ)
      (ω (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ)) 0 :=
  hasDerivAt_informationPartitionFunction_zero
    (ω := ω) (K := InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ)

/-- Normalized log-partition Taylor law for the lifted relative Tomita-Takesaki operator. -/
theorem hasDerivAt_logInformationPartitionFunction_zero_relativeTomitaTakesakiOp_of_normalized
    (ω : EndRA →L[ℝ] ℝ)
    (hω1 : ω (1 : EndRA) = 1)
    (ρ : Fin n → ℝ) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ) τ)
      (ω (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ)) 0 :=
  hasDerivAt_logInformationPartitionFunction_zero_of_normalized
    (ω := ω) (K := InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n ρ) hω1

/-- Count-side specialization of the normalized spectral/Taylor law. -/
theorem hasDerivAt_logInformationPartitionFunction_zero_relativeCountLift_of_normalized
    (ω : EndRA →L[ℝ] ℝ)
    (hω1 : ω (1 : EndRA) = 1)
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n
            (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity n counts ref)) τ)
      (ω (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp n
        (InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity n counts ref))) 0 :=
  hasDerivAt_logInformationPartitionFunction_zero_relativeTomitaTakesakiOp_of_normalized
    (ω := ω) (hω1 := hω1)
    (ρ := InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity n counts ref)

end SpectralTaylor

end InfoGeometry.Canonical.RelativeSurprisalOperatorLift
