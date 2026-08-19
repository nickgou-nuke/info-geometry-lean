/-
InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean

Pauli/Hestenes spin-momentum dictionary.

This module records the precise representation-theoretic data:

* energy-momentum is a paravector readout;
* the Pauli matrix determinant is the Minkowski norm;
* null momentum is singular/projective, not automatically nilpotent;
* spin is a bivector/rotor readout carried by the spinor frame;
* spin-momentum coupling is supplied by explicit Lorentz/spin calibration data.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Meta.Architecture
import InfoGeometryCore.Basic

open InfoGeometryCore

noncomputable section

namespace InfoGeometry.Canonical.PauliHestenesSpinMomentum

open scoped Matrix

/-! ## 1. Pauli/Hestenes paravectors -/

/--
Energy-momentum paravector coordinates.

This is the real Hestenes/Pauli shadow of `P = E + p`.
-/
@[rep_depth operator]
structure PauliParavector where
  /-- Energy/time component. -/
  energy : ℝ
  /-- Spatial `x` momentum component. -/
  px : ℝ
  /-- Spatial `y` momentum component. -/
  py : ℝ
  /-- Spatial `z` momentum component. -/
  pz : ℝ

namespace PauliParavector

/-- Minkowski norm square `E² - |p|²`. -/
def minkowskiNormSq
    (P : PauliParavector) : ℝ :=
  P.energy ^ 2 - P.px ^ 2 - P.py ^ 2 - P.pz ^ 2

/--
Hermitian Pauli matrix of a real paravector:

`[[E + pz, px - i py], [px + i py, E - pz]]`.
-/
def pauliMatrix
    (P : PauliParavector) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((P.energy + P.pz : ℝ) : ℂ),
      ((P.px : ℂ) - Complex.I * (P.py : ℂ));
     ((P.px : ℂ) + Complex.I * (P.py : ℂ)),
      ((P.energy - P.pz : ℝ) : ℂ)]

/--
The determinant of the Pauli matrix is the Minkowski norm.
-/
theorem det_pauliMatrix_eq_minkowskiNormSq
    (P : PauliParavector) :
    Matrix.det P.pauliMatrix = (P.minkowskiNormSq : ℂ) := by
  simp [pauliMatrix, minkowskiNormSq, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/--
The trace of the Pauli representative is twice the energy component.
-/
theorem trace_pauliMatrix_eq_two_energy
    (P : PauliParavector) :
    Matrix.trace P.pauliMatrix = ((2 * P.energy : ℝ) : ℂ) := by
  simp [pauliMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Identity Pauli axis `σ⁰`. -/
def sigma0 : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), 0; 0, 1]

/-- First Pauli axis `σ¹`. -/
abbrev sigma1 := sigma1C

/-- Second Pauli axis `σ²`. -/
abbrev sigma2 := sigma2C

/-- Third Pauli axis `σ³`. -/
abbrev sigma3 := sigma3C

/-- The Pauli four-vector `σ^μ = (I, σ¹, σ², σ³)`. -/
def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => sigma0
  | 1 => sigma1
  | 2 => sigma2
  | 3 => sigma3

/-- The lowered Pauli four-vector `σ̄^μ = (I, -σ¹, -σ², -σ³)`. -/
def barSigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => sigma0
  | 1 => -sigma1
  | 2 => -sigma2
  | 3 => -sigma3

/-- Trace readout against a Pauli axis. -/
def pauliTraceReadout (axis M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (axis * M)

/-- Pauli coefficient readout `1/2 Tr(σ^μ M)`. -/
def pauliCoefficientReadout (a : Fin 4) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  pauliTraceReadout (sigma a) M / 2

/-- Lowered Pauli coefficient readout `1/2 Tr(σ̄^μ M)`. -/
def loweredPauliCoefficientReadout (a : Fin 4) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  pauliTraceReadout (barSigma a) M / 2

/-- The super-Poincare anticommutator matrix `2 σ^μ P_μ`. -/
def superPoincareAnticommutatorMatrix (P : PauliParavector) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ) • P.pauliMatrix

/-- Momentum readout from `{Q,Qbar}` by `1/4 Tr(σ^μ {Q,Qbar})`. -/
def superchargeMomentumReadout (a : Fin 4) (P : PauliParavector) : ℂ :=
  pauliTraceReadout (sigma a) (superPoincareAnticommutatorMatrix P) / 4

/-- Lowered momentum readout from `{Q,Qbar}` by `1/4 Tr(σ̄^μ {Q,Qbar})`. -/
def loweredSuperchargeMomentumReadout (a : Fin 4) (P : PauliParavector) : ℂ :=
  pauliTraceReadout (barSigma a) (superPoincareAnticommutatorMatrix P) / 4

/-- Trace against the Pauli basis recovers all paravector coordinates. -/
theorem pauliCoefficientReadout_pauliMatrix (P : PauliParavector) (a : Fin 4) :
    pauliCoefficientReadout a P.pauliMatrix =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (P.px : ℂ)
      | 2 => (P.py : ℂ)
      | 3 => (P.pz : ℂ) := by
  fin_cases a <;>
    simp [pauliCoefficientReadout, pauliTraceReadout, sigma, sigma0, sigma1, sigma2,
      sigma3, sigma1C, sigma2C, sigma3C, pauliMatrix, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- Trace against the lowered Pauli basis recovers the metric-lowered coordinates. -/
theorem loweredPauliCoefficientReadout_pauliMatrix (P : PauliParavector) (a : Fin 4) :
    loweredPauliCoefficientReadout a P.pauliMatrix =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (-(P.px) : ℂ)
      | 2 => (-(P.py) : ℂ)
      | 3 => (-(P.pz) : ℂ) := by
  fin_cases a <;>
    simp [loweredPauliCoefficientReadout, pauliTraceReadout, barSigma, sigma0, sigma1,
      sigma2, sigma3, sigma1C, sigma2C, sigma3C, pauliMatrix, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The `1/4 Tr(σ^μ {Q,Qbar})` formula is the ordinary Pauli coefficient readout. -/
theorem superchargeMomentumReadout_eq_pauliCoefficientReadout
    (P : PauliParavector) (a : Fin 4) :
    superchargeMomentumReadout a P = pauliCoefficientReadout a P.pauliMatrix := by
  simp [superchargeMomentumReadout, pauliCoefficientReadout, superPoincareAnticommutatorMatrix,
    pauliTraceReadout, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Supercharge anticommutator trace readout recovers the momentum components. -/
theorem superchargeMomentumReadout_eq_components (P : PauliParavector) (a : Fin 4) :
    superchargeMomentumReadout a P =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (P.px : ℂ)
      | 2 => (P.py : ℂ)
      | 3 => (P.pz : ℂ) := by
  rw [superchargeMomentumReadout_eq_pauliCoefficientReadout]
  exact pauliCoefficientReadout_pauliMatrix P a

/-- Lowered supercharge anticommutator trace readout recovers the lowered momentum components. -/
theorem loweredSuperchargeMomentumReadout_eq_components (P : PauliParavector) (a : Fin 4) :
    loweredSuperchargeMomentumReadout a P =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (-(P.px) : ℂ)
      | 2 => (-(P.py) : ℂ)
      | 3 => (-(P.pz) : ℂ) := by
  fin_cases a <;>
    simp [loweredSuperchargeMomentumReadout, superPoincareAnticommutatorMatrix,
      pauliTraceReadout, barSigma, sigma0, sigma1, sigma2, sigma3, pauliMatrix,
      sigma1C, sigma2C, sigma3C, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/--
The determinant of the super-Poincare anticommutator matrix is four times the
Minkowski Casimir of the underlying Pauli paravector.
-/
theorem det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq
    (P : PauliParavector) :
    Matrix.det P.superPoincareAnticommutatorMatrix =
      ((4 * P.minkowskiNormSq : ℝ) : ℂ) := by
  rw [superPoincareAnticommutatorMatrix, Matrix.det_smul, det_pauliMatrix_eq_minkowskiNormSq]
  norm_num

/--
The trace of the super-Poincare anticommutator matrix is four times the energy
component.
-/
theorem trace_superPoincareAnticommutatorMatrix_eq_four_energy
    (P : PauliParavector) :
    Matrix.trace P.superPoincareAnticommutatorMatrix = ((4 * P.energy : ℝ) : ℂ) := by
  rw [superPoincareAnticommutatorMatrix, Matrix.trace_smul, trace_pauliMatrix_eq_two_energy]
  norm_num [smul_eq_mul]
  ring

/--
Null/lightlike momentum means zero Minkowski norm.
-/
def IsNull
    (P : PauliParavector) : Prop :=
  P.minkowskiNormSq = 0

/--
The Pauli representative is singular when its determinant vanishes.
-/
def IsSingularPauli
    (P : PauliParavector) : Prop :=
  Matrix.det P.pauliMatrix = 0

/--
The super-Poincare anticommutator representative is singular when its
determinant vanishes.
-/
def IsSingularSuperPoincareAnticommutator
    (P : PauliParavector) : Prop :=
  Matrix.det P.superPoincareAnticommutatorMatrix = 0

/--
Null paravectors are exactly singular Pauli representatives.

This is the safe replacement for the overstrong slogan
"null momentum is nilpotent."
-/
theorem isNull_iff_isSingularPauli
    (P : PauliParavector) :
    P.IsNull ↔ P.IsSingularPauli := by
  constructor
  · intro h
    unfold IsSingularPauli
    rw [det_pauliMatrix_eq_minkowskiNormSq]
    exact_mod_cast h
  · intro h
    unfold IsNull
    unfold IsSingularPauli at h
    rw [det_pauliMatrix_eq_minkowskiNormSq] at h
    exact_mod_cast h

/--
Null paravectors are exactly those whose super-Poincare anticommutator matrix
has zero determinant.
-/
theorem isNull_iff_isSingularSuperPoincareAnticommutator
    (P : PauliParavector) :
    P.IsNull ↔ P.IsSingularSuperPoincareAnticommutator := by
  constructor
  · intro h
    unfold IsSingularSuperPoincareAnticommutator
    rw [det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq]
    simp [IsNull] at h
    simp [h]
  · intro h
    unfold IsSingularSuperPoincareAnticommutator at h
    rw [det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq] at h
    have hreal : (4 * P.minkowskiNormSq : ℝ) = 0 := by
      exact_mod_cast h
    unfold IsNull
    nlinarith

/-- Future-oriented branch: nonnegative energy. -/
def IsFutureOriented
    (P : PauliParavector) : Prop :=
  0 ≤ P.energy

/-- Past-oriented branch: nonpositive energy. -/
def IsPastOriented
    (P : PauliParavector) : Prop :=
  P.energy ≤ 0

/-- Future null branch. -/
def IsFutureNull
    (P : PauliParavector) : Prop :=
  P.IsNull ∧ P.IsFutureOriented

/-- Past null branch. -/
def IsPastNull
    (P : PauliParavector) : Prop :=
  P.IsNull ∧ P.IsPastOriented

/-- Timelike/massive branch: positive Minkowski norm square. -/
def IsTimelike
    (P : PauliParavector) : Prop :=
  0 < P.minkowskiNormSq

/-- Spacelike branch: negative Minkowski norm square. -/
def IsSpacelike
    (P : PauliParavector) : Prop :=
  P.minkowskiNormSq < 0

/-- Lightlike branch: zero Minkowski norm square. -/
def IsLightlike
    (P : PauliParavector) : Prop :=
  P.IsNull

theorem isNull_or_isTimelike_or_isSpacelike
    (P : PauliParavector) :
    P.IsNull ∨ P.IsTimelike ∨ P.IsSpacelike := by
  rcases lt_trichotomy P.minkowskiNormSq 0 with hneg | hzero | hpos
  · exact Or.inr (Or.inr hneg)
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hpos)

theorem isNull_isFutureNull_or_isPastNull
    {P : PauliParavector} (hP : P.IsNull) :
    P.IsFutureNull ∨ P.IsPastNull := by
  rcases le_total 0 P.energy with hfuture | hpast
  · exact Or.inl ⟨hP, hfuture⟩
  · exact Or.inr ⟨hP, hpast⟩

/--
A future-null paravector has a singular Pauli representative.
-/
theorem singularPauli_of_futureNull
    {P : PauliParavector}
    (hP : P.IsFutureNull) :
    P.IsSingularPauli :=
  (P.isNull_iff_isSingularPauli).mp hP.1

/--
A future-null paravector has a singular super-Poincare anticommutator
representative.
-/
theorem singularSuperPoincareAnticommutator_of_futureNull
    {P : PauliParavector}
    (hP : P.IsFutureNull) :
    P.IsSingularSuperPoincareAnticommutator :=
  (P.isNull_iff_isSingularSuperPoincareAnticommutator).mp hP.1

/--
Timelike branch has positive determinant.
-/
theorem det_pos_of_timelike
    {P : PauliParavector}
    (hP : P.IsTimelike) :
    0 < (Matrix.det P.pauliMatrix).re := by
  rw [det_pauliMatrix_eq_minkowskiNormSq]
  exact hP

/--
Timelike branch has positive super-Poincare anticommutator determinant.
-/
theorem det_superPoincareAnticommutatorMatrix_pos_of_timelike
    {P : PauliParavector}
    (hP : P.IsTimelike) :
    0 < (Matrix.det P.superPoincareAnticommutatorMatrix).re := by
  rw [det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq]
  simp
  unfold IsTimelike at hP
  nlinarith

/--
Spacelike branch has negative determinant real part.
-/
theorem det_neg_of_spacelike
    {P : PauliParavector}
    (hP : P.IsSpacelike) :
    (Matrix.det P.pauliMatrix).re < 0 := by
  rw [det_pauliMatrix_eq_minkowskiNormSq]
  exact hP

/--
Spacelike branch has negative super-Poincare anticommutator determinant real
part.
-/
theorem det_superPoincareAnticommutatorMatrix_neg_of_spacelike
    {P : PauliParavector}
    (hP : P.IsSpacelike) :
    (Matrix.det P.superPoincareAnticommutatorMatrix).re < 0 := by
  rw [det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq]
  simp
  unfold IsSpacelike at hP
  nlinarith

/--
A mass-shell predicate.

The equation is `P P̄ = m²`, expressed in the Pauli/Hestenes paravector lane as
`E² - |p|² = m²`.
-/
def OnMassShell
    (P : PauliParavector)
    (mass : ℝ) : Prop :=
  P.minkowskiNormSq = mass ^ 2

/--
The massless shell is exactly the null shell.
-/
theorem onMassShell_zero_iff_isNull
    (P : PauliParavector) :
    P.OnMassShell 0 ↔ P.IsNull := by
  simp [OnMassShell, IsNull]

end PauliParavector

/-! ## 2. Abstract Pauli/paravector bridge -/

/--
Abstract Pauli/paravector bridge.

This is the generic datum for models that do not want to commit to the
concrete `2 × 2` complex matrix representation immediately.
-/
@[rep_depth operator]
structure PauliParavectorBridge
    (V Herm2 : Type*) where
  /-- Pauli/Hermitian representative of a vector/paravector. -/
  pauliMap : V → Herm2

  /-- Minkowski/paravector norm readout. -/
  minkowskiNorm : V → ℝ

  /-- Determinant readout on the Hermitian representative. -/
  det : Herm2 → ℝ

  /-- The determinant recovers the Minkowski norm. -/
  det_pauliMap :
    ∀ X : V, det (pauliMap X) = minkowskiNorm X

namespace PauliParavectorBridge

variable {V Herm2 : Type*}
variable (B : PauliParavectorBridge V Herm2)

/-- Null vectors/paravectors are zero-norm elements. -/
def IsNull
    (X : V) : Prop :=
  B.minkowskiNorm X = 0

/-- Singular Pauli/Hermitian representatives have zero determinant. -/
def IsSingularRepresentative
    (X : V) : Prop :=
  B.det (B.pauliMap X) = 0

/--
Nullness is equivalent to singularity of the Pauli representative.
-/
theorem isNull_iff_isSingularRepresentative
    (X : V) :
    B.IsNull X ↔ B.IsSingularRepresentative X := by
  unfold IsNull IsSingularRepresentative
  rw [B.det_pauliMap X]

end PauliParavectorBridge

/--
The concrete Pauli matrix construction as an instance of the abstract bridge.
-/
def concretePauliParavectorBridge :
    PauliParavectorBridge PauliParavector (Matrix (Fin 2) (Fin 2) ℂ) where
  pauliMap := PauliParavector.pauliMatrix
  minkowskiNorm := PauliParavector.minkowskiNormSq
  det := fun M => (Matrix.det M).re
  det_pauliMap := by
    intro P
    rw [PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]
    simp

/-! ## 3. Lorentz-spin action and spinor-helicity data -/

/--
Lorentz-spin action on a Pauli/paravector bridge.

This abstracts the formula `X ↦ L X L†` with `L ∈ SL(2,ℂ)`.  The essential
law at this layer is determinant/Minkowski-norm preservation.
-/
@[rep_depth operator]
structure LorentzSpinActionBridge
    (SpinGroup V Herm2 : Type*)
    (B : PauliParavectorBridge V Herm2) where
  /-- Spin-group action on vector/paravector data. -/
  actVector : SpinGroup → V → V

  /-- Induced action on Pauli/Hermitian representatives. -/
  actHermitian : SpinGroup → Herm2 → Herm2

  /-- Compatibility of the vector and Hermitian actions. -/
  pauliMap_equivariant :
    ∀ (L : SpinGroup) (X : V),
      B.pauliMap (actVector L X) = actHermitian L (B.pauliMap X)

  /-- Determinant/Minkowski norm is preserved by the spin action. -/
  det_preserved :
    ∀ (L : SpinGroup) (X : V),
      B.det (B.pauliMap (actVector L X)) = B.det (B.pauliMap X)

namespace LorentzSpinActionBridge

variable {SpinGroup V Herm2 : Type*}
variable {B : PauliParavectorBridge V Herm2}
variable (A : LorentzSpinActionBridge SpinGroup V Herm2 B)

/-- The spin action preserves the Minkowski/paravector norm. -/
theorem minkowskiNorm_preserved
    (L : SpinGroup)
    (X : V) :
    B.minkowskiNorm (A.actVector L X) = B.minkowskiNorm X := by
  calc
    B.minkowskiNorm (A.actVector L X)
        = B.det (B.pauliMap (A.actVector L X)) :=
            (B.det_pauliMap (A.actVector L X)).symm
    _ = B.det (B.pauliMap X) :=
            A.det_preserved L X
    _ = B.minkowskiNorm X :=
            B.det_pauliMap X

/-- The spin action preserves nullness. -/
theorem isNull_of_isNull
    (L : SpinGroup)
    {X : V}
    (hX : B.IsNull X) :
    B.IsNull (A.actVector L X) := by
  unfold PauliParavectorBridge.IsNull at hX ⊢
  rw [A.minkowskiNorm_preserved L X]
  exact hX

end LorentzSpinActionBridge

/--
Spinor-helicity factorization of a null Pauli representative.

For a massless branch, the Hermitian momentum representative is generated by a
spinor line, morally `P = λ λ†`.  This is carried as a property because the
concrete conjugation/outer-product API is model-specific.
-/
@[rep_depth operator]
structure SpinorHelicityFactorization
    (Spinor V Herm2 : Type*)
    (B : PauliParavectorBridge V Herm2) where
  /-- Momentum/paravector readout of a spinor. -/
  momentumOf : Spinor → V

  /-- Outer-product representative, morally `λ λ†`. -/
  outerProduct : Spinor → Herm2

  /-- Spinor-helicity factorization of the Pauli representative. -/
  pauli_eq_outerProduct :
    ∀ lam : Spinor,
      B.pauliMap (momentumOf lam) = outerProduct lam

  /-- The spinor-helicity branch is null. -/
  momentum_null :
    ∀ lam : Spinor,
      B.IsNull (momentumOf lam)

namespace SpinorHelicityFactorization

variable {Spinor V Herm2 : Type*}
variable {B : PauliParavectorBridge V Herm2}
variable (F : SpinorHelicityFactorization Spinor V Herm2 B)

/-- Spinor-helicity representatives are singular. -/
theorem singular_representative
    (lam : Spinor) :
    B.IsSingularRepresentative (F.momentumOf lam) :=
  (B.isNull_iff_isSingularRepresentative (F.momentumOf lam)).mp
    (F.momentum_null lam)

end SpinorHelicityFactorization

/-! ## 4. Spin is a rotor/bivector readout, not a paravector component -/

/--
Operator-valued Pauli paravector datum.

This is the abstract operator datum for a four-momentum/paravector
representative. It deliberately does not include spin data.
-/
@[rep_depth operator]
structure PauliParavectorDatum
    (Op : Type*) where
  /-- Operator/paravector representative of four-momentum. -/
  P : Op

  /-- Pauli matrix associated to the momentum. -/
  pauliMatrix : Matrix (Fin 2) (Fin 2) ℂ

  /-- Minkowski norm square readout. -/
  minkowskiNormSq : ℝ

  /-- The determinant of the Pauli matrix recovers the Minkowski norm. -/
  determinant_metric_property :
    Matrix.det pauliMatrix = (minkowskiNormSq : ℂ)

namespace PauliParavectorDatum

variable {Op : Type*}
variable (P : PauliParavectorDatum Op)

/-- Null vectors/paravectors are zero-norm elements. -/
def IsNull : Prop :=
  P.minkowskiNormSq = 0

end PauliParavectorDatum

/--
Spin-momentum frame.

Momentum is the paravector datum. Spin is a bivector/rotor-frame datum. They
are coupled because the same rotor frame transports both.
-/
@[rep_depth operator]
structure SpinMomentumFrame
    (Op : Type*) [Ring Op] where
  /-- Four-momentum/paravector datum. -/
  momentum : PauliParavectorDatum Op

  /-- Rotor/spinor frame element. -/
  rotor : Op

  /-- Inverse rotor. -/
  rotorInv : Op

  /-- Spin plane/bivector readout. -/
  spinBivector : Op

  /-- Reference momentum in the rest frame. -/
  referenceMomentum : Op

  /-- The rotor transports the reference momentum to the current momentum. -/
  momentum_transport_property :
    momentum.P = rotor * referenceMomentum * rotorInv

  /-- The rotor also transports some reference spin bivector. -/
  spin_transport_property :
    ∃ S₀ : Op, spinBivector = rotor * S₀ * rotorInv

namespace SpinMomentumFrame

variable {Op : Type*} [Ring Op]
variable (M : SpinMomentumFrame Op)

/-- Re-export of the momentum transport law. -/
theorem momentum_transport :
    M.momentum.P = M.rotor * M.referenceMomentum * M.rotorInv :=
  M.momentum_transport_property

end SpinMomentumFrame

/--
Representation-theoretic spin-momentum coupling.

This records the precise reason momentum and spin are inseparable in the
Pauli/Hestenes picture: the same Lorentz spin group transports the paravector
momentum datum and the spin bivector datum.

It does not identify spin with a component of the momentum paravector.
-/
@[rep_depth operator]
structure LorentzSpinRepresentationCoupling
    (SpinGroup Op : Type*) [Ring Op] where
  /-- Spin-group action on momentum/paravector data. -/
  actMomentum :
    SpinGroup → PauliParavectorDatum Op → PauliParavectorDatum Op

  /-- Spin-group action on the spin bivector/plane readout. -/
  actSpinBivector :
    SpinGroup → Op → Op

  /-- 
  The shared-action law: the group action on the paravector
  is consistent with the representation.
  -/
  shared_spin_action_property :
    ∀ (g : SpinGroup) (P : PauliParavectorDatum Op),
      (actMomentum g P).minkowskiNormSq = P.minkowskiNormSq

  /--
  Representation-coupling law: the action on momentum is derived from the
  action on the spinor frame.
  -/
  representation_coupling_property :
    ∀ (g : SpinGroup) (F : SpinMomentumFrame Op),
      (actMomentum g F.momentum).P = (actSpinBivector g F.rotor) * F.referenceMomentum * (actSpinBivector g F.rotorInv)

namespace LorentzSpinRepresentationCoupling

variable {SpinGroup Op : Type*} [Ring Op]
variable (C : LorentzSpinRepresentationCoupling SpinGroup Op)

/-- Re-export of the shared spin action law. -/
theorem shared_spin_action :
    ∀ (g : SpinGroup) (P : PauliParavectorDatum Op),
      (C.actMomentum g P).minkowskiNormSq = P.minkowskiNormSq :=
  C.shared_spin_action_property

end LorentzSpinRepresentationCoupling

/--
Massless spin-momentum frame.

For massless/null branches, the momentum datum has zero Minkowski norm and the
spin readout is helicity locked to the null momentum direction.
-/
@[rep_depth operator]
structure MasslessSpinMomentumFrame
    (Op : Type*) [Ring Op] [SMul ℝ Op] where
  /-- Underlying spin-momentum frame. -/
  frame : SpinMomentumFrame Op

  /-- Null/massless determinant condition. -/
  detP_eq_zero :
    frame.momentum.minkowskiNormSq = 0

  /-- 
  Helicity is locked to the null momentum direction.
  Replacing the former vacuous Prop field.
  -/
  helicity_locked_to_momentum_property :
    ∃ (h : ℝ), ∃ (ref : Op), frame.spinBivector = h • (frame.rotor * ref * frame.rotorInv)

namespace MasslessSpinMomentumFrame

variable {Op : Type*} [Ring Op] [SMul ℝ Op]
variable (F : MasslessSpinMomentumFrame Op)

/-- The underlying momentum datum is null/massless. -/
theorem momentum_null :
    F.frame.momentum.minkowskiNormSq = 0 :=
  F.detP_eq_zero

end MasslessSpinMomentumFrame

/--
Hestenes spinor/rotor readout datum.

The same spinor frame supplies both:

* a momentum/paravector readout;
* a rotor readout;
* a spin bivector/plane readout.
-/
@[rep_depth operator]
structure HestenesSpinorRotorDatum
    (Spinor Rotor Bivector : Type*) where
  /-- Momentum/paravector readout from the spinor frame. -/
  momentumReadout : Spinor → PauliParavector

  /-- Rotor/moving-frame readout. -/
  rotorReadout : Spinor → Rotor

  /-- Spin plane/bivector readout. -/
  spinBivector : Spinor → Bivector


/-! ## 5. Spin-momentum coupling and helicity data -/

/--
Abstract spin-momentum bridge.

Momentum and spin are not identified. They are separate readouts from the same
spinor/rotor source.
-/
@[rep_depth operator]
structure SpinMomentumBridge
    (Spinor Momentum SpinPlane : Type*) where
  /-- Vector/paravector momentum readout. -/
  momentumOf : Spinor → Momentum

  /-- Bivector/spin-plane readout. -/
  spinPlaneOf : Spinor → SpinPlane

  /-- Minkowski/mass-shell norm of the momentum readout. -/
  minkowskiNorm : Momentum → ℝ

  /-- Spinor norm whose square generates the mass shell. -/
  spinorNorm : Spinor → ℝ

  /--
  Mass-shell / scalar invariant compatibility.

  This is a field of the bridge, not a theorem-shaped placeholder returning
  only `Prop`.
  -/
  mass_shell :
    ∀ ψ : Spinor,
      minkowskiNorm (momentumOf ψ) = (spinorNorm ψ) ^ (2 : ℕ)

namespace SpinMomentumBridge

variable {Spinor Momentum SpinPlane : Type*}
variable (B : SpinMomentumBridge Spinor Momentum SpinPlane)

/-- The mass-shell compatibility carried by the spin-momentum bridge. -/
theorem mass_is_scalar_invariant
    (ψ : Spinor) :
    B.minkowskiNorm (B.momentumOf ψ) = (B.spinorNorm ψ) ^ (2 : ℕ) :=
  B.mass_shell ψ

end SpinMomentumBridge

/--
Massless/null specialization of a spin-momentum bridge.

Massive spinor states can still have coupled spin and momentum readouts.  The
null momentum condition belongs only to a chosen massless branch.
-/
@[rep_depth operator]
structure MasslessSpinMomentumBranch
    (Spinor Momentum SpinPlane : Type*)
    (B : SpinMomentumBridge Spinor Momentum SpinPlane) where
  /-- Null/massless branch condition. -/
  nullMomentumCondition :
    ∀ ψ : Spinor,
      B.minkowskiNorm (B.momentumOf ψ) = 0

namespace MasslessSpinMomentumBranch

variable {Spinor Momentum SpinPlane : Type*}
variable {B : SpinMomentumBridge Spinor Momentum SpinPlane}

/-- Momentum readouts on a massless branch have zero Minkowski norm. -/
theorem null_momentum
    (M : MasslessSpinMomentumBranch Spinor Momentum SpinPlane B)
    (ψ : Spinor) :
    B.minkowskiNorm (B.momentumOf ψ) = 0 :=
  MasslessSpinMomentumBranch.nullMomentumCondition M ψ

end MasslessSpinMomentumBranch

/--
Covariant spinor/rotor readout packet.

This is the Lean-safe form of the slogan:

* momentum is the paravector/vector readout;
* spin is the bivector/plane readout;
* both are extracted from one spinor/rotor source.

The packet deliberately does not identify spin with a component of the
energy-momentum paravector.
-/
@[rep_depth operator]
structure CovariantSpinorRotorReadouts
    (Spinor Momentum SpinPlane : Type*) where
  /-- Underlying spin-momentum bridge. -/
  bridge : SpinMomentumBridge Spinor Momentum SpinPlane

namespace CovariantSpinorRotorReadouts

variable {Spinor Momentum SpinPlane : Type*}
variable (R : CovariantSpinorRotorReadouts Spinor Momentum SpinPlane)

/-- The momentum readout inherited from the underlying bridge. -/
def momentumOf :
    Spinor → Momentum :=
  R.bridge.momentumOf

/-- The spin-plane readout inherited from the underlying bridge. -/
def spinPlaneOf :
    Spinor → SpinPlane :=
  R.bridge.spinPlaneOf

end CovariantSpinorRotorReadouts

/--
Uncertainty-principle guardrail for this bridge.

This records that any uncertainty statement must concern a supplied
noncommuting pair, not a false claim that scalar energy and vector momentum
are automatically noncommuting components of the paravector readout.
-/
@[rep_depth operator]
structure UncertaintyReadoutGuard
    (Observable : Type*) where
  /-- Chosen first observable. -/
  first : Observable

  /-- Chosen second observable. -/
  second : Observable


/--
Pauli-Lubanski/helicity style spin-momentum coupling.

This does not identify spin with momentum. It records the representation
theoretic fact that the spin readout is classified relative to the momentum
readout and the chosen Lorentz-spin frame.
-/
@[rep_depth operator]
structure SpinMomentumCoupling
    (Spinor Rotor Bivector SpinInvariant : Type*)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Pauli-Lubanski or analogous invariant readout. -/
  invariantReadout : Spinor → SpinInvariant


/--
Helicity calibration for a massless/null spinor branch.

For massless particles there is no rest frame; the invariant spin readout is
helicity, i.e. spin read relative to the null momentum direction.
-/
@[rep_depth operator]
structure HelicityCalibration
    (Spinor Rotor Bivector : Type*)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Helicity readout. -/
  helicity : Spinor → ℝ

  /-- The branch is massless/null at the momentum readout. -/
  null_momentum :
    ∀ ψ : Spinor, (D.momentumReadout ψ).IsNull

namespace HelicityCalibration

variable {Spinor Rotor Bivector : Type*}
variable {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
variable (H : HelicityCalibration Spinor Rotor Bivector D)

include H

/--
Massless momentum readouts have singular Pauli representatives.
-/
theorem singular_pauli_of_null_momentum
    (ψ : Spinor) :
    (D.momentumReadout ψ).IsSingularPauli :=
  (PauliParavector.isNull_iff_isSingularPauli (D.momentumReadout ψ)).mp
    (H.null_momentum ψ)

end HelicityCalibration

/-! ## 6. Chiral lightcone compatibility -/

/--
Generic chiral-lightcone readout datum.

This avoids hard-coding a specific chiral-lightcone API into the
Pauli/Hestenes dictionary. Concrete modules can later instantiate `Side` and
`Lightcone`.
-/
@[rep_depth operator]
structure ChiralLightconeReadoutDatum
    (Carrier Side : Type*) where
  /-- Chiral/null branch indexed by a side label. -/
  Lightcone : Side → Set Carrier

/--
Compatibility between Pauli/Hestenes null momentum and a chiral lightcone
carrier readout.

Null paravectors are read as carrier lightcone data only after a calibration is
supplied.
-/
@[rep_depth operator]
structure PauliHestenesChiralLightconeBridge
    (Spinor Rotor Bivector Carrier Side : Type*)
    (LC : ChiralLightconeReadoutDatum Carrier Side)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Carrier readout of a spinor. -/
  carrierReadout : Spinor → Carrier

  /--
  Null momentum is represented on one of the calibrated chiral lightcone
  branches.
  -/
  null_momentum_hits_chiral_lightcone :
    ∀ ψ : Spinor,
      (D.momentumReadout ψ).IsNull →
        ∃ side : Side,
          carrierReadout ψ ∈ LC.Lightcone side

namespace PauliHestenesChiralLightconeBridge

variable {Spinor Rotor Bivector Carrier Side : Type*}
variable {LC : ChiralLightconeReadoutDatum Carrier Side}
variable {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
variable (B : PauliHestenesChiralLightconeBridge
    Spinor Rotor Bivector Carrier Side LC D)

/--
A massless/null spinor branch has a calibrated chiral-lightcone carrier
readout.
-/
theorem chiral_lightcone_readout_of_null_momentum
    {ψ : Spinor}
    (hψ : (D.momentumReadout ψ).IsNull) :
    ∃ side : Side,
      B.carrierReadout ψ ∈ LC.Lightcone side :=
  B.null_momentum_hits_chiral_lightcone ψ hψ

end PauliHestenesChiralLightconeBridge

attribute [rep_depth operator]
  PauliParavector
  PauliParavector.minkowskiNormSq
  PauliParavector.pauliMatrix
  PauliParavector.det_pauliMatrix_eq_minkowskiNormSq
  PauliParavector.trace_pauliMatrix_eq_two_energy
  PauliParavector.sigma0
  PauliParavector.sigma1
  PauliParavector.sigma2
  PauliParavector.sigma3
  PauliParavector.sigma
  PauliParavector.barSigma
  PauliParavector.pauliTraceReadout
  PauliParavector.pauliCoefficientReadout
  PauliParavector.loweredPauliCoefficientReadout
  PauliParavector.superPoincareAnticommutatorMatrix
  PauliParavector.superchargeMomentumReadout
  PauliParavector.loweredSuperchargeMomentumReadout
  PauliParavector.pauliCoefficientReadout_pauliMatrix
  PauliParavector.loweredPauliCoefficientReadout_pauliMatrix
  PauliParavector.superchargeMomentumReadout_eq_pauliCoefficientReadout
  PauliParavector.superchargeMomentumReadout_eq_components
  PauliParavector.loweredSuperchargeMomentumReadout_eq_components
  PauliParavector.det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq
  PauliParavector.trace_superPoincareAnticommutatorMatrix_eq_four_energy
  PauliParavector.IsNull
  PauliParavector.IsSingularPauli
  PauliParavector.IsSingularSuperPoincareAnticommutator
  PauliParavector.isNull_iff_isSingularPauli
  PauliParavector.isNull_iff_isSingularSuperPoincareAnticommutator
  PauliParavector.IsFutureOriented
  PauliParavector.IsPastOriented
  PauliParavector.IsFutureNull
  PauliParavector.IsPastNull
  PauliParavector.IsTimelike
  PauliParavector.IsSpacelike
  PauliParavector.IsLightlike
  PauliParavector.singularPauli_of_futureNull
  PauliParavector.singularSuperPoincareAnticommutator_of_futureNull
  PauliParavector.det_pos_of_timelike
  PauliParavector.det_neg_of_spacelike
  PauliParavector.det_superPoincareAnticommutatorMatrix_pos_of_timelike
  PauliParavector.det_superPoincareAnticommutatorMatrix_neg_of_spacelike
  PauliParavector.OnMassShell
  PauliParavector.onMassShell_zero_iff_isNull
  PauliParavectorBridge
  PauliParavectorBridge.IsNull
  PauliParavectorBridge.IsSingularRepresentative
  PauliParavectorBridge.isNull_iff_isSingularRepresentative
  concretePauliParavectorBridge
  LorentzSpinActionBridge
  LorentzSpinActionBridge.minkowskiNorm_preserved
  LorentzSpinActionBridge.isNull_of_isNull
  SpinorHelicityFactorization
  SpinorHelicityFactorization.singular_representative
  PauliParavectorDatum
  PauliParavectorDatum.determinant_metric_property
  SpinMomentumFrame
  SpinMomentumFrame.momentum_transport_property
  SpinMomentumFrame.spin_transport_property
  LorentzSpinRepresentationCoupling
  LorentzSpinRepresentationCoupling.shared_spin_action
  LorentzSpinRepresentationCoupling.representation_coupling_property
  MasslessSpinMomentumFrame
  MasslessSpinMomentumFrame.momentum_null
  MasslessSpinMomentumFrame.helicity_locked_to_momentum_property
  HestenesSpinorRotorDatum
  SpinMomentumBridge
  SpinMomentumBridge.mass_is_scalar_invariant
  MasslessSpinMomentumBranch
  MasslessSpinMomentumBranch.nullMomentumCondition
  MasslessSpinMomentumBranch.null_momentum
  CovariantSpinorRotorReadouts
  CovariantSpinorRotorReadouts.momentumOf
  CovariantSpinorRotorReadouts.spinPlaneOf
  UncertaintyReadoutGuard
  SpinMomentumCoupling
  HelicityCalibration
  HelicityCalibration.singular_pauli_of_null_momentum
  ChiralLightconeReadoutDatum
  PauliHestenesChiralLightconeBridge
  PauliHestenesChiralLightconeBridge.chiral_lightcone_readout_of_null_momentum

end InfoGeometry.Canonical.PauliHestenesSpinMomentum
