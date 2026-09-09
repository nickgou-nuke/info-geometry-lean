/-
InfoGeometry/OperatorAlgebra/ConstructiveKasparovBoundary.lean

Constructive Kasparov boundary and defect ledger.
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.BilingualAnalyticity

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary

open InfoGeometry.Geometry.BilingualAnalyticity

/-! ## 1. Algebraic Kasparov defects -/

/-- Left Kasparov defect `1 - F*F`. -/
def leftKasparovDefect
    {A : Type*} [Ring A] [Star A]
    (F : A) : A :=
  1 - star F * F

/-- Right Kasparov defect `1 - FF*`. -/
def rightKasparovDefect
    {A : Type*} [Ring A] [Star A]
    (F : A) : A :=
  1 - F * star F

/-- Involutive Kasparov defect `1 - F²`. -/
def involutiveKasparovDefect
    {A : Type*} [Ring A]
    (F : A) : A :=
  1 - F * F

/-- If `F*F = 1`, the left defect vanishes. -/
theorem leftKasparovDefect_eq_zero_of_isometry
    {A : Type*} [Ring A] [Star A]
    {F : A}
    (h : star F * F = 1) :
    leftKasparovDefect F = 0 := by
  dsimp [leftKasparovDefect]
  rw [h]
  simp

/-- If `FF* = 1`, the right defect vanishes. -/
theorem rightKasparovDefect_eq_zero_of_coisometry
    {A : Type*} [Ring A] [Star A]
    {F : A}
    (h : F * star F = 1) :
    rightKasparovDefect F = 0 := by
  dsimp [rightKasparovDefect]
  rw [h]
  simp

/-- If `F² = 1`, the involutive defect vanishes. -/
theorem involutiveKasparovDefect_eq_zero_of_square_one
    {A : Type*} [Ring A]
    {F : A}
    (h : F * F = 1) :
    involutiveKasparovDefect F = 0 := by
  dsimp [involutiveKasparovDefect]
  rw [h]
  simp

/--
Bundled bounded-transform defect laws.

This records the actual algebraic defects; interpreting any of them as a
boundary/horizon requires further model-specific structure.
-/
structure KasparovDefectDatum
    (A : Type*) [Ring A] [Star A] where
  /-- Bounded transform / phase operator. -/
  F : A

namespace KasparovDefectDatum

variable {A : Type*} [Ring A] [Star A]
variable (D : KasparovDefectDatum A)

/-- Left defect computed from the stored bounded transform. -/
def leftDefect : A :=
  leftKasparovDefect D.F

/-- Right defect computed from the stored bounded transform. -/
def rightDefect : A :=
  rightKasparovDefect D.F

/-- Involutive defect computed from the stored bounded transform. -/
def involutiveDefect : A :=
  involutiveKasparovDefect D.F

@[simp]
theorem leftDefect_eq :
    D.leftDefect = leftKasparovDefect D.F :=
  rfl

@[simp]
theorem rightDefect_eq :
    D.rightDefect = rightKasparovDefect D.F :=
  rfl

@[simp]
theorem involutiveDefect_eq :
    D.involutiveDefect = involutiveKasparovDefect D.F :=
  rfl

end KasparovDefectDatum

/-! ## 2. Graded kernel projector and index readout -/

/--
An idempotent kernel projector.

No analytic kernel construction is claimed here; this is the algebraic
projector once a concrete model has supplied one.
-/
structure KernelProjector
    (A : Type*) [Ring A] where
  Pker : A
  idempotent :
    Pker * Pker = Pker

namespace KernelProjector

variable {A : Type*} [Ring A]

/-- Invertible conjugation transports kernel projectors to kernel projectors. -/
def conjugate
    (P : KernelProjector A)
    (g : Units A) :
    KernelProjector A where
  Pker := g.val * P.Pker * g.inv
  idempotent := by
    calc
      (g.val * P.Pker * g.inv) * (g.val * P.Pker * g.inv)
          = g.val * P.Pker * (g.inv * g.val) * P.Pker * g.inv := by
            simp only [mul_assoc]
      _ = g.val * P.Pker * 1 * P.Pker * g.inv := by
            rw [g.inv_val]
      _ = g.val * (P.Pker * P.Pker) * g.inv := by
            simp only [mul_assoc, mul_one]
      _ = g.val * P.Pker * g.inv := by
            rw [P.idempotent]

/-- The conjugated kernel projector has the expected underlying element. -/
theorem conjugate_Pker
    (P : KernelProjector A)
    (g : Units A) :
    (P.conjugate g).Pker = g.val * P.Pker * g.inv :=
  rfl

end KernelProjector

/--
A super/graded readout.

This is not a bare trace. It is whatever graded integration backend the model
supplies.
-/
def SuperReadout
    (A Scalar : Type*) [Ring A] : Type _ :=
  A → Scalar

namespace SuperReadout

/-- The graded/super readout carried by the direct function owner. -/
abbrev read
    {A Scalar : Type*} [Ring A]
    (R : SuperReadout A Scalar) : A → Scalar :=
  R

/-- Construct a direct super readout. -/
def mk
    {A Scalar : Type*} [Ring A]
    (readout : A → Scalar) : SuperReadout A Scalar :=
  readout

end SuperReadout

/-- A unit-conjugation invariant superreadout. -/
def UnitInvariantSuperReadout
    (A Scalar : Type*) [Ring A] : Type _ :=
  {read : A → Scalar //
    ∀ (g : Units A) (x : A),
      read (g.val * x * g.inv) = read x}

namespace UnitInvariantSuperReadout

variable {A Scalar : Type*} [Ring A]
variable (R : UnitInvariantSuperReadout A Scalar)

/-- The readout carried by a unit-invariant superreadout. -/
abbrev read (R : UnitInvariantSuperReadout A Scalar) : A → Scalar :=
  R.1

/-- The unit-conjugation invariance law carried by the readout. -/
theorem invariant
    (R : UnitInvariantSuperReadout A Scalar)
    (g : Units A) (x : A) :
    read R (g.val * x * g.inv) = read R x :=
  R.2 g x

/-- Construct a unit-invariant superreadout from its law. -/
def mk
    (readout : A → Scalar)
    (h : ∀ (g : Units A) (x : A),
      readout (g.val * x * g.inv) = readout x) :
    UnitInvariantSuperReadout A Scalar :=
  ⟨readout, h⟩

/-- The graded index readout of a kernel projector. -/
def indexOf
    (P : KernelProjector A) : Scalar :=
  R.read P.Pker

/-- The index readout is invariant under unit-conjugation transport. -/
theorem indexOf_conjugate
    (P : KernelProjector A)
    (g : Units A) :
    R.indexOf (P.conjugate g) = R.indexOf P := by
  dsimp [indexOf]
  rw [KernelProjector.conjugate_Pker]
  exact invariant R g P.Pker

end UnitInvariantSuperReadout

/-! ## 3. Boundary defect ledger -/

/--
Boundary defect ledger.

This is the defect-supported Stokes statement:

`d_geo ω = defectDensity`

not the closed-form statement `d_geo ω = 0`.
-/
structure BoundaryDefectLedger
    (Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) where
  /-- Boundary one-form. -/
  omega :
    OperatorOneForm Point Tangent Value
  /-- Volume defect density. -/
  defectDensity :
    Point → Value
  /-- The geometric derivative of the boundary one-form is the defect density. -/
  derivative_eq_defect :
    ∀ p : Point,
      I.geometricDerivative omega p = defectDensity p

namespace BoundaryDefectLedger

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (L : BoundaryDefectLedger Region Point Tangent Value I)

/-- The boundary integral equals the volume integral of the defect density. -/
theorem boundaryIntegral_eq_volumeDefect
    (Ω : Region) :
    I.boundaryIntegral Ω L.omega =
      I.volumeIntegral Ω L.defectDensity := by
  rw [I.stokes_eq Ω L.omega]
  have h :
      I.geometricDerivative L.omega = L.defectDensity :=
    funext L.derivative_eq_defect
  rw [h]

/-- Closedness of the boundary form is equivalent to zero defect density. -/
theorem closed_iff_zero_defect :
    I.IsClosedGeometricForm L.omega ↔
      ∀ p : Point, L.defectDensity p = 0 := by
  constructor
  · intro h p
    rw [← L.derivative_eq_defect p]
    exact h p
  · intro h p
    rw [L.derivative_eq_defect p]
    exact h p

/-- If the defect density vanishes pointwise, the boundary integral vanishes. -/
theorem boundaryIntegral_eq_zero_of_zero_defect
    (Ω : Region)
    (hzero : ∀ p : Point, L.defectDensity p = 0) :
    I.boundaryIntegral Ω L.omega = 0 := by
  rw [L.boundaryIntegral_eq_volumeDefect Ω]
  exact
    I.volumeIntegral_zero_of_pointwise_zero
      Ω
      L.defectDensity
      hzero

end BoundaryDefectLedger

/-! ## 4. Kasparov boundary accounting package -/

/--
Constructive Kasparov boundary accounting package.

It packages algebraic bounded-transform defects, a graded kernel/index
readout, and a Stokes boundary/volume defect ledger. It does not claim a
physical anomaly or holographic reconstruction without a model-specific bridge.
-/
structure KasparovBoundaryAccounting
    (A Scalar Region Point Tangent Value : Type*)
    [Ring A] [Star A]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) where
  /-- Algebraic bounded-transform defect data. -/
  defect :
    KasparovDefectDatum A
  /-- Kernel projector. -/
  kernelProjector :
    KernelProjector A
  /-- Graded index readout. -/
  superReadout :
    SuperReadout A Scalar
  /-- Boundary/volume defect ledger. -/
  boundaryLedger :
    BoundaryDefectLedger Region Point Tangent Value I

namespace KasparovBoundaryAccounting

variable
    {A Scalar Region Point Tangent Value : Type*}
    [Ring A] [Star A]
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (K : KasparovBoundaryAccounting A Scalar Region Point Tangent Value I)

/-- The index readout is the graded/super readout of the kernel projector. -/
def index : Scalar :=
  SuperReadout.read K.superReadout K.kernelProjector.Pker

/-- Boundary equals volume defect by the stored boundary ledger. -/
theorem boundary_eq_volume_defect
    (Ω : Region) :
    I.boundaryIntegral Ω K.boundaryLedger.omega =
      I.volumeIntegral Ω K.boundaryLedger.defectDensity :=
  K.boundaryLedger.boundaryIntegral_eq_volumeDefect Ω

end KasparovBoundaryAccounting

end InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary
