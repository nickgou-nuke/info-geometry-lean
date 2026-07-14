/-
InfoGeometry/Geometry/ConstructiveKasparov.lean

Constructive Kasparov residue/index bridge.

This module removes rhetorical/global assumptions and replaces them with
computable finite readouts and derived theorems.

Core chain:

  projected finite kernel
    -> graded finite index
    -> algebraic defect P = 1 - F^2
    -> Stokes boundary = volume defect
    -> residue winding = index
    -> nonzero residue obstructs flow to Flat
-/

import Mathlib
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Geometry.SpectralDivisors

noncomputable section

namespace ConstructiveKasparov

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors

/-! ## 0. Existing bounded-Dirac algebra -/

structure VerifiedBoundedDirac (A : Type*) [Ring A] where
  F : A
  P : A
  F_sq_add_P : F * F + P = 1
  F_P_zero : F * P = 0
  P_F_zero : P * F = 0
  P_sq : P * P = P

theorem F_cube_eq_F {A : Type*} [Ring A]
    (D : VerifiedBoundedDirac A) :
    D.F * D.F * D.F = D.F := by
  have h1 : D.F * D.F = 1 - D.P := by
    calc
      D.F * D.F
          = D.F * D.F + D.P - D.P := by
            rw [add_sub_cancel_right]
      _ = 1 - D.P := by
            rw [D.F_sq_add_P]
  calc
    D.F * D.F * D.F
        = (1 - D.P) * D.F := by
          rw [h1]
    _ = 1 * D.F - D.P * D.F := by
          rw [sub_mul]
    _ = D.F - 0 := by
          rw [one_mul, D.P_F_zero]
    _ = D.F := by
          rw [sub_zero]

structure KasparovIndexDatum
    (A Scalar : Type*) [Ring A] [AddCommGroup Scalar] where
  superReadout : A → Scalar
  super_sub :
    ∀ x y : A, superReadout (x - y) = superReadout x - superReadout y

theorem mckean_singer_is_kasparov_defect
    {A Scalar : Type*} [Ring A] [AddCommGroup Scalar]
    (D : VerifiedBoundedDirac A)
    (Idx : KasparovIndexDatum A Scalar) :
    Idx.superReadout D.P =
      Idx.superReadout 1 - Idx.superReadout (D.F * D.F) := by
  have hP : D.P = 1 - D.F * D.F := by
    calc
      D.P
          = D.F * D.F + D.P - D.F * D.F := by
            rw [add_sub_cancel_left]
      _ = 1 - D.F * D.F := by
            rw [D.F_sq_add_P]
  rw [hP]
  exact Idx.super_sub 1 (D.F * D.F)

/-! ## 1. Finite graded kernel index -/

/--
The two kernel grades used for a finite Fredholm/Kasparov index readout.
-/
inductive KernelGrade where
  | even
  | odd
deriving DecidableEq, Repr

namespace KernelGrade

/--
The signed contribution of a kernel mode.
-/
def weight : KernelGrade → ℤ
  | even => 1
  | odd => -1

end KernelGrade

/--
A finite graded kernel datum.

This is the constructive replacement for an asymptotic heat-kernel trace:
the index is computed from an explicit finite list of kernel modes.
-/
structure FiniteGradedKernelDatum
    (State Mode : Type*) where
  /-- Finite kernel basis/mode list for a state. -/
  kernelBasis : State → List Mode

  /-- Grade of each mode. -/
  grade : Mode → KernelGrade

namespace FiniteGradedKernelDatum

variable {State Mode : Type*}
variable (K : FiniteGradedKernelDatum State Mode)

/--
Boolean test for even modes.
-/
def modeIsEven
    (m : Mode) : Bool :=
  match K.grade m with
  | KernelGrade.even => true
  | KernelGrade.odd => false

/--
Boolean test for odd modes.
-/
def modeIsOdd
    (m : Mode) : Bool :=
  match K.grade m with
  | KernelGrade.even => false
  | KernelGrade.odd => true

/--
Even kernel modes of a state.
-/
def evenModes
    (x : State) : List Mode :=
  (K.kernelBasis x).filter (fun m => K.modeIsEven m)

/--
Odd kernel modes of a state.
-/
def oddModes
    (x : State) : List Mode :=
  (K.kernelBasis x).filter (fun m => K.modeIsOdd m)

/--
The finite graded kernel index.

This is the constructive Fredholm/Kasparov index readout:

`# even kernel modes - # odd kernel modes`.
-/
def kernelIndex
    (x : State) : ℤ :=
  ((K.evenModes x).length : ℤ) -
    ((K.oddModes x).length : ℤ)

/--
The index is definitionally the even count minus the odd count.
-/
theorem kernelIndex_eq_even_count_sub_odd_count
    (x : State) :
    K.kernelIndex x =
      ((K.evenModes x).length : ℤ) -
        ((K.oddModes x).length : ℤ) :=
  rfl

/--
If the finite kernel basis is empty, the finite index is zero.
-/
theorem kernelIndex_eq_zero_of_kernelBasis_eq_nil
    {x : State}
    (hx : K.kernelBasis x = []) :
    K.kernelIndex x = 0 := by
  simp [kernelIndex, evenModes, oddModes, hx]

/--
A nonzero finite index forces the kernel list to contain a mode.
-/
theorem exists_mode_of_kernelIndex_ne_zero
    {x : State}
    (hx : K.kernelIndex x ≠ 0) :
    ∃ m : Mode, m ∈ K.kernelBasis x := by
  cases hlist : K.kernelBasis x with
  | nil =>
      exfalso
      exact hx (K.kernelIndex_eq_zero_of_kernelBasis_eq_nil hlist)
  | cons m _ms =>
      exact ⟨m, by simp⟩

/-- A nonzero finite index forces the kernel basis to be nonempty. -/
theorem kernelBasis_nonempty_of_kernelIndex_ne_zero
    {x : State}
    (hx : K.kernelIndex x ≠ 0) :
    K.kernelBasis x ≠ [] := by
  intro hEmpty
  exact hx (K.kernelIndex_eq_zero_of_kernelBasis_eq_nil hEmpty)

end FiniteGradedKernelDatum

/-! ## 2. Algebraic Kasparov defect and projected kernel -/

/--
A constructive Kasparov datum.

`Pker` is not independently postulated. It is obtained by applying a concrete
projection/readout map to the algebraic defect `1 - F^2`.
-/
structure ConstructiveKasparovDatum
    (State Op Projection Mode : Type*)
    [Ring Op] where
  /-- Kasparov/Fredholm phase operator. -/
  F : State → Op

  /-- Concrete readout sending an algebraic defect to a kernel projection. -/
  defectToKernelProjection : Op → Projection

  /-- Finite basis/readout of the range of a projected kernel. -/
  kernelBasisOfProjection : Projection → List Mode

  /-- Grade of each projected kernel mode. -/
  grade : Mode → KernelGrade

namespace ConstructiveKasparovDatum

variable {State Op Projection Mode : Type*}
variable [Ring Op]
variable (K : ConstructiveKasparovDatum State Op Projection Mode)

/--
The strict algebraic Kasparov defect: `P = 1 - F^2`.
-/
def defect
    (x : State) : Op :=
  1 - K.F x * K.F x

/--
The defect is definitionally `1 - F^2`.
-/
theorem defect_eq_one_sub_square
    (x : State) :
    K.defect x = 1 - K.F x * K.F x :=
  rfl

/--
The projected kernel readout of the algebraic defect.
-/
def Pker
    (x : State) : Projection :=
  K.defectToKernelProjection (K.defect x)

/--
The projected kernel is obtained from the strict defect.
-/
theorem Pker_eq_defect_readout
    (x : State) :
    K.Pker x =
      K.defectToKernelProjection (1 - K.F x * K.F x) :=
  rfl

/--
Finite kernel basis extracted from the projected defect.
-/
def kernelBasis
    (x : State) : List Mode :=
  K.kernelBasisOfProjection (K.Pker x)

/--
The associated finite graded kernel datum.
-/
def finiteKernelDatum :
    FiniteGradedKernelDatum State Mode where
  kernelBasis := K.kernelBasis
  grade := K.grade

/--
The constructive finite index of a state.
-/
def index
    (x : State) : ℤ :=
  K.finiteKernelDatum.kernelIndex x

/--
The index is computed from the projected kernel basis.
-/
theorem index_eq_projected_kernel_index
    (x : State) :
    K.index x =
      K.finiteKernelDatum.kernelIndex x :=
  rfl

/--
If the projected kernel basis is empty, the constructive index is zero.
-/
theorem index_eq_zero_of_projected_kernel_empty
    {x : State}
    (hx : K.kernelBasis x = []) :
    K.index x = 0 := by
  simpa [index, finiteKernelDatum, kernelBasis] using
    K.finiteKernelDatum.kernelIndex_eq_zero_of_kernelBasis_eq_nil
      (x := x) hx

/--
A nonzero constructive index produces an explicit projected kernel mode.
-/
theorem exists_projected_kernel_mode_of_index_ne_zero
    {x : State}
    (hx : K.index x ≠ 0) :
    ∃ m : Mode, m ∈ K.kernelBasis x :=
  K.finiteKernelDatum.exists_mode_of_kernelIndex_ne_zero
    (x := x)
    (by simpa [index] using hx)

end ConstructiveKasparovDatum

/-! ## 3. Stokes bridge from boundary to volume defect -/

/--
An exact Stokes defect bridge.

The density is not guessed. It is the geometric derivative of the boundary
one-form, expressed through an explicit equality.
-/
structure ExactDefectStokesBridge
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (ω : OperatorOneForm Point Tangent Value) where
  /-- Volume defect density. -/
  defectDensity : Point → Value

  /-- The defect density is exactly the geometric derivative of the boundary form. -/
  geometricDerivative_eq_defectDensity :
    ∀ p : Point,
      I.geometricDerivative ω p = defectDensity p

namespace ExactDefectStokesBridge

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {ω : OperatorOneForm Point Tangent Value}

variable (B : ExactDefectStokesBridge I ω)

/--
The boundary integral equals the volume integral of the defect density.

This is the formal boundary/volume equality. It is derived from the supplied
Stokes backend and the explicit density equality.
-/
theorem boundaryIntegral_eq_volumeDefect
    (Ω : Region) :
    I.boundaryIntegral Ω ω =
      I.volumeIntegral Ω B.defectDensity := by
  rw [I.stokes_eq Ω ω]
  exact
    congrArg (I.volumeIntegral Ω)
      (funext B.geometricDerivative_eq_defectDensity)

/--
If the boundary form is geometrically closed, the volume defect vanishes.
-/
theorem volumeDefect_eq_zero_of_closed
    (Ω : Region)
    (hclosed : I.IsClosedGeometricForm ω) :
    I.volumeIntegral Ω B.defectDensity = 0 := by
  apply I.volumeIntegral_zero_of_pointwise_zero
  intro p
  rw [← B.geometricDerivative_eq_defectDensity p]
  exact hclosed p

/--
If the boundary form is geometrically closed, the boundary integral vanishes.
-/
theorem boundaryIntegral_eq_zero_of_closed
    (Ω : Region)
    (hclosed : I.IsClosedGeometricForm ω) :
    I.boundaryIntegral Ω ω = 0 := by
  exact I.boundaryIntegral_eq_zero_of_closed Ω ω hclosed

end ExactDefectStokesBridge

/-! ## 4. Residue/winding readout of the volume defect -/

namespace ExactDefectStokesBridge

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}

variable (B : ExactDefectStokesBridge I ω)

/--
The volume defect is the winding times the phase period.
-/
theorem volumeDefect_eq_winding_period
    (Ω : Region) :
    I.volumeIntegral Ω B.defectDensity =
      (W.winding Ω : ℝ) • N.phasePeriod := by
  rw [← boundaryIntegral_eq_volumeDefect B Ω]
  exact W.boundaryIntegral_eq_winding_smul Ω

/--
The volume defect vanishes iff the winding vanishes.
-/
theorem volumeDefect_eq_zero_iff_winding_eq_zero
    (Ω : Region) :
    I.volumeIntegral Ω B.defectDensity = 0
      ↔ W.winding Ω = 0 := by
  rw [← boundaryIntegral_eq_volumeDefect B Ω]
  exact W.boundaryIntegral_eq_zero_iff

/--
The volume defect is nonzero iff the winding is nonzero.
-/
theorem volumeDefect_ne_zero_iff_winding_ne_zero
    (Ω : Region) :
    I.volumeIntegral Ω B.defectDensity ≠ 0
      ↔ W.winding Ω ≠ 0 := by
  rw [← boundaryIntegral_eq_volumeDefect B Ω]
  exact W.boundaryIntegral_ne_zero_iff

end ExactDefectStokesBridge

/-! ## 5. Constructing an index datum from finite kernel readout -/

/--
Build a topological index datum from a finite projected-kernel index.

The only required equality is the concrete readout identification:

`finite kernel index = residue winding`.

Once supplied, the index and spectral-flow fields are not independent.
-/
def topologicalIndexFromFiniteKernel
    {State Op Projection Mode Region Point Tangent Value : Type*}
    [Ring Op]
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (K : ConstructiveKasparovDatum State Op Projection Mode)
    (W : WindingNumberDatum I N ω)
    (regionOf : State → Region)
    (hindex_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x)) :
    TopologicalIndexDatum I N ω W State where
  regionOf := regionOf
  index := K.index
  spectralFlow := K.index
  index_eq_winding := hindex_winding
  index_eq_spectralFlow := by
    intro _x
    rfl

namespace ConstructiveKasparovDatum

variable
    {State Op Projection Mode Region Point Tangent Value : Type*}
    [Ring Op]
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}

variable (K : ConstructiveKasparovDatum State Op Projection Mode)

/--
Boundary residue equals the finite projected-kernel index times the phase
period.
-/
theorem boundaryIntegral_eq_finiteKernelIndex_period
    (regionOf : State → Region)
    (hindex_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x))
    (x : State) :
    I.boundaryIntegral (regionOf x) ω =
      (K.index x : ℝ) • N.phasePeriod := by
  calc
    I.boundaryIntegral (regionOf x) ω =
        (W.winding (regionOf x) : ℝ) • N.phasePeriod :=
      W.boundaryIntegral_eq_winding_smul (regionOf x)
    _ = (K.index x : ℝ) • N.phasePeriod := by
      rw [← hindex_winding x]

/--
Boundary residue is nonzero iff the finite projected-kernel index is nonzero.
-/
theorem boundaryIntegral_ne_zero_iff_finiteKernelIndex_ne_zero
    (regionOf : State → Region)
    (hindex_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x))
    (x : State) :
    I.boundaryIntegral (regionOf x) ω ≠ 0
      ↔ K.index x ≠ 0 := by
  constructor
  · intro hBoundary hIndex
    have hW :
        W.winding (regionOf x) = 0 := by
      rw [← hindex_winding x]
      exact hIndex
    exact hBoundary
      (W.boundaryIntegral_eq_zero_of_winding_zero hW)
  · intro hIndex hBoundary
    have hW :
        W.winding (regionOf x) = 0 :=
      W.winding_eq_zero_of_boundaryIntegral_eq_zero hBoundary
    exact hIndex
      (by
        rw [hindex_winding x]
        exact hW)

/--
Volume defect equals the finite projected-kernel index times the phase period.
-/
theorem volumeDefect_eq_finiteKernelIndex_period
    (B : ExactDefectStokesBridge I ω)
    (regionOf : State → Region)
    (hindex_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x))
    (x : State) :
    I.volumeIntegral (regionOf x) B.defectDensity =
      (K.index x : ℝ) • N.phasePeriod := by
  rw [← ExactDefectStokesBridge.boundaryIntegral_eq_volumeDefect B (regionOf x)]
  exact K.boundaryIntegral_eq_finiteKernelIndex_period
    regionOf hindex_winding x

/--
Volume defect is nonzero iff the finite projected-kernel index is nonzero.
-/
theorem volumeDefect_ne_zero_iff_finiteKernelIndex_ne_zero
    (B : ExactDefectStokesBridge I ω)
    (regionOf : State → Region)
    (hindex_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x))
    (x : State) :
    I.volumeIntegral (regionOf x) B.defectDensity ≠ 0
      ↔ K.index x ≠ 0 := by
  rw [← ExactDefectStokesBridge.boundaryIntegral_eq_volumeDefect B (regionOf x)]
  exact
    K.boundaryIntegral_ne_zero_iff_finiteKernelIndex_ne_zero
      regionOf hindex_winding x

end ConstructiveKasparovDatum

/-! ## 6. Constructive obstruction flow -/

/--
A flow whose conserved obstruction is the constructive finite Kasparov index.
-/
structure ConstructiveKasparovFlow
    {State Op Projection Mode : Type*}
    [Ring Op]
    (K : ConstructiveKasparovDatum State Op Projection Mode) where
  /-- Flat/trivial sector. -/
  Flat : Set State

  /-- Admissible flow. -/
  flow : ℝ → State → State

  /-- Flat states have zero constructive index. -/
  flat_index_zero :
    ∀ x : State,
      x ∈ Flat →
        K.index x = 0

  /-- The flow preserves the constructive index. -/
  flow_preserves_index :
    ∀ t x,
      K.index (flow t x) = K.index x

namespace ConstructiveKasparovFlow

variable {State Op Projection Mode : Type*}
variable [Ring Op]
variable {K : ConstructiveKasparovDatum State Op Projection Mode}

variable (F : ConstructiveKasparovFlow K)

/--
A state with nonzero constructive finite index cannot flow to the flat sector.
-/
theorem nonzero_index_cannot_flow_to_flat
    {x : State}
    (hx : K.index x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  intro hFlat
  have h0 :
      K.index (F.flow t x) = 0 :=
    F.flat_index_zero (F.flow t x) hFlat
  have hpres :
      K.index (F.flow t x) = K.index x :=
    F.flow_preserves_index t x
  rw [hpres] at h0
  exact hx h0

end ConstructiveKasparovFlow

/-! ## 7. Residue obstruction theorem -/

/--
Concrete readout identifying a state with a residue region.

This packages the one equality needed to connect the finite kernel index to
the residue winding.
-/
structure ConstructiveResidueReadout
    {State Op Projection Mode Region Point Tangent Value : Type*}
    [Ring Op]
    [AddCommGroup Value] [Module ℝ Value]
    (K : ConstructiveKasparovDatum State Op Projection Mode)
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (W : WindingNumberDatum I N ω) where
  /-- Region/contour associated to a state. -/
  regionOf : State → Region

  /-- The finite projected-kernel index equals the residue winding. -/
  index_eq_winding :
    ∀ x : State,
      K.index x = W.winding (regionOf x)

namespace ConstructiveResidueReadout

variable
    {State Op Projection Mode Region Point Tangent Value : Type*}
    [Ring Op]
    [AddCommGroup Value] [Module ℝ Value]
    {K : ConstructiveKasparovDatum State Op Projection Mode}
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}

variable (R : ConstructiveResidueReadout K I N ω W)

/--
Nonzero boundary residue obstructs relaxation into the flat sector.
-/
theorem nonzero_boundaryIntegral_cannot_flow_to_flat
    (F : ConstructiveKasparovFlow K)
    {x : State}
    (hx :
      I.boundaryIntegral (R.regionOf x) ω ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply F.nonzero_index_cannot_flow_to_flat
  intro hIndex
  have hW :
      W.winding (R.regionOf x) = 0 := by
    rw [← R.index_eq_winding x]
    exact hIndex
  exact hx
    (W.boundaryIntegral_eq_zero_of_winding_zero hW)

/--
Nonzero volume defect obstructs relaxation into the flat sector.
-/
theorem nonzero_volumeDefect_cannot_flow_to_flat
    (B : ExactDefectStokesBridge I ω)
    (F : ConstructiveKasparovFlow K)
    {x : State}
    (hx :
      I.volumeIntegral (R.regionOf x) B.defectDensity ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply R.nonzero_boundaryIntegral_cannot_flow_to_flat F
  intro hBoundary
  exact hx
    (by
      rw [← ExactDefectStokesBridge.boundaryIntegral_eq_volumeDefect B (R.regionOf x)]
      exact hBoundary)

/--
Nonzero finite projected-kernel index obstructs relaxation into the flat sector.
-/
theorem nonzero_constructive_index_cannot_flow_to_flat
    (F : ConstructiveKasparovFlow K)
    {x : State}
    (hx : K.index x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat :=
  F.nonzero_index_cannot_flow_to_flat hx t

end ConstructiveResidueReadout

end ConstructiveKasparov
