/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Geometry.SpectralDivisors
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary
import InfoGeometry.Erlangen.SmoothCartanGeometry
import InfoGeometry.Canonical.ConnesNCGFormAlgebra
import InfoGeometry.KK.RealSplitKreinBoundedTransform
import InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms

/-!
# Constructive Kasparov Residue / Index Bridge & Gauge Fluctuation (`D_A`)

Constructive Kasparov residue/index bridge:

  projected finite kernel
    -> graded finite index
    -> algebraic defect P = 1 - F^2
    -> Stokes boundary = volume defect
    -> residue winding = index
    -> nonzero residue obstructs flow to Flat

Together with the R1/R2 cross-pillar gauge-fluctuation bridge (`F2.4` / `M3.5`)
connecting `MaurerCartanTower` (`thetaL`, `actionCurvature`), `SmoothCartanGeometry`
(`gl2R_maurerCartan_flat` vs `homothetyCartanGeometry κ`), `OneForms`, and
`D_A = D + A + J A J⁻¹` to `ConstructiveKasparovDatum.defect` (`1 - F^2`) and
`finiteDimPhase`.
-/

noncomputable section

namespace InfoGeometry.Geometry.ConstructiveKasparov

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
def ConstructiveResidueReadout
    {State Op Projection Mode Region Point Tangent Value : Type*}
    [Ring Op]
    [AddCommGroup Value] [Module ℝ Value]
    (K : ConstructiveKasparovDatum State Op Projection Mode)
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (W : WindingNumberDatum I N ω) :=
  {regionOf : State → Region //
    ∀ x : State,
      K.index x = W.winding (regionOf x)}

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

abbrev regionOf : State → Region := R.1

theorem index_eq_winding
    (x : State) :
    K.index x = W.winding (R.regionOf x) :=
  R.2 x

def mk
    (regionOf : State → Region)
    (index_eq_winding :
      ∀ x : State,
        K.index x = W.winding (regionOf x)) :
    ConstructiveResidueReadout K I N ω W :=
  ⟨regionOf, index_eq_winding⟩

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

/-! ## 8. Gauge Fluctuation `D_A`, Maurer–Cartan Tower, & `1 - F²` Defect Bridge (F2.4 / M3.5) -/

section GaugeFluctuationAndMaurerCartanBridge

open scoped Manifold
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.Erlangen.SmoothCartanGeometry
open InfoGeometry.Canonical.ConnesNCGFormAlgebra
open InfoGeometry.KK
open InfoGeometry.Krein

/-- Inner gauge fluctuation of a Dirac operator `D` by a Connes 1-form `A` with real
structure `J : Opˣ` (`D_A = D + A + J A J⁻¹`) over an arbitrary noncommutative `[Ring Op]`. -/
def fluctuatedDirac {Op : Type*} [Ring Op] (D : Op) (J : Opˣ) (A : Op) : Op :=
  D + A + (J : Op) * A * (↑J⁻¹ : Op)

/-- Signed KO-dimension variant `D_A(ε_D) = D + A + ε_D • (J A J⁻¹)` (`ε_D ∈ {1, -1}`). -/
def fluctuatedDiracSigned {Op : Type*} [Ring Op] (epsD : ℤ) (D : Op) (J : Opˣ) (A : Op) : Op :=
  D + A + epsD • ((J : Op) * A * (↑J⁻¹ : Op))

/-- Canonical alias `D_A` for the gauge-fluctuated Dirac operator `fluctuatedDirac`. -/
abbrev D_A {Op : Type*} [Ring Op] (D : Op) (J : Opˣ) (A : Op) : Op :=
  fluctuatedDirac D J A

/-- Pure-gauge Connes 1-form `A_u = u * [D, u⁻¹] = u * D * u⁻¹ - D` for `u : Opˣ`. -/
def pureGaugeOneForm {Op : Type*} [Ring Op] (D : Op) (u : Opˣ) : Op :=
  (u : Op) * ncDeriv D (↑u⁻¹ : Op)

theorem pureGaugeOneForm_eq_conj_sub {Op : Type*} [Ring Op] (D : Op) (u : Opˣ) :
    pureGaugeOneForm D u = (u : Op) * D * (↑u⁻¹ : Op) - D := by
  dsimp [pureGaugeOneForm, ncDeriv]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

/-- `pureGaugeOneForm D u` agrees with R1 `MaurerCartanTower.actionThetaL` (`u⁻¹`),
`-(actionThetaR u)`, and `connesUniversalOneFormMap D (leftDifferentialForm Op u u⁻¹)`. -/
theorem pureGaugeOneForm_eq_maurerCartan_and_universalOneForm
    {Op : Type*} [Ring Op] (D : Op) (u : Opˣ) :
    pureGaugeOneForm D u = actionThetaL (innerLieActionLane Op) u⁻¹ ![D] ∧
      pureGaugeOneForm D u = -(actionThetaR (innerLieActionLane Op) u ![D]) ∧
      pureGaugeOneForm D u =
        connesUniversalOneFormMap D (leftDifferentialForm Op (u : Op) (↑u⁻¹ : Op)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pureGaugeOneForm, actionThetaL_apply, ncDeriv_eq_innerLieActionLane]
  · change pureGaugeOneForm D u = -((innerLieActionLane Op).operatorAction D (u : Op) * (↑u⁻¹ : Op))
    rw [pureGaugeOneForm_eq_conj_sub, ← ncDeriv_eq_innerLieActionLane]
    dsimp [ncDeriv]
    rw [sub_mul]
    simp only [mul_assoc, Units.mul_inv, mul_one, neg_sub]
  · rw [connesUniversalOneFormMap_leftDifferentialForm]
    rfl

/-- Pure-gauge equivalence (`T2-F2.4-4`, `T4-07`): under `J * D * J⁻¹ = epsD • D` (`epsD = ±1`),
order-zero `Commute u (J u J⁻¹)`, and order-one `Commute u (ncDeriv D (J u⁻¹ J⁻¹))`,
`fluctuatedDiracSigned epsD D J (pureGaugeOneForm D u)` equals the unitary/invertible gauge
conjugate `(u * (J u J⁻¹)) * D * (u * (J u J⁻¹))⁻¹`. -/
theorem fluctuatedDiracSigned_pureGauge_eq_conj
    {Op : Type*} [Ring Op] (epsD : ℤ) (hepsD : epsD * epsD = 1)
    (D : Op) (J u : Opˣ)
    (hJD : (J : Op) * D * (↑J⁻¹ : Op) = epsD • D)
    (hOrderZero : Commute (u : Op) ((J : Op) * (u : Op) * (↑J⁻¹ : Op)))
    (hOrderOne : Commute (u : Op) (ncDeriv D ((J : Op) * (↑u⁻¹ : Op) * (↑J⁻¹ : Op)))) :
    let v : Opˣ := J * u * J⁻¹
    let U : Opˣ := u * v
    fluctuatedDiracSigned epsD D J (pureGaugeOneForm D u) = (U : Op) * D * (↑U⁻¹ : Op) := by
  intro v U
  have hv_val : (v : Op) = (J : Op) * (u : Op) * (↑J⁻¹ : Op) := by
    simp [v, Units.val_mul, mul_assoc]
  have hv_inv : (↑v⁻¹ : Op) = (J : Op) * (↑u⁻¹ : Op) * (↑J⁻¹ : Op) := by
    have hv' : v⁻¹ = J * u⁻¹ * J⁻¹ := by
      simp [v, _root_.mul_inv_rev, mul_assoc]
    rw [hv']
    simp [Units.val_mul, mul_assoc]
  have hJ_pure :
      epsD • ((J : Op) * pureGaugeOneForm D u * (↑J⁻¹ : Op)) =
        (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
    rw [pureGaugeOneForm_eq_conj_sub, mul_sub, sub_mul]
    have h1 : (J : Op) * ((u : Op) * D * (↑u⁻¹ : Op)) * (↑J⁻¹ : Op) =
        (v : Op) * ((J : Op) * D * (↑J⁻¹ : Op)) * (↑v⁻¹ : Op) := by
      rw [hv_val, hv_inv]
      simp only [mul_assoc]
      rw [← mul_assoc (↑J⁻¹ : Op) (J : Op) (D * _), Units.inv_mul, one_mul,
        ← mul_assoc (↑J⁻¹ : Op) (J : Op) ((↑u⁻¹ : Op) * _), Units.inv_mul, one_mul]
    rw [h1, hJD]
    have hsm :
        epsD • ((v : Op) * (epsD • D) * (↑v⁻¹ : Op) - epsD • D) =
          (epsD * epsD) • ((v : Op) * D * (↑v⁻¹ : Op) - D) := by
      simp only [smul_sub, mul_smul_comm, smul_mul_assoc, ← mul_smul]
    rw [hsm, hepsD, one_smul]
    dsimp [ncDeriv]
    rw [mul_sub, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have hu_comm_v : (u : Op) * ((v : Op) * ncDeriv D (↑v⁻¹ : Op)) * (↑u⁻¹ : Op) =
      (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
    have h0 : (u : Op) * (v : Op) = (v : Op) * (u : Op) := by
      rw [hv_val]; exact hOrderZero.eq
    have h1 : (u : Op) * ncDeriv D (↑v⁻¹ : Op) = ncDeriv D (↑v⁻¹ : Op) * (u : Op) := by
      rw [hv_inv]; exact hOrderOne.eq
    calc
      (u : Op) * ((v : Op) * ncDeriv D (↑v⁻¹ : Op)) * (↑u⁻¹ : Op)
          = ((u : Op) * (v : Op)) * ncDeriv D (↑v⁻¹ : Op) * (↑u⁻¹ : Op) := by
              simp only [mul_assoc]
      _ = (v : Op) * ((u : Op) * ncDeriv D (↑v⁻¹ : Op)) * (↑u⁻¹ : Op) := by
              rw [h0]; simp only [mul_assoc]
      _ = (v : Op) * (ncDeriv D (↑v⁻¹ : Op) * ((u : Op) * (↑u⁻¹ : Op))) := by
              rw [h1]; simp only [mul_assoc]
      _ = (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
              rw [Units.mul_inv, mul_one]
  have hU_conj : (U : Op) * D * (↑U⁻¹ : Op) =
      (u : Op) * D * (↑u⁻¹ : Op) + (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
    have hUval : (U : Op) = (u : Op) * (v : Op) := rfl
    have hUinv : (↑U⁻¹ : Op) = (↑v⁻¹ : Op) * (↑u⁻¹ : Op) := by
      simp [U, _root_.mul_inv_rev, Units.val_mul]
    rw [hUval, hUinv]
    have hstep : (v : Op) * D * (↑v⁻¹ : Op) = D + (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
      dsimp [ncDeriv]
      rw [mul_sub, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
      abel
    calc
      (u : Op) * (v : Op) * D * ((↑v⁻¹ : Op) * (↑u⁻¹ : Op))
          = (u : Op) * ((v : Op) * D * (↑v⁻¹ : Op)) * (↑u⁻¹ : Op) := by
              simp only [mul_assoc]
      _ = (u : Op) * (D + (v : Op) * ncDeriv D (↑v⁻¹ : Op)) * (↑u⁻¹ : Op) := by
              rw [hstep]
      _ = (u : Op) * D * (↑u⁻¹ : Op) +
            (u : Op) * ((v : Op) * ncDeriv D (↑v⁻¹ : Op)) * (↑u⁻¹ : Op) := by
              rw [mul_add, add_mul]
      _ = (u : Op) * D * (↑u⁻¹ : Op) + (v : Op) * ncDeriv D (↑v⁻¹ : Op) := by
              rw [hu_comm_v]
  dsimp [fluctuatedDiracSigned]
  rw [hJ_pure, hU_conj, pureGaugeOneForm_eq_conj_sub]
  abel

/-- Unitary/invertible gauge conjugation preserves the Kasparov defect `1 - F²` up to
conjugation (`defect(U F U⁻¹) = U (defect F) U⁻¹`), matching flat Maurer–Cartan
`actionThetaL_flat` and `gl2R_maurerCartan_flat` / `homothetyCartanGeometry_flat_of_zero`. -/
theorem constructiveKasparovDatum_defect_conjugate
    {State Op Projection Mode : Type*} [Ring Op]
    (K : ConstructiveKasparovDatum State Op Projection Mode)
    (U : State → Opˣ) :
    let K_conj : ConstructiveKasparovDatum State Op Projection Mode :=
      { K with F := fun x => (U x : Op) * K.F x * (↑(U x)⁻¹ : Op) }
    (∀ x : State, K_conj.defect x = (U x : Op) * K.defect x * (↑(U x)⁻¹ : Op)) ∧
      (∀ x : State, K.defect x = 0 → K_conj.defect x = 0) := by
  intro K_conj
  have hconj : ∀ x : State, K_conj.defect x = (U x : Op) * K.defect x * (↑(U x)⁻¹ : Op) := by
    intro x
    change 1 - ((U x : Op) * K.F x * (↑(U x)⁻¹ : Op)) * ((U x : Op) * K.F x * (↑(U x)⁻¹ : Op)) =
      (U x : Op) * (1 - K.F x * K.F x) * (↑(U x)⁻¹ : Op)
    calc
      1 - ((U x : Op) * K.F x * (↑(U x)⁻¹ : Op)) * ((U x : Op) * K.F x * (↑(U x)⁻¹ : Op))
          = (U x : Op) * (↑(U x)⁻¹ : Op) -
              (U x : Op) * (K.F x * (((↑(U x)⁻¹ : Op) * (U x : Op)) * K.F x)) *
                (↑(U x)⁻¹ : Op) := by
              rw [Units.mul_inv]
              simp only [mul_assoc]
      _ = (U x : Op) * (↑(U x)⁻¹ : Op) -
            (U x : Op) * (K.F x * K.F x) * (↑(U x)⁻¹ : Op) := by
              rw [Units.inv_mul, one_mul]
      _ = (U x : Op) * (1 - K.F x * K.F x) * (↑(U x)⁻¹ : Op) := by
              rw [mul_sub, sub_mul, mul_one]
  refine ⟨hconj, fun x hx => ?_⟩
  rw [hconj x, hx, mul_zero, zero_mul]

/-- Exact non-flat defect shift identity under a general bounded fluctuation `F_A := F + δF`:
`1 - (F + δF)² = (1 - F²) - (F * δF + δF * F + δF * δF)`, matching
`ConstructiveKasparovBoundary.involutiveKasparovDefect`. -/
theorem defect_add_fluctuation
    {State Op Projection Mode : Type*} [Ring Op]
    (K : ConstructiveKasparovDatum State Op Projection Mode)
    (δF : State → Op) (x : State) :
    let K_fluct : ConstructiveKasparovDatum State Op Projection Mode :=
      { K with F := fun s => K.F s + δF s }
    K_fluct.defect x =
        K.defect x - (K.F x * δF x + δF x * K.F x + δF x * δF x) ∧
      K_fluct.defect x = involutiveKasparovDefect (K.F x + δF x) := by
  refine ⟨?_, rfl⟩
  change 1 - (K.F x + δF x) * (K.F x + δF x) =
    (1 - K.F x * K.F x) - (K.F x * δF x + δF x * K.F x + δF x * δF x)
  noncomm_ring

/-- Unified R1/R2 flatness vs curvature witness (`T3-08`, `T2-F2.4-4`):
1. Pure-gauge R1 Maurer–Cartan (`actionThetaL_flat`) and flat Cartan geometry
   (`gl2R_maurerCartan_flat`, `homothetyCartanGeometry_flat_of_zero`) match `defect = 0`
   on `ConstructiveKasparovDatum` with noncommuting `M₂(ℝ)` flat phase `F = diag(1, -1)`;
2. Curved non-flat fluctuation `δF = !![0, 1; 0, 0]` (`F_A = F + δF` or off-diagonal shift
   `δF = !![0, 1; 1, 0]`) yields nonzero Kasparov defect `1 - F_A² ≠ 0`, parallel to
   `homothetyCartanGeometry_curved_of_ne_zero` (`κ ≠ 0`). -/
theorem maurerCartan_smoothCartan_vs_kasparov_defect_witness
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : InfoGeometry.Algebra.LieActionLane R A)
    (hK : IsLeibnizAction K) (g : Aˣ)
    (v w : _root_.GroupLieAlgebra
      𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
      InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R)
    (gGL : InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R)
    (p : (Fin 2 → ℝ) × ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) :
    let F₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let δF : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let KDatum : ConstructiveKasparovDatum Unit (Matrix (Fin 2) (Fin 2) ℝ)
        (Matrix (Fin 2) (Fin 2) ℝ) Empty :=
      { F := fun _ => F₀
        defectToKernelProjection := id
        kernelBasisOfProjection := fun _ => []
        grade := fun e => Empty.elim e }
    let KCurved : ConstructiveKasparovDatum Unit (Matrix (Fin 2) (Fin 2) ℝ)
        (Matrix (Fin 2) (Fin 2) ℝ) Empty :=
      { KDatum with F := fun _ => F₀ + δF }
    actionCurvature K (actionThetaL K g) = 0 ∧
      cartanCurvatureFormWith 𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
          (tangentSpaceCastModel 𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2)
            (1 : InfoGeometry.Erlangen.SmoothCartanGeometry.GL2R))
          (fun q => (leftMaurerCartanEquiv
            𝓘(ℝ, InfoGeometry.Erlangen.SmoothCartanGeometry.EndR2) q).toContinuousLinearMap)
          (mulInvariantVectorField v) (mulInvariantVectorField w) gGL = 0 ∧
      cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
          (fun q => ((homothetyCartanGeometry 0).omega q).toContinuousLinearMap)
          homothetyCoordX0 homothetyCoordX1 p = 0 ∧
      cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
          (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
          homothetyCoordX0 homothetyCoordX1 p ≠ 0 ∧
      KDatum.defect () = 0 ∧
      KCurved.defect () ≠ 0 := by
  refine ⟨actionThetaL_flat K hK g, gl2R_maurerCartan_flat v w gGL,
    homothetyCartanGeometry_flat_of_zero p, homothetyCartanGeometry_curved_of_ne_zero hκ p, ?_, ?_⟩
  · change (1 : Matrix (Fin 2) (Fin 2) ℝ) -
        !![1, 0; 0, -1] * !![1, 0; 0, -1] = 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h0
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h0
    change ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
        ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) +
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) *
        ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) +
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))) 0 0 = 0 at h00
    simp at h00

/-- `BUCKET 2` finite-dimensional realization of `ConstructiveKasparovDatum.defect` on
`D_A = fluctuatedDirac D J A` via `RealSplitKreinBoundedTransform.finiteDimPhase`:
`(1 + D_A²) * (1 - finiteDimPhase D_A * finiteDimPhase D_A) = 1`. -/
theorem fluctuatedDirac_finiteDimPhase_defect_inv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]
    (D : EndH H) (J : (EndH H)ˣ) (A : EndH H)
    (hDA_self : IsSelfAdjoint (D_A D J A)) :
    let KDatum : ConstructiveKasparovDatum Unit (EndH H) (EndH H) Empty :=
      { F := fun _ => finiteDimPhase (D_A D J A)
        defectToKernelProjection := id
        kernelBasisOfProjection := fun _ => []
        grade := fun e => Empty.elim e }
    (1 + D_A D J A * D_A D J A) * KDatum.defect () = 1 ∧
      KDatum.defect () * (1 + D_A D J A * D_A D J A) = 1 :=
  finiteDimPhase_sq_add_inv_one_add_sq hDA_self

/-- Exact involutive defect shift for a bounded fluctuation `F + δF` (`T2-F2.4-4`):
`involutiveKasparovDefect F = 1 - F * F` and
`involutiveKasparovDefect (F + δF) = (1 - F * F) - (F * δF + δF * F + δF * δF)`. -/
theorem fluctuated_involutiveKasparovDefect_shift
    {Op : Type*} [Ring Op] (F δF : Op) :
    involutiveKasparovDefect F = 1 - F * F ∧
      involutiveKasparovDefect (F + δF) =
        (1 - F * F) - (F * δF + δF * F + δF * δF) := by
  refine ⟨rfl, ?_⟩
  dsimp [involutiveKasparovDefect]
  noncomm_ring

end GaugeFluctuationAndMaurerCartanBridge

end InfoGeometry.Geometry.ConstructiveKasparov
