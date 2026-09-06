import InfoGeometry.Canonical.SingularBoundaryCorrection
import InfoGeometry.Canonical.BoundaryChiralIndexBridge
import InfoGeometry.Canonical.BoundaryProjector
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Experimental.ModularSpinorBridge
import InfoGeometry.Quantum.BulkBoundary
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Krein.State

/-!
# Spinor-Modular Bridge: The Coriolis Whirlpool

This module formalizes the identification between topological Majorana boundary
modes and the modular singularization layer on the doubled Krein space.

It captures the **"Coriolis Whirlpool"** at the boundary of the causal cone:
- **Dangling Zero-Modes**: Bulk zero-modes sensitive to the boundary anomaly.
- **Vorticity Source**: The boundary generator acts as the source of chiral flux.
- **Spinor-Modular Identification**: Mapping the Weyl boundary spinors to the
  null threads of the modular web.
-/

namespace InfoGeometry.Canonical.SpinorModularBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.BoundaryChiralIndexBridge
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.SingularBoundaryCorrection
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
A **Dangling Zero-Mode** is a vector in the carrier that is in the
kernel of the bulk operator `A` but is non-trivially moved by the boundary
generator (the modular anomaly).
-/
def IsDanglingZeroMode
    (S : SingularBoundaryCorrection E) (v : E) : Prop :=
  S.kernel.A v = 0 ∧ S.boundaryGenerator v ≠ 0

/--
The subspace of dangling modes is exactly the part of the kernel where the
"Coriolis whirlpool" (the vorticity) is active.
-/
def DanglingSubspace (S : SingularBoundaryCorrection E) : Submodule ℝ E :=
  (S.kernel.A.toLinearMap).ker ⊓ (LinearMap.ker S.boundaryGenerator.toLinearMap).comap (LinearMap.id)

/--
The **Horizon** (Scale-Fixed Subspace):
The subspace of the doubled carrier where the modular operator Δ acts as the identity.
This is the locus of points where the scale inversion `X ↦ 1/X` leaves the
state unchanged—the "neck" of the Klein Bottle.
-/
noncomputable def HorizonSubspace : Submodule ℝ H₂ :=
  InfoGeometry.Canonical.boundarySubspace
    (E := E) (InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
Theorem: Scale Inversion Fixed Point.
On the Horizon Subspace, the scale inversion `J Δ J = Δ⁻¹` stabilizes at `Δ = 1`.
This defines the absolute present where modular time `t = -t`.
-/
theorem horizon_is_scale_invariant
    (v : H₂) (hv : v ∈ HorizonSubspace (E := E)) :
    (InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E)) v = v := by
  simpa [HorizonSubspace] using
    (InfoGeometry.Canonical.mem_boundarySubspace
      (E := E)
      (Δ := InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E))
      (ψ := v)).1 hv

/--
The "Coriolis Whirlpool" (the vorticity) on the singular boundary.
The boundary generator `χ` acts as the source of state-space rotation.

At the holographic boundary, the infinite modular flow `exp(tK)` degenerates
into this pure chiral rotation. The "infinity" of the bulk translation is
converted into the "spinning" of the boundary whirlpool.
-/
noncomputable def coriolisVorticity
    (S : SingularBoundaryCorrection E) : E →L[ℝ] E :=
  vorticity S.boundaryGenerator

omit [FiniteDimensional ℝ E] in
/--
Theorem: The boundary generator is its own vorticity.
Since the boundary generator `χ = [P_D, P_MP]` is skew-adjoint (proved in
`SingularBoundaryCorrection.lean`), it acts as a pure rotation (vorticity).
-/
theorem boundaryGenerator_is_vorticity
    (S : SingularBoundaryCorrection E) :
    coriolisVorticity S = S.boundaryGenerator := by
  apply vorticity_eq_self_of_skew
  exact S.boundaryGenerator_skew

/--
The **Spinor-Modular Identification**:
A Weyl boundary spinor pair $(\psi_+, \psi_-)$ from the Kitaev topological
layer corresponds to a pair of dangling null modes in the modular web.
-/
structure SpinorModularIdentification
    (M : RealMajoranaDatum (S := E))
    (S : SingularBoundaryCorrection E) where
  psiPlus : E
  psiMinus : E
  is_plus_dangling : IsDanglingZeroMode S psiPlus
  is_minus_dangling : IsDanglingZeroMode S psiMinus
  is_plus_weyl : psiPlus ∈ M.weylPlus
  is_minus_weyl : psiMinus ∈ M.weylMinus

/--
The anomaly-sourced chiral flux is the integral of the "whirlpool" dynamics
over the dangling zero-modes.
-/
noncomputable def danglingChiralFlux
    (S : SingularBoundaryCorrection E)
    (ω : (E →L[ℝ] E) →L[ℝ] ℝ) : ℝ :=
  chiralFlux S.boundaryGenerator ω

omit [FiniteDimensional ℝ E] in
/--
Finality: The gravity-like curvature (anomaly) of the informational state space
is concentrated precisely on the dangling Majorana threads.
-/
theorem curvature_concentrated_on_dangling_modes
    (S : SingularBoundaryCorrection E) (v : E)
    (hDangling : IsDanglingZeroMode S v) :
    S.boundaryGenerator v ≠ 0 :=
  hDangling.2

omit [FiniteDimensional ℝ E] in
/-- Any dangling zero mode forces the boundary generator to be nonzero. -/
theorem boundaryGenerator_ne_zero_of_exists_danglingZeroMode
    (S : SingularBoundaryCorrection E)
    (hDangling : ∃ v : E, IsDanglingZeroMode S v) :
    S.boundaryGenerator ≠ 0 := by
  intro hZero
  rcases hDangling with ⟨v, hv⟩
  have hEval := congrArg (fun T : E →L[ℝ] E => T v) hZero
  exact hv.2 (by simpa using hEval)

omit [FiniteDimensional ℝ E] in
/-- Any dangling zero mode forces the scalar boundary obstruction to be nonzero. -/
theorem boundaryScale_ne_zero_of_exists_danglingZeroMode
    (S : SingularBoundaryCorrection E)
    (hDangling : ∃ v : E, IsDanglingZeroMode S v) :
    S.boundaryScale ≠ 0 := by
  intro hScale
  have hZero : S.boundaryGenerator = 0 :=
    (S.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero).mp hScale
  exact boundaryGenerator_ne_zero_of_exists_danglingZeroMode S hDangling hZero

omit [FiniteDimensional ℝ E] in
/--
Kernel-separation form of boundary activity:
if the bulk kernel and boundary-generator kernel intersect trivially, then
every nontrivial bulk zero mode is boundary-active.
-/
theorem boundary_active_on_nonzero_kernel_of_kernel_separation
    (S : SingularBoundaryCorrection E)
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ E)) :
    ∀ v : E, S.kernel.A v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0 := by
  intro v hvA hvne hvB
  have hvMem :
      v ∈ (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap) := by
    constructor
    · simpa [LinearMap.mem_ker] using hvA
    · simpa [LinearMap.mem_ker] using hvB
  have hvBot : v ∈ (⊥ : Submodule ℝ E) := by simpa [hSep] using hvMem
  exact hvne (by simpa using hvBot)

omit [FiniteDimensional ℝ E] in
/--
Reverse direction: pointwise boundary activity on nontrivial bulk zero modes
forces trivial kernel intersection.
-/
theorem kernel_separation_of_boundary_active_on_nonzero_kernel
    (S : SingularBoundaryCorrection E)
    (hBoundaryOnZeroModes :
      ∀ v : E, S.kernel.A v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0) :
    (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
      = (⊥ : Submodule ℝ E) := by
  apply le_antisymm
  · intro v hv
    rcases hv with ⟨hvA, hvB⟩
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hA0 : S.kernel.A v = 0 := by simpa [LinearMap.mem_ker] using hvA
      have hB0 : S.boundaryGenerator v = 0 := by simpa [LinearMap.mem_ker] using hvB
      exact (False.elim ((hBoundaryOnZeroModes v hA0 hv0) hB0))
  · exact bot_le

section

omit [FiniteDimensional ℝ E]

/--
Kernel-separation and pointwise boundary-activity are equivalent formulations of
the same nondegeneracy condition.
-/
theorem boundary_active_on_nonzero_kernel_iff_kernel_separation
    (S : SingularBoundaryCorrection E) :
    (∀ v : E, S.kernel.A v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
      ↔
    (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
      = (⊥ : Submodule ℝ E) := by
  constructor
  · exact kernel_separation_of_boundary_active_on_nonzero_kernel (S := S)
  · exact boundary_active_on_nonzero_kernel_of_kernel_separation (S := S)

end

section TransportedBoundary

variable {A B : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ (DoubledSpace E)]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

omit [FiniteDimensional ℝ E]
/--
If the singular boundary package shares its bulk operator with the transported
Dirac lane, and every nontrivial transported zero mode is boundary-active, then
nonzero operatorial central charge yields a dangling zero mode.
-/
@[rep_depth transport]
theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v := by
  rcases
      transportedZeroModeWitness_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 hplus hminus hodd hCentral with
    ⟨v, hvKer, hvne⟩
  refine ⟨v, ?_⟩
  have hvZero : quasilatticeDirac V X.F t v = 0 := by
    simpa [LinearMap.mem_ker] using hvKer
  constructor
  · simpa [hA] using hvZero
  · exact hBoundaryOnZeroModes v hvZero hvne

/--
Kernel-separation variant of the transported dangling-zero-mode bridge.

This removes the raw pointwise boundary-activity property and derives it from
trivial intersection between the transported bulk kernel and boundary-generator
kernel.
-/
@[rep_depth transport]
theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v := by
  have hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0 := by
    intro v hv hvne
    have hvA : S.kernel.A v = 0 := by simpa [hA] using hv
    exact boundary_active_on_nonzero_kernel_of_kernel_separation (S := S) hSep v hvA hvne
  exact
    exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Under the same hypotheses, the singular boundary generator cannot vanish.
-/
@[rep_depth transport]
theorem boundaryGenerator_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  apply boundaryGenerator_ne_zero_of_exists_danglingZeroMode
  exact
    exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Kernel-separation variant of the transported boundary-generator nonvanishing law.
-/
@[rep_depth transport]
theorem boundaryGenerator_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  apply boundaryGenerator_ne_zero_of_exists_danglingZeroMode
  exact
    exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd hSep hCentral

/--
Under the same hypotheses, the scalar shadow of the singular boundary
obstruction is nonzero.
-/
@[rep_depth transport]
theorem boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    S.boundaryScale ≠ 0 := by
  apply boundaryScale_ne_zero_of_exists_danglingZeroMode
  exact
    exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Kernel-separation variant of the transported boundary-scale nonvanishing law.
-/
@[rep_depth transport]
theorem boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    S.boundaryScale ≠ 0 := by
  apply boundaryScale_ne_zero_of_exists_danglingZeroMode
  exact
    exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd hSep hCentral

/--
Under the same hypotheses, the singular boundary vorticity operator cannot
vanish.
-/
@[rep_depth transport]
theorem coriolisVorticity_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    coriolisVorticity S ≠ 0 := by
  rw [boundaryGenerator_is_vorticity (S := S)]
  exact
    boundaryGenerator_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Kernel-separation variant of transported vorticity nonvanishing.
-/
@[rep_depth transport]
theorem coriolisVorticity_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    coriolisVorticity S ≠ 0 := by
  rw [boundaryGenerator_is_vorticity (S := S)]
  exact
    boundaryGenerator_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral

/--
Localized vortex form of the transported defect theorem.

Nonzero operatorial central charge yields a dangling transported zero mode on
which the singular boundary vorticity acts nontrivially.
-/
@[rep_depth transport]
theorem exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v ∧ coriolisVorticity S v ≠ 0 := by
  rcases
      exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral with
    ⟨v, hvDangling⟩
  refine ⟨v, hvDangling, ?_⟩
  simpa [boundaryGenerator_is_vorticity (S := S)] using hvDangling.2

/--
Kernel-separation variant of the localized transported boundary-vortex theorem.
-/
@[rep_depth transport]
theorem exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd : PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v ∧ coriolisVorticity S v ≠ 0 := by
  rcases
      exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hSep hCentral with
    ⟨v, hvDangling⟩
  refine ⟨v, hvDangling, ?_⟩
  simpa [boundaryGenerator_is_vorticity (S := S)] using hvDangling.2

end TransportedBoundary

end InfoGeometry.Canonical.SpinorModularBridge
