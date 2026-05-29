import InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
import InfoGeometry.Canonical.ChiralDefectIndexBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BoundaryChiralIndexBridge

Thin boundary-facing bridge from the transported chiral defect lane to the
existing bulk-boundary regularization package.

This file does not assert that the canonical vortex package is already the
transported KK defect polarization. Instead it proves the honest conditional
statement needed for the next boundary step:

- if a boundary polarization is explicitly identified with the transported
  plus/minus chiral defect slices,
- and the transported operator remains odd for that polarization,
- then nonzero operatorial central charge upgrades to the existing zero-mode
  plus nontrivial regularization package.
-/

namespace InfoGeometry.Canonical.BoundaryChiralIndexBridge

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ (DoubledSpace E)]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

omit [FiniteDimensional ℝ H₂] in
/--
If a boundary polarization is explicitly identified with the transported
plus/minus defect slices, then nonzero operatorial central charge forces a
plus/minus boundary-dimension mismatch.
-/
@[rep_depth transport]
theorem dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus := by
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) :=
    transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hCentral
  intro hEq
  rw [hplus, hminus] at hEq
  exact hMismatch hEq

/--
Boundary upgrade of the transported defect lane.

Once a boundary polarization is explicitly identified with the transported
plus/minus defect slices, nonzero operatorial central charge yields a genuine
zero mode together with a nontrivial Moore-Penrose/Drazin regularization
package for the transported Dirac operator.
-/
noncomputable def zeroModeRegularizationPackage_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (v : H₂)
    (hv : InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0)
    (hvne : v ≠ 0)
    (Q_MP Q_D : H₂ →L[ℝ] H₂)
    (k : ℕ)
    (hMP :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) Q_MP)
    (hD :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) Q_D k) :
    ZeroModeRegularizationPackage (S := H₂)
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) := by
  have hdim :
      Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus :=
    dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 hplus hminus hCentral
  have _hZeroFromIndex :
      HasZeroMode (S := H₂)
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) :=
    hasZeroMode_of_dim_mismatch (M := M) P0
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) hodd hdim
  exact
    zeroModeRegularizationPackage_of_explicit
      (S := H₂)
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
      v hv hvne Q_MP Q_D k hMP hD

/--
Under the same identification and oddness hypotheses, nonzero operatorial
central charge forces a genuine zero mode of the transported Dirac operator.
-/
@[rep_depth transport, capstone]
theorem transportedHasZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    HasZeroMode (S := H₂)
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) := by
  unfold HasZeroMode
  have hdim :
      Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus :=
    dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 hplus hminus hCentral
  have hZero :
      HasZeroMode (S := H₂)
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) :=
    hasZeroMode_of_dim_mismatch (M := M) P0
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) hodd hdim
  unfold HasZeroMode at hZero
  exact hZero

/--
Witness form of the transported zero-mode consequence.
-/
@[rep_depth transport, capstone]
theorem transportedZeroModeWitness_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    ∃ v : H₂,
      v ∈ (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t).toLinearMap.ker
        ∧ v ≠ 0 := by
  have hZero :
      HasZeroMode (S := H₂)
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t) :=
    transportedHasZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 hplus hminus hodd hCentral
  exact (InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode
    (S := H₂)
    (H := InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    hZero)

end Core

end InfoGeometry.Canonical.BoundaryChiralIndexBridge
