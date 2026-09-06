import InfoGeometry.Canonical.ChiralDefectIndexBridge
import InfoGeometry.KK.RealSplitKKTBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Data.ZMod.Basic

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CentralChargeKKTParityBridge

Bridge layer from the transported operatorial central-charge lane to:

- a `ZMod 2` parity readout of that central charge,
- transported chiral-kernel mismatch consequences,
- and the already-owned KKT odd/even closure on the same Dirac carrier.

This file is intentionally compositional. It does not introduce a new central
charge owner, a new KKT ontology, or a new Dirac presentation.
-/

namespace InfoGeometry.Canonical.CentralChargeKKTParityBridge

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.KK.RealSplitKKTBridge
open InfoGeometry.Krein

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/-- `Z₂` parity shadow of the operatorial central charge. -/
@[rep_depth transport]
noncomputable def operatorialCentralChargeParity
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : ZMod 2 :=
  (operatorialCentralCharge (A := A) (B := B) (E := E) X hX : ZMod 2)

/--
Transported parity readout:
the `Z₂` shadow of the central charge equals the `Z₂` shadow of any transported
quasilattice analytical-index slice.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_eq_transport_slice
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    operatorialCentralChargeParity (A := A) (B := B) X hX
      =
    (quasilatticeAnalyticalIndex V X t
      (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) : ZMod 2) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  unfold operatorialCentralChargeParity
  have hSlice :
      quasilatticeAnalyticalIndex V X t
          hVX
        =
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX :=
    operatorialCentralCharge_eq_transport_slice (A := A) (B := B) (E := E) V X hX hEven t
  -- Align the transported-slice property with the theorem statement property.
  change
      (operatorialCentralCharge (A := A) (B := B) (E := E) X hX : ZMod 2)
        =
      (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) : ZMod 2)
  exact congrArg (fun z : ℤ => (z : ZMod 2)) hSlice |>.symm

/--
Transport invariance of the `Z₂` analytical-index shadow along quasilattice
slices.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndexParity_transport_invariant
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    (quasilatticeAnalyticalIndex V X s
      (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s) : ZMod 2)
      =
    (quasilatticeAnalyticalIndex V X t
      (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) : ZMod 2) := by
  let hVs := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s
  let hVt := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  exact congrArg (fun z : ℤ => (z : ZMod 2))
    (by
      change quasilatticeAnalyticalIndex V X s hVs = quasilatticeAnalyticalIndex V X t hVt
      exact quasilatticeAnalyticalIndex_eq (E := E) V X hX hEven s t)

/--
If the `Z₂` shadow is nonzero, the full operatorial central charge is nonzero.
-/
@[rep_depth transport]
theorem operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
  intro hZero
  apply hParity
  unfold operatorialCentralChargeParity
  simp [hZero]

/--
Parity-lifted mismatch law:
nonzero central-charge parity forces transported plus/minus chiral-kernel
dimension mismatch.
-/
@[rep_depth transport]
theorem transportedChiralKernelDimMismatch_of_operatorialCentralChargeParity_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  change TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX
  exact
    transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hCentral

/--
KKT closure on the bounded Dirac carrier:
if the ambient grading agrees with the split-`Cl(1,1)` pseudoscalar, then the
Dirac phase is exactly odd (`g₁ ⊕ g₋₁`) and its odd-odd commutator is grade
zero.
-/
@[rep_depth transport]
theorem dirac_kkt_odd_split_and_commutator_isGZero_of_gradeCLM_eq_eps
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧ IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  refine ⟨?_, ?_⟩
  · exact F_eq_gOnePart_add_gNegOnePart_of_gradeCLM_eq_eps (X := X) hGrade
  · exact commutator_gOne_gNegOne_isGZero (X := X.cl11) X.F X.F

/--
Combined closure packet:
nonzero operatorial central charge forces transported chiral mismatch, and the
same Dirac carrier admits the KKT odd split with grade-zero odd-odd commutator
whenever the grading/pseudoscalar identification is fixed.
-/
@[rep_depth transport]
theorem centralCharge_nonzero_forces_dimMismatch_and_kkt_odd_split
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
      X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
      IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  refine ⟨?_, ?_⟩
  · exact
      transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
        (A := A) (B := B) (E := E) V X hX hEven t hCentral
  · exact dirac_kkt_odd_split_and_commutator_isGZero_of_gradeCLM_eq_eps
      (A := A) (B := B) (E := E) X hGrade

end Core

end InfoGeometry.Canonical.CentralChargeKKTParityBridge
