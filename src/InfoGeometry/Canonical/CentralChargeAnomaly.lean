import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TopologicalResidue
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CentralChargeAnomaly

Operatorial anomaly surface for the canonical doubled-carrier lane.

This file is transport/operatorial by construction:
- the central charge is the KK/Fredholm owner (`operatorialCentralCharge`);
- anomaly-freeness compares that operatorial central charge with the
  topological residue (`wittenIndexResidue`);
- transport slices are related to anomaly-freeness through the existing
  quasilattice index-invariance lane.
-/

namespace InfoGeometry.Canonical.CentralChargeAnomaly

open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.TopologicalResidue
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Quantum
open InfoGeometry.Krein

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Operatorial central charge on the real split-Krein Fredholm owner.
-/
@[rep_depth krein]
noncomputable def centralCharge
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : ℤ :=
  operatorialCentralCharge (A := A) (B := B) (E := E) X hX

/--
Transport slice readout equals the operatorial central charge.
-/
@[rep_depth transport]
theorem centralCharge_eq_transport_slice
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    centralCharge (A := A) (B := B) (E := E) X hX := by
  simpa [centralCharge] using
    operatorialCentralCharge_eq_transport_slice
      (A := A) (B := B) (E := E) V X hX hEven t

/--
Anomaly-freeness on the canonical lane: operatorial central charge matches the
topological residue readout.
-/
@[rep_depth transport]
def IsAnomalyFree
    [FiniteDimensional ℝ E]
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (M : SuperchargeMultiplet (E := E)) : Prop :=
  centralCharge (A := A) (B := B) (E := E) X hX =
    wittenIndexResidue (E := E) M

/--
Transport slice form of anomaly-freeness.
-/
@[rep_depth transport]
theorem isAnomalyFree_iff_transportSlice_eq_wittenIndexResidue
    [FiniteDimensional ℝ E]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : SuperchargeMultiplet (E := E)) :
    IsAnomalyFree (A := A) (B := B) (E := E) X hX M
      ↔
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    wittenIndexResidue (E := E) M := by
  constructor
  · intro h
    calc
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        = centralCharge (A := A) (B := B) (E := E) X hX :=
            centralCharge_eq_transport_slice (A := A) (B := B) (E := E) V X hX hEven t
      _ = wittenIndexResidue (E := E) M := h
  · intro h
    calc
      centralCharge (A := A) (B := B) (E := E) X hX
        =
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
            symm
            exact centralCharge_eq_transport_slice (A := A) (B := B) (E := E) V X hX hEven t
      _ = wittenIndexResidue (E := E) M := h

/--
Canonical doubled-carrier specialization:
anomaly-freeness is equivalent to vanishing transported quasilattice slice.
-/
@[rep_depth transport]
theorem isAnomalyFree_iff_transportSlice_eq_zero_of_canonicalMultiplet
    [FiniteDimensional ℝ E]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    IsAnomalyFree (A := A) (B := B) (E := E) X hX
        (canonicalSuperchargeMultiplet.inst (E := E))
      ↔
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      = 0 := by
  rw [isAnomalyFree_iff_transportSlice_eq_wittenIndexResidue
        (A := A) (B := B) (E := E) V X hX hEven t
        (canonicalSuperchargeMultiplet.inst (E := E))]
  have hResidue :
      wittenIndexResidue (E := E) (canonicalSuperchargeMultiplet.inst (E := E)) = 0 := by
    simpa using canonicalSuperchargeMultiplet_wittenIndexResidue_eq_zero (E := E)
  constructor
  · intro h
    simpa [hResidue] using h
  · intro h
    simpa [hResidue] using h

/--
Canonical doubled-carrier specialization:
anomaly-freeness is equivalent to vanishing operatorial central charge.
-/
@[rep_depth transport]
theorem isAnomalyFree_iff_centralCharge_eq_zero_of_canonicalMultiplet
    [FiniteDimensional ℝ E]
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    IsAnomalyFree (A := A) (B := B) (E := E) X hX
        (canonicalSuperchargeMultiplet.inst (E := E))
      ↔
    centralCharge (A := A) (B := B) (E := E) X hX = 0 := by
  unfold IsAnomalyFree
  have hResidue :
      wittenIndexResidue (E := E) (canonicalSuperchargeMultiplet.inst (E := E)) = 0 := by
    simpa using canonicalSuperchargeMultiplet_wittenIndexResidue_eq_zero (E := E)
  constructor
  · intro h
    simpa [hResidue] using h
  · intro h
    simpa [hResidue] using h

/--
Nonzero operatorial central charge forces nonzero transported index on every
quasilattice slice.
-/
@[rep_depth transport]
theorem transportSlice_ne_zero_of_centralCharge_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (hCentral : centralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0 := by
  simpa [centralCharge] using
    quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven hCentral t

end InfoGeometry.Canonical.CentralChargeAnomaly
