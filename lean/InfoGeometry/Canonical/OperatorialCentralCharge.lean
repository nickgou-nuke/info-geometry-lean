import InfoGeometry.KK.DiracFredholmIndex
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCentralCharge

Coordinate-free operatorial central-charge surface.

This file is intentionally noncommutative/operatorial:
- no frame sums,
- no scalar-coordinate contractions,
- no diagonal coordinate models.

The central charge is represented directly by the Fredholm/chiral analytical
index on the bounded real split-Krein Dirac module, with its existing
Bogoliubov transport invariance.
-/

namespace OperatorialCentralCharge

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Operatorial central charge: the Fredholm/chiral analytical index of the bounded
real split-Krein Dirac module.
-/
@[rep_depth krein]
noncomputable def operatorialCentralCharge
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : ℤ :=
  X.analyticalIndex hX

/--
Bogoliubov transport preserves the operatorial central charge.
-/
@[rep_depth transport]
theorem operatorialCentralCharge_eq_transport_slice
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
  simpa [operatorialCentralCharge] using
    quasilatticeAnalyticalIndex_eq_initial (E := E) V X hX hEven t

/--
Any two quasilattice transport slices carry the same operatorial central
charge.
-/
@[rep_depth transport]
theorem operatorialCentralCharge_transport_invariant
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
      =
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  simpa using quasilatticeAnalyticalIndex_eq (E := E) V X hX hEven s t

/--
Zero-value equivalence between a transported quasilattice slice and the
operatorial central charge.
-/
@[rep_depth transport]
theorem quasilatticeSlice_eq_zero_iff_operatorialCentralCharge_eq_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      = 0
      ↔
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX = 0 := by
  constructor
  · intro h
    calc
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX
        = quasilatticeAnalyticalIndex V X t
            (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
              symm
              exact operatorialCentralCharge_eq_transport_slice
                (A := A) (B := B) (E := E) V X hX hEven t
      _ = 0 := h
  · intro h
    calc
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        = operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
            exact operatorialCentralCharge_eq_transport_slice
              (A := A) (B := B) (E := E) V X hX hEven t
      _ = 0 := h

/--
Nonzero-value equivalence between a transported quasilattice slice and the
operatorial central charge.
-/
@[rep_depth transport]
theorem quasilatticeSlice_ne_zero_iff_operatorialCentralCharge_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0
      ↔
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
  exact not_congr
    (quasilatticeSlice_eq_zero_iff_operatorialCentralCharge_eq_zero
      (A := A) (B := B) (E := E) V X hX hEven t)

/--
If the operatorial central charge is nonzero, no transported quasilattice slice
can collapse to zero analytical index.
-/
@[rep_depth transport]
theorem quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0 := by
  exact
    (quasilatticeSlice_ne_zero_iff_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t).2 hCentral

/--
Nonvanishing at one transported quasilattice slice forces nonvanishing at every
other slice: the operatorial central-charge lane is transport-protected.
-/
@[rep_depth transport]
theorem quasilatticeSlice_ne_zero_transport_protected
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    {s t : ℝ}
    (hs :
      quasilatticeAnalyticalIndex V X s
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
        ≠ 0) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0 := by
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    exact
      (quasilatticeSlice_ne_zero_iff_operatorialCentralCharge_ne_zero
        (A := A) (B := B) (E := E) V X hX hEven s).1 hs
  exact quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
    (A := A) (B := B) (E := E) V X hX hEven hCentral t

end OperatorialCentralCharge
