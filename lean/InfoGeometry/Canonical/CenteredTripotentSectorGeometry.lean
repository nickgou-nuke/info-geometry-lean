import Mathlib.Tactic
import InfoGeometry.Canonical.ZetaStandardRealizations
import InfoGeometry.Canonical.TomitaTakesakiTrifactor
import InfoGeometry.Canonical.TwoSheetedComplexPolarization

/-!
# InfoGeometry.Canonical.CenteredTripotentSectorGeometry

Bridge file combining three already-formalized surfaces:

- centered zeta coordinate `s = 1/2 + z`,
- doubled real polarization axis `K = J ε` with `K^2 = -1`,
- tripotent/trifactor sector decomposition `T^3 = T`.

The point is not to replace one symmetry by another, but to formalize the
statement that the centered coordinate threads through the tripotent sectors,
while the imaginary axis is read back operatorially on the doubled carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.CenteredTripotentSectorGeometry

open InfoGeometry.Canonical.ZetaStandardRealizations
open InfoGeometry.Canonical.TrifactorDecomposition
open InfoGeometry.Canonical.TwoSheetedComplexPolarization
open InfoGeometry.Krein

/-- Boundary / flow / mirror sector triple. -/
structure SectorTriple (R : Type*) where
  boundary : R
  flow : R
  mirror : R

namespace SectorTriple

variable {R : Type*} [Add R]

/-- Recombine the three sector components. -/
def total (S : SectorTriple R) : R :=
  S.boundary + S.flow + S.mirror

end SectorTriple

section ComplexTripotent

/-- Tripotent sector readout of a complex quantity. -/
def sectorReadout (T w : ℂ) : SectorTriple ℂ where
  boundary := P_zero T * w
  flow := P_plus T * w
  mirror := P_minus T * w

/-- The three sector components recombine to the original quantity. -/
theorem sectorReadout_total (T w : ℂ) :
    (sectorReadout T w).total = w := by
  unfold SectorTriple.total sectorReadout
  calc
    P_zero T * w + P_plus T * w + P_minus T * w = (P_zero T + P_plus T + P_minus T) * w := by ring
    _ = 1 * w := by rw [partition_of_unity]
    _ = w := by ring

/-- Sector readout of the symmetry-adapted centered coordinate `1/2 + z`. -/
def centeredSectorReadout (T z : ℂ) : SectorTriple ℂ :=
  sectorReadout T (criticalCentered z)

/-- The centered-coordinate sector readout recombines to `1/2 + z`. -/
theorem centeredSectorReadout_total (T z : ℂ) :
    (centeredSectorReadout T z).total = criticalCentered z :=
  sectorReadout_total T (criticalCentered z)

/-- Reflecting `z` to `-z` is exactly the centered functional-equation involution. -/
theorem centeredSectorReadout_total_reflected (T z : ℂ) :
    (centeredSectorReadout T (-z)).total = 1 - criticalCentered z := by
  rw [centeredSectorReadout_total, criticalCentered_neg]

/-- Tripotent action on the three sectors is `0`, `+1`, and `-1`. -/
theorem tripotentActsOn_sectorReadout
    (T w : ℂ) (hT : T ^ 3 = T) :
    T * (sectorReadout T w).boundary = 0 ∧
      T * (sectorReadout T w).flow = (sectorReadout T w).flow ∧
      T * (sectorReadout T w).mirror = -(sectorReadout T w).mirror := by
  constructor
  · unfold sectorReadout
    calc
      T * (P_zero T * w) = (T * P_zero T) * w := by ring
      _ = 0 * w := by rw [T_on_P_zero T hT]
      _ = 0 := by ring
  · constructor
    · unfold sectorReadout
      calc
        T * (P_plus T * w) = (T * P_plus T) * w := by ring
        _ = P_plus T * w := by rw [T_on_P_plus T hT]
    · unfold sectorReadout
      calc
        T * (P_minus T * w) = (T * P_minus T) * w := by ring
        _ = (-P_minus T) * w := by rw [T_on_P_minus T hT]
        _ = -(P_minus T * w) := by ring

/--
If `Ξ(z) = ξ(1/2 + z)` is the centered completed-zeta realization, then the
three-sector readout still recombines to the same even centered function.
-/
theorem centeredXi_on_sector_total
    (X : CompletedXiRealization) (T z : ℂ) :
    X.xi ((centeredSectorReadout T z).total) = X.centeredXi z := by
  rw [centeredSectorReadout_total, CompletedXiRealization.centeredXi_apply]

/-- Sectorwise recombination is compatible with `Ξ(z) = Ξ(-z)`. -/
theorem centeredXi_on_sector_total_even
    (X : CompletedXiRealization) (T z : ℂ) :
    X.xi ((centeredSectorReadout T z).total) = X.xi ((centeredSectorReadout T (-z)).total) := by
  rw [centeredXi_on_sector_total, centeredXi_on_sector_total]
  exact X.centeredXi_even z

end ComplexTripotent

section DoubledReadback

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Centered complex coordinate read back on the doubled real carrier. -/
def centeredHestenesCoordinate (z : ℂ) : EndH :=
  InfoGeometry.Canonical.HestenesComplexTranslation.hestenesScalar (E := E) (criticalCentered z)

/--
The centered coordinate `1/2 + z` reads back as a real shift plus imaginary
polarization-axis component on the doubled carrier.
-/
theorem centeredHestenesCoordinate_eq_real_shift_plus_imag_axis (z : ℂ) :
    centeredHestenesCoordinate (E := E) z =
      (((1 / 2 : ℝ) + z.re) • (1 : EndH)) + z.im • polarizationAxis (E := E) := by
  unfold centeredHestenesCoordinate
  simpa [criticalCentered] using
    hestenesScalar_eq_real_plus_imag_polarization (E := E) (criticalCentered z)

end DoubledReadback

end InfoGeometry.Canonical.CenteredTripotentSectorGeometry
