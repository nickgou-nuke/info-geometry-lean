import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.ChiralDiracHomologyCalibration
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.ChiralDiracHomologyBridge

This file separates the chain-complex and Hodge/Dirac readings.

* A nilpotent chiral differential pair gives cycle/boundary predicates.
* A chiral Dirac pair gives Laplace/Hodge loops.
* Identifying homology classes with harmonic representatives requires an
  explicit Hodge property/calibration.

No full Hodge theorem or cohomology theorem is asserted here.
-/

namespace InfoGeometry.Canonical.ChiralDiracHomologyBridge

open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

/-! ## Root doubled-carrier readbacks from the owner lane -/

section RootReadbacks

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Root plus harmonic predicate from the owned chiral Laplacian. -/
@[rep_depth krein]
def rootPlusHarmonic (u : H₂) : Prop :=
  (rootChiralLaplacianPlus (E := E)) u = 0

/-- Root minus harmonic predicate from the owned chiral Laplacian. -/
@[rep_depth krein]
def rootMinusHarmonic (u : H₂) : Prop :=
  (rootChiralLaplacianMinus (E := E)) u = 0

/-- Root plus harmonic states are exactly the kernel of the plus spectral projector. -/
@[rep_depth krein]
theorem rootPlusHarmonic_iff_spectralPlus_zero
    (u : H₂) :
    rootPlusHarmonic (E := E) u ↔
      (spectralChiralPlusProjector (E := E)) u = 0 := by
  unfold rootPlusHarmonic
  rw [rootChiralLaplacianPlus_eq_spectralChiralPlusProjector]

/-- Root minus harmonic states are exactly the kernel of the minus spectral projector. -/
@[rep_depth krein]
theorem rootMinusHarmonic_iff_spectralMinus_zero
    (u : H₂) :
    rootMinusHarmonic (E := E) u ↔
      (spectralChiralMinusProjector (E := E)) u = 0 := by
  unfold rootMinusHarmonic
  rw [rootChiralLaplacianMinus_eq_spectralChiralMinusProjector]

/-- Owner-lane readback: the root odd Dirac lane splits into chiral arrows. -/
@[rep_depth krein]
theorem rootDirac_eq_Dplus_add_Dminus :
    rootDiracOddLane (E := E) =
      rootDiracPlus (E := E) + rootDiracMinus (E := E) :=
  rootDiracOddLane_eq_chiral_sum (E := E)

/-- Owner-lane readback: `D² = Δ₊ + Δ₋` for the root doubled carrier. -/
@[rep_depth krein]
theorem rootDirac_sq_eq_hodge_loop_sum :
    (rootDiracOddLane (E := E)).comp (rootDiracOddLane (E := E)) =
      rootChiralLaplacianPlus (E := E) +
        rootChiralLaplacianMinus (E := E) :=
  rootDiracOddLane_sq_eq_chiralLaplacian_sum (E := E)

end RootReadbacks

/-! ## 5. K-linear real cochain readout -/

section KLinearReadout

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
A real Hestenes cochain/readout is `K`-linear when it preserves the internal
phase axis. This is just the already-owned Hestenes analytic symmetry predicate.
-/
@[rep_depth krein]
abbrev IsKLinearCochain (A : EndH) : Prop :=
  IsHestenesAnalyticSymmetry (E := E) A

/--
K-linear cochains are closed under the operator commutator.

This reuses the existing Hestenes analytic closure theorem.
-/
@[rep_depth krein]
theorem KLinearCochain_commutator
    {A B : EndH}
    (hA : IsKLinearCochain (E := E) A)
    (hB : IsKLinearCochain (E := E) B) :
    IsKLinearCochain (E := E)
      (hestenesSymmetryCommutator (E := E) A B) :=
  hestenesAnalyticSymmetry_commutator (E := E) hA hB

end KLinearReadout

end InfoGeometry.Canonical.ChiralDiracHomologyBridge
