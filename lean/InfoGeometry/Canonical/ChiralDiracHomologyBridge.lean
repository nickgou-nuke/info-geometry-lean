import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.ChiralDiracHomologyBridge

This file separates the chain-complex and Hodge/Dirac readings.

* A nilpotent chiral differential pair gives cycle/boundary predicates.
* A chiral Dirac pair gives Laplace/Hodge loops.
* Identifying homology classes with harmonic representatives requires an
  explicit Hodge witness/calibration.

No full Hodge theorem or cohomology theorem is asserted here.
-/

namespace InfoGeometry.Canonical.ChiralDiracHomologyBridge

open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

/-! ## 1. Pure chiral chain-complex socket -/

/--
A chiral differential pair.

`dPlus : C₊ → C₋` and `dMinus : C₋ → C₊`.

This is the chain-complex/homology socket. It is valid only when the two
same-direction two-step composites vanish.
-/
@[socket_debt_tag, rep_depth operator]
structure ChiralComplexSocket (Cplus Cminus : Type*) [Zero Cplus] [Zero Cminus] where
  dPlus : Cplus → Cminus
  dMinus : Cminus → Cplus

  /-- `d⁺ ∘ d⁻ = 0`, so plus-boundaries land inside plus-cycles. -/
  dPlus_dMinus_zero :
    ∀ y : Cminus, dPlus (dMinus y) = 0

  /-- `d⁻ ∘ d⁺ = 0`, so minus-boundaries land inside minus-cycles. -/
  dMinus_dPlus_zero :
    ∀ x : Cplus, dMinus (dPlus x) = 0

namespace ChiralComplexSocket

variable {Cplus Cminus : Type*}
variable [Zero Cplus] [Zero Cminus]
variable (C : ChiralComplexSocket Cplus Cminus)

/-- Plus cycles: states killed by the outgoing `dPlus` arrow. -/
@[rep_depth operator]
def plusCycle (x : Cplus) : Prop :=
  C.dPlus x = 0

/-- Minus cycles: states killed by the outgoing `dMinus` arrow. -/
@[rep_depth operator]
def minusCycle (y : Cminus) : Prop :=
  C.dMinus y = 0

/-- Plus boundaries: states produced by the incoming `dMinus` arrow. -/
@[rep_depth operator]
def plusBoundary (x : Cplus) : Prop :=
  ∃ y : Cminus, C.dMinus y = x

/-- Minus boundaries: states produced by the incoming `dPlus` arrow. -/
@[rep_depth operator]
def minusBoundary (y : Cminus) : Prop :=
  ∃ x : Cplus, C.dPlus x = y

/--
Boundary-to-cycle law in the plus sector.

This is the exact algebraic condition needed for the quotient
`ker dPlus / im dMinus`.
-/
@[rep_depth operator]
theorem plus_boundary_is_cycle
    {x : Cplus}
    (hx : plusBoundary C x) :
    plusCycle C x := by
  rcases hx with ⟨y, hy⟩
  unfold plusCycle
  rw [← hy]
  exact C.dPlus_dMinus_zero y

/--
Boundary-to-cycle law in the minus sector.

This is the exact algebraic condition needed for the quotient
`ker dMinus / im dPlus`.
-/
@[rep_depth operator]
theorem minus_boundary_is_cycle
    {y : Cminus}
    (hy : minusBoundary C y) :
    minusCycle C y := by
  rcases hy with ⟨x, hx⟩
  unfold minusCycle
  rw [← hx]
  exact C.dMinus_dPlus_zero x

end ChiralComplexSocket

/-! ## 2. Chiral Hodge/Dirac socket -/

/--
A chiral Hodge/Dirac pair.

This does not require nilpotence. Instead, it carries the Laplace/Hodge loops:

`Δ₊ = D⁻D⁺`, `Δ₋ = D⁺D⁻`.
-/
@[socket_debt_tag, rep_depth krein]
structure ChiralHodgeDiracSocket (Cplus Cminus : Type*) [Zero Cplus] [Zero Cminus] where
  Dplus : Cplus → Cminus
  Dminus : Cminus → Cplus
  LapPlus : Cplus → Cplus
  LapMinus : Cminus → Cminus

  /-- Positive-sector Hodge loop `Δ₊ = D⁻D⁺`. -/
  LapPlus_law :
    ∀ x : Cplus, LapPlus x = Dminus (Dplus x)

  /-- Negative-sector Hodge loop `Δ₋ = D⁺D⁻`. -/
  LapMinus_law :
    ∀ y : Cminus, LapMinus y = Dplus (Dminus y)

namespace ChiralHodgeDiracSocket

variable {Cplus Cminus : Type*}
variable [Zero Cplus] [Zero Cminus]
variable (H : ChiralHodgeDiracSocket Cplus Cminus)

/-- Harmonic plus-sector states: kernel of the plus Laplacian. -/
@[rep_depth krein]
def plusHarmonic (x : Cplus) : Prop :=
  H.LapPlus x = 0

/-- Harmonic minus-sector states: kernel of the minus Laplacian. -/
@[rep_depth krein]
def minusHarmonic (y : Cminus) : Prop :=
  H.LapMinus y = 0

/-- Readback: plus harmonic means the `D⁻D⁺` loop vanishes. -/
@[rep_depth krein]
theorem plusHarmonic_iff_loop_zero
    (x : Cplus) :
    plusHarmonic H x ↔ H.Dminus (H.Dplus x) = 0 := by
  unfold plusHarmonic
  rw [H.LapPlus_law x]

/-- Readback: minus harmonic means the `D⁺D⁻` loop vanishes. -/
@[rep_depth krein]
theorem minusHarmonic_iff_loop_zero
    (y : Cminus) :
    minusHarmonic H y ↔ H.Dplus (H.Dminus y) = 0 := by
  unfold minusHarmonic
  rw [H.LapMinus_law y]

end ChiralHodgeDiracSocket

/-! ## 3. Hodge theorem/calibration socket -/

/--
Explicit witness that a chiral complex and a chiral Hodge/Dirac socket are
calibrated.

This is where a future Hodge theorem may be installed. Until such a witness is
supplied, `ker Δ±` is only the harmonic readout, not automatically a homology
quotient.
-/
@[rep_depth krein]
structure ChiralHodgeHomologyCalibration
    (Cplus Cminus : Type*) [Zero Cplus] [Zero Cminus] where
  complex : ChiralComplexSocket Cplus Cminus
  hodge : ChiralHodgeDiracSocket Cplus Cminus

  /-- The Hodge `D⁺` agrees with the differential `d⁺`. -/
  Dplus_eq_dPlus :
    ∀ x : Cplus, hodge.Dplus x = complex.dPlus x

  /-- The Hodge `D⁻` agrees with the differential `d⁻`. -/
  Dminus_eq_dMinus :
    ∀ y : Cminus, hodge.Dminus y = complex.dMinus y

  /-- Plus harmonic representatives are supplied as the readout of plus homology. -/
  plus_harmonic_represents_homology : Prop
  plus_harmonic_represents_homology_holds : plus_harmonic_represents_homology

  /-- Minus harmonic representatives are supplied as the readout of minus homology. -/
  minus_harmonic_represents_homology : Prop
  minus_harmonic_represents_homology_holds : minus_harmonic_represents_homology

namespace ChiralHodgeHomologyCalibration

variable {Cplus Cminus : Type*}
variable [Zero Cplus] [Zero Cminus]
variable (K : ChiralHodgeHomologyCalibration Cplus Cminus)

/-- Readback of the plus Hodge/homology calibration witness. -/
@[rep_depth krein]
theorem plus_hodge_witness :
    K.plus_harmonic_represents_homology :=
  K.plus_harmonic_represents_homology_holds

/-- Readback of the minus Hodge/homology calibration witness. -/
@[rep_depth krein]
theorem minus_hodge_witness :
    K.minus_harmonic_represents_homology :=
  K.minus_harmonic_represents_homology_holds

end ChiralHodgeHomologyCalibration

/-! ## 4. Root doubled-carrier readbacks from the owner lane -/

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
