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
  LapPlus_True :
    ∀ x : Cplus, LapPlus x = Dminus (Dplus x)

  /-- Negative-sector Hodge loop `Δ₋ = D⁺D⁻`. -/
  LapMinus_True :
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
  rw [H.LapPlus_True x]

/-- Readback: minus harmonic means the `D⁺D⁻` loop vanishes. -/
@[rep_depth krein]
theorem minusHarmonic_iff_loop_zero
    (y : Cminus) :
    minusHarmonic H y ↔ H.Dplus (H.Dminus y) = 0 := by
  unfold minusHarmonic
  rw [H.LapMinus_True y]

end ChiralHodgeDiracSocket

/-! ## 3. Chiral Hodge/Dirac calibration data -/

/--
Explicit data aligning a chiral complex and a chiral Hodge/Dirac socket.
This file does not assert a Hodge theorem identifying harmonic representatives
with homology classes.
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

/-! ## 4. File-level owner theorem -/

/-- The chiral/Dirac homology owner target is discharged by the local witnesses. -/
theorem chiralDiracHomologyBridgeOwnerTarget :
    (∀ {Cplus Cminus : Type*} [Zero Cplus] [Zero Cminus]
        (C : ChiralComplexSocket Cplus Cminus)
        {x : Cplus}, C.plusBoundary x → C.plusCycle x) ∧
    (∀ {Cplus Cminus : Type*} [Zero Cplus] [Zero Cminus]
        (C : ChiralComplexSocket Cplus Cminus)