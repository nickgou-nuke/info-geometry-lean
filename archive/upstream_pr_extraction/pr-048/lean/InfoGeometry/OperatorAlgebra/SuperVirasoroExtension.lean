/-
InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean

Virasoro and super-Virasoro central-extension hypotheses.

This module records the infinite-dimensional boundary route for absorbing
TKK/global-conformal closure defects as central charges.

It is deliberately separate from finite five-grade absorption. In the finite
exceptional/quasiconformal route, grade `±2` is a genuine grade sector and is
not automatically central in the full algebra. In the Virasoro route, the
adjoined central charge is genuinely central by an explicit field.
-/

import Mathlib.Tactic
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.External.Virasoro.VirasoroCocycle

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SuperVirasoroExtension

/-! ## 1. Virasoro algebra datum -/

/--
Virasoro algebra datum with a central charge generator.

The bracket law is kept proof-carrying. A concrete representation may later
instantiate it by actual modes.
-/
structure VirasoroAlgebraDatum
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  /-- The Virasoro generators `L_n`. -/
  genL : ℤ → L

  /-- Central charge generator. -/
  centralCharge : L

  /-- The central charge commutes with every element. -/
  central_commutes_hyp :
    ∀ X : L, ⁅centralCharge, X⁆ = 0

  /-- Virasoro mode bracket with central term. -/
  virasoro_bracket :
    ∀ m n : ℤ,
      ⁅genL m, genL n⁆ =
        (((m - n : ℤ) : ℝ) • genL (m + n)) +
          (if m + n = 0 then
            ((((m ^ 3 - m : ℤ) : ℝ) / 12) • centralCharge)
          else
            0)

namespace VirasoroAlgebraDatum

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (V : VirasoroAlgebraDatum L)

/-- The central charge is central. -/
alias central_commutes := VirasoroAlgebraDatum.central_commutes_hyp

end VirasoroAlgebraDatum

/-! ## 2. Global conformal anomaly coefficient -/

/--
The Virasoro anomaly polynomial before multiplying by the central scalar and
the Kronecker delta.

`m * (m^2 - 1)` vanishes for the global conformal modes `m = -1, 0, 1`.
-/
def virasoroCentralPolynomial
    (m : ℤ) : ℤ :=
  m * (m ^ 2 - 1)

/-- The scalar anomaly coefficient vanishes on global conformal modes. -/
theorem anomalyCoefficient_zero_on_global_modes
    (m : ℤ)
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    virasoroCentralPolynomial m = 0 := by
  rcases hm with h | h | h
  · subst h
    norm_num [virasoroCentralPolynomial]
  · subst h
    norm_num [virasoroCentralPolynomial]
  · subst h
    norm_num [virasoroCentralPolynomial]

/-! ## 3. Super-Virasoro hypotheses -/

/--
Super-Virasoro extension.

The chiral supercharges are represented by `genG`.

The anticommutation law is kept as a proof-carrying property because the
index set differs between the Ramond and Neveu-Schwarz sectors.
-/
structure SuperVirasoroAlgebraDatum
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  /-- Bosonic Virasoro sector. -/
  bosonic : VirasoroAlgebraDatum L

  /-- Chiral supercharge modes. -/
  genG : ℚ → L

  /-- Sector-dependent projection of a supercharge mode sum to a Virasoro mode. -/
  superModeSum : ℚ → ℚ → ℤ

  /-- Sector-dependent central coefficient in the odd/odd bracket. -/
  superCentralCoefficient : ℚ → ℚ → ℝ

  /-- Supercharge odd/odd bracket formula with explicit sector data. -/
  super_bracket :
    ∀ r s : ℚ,
      ⁅genG r, genG s⁆ =
        (2 : ℝ) • bosonic.genL (superModeSum r s) +
          superCentralCoefficient r s • bosonic.centralCharge

namespace SuperVirasoroAlgebraDatum

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (S : SuperVirasoroAlgebraDatum L)

end SuperVirasoroAlgebraDatum

/-! ## 4. Central charge bridge -/

/--
A bridge from a macroscopic closure defect to a Virasoro central-charge readout.
-/
structure VirasoroCentralChargeBridge
    (L State Defect : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Defect] [Module ℝ Defect] where
  virasoro :
    VirasoroAlgebraDatum L

  /-- Macroscopic defect readout. -/
  macroscopicDefect :
    State → Defect

  /-- Readout mapping the algebraic central charge to the physical defect. -/
  centralChargeReadout :
    L → State → Defect

  /--
  Bridge law: the macroscopic defect is the readout of the Virasoro central
  charge.
  -/
  defect_is_central_charge :
    ∀ s : State,
      macroscopicDefect s =
        centralChargeReadout virasoro.centralCharge s

namespace VirasoroCentralChargeBridge

variable
    {L State Defect : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Defect] [Module ℝ Defect]

variable
    (B : VirasoroCentralChargeBridge L State Defect)

end VirasoroCentralChargeBridge

/-! ## 5. Literature-backed Virasoro lemmas from Kytölä's Lean formalization -/

open VirasoroProject

/--
`LEMMA_DEBT virasoro_central_generator_commutes`.

Source: K. Kytölä, *Virasoro algebra and Sugawara constructions formally in
Lean*; vendored formal source `InfoGeometry.External.Virasoro.VirasoroAlgebra`.
The central generator `C` of the Virasoro algebra commutes with every element.
-/
theorem virasoroProject_central_commutes
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X : VirasoroAlgebra 𝕜) :
    ⁅VirasoroAlgebra.cgen 𝕜, X⁆ = 0 := by
  simp

/--
`LEMMA_DEBT virasoro_lgen_bracket`.

Source: K. Kytölä's formal Virasoro project, theorem
`VirasoroProject.VirasoroAlgebra.lgen_bracket`.  For all integers `n,m`,
`[Lₙ,Lₘ] = (n-m)Lₙ₊ₘ + ((n³-n)/12) C` when `n+m=0`, and has no central
term otherwise.
-/
theorem virasoroProject_lgen_bracket
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (n m : ℤ) :
    ⁅VirasoroAlgebra.lgen 𝕜 n, VirasoroAlgebra.lgen 𝕜 m⁆
      = (n - m : 𝕜) • VirasoroAlgebra.lgen 𝕜 (n + m) +
          if n + m = 0 then ((n^3 - n : 𝕜)/12) • VirasoroAlgebra.cgen 𝕜 else 0 := by
  simp

/--
`LEMMA_DEBT virasoro_cocycle_nontrivial`.

Source: Kytölä's formal Virasoro project, theorem
`WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero`.  The Gelfand-Fuchs /
Virasoro 2-cocycle has nonzero cohomology class; hence the central extension is
not cohomologically trivial.
-/
theorem virasoroProject_cocycle_class_nonzero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    (VirasoroProject.WittAlgebra.virasoroCocycle 𝕜).cohomologyClass ≠ 0 := by
  exact VirasoroProject.WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero 𝕜

end InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
