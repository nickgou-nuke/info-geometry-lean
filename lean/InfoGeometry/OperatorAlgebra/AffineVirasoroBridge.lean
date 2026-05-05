/-
InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean

Affine-current / Virasoro bridge.

This module records the formal socket connecting a finite symmetry algebra,
its affine/current extension, and a Virasoro reparametrization algebra.

For exceptional models, the finite algebra may later be instantiated by
`E8(8)`, and the affine extension by `E9(9)`.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## 1. Virasoro data -/

/--
A Virasoro-like datum.

`Lmode n` is the Virasoro generator `L_n`.

`central` is the Virasoro central element.

The bracket law is proof-carrying because this file does not build the analytic
central extension of vector fields on the circle.
-/
structure VirasoroDatum
    (Alg : Type*) [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  Lmode : ℤ → Alg
  central : Alg

  central_commutes :
    ∀ X : Alg, ⁅central, X⁆ = 0

  virasoro_law : Prop
  virasoro_law_holds : virasoro_law

/--
The Virasoro central polynomial.

It vanishes on the global conformal modes `-1, 0, 1`.
-/
def virasoroCentralPolynomial (m : ℤ) : ℤ :=
  m * (m ^ 2 - 1)

/--
The central polynomial vanishes for the global `sl₂`/TKK modes.
-/
theorem virasoroCentralPolynomial_global_zero
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

/-! ## 1A. Sugawara central-charge calibration -/

/--
Sugawara central charge for an affine current algebra:

`c = k * dim(g) / (k + h∨)`.

This is kept as rational arithmetic in this generic bridge. Concrete real-form
and representation-category choices still belong to later model modules.
-/
def sugawaraCentralCharge
    (level finiteDimension dualCoxeterNumber : ℚ) : ℚ :=
  level * finiteDimension / (level + dualCoxeterNumber)

/-- The level-one `E₈` Sugawara central charge is `8`. -/
theorem sugawaraCentralCharge_E8_levelOne :
    sugawaraCentralCharge 1 248 30 = 8 := by
  norm_num [sugawaraCentralCharge]

/--
The level-one `so(4,4)` / `D₄` Sugawara central charge is `4`.

The real form has the same complexified dimension and dual Coxeter number for
this Sugawara readout: `dim so(8) = 28` and `h∨ = 6`.
-/
theorem sugawaraCentralCharge_so44_levelOne :
    sugawaraCentralCharge 1 28 6 = 4 := by
  norm_num [sugawaraCentralCharge]

/-! ## 2. Affine current data -/

/--
An affine-current datum for a finite symmetry algebra.

`Current n X` should be read as the loop/current mode `X ⊗ t^n`.

`kCentral` is the affine Kac-Moody central element.

This is generic; a later exceptional module may instantiate `Finite` with a
formal `E8(8)` model.
-/
structure AffineCurrentDatum
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  Current : ℤ → Finite → Alg

  kCentral : Alg

  kCentral_commutes :
    ∀ X : Alg, ⁅kCentral, X⁆ = 0

  affine_bracket_law : Prop
  affine_bracket_law_holds : affine_bracket_law

/-! ## 3. Affine-Virasoro bridge -/

/--
Affine-Virasoro bridge.

This records the two key facts:

1. Virasoro modes reparametrize affine current modes.
2. A Sugawara or stress-tensor construction may produce the Virasoro datum from
   the affine currents.

Both are proof-carrying laws at this level.
-/
structure AffineVirasoroBridgeDatum
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  affine :
    AffineCurrentDatum Finite Alg

  virasoro :
    VirasoroDatum Alg

  /--
  Reparametrization law, morally:

  `[L_m, J_X,n] = -n J_X,m+n`.
  -/
  virasoro_acts_on_currents_law : Prop
  virasoro_acts_on_currents_law_holds :
    virasoro_acts_on_currents_law

  /--
  Sugawara/stress-tensor law producing or calibrating the Virasoro generators
  from affine currents.
  -/
  sugawara_law : Prop
  sugawara_law_holds :
    sugawara_law

  /--
  Central charge readout of the Virasoro algebra.
  -/
  centralCharge : ℝ

  /-- Affine level `k` used by the Sugawara calibration. -/
  level : ℝ

  /-- Dimension of the finite current algebra. -/
  finiteDimension : ℝ

  /-- Dual Coxeter number `h∨` of the finite current algebra. -/
  dualCoxeterNumber : ℝ

  /--
  Explicit central-charge calibration:

  `c = k * dim(g) / (k + h∨)`.
  -/
  centralCharge_eq_sugawara :
    centralCharge =
      level * finiteDimension / (level + dualCoxeterNumber)

namespace AffineVirasoroBridgeDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : AffineVirasoroBridgeDatum Finite Alg)

/--
The bridge carries a Virasoro central-charge readout.
-/
def c : ℝ :=
  B.centralCharge

/-- The bridge's central charge is the explicit Sugawara value. -/
theorem centralCharge_calibrated :
    B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber) :=
  B.centralCharge_eq_sugawara

/--
The bridge supplies the Sugawara/stress-tensor calibration.
-/
theorem sugawara_holds :
    B.sugawara_law :=
  B.sugawara_law_holds

/--
The bridge supplies the Virasoro-current reparametrization law.
-/
theorem virasoro_acts_on_currents :
    B.virasoro_acts_on_currents_law :=
  B.virasoro_acts_on_currents_law_holds

end AffineVirasoroBridgeDatum

/-! ## 4. E8/E9-style calibration socket -/

/--
Exceptional affine-Virasoro calibration.

This is the socket for the statement:

`E8(8)` finite symmetry
    → affine `E9(9)` current symmetry
    → Virasoro reparametrization/stress-tensor ledger.

The concrete construction is supplied later.
-/
structure ExceptionalAffineVirasoroCalibration
    (Finite AffineAlg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg] where

  bridge :
    AffineVirasoroBridgeDatum Finite AffineAlg

  /-- Finite algebra is interpreted as split real `E8(8)`. -/
  finite_is_E8_split_real : Prop
  finite_is_E8_split_real_holds :
    finite_is_E8_split_real

  /-- Affine algebra is interpreted as `E9(9)` / affine `E8(8)`. -/
  affine_is_E9_extension : Prop
  affine_is_E9_extension_holds :
    affine_is_E9_extension

  /--
  Physical/geometric calibration: the Virasoro coordinate is the helical or
  local modular/spectral parameter.
  -/
  virasoro_is_helical_reparametrization : Prop
  virasoro_is_helical_reparametrization_holds :
    virasoro_is_helical_reparametrization

/-! ## 5. Owner target -/

/--
Owner target for the affine-Virasoro bridge.

Once the bridge is supplied, the Sugawara and reparametrization laws are
available.
-/
def AffineVirasoroBridgeOwnerTarget : Prop :=
  ∀ (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg],
  ∀ B : AffineVirasoroBridgeDatum Finite Alg,
    B.sugawara_law ∧
      B.virasoro_acts_on_currents_law ∧
      B.centralCharge =
        B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)

/--
The owner target follows from the supplied bridge.
-/
theorem affineVirasoroBridgeOwnerTarget :
    AffineVirasoroBridgeOwnerTarget := by
  intro Finite Alg _ _ _ _ _ _ _ _ B
  exact
    ⟨B.sugawara_holds,
      B.virasoro_acts_on_currents,
      B.centralCharge_calibrated⟩

end InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
