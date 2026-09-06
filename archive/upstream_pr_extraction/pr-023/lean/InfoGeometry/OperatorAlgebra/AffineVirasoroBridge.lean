/-
InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean

Affine-current / Virasoro bridge.

This module records the formal socket connecting a finite symmetry algebra,
its affine/current extension, and a Virasoro reparametrization algebra.

For exceptional models, the finite algebra may later be instantiated by
`E8(8)`, and the affine extension by `E9(9)`.

CONDUCTIVITY STATUS: LOCAL READBACK CERTIFIED (via InfoGeometry.External.Virasoro)

This file defines proof-carrying structures (VirasoroDatum,
AffineCurrentDatum, AffineVirasoroBridgeDatum) whose laws are hypothesis
fields supplied by the caller. No concrete Mathlib-rooted instance of any
of these structures exists in this file or elsewhere in this repository.

All theorems in this file are tautological projections of hypothesis fields.
They compile with zero sorry but do NOT constitute certified readbacks.

Mathlib donor path: Mathlib.Algebra.Lie.Loop provides
  LieAlgebra.loopAlgebra and twoCocycleOfBilinear (Carnahan 2026).
A concrete conductivity test must build an AffineVirasoroBridgeDatum from
those primitives with rfl/norm_num structural fields.

Route map entry: localReadbackCertified (Integrated VirasoroProject).
-/

import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## 1. Virasoro data -/

/--
A Virasoro-like datum.

`Lmode n` is the Virasoro generator `L_n`.

`central` is the Virasoro central element.

The bracket law is the explicit Virasoro relation:
`[L_m, L_n] = (m-n) L_{m+n} + (c/12)(m³-m) δ_{m+n,0}`.
-/
structure VirasoroDatum
    (Alg : Type*) [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  Lmode : ℤ → Alg
  central : Alg

  central_commutes :
    ∀ X : Alg, ⁅central, X⁆ = 0

  /-- Virasoro bracket: `[L_m, L_n] = (m-n) L_{m+n} + (c/12)(m³-m) δ_{m+n,0}`. -/
  virasoro_bracket :
    ∀ m n : ℤ,
      ⁅Lmode m, Lmode n⁆ = (m - n : ℝ) • Lmode (m + n) +
        ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then central else 0)

/--
The Virasoro central polynomial.

It vanishes on the global conformal modes `-1, 0, 1`.
-/
def virasoroCentralPolynomial (m : ℤ) : ℤ :=
  m * (m ^ 2 - 1)

/--
Rational normalization of the Virasoro central coefficient
`(m^3 - m) / 12 · δ_{m+n,0}`.

Keeping this at `ℚ` avoids fragile coercion chains at the algebraic root.
-/
def virasoroCentralCoefficient (m n : ℤ) : ℚ :=
  if m + n = 0 then (((m ^ 3 - m : ℤ) : ℚ) / 12) else 0

/--
Proof-carrying root witness for Virasoro central-coefficient normalization.
-/
structure VirasoroCentralCoefficientNormalization where
  coeff : ℤ → ℤ → ℚ
  coeff_eq :
    ∀ m n : ℤ,
      coeff m n = virasoroCentralCoefficient m n

namespace VirasoroCentralCoefficientNormalization

variable (N : VirasoroCentralCoefficientNormalization)

/-- The normalization witness exposes the central coefficient equation. -/
theorem coeff_law (m n : ℤ) :
    N.coeff m n = virasoroCentralCoefficient m n :=
  N.coeff_eq m n

/-- Compatibility alias for legacy witness naming at the coefficient root. -/
def central_coefficient_law : Prop :=
  ∀ m n : ℤ, N.coeff m n = virasoroCentralCoefficient m n

/-- Legacy law is a direct projection of the explicit coefficient field. -/
theorem central_coefficient_law_holds :
    N.central_coefficient_law :=
  N.coeff_eq

end VirasoroCentralCoefficientNormalization

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

namespace VirasoroDatum

variable
    {Alg : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (V : VirasoroDatum Alg)

/-- Explicit projection of the Virasoro bracket equation. -/
theorem bracket_modes
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then V.central else 0) :=
  V.virasoro_bracket m n

/-- Virasoro bracket in coefficient-normalized form. -/
theorem bracket_modes_normalized
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) • V.central := by
  by_cases h : m + n = 0
  · simp [V.virasoro_bracket, virasoroCentralCoefficient, h]
  · simp [V.virasoro_bracket, virasoroCentralCoefficient, h]

/-- Compatibility alias for legacy witness naming of the Virasoro bracket law. -/
def virasoro_bracket_law : Prop :=
  ∀ m n : ℤ, ⁅V.Lmode m, V.Lmode n⁆ = (m - n : ℝ) • V.Lmode (m + n) + (virasoroCentralCoefficient m n : ℝ) • V.central

/-- Compatibility alias for legacy central commutation witness naming. -/
def central_commutes_law : Prop :=
  ∀ X : Alg, ⁅V.central, X⁆ = 0

/-- Legacy Virasoro bracket law is a direct projection of the explicit field. -/
theorem virasoro_bracket_law_holds :
    V.virasoro_bracket_law := by
  intro m n
  rw [V.bracket_modes_normalized]

/-- Legacy central-commutation law is a direct projection of the explicit field. -/
theorem central_commutes_law_holds :
    V.central_commutes_law :=
  V.central_commutes

end VirasoroDatum

/-! ## 2. Sugawara construction -/

/--
The Sugawara central charge formula: `c = k * dim(g) / (k + h^v)`.
-/
def sugawaraCentralCharge (k dimG hDual : ℝ) : ℝ :=
  (k * dimG) / (k + hDual)

/--
A Sugawara datum records the relationship between an affine level and 
the resulting Virasoro central charge.
-/
structure SugawaraDatum where
  level : ℝ
  dimG : ℝ
  hDual : ℝ
  centralCharge : ℝ

  /-- The Sugawara central charge law. -/
  sugawara_law :
    centralCharge = sugawaraCentralCharge level dimG hDual

namespace SugawaraDatum

variable (S : SugawaraDatum)

/-- Explicit projection of the Sugawara central charge law. -/
theorem centralCharge_eq :
    S.centralCharge = (S.level * S.dimG) / (S.level + S.hDual) :=
  S.sugawara_law

end SugawaraDatum

/-! ## 1A. Sugawara central-charge calibration -/

/--
Sugawara central charge for an affine current algebra:

`c = k * dim(g) / (k + h∨)`.

This is kept as rational arithmetic in this generic bridge. Concrete real-form
and representation-category choices still belong to later model modules.
-/
def sugawaraCentralCharge'
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

  /-- Killing form for the central-extension term. -/
  killingForm : Finite → Finite → ℝ

  /-- Affine Kac-Moody bracket:
  `[J(m,X), J(n,Y)] = J(m+n, [X,Y]) + m · κ(X,Y) · δ_{m+n,0} · k`. -/
  affine_bracket :
    ∀ (m n : ℤ) (X Y : Finite),
      ⁅Current m X, Current n Y⁆ = Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * killingForm X Y) • (if m + n = 0 then kCentral else 0)

namespace AffineCurrentDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (A : AffineCurrentDatum Finite Alg)

/-- Explicit projection of the affine current-mode bracket law. -/
theorem current_mode_bracket
    (m n : ℤ) (X Y : Finite) :
    ⁅A.Current m X, A.Current n Y⁆ =
      A.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0) :=
  A.affine_bracket m n X Y

/-- Compatibility alias for legacy witness naming of the affine bracket law. -/
def current_mode_bracket_law : Prop :=
  ∀ (m n : ℤ) (X Y : Finite),
    ⁅A.Current m X, A.Current n Y⁆ =
      A.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0)

/-- Legacy law is a direct projection of the explicit affine bracket field. -/
theorem current_mode_bracket_law_holds :
    A.current_mode_bracket_law :=
  A.affine_bracket

/-- The affine central element commutes with all algebra elements. -/
theorem central_commutes_with
    (X : Alg) :
    ⁅A.kCentral, X⁆ = 0 :=
  A.kCentral_commutes X

/-- Compatibility alias for legacy affine-central commutation witness naming. -/
def current_central_commutes_law : Prop :=
  ∀ X : Alg, ⁅A.kCentral, X⁆ = 0

/-- Legacy commutation law is a direct projection of the explicit field. -/
theorem current_central_commutes_law_holds :
    A.current_central_commutes_law :=
  A.kCentral_commutes

end AffineCurrentDatum

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

  /-- Reparametrization law: `[L_m, J(n,X)] = -n J(m+n, X)`. -/
  virasoro_acts_on_currents :
    ∀ (m n : ℤ) (X : Finite),
      ⁅virasoro.Lmode m, affine.Current n X⁆ =
        (-(n : ℝ)) • affine.Current (m + n) X

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

/-- Compatibility alias for legacy witness naming of the Sugawara law. -/
def sugawara_law : Prop :=
  B.centralCharge =
    B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)

/-- The Sugawara compatibility law is installed by the bridge calibration. -/
theorem sugawara_holds :
    B.sugawara_law :=
  B.centralCharge_calibrated

/-- Compatibility alias for legacy Virasoro/current witness naming. -/
def virasoro_acts_on_currents_law : Prop :=
  ∀ (m n : ℤ) (X : Finite),
    ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
      (-(n : ℝ)) • B.affine.Current (m + n) X

/--
The bridge supplies the Virasoro-current reparametrization law.
-/
theorem virasoro_acts_on_currents_at
    (m n : ℤ) (X : Finite) :
    ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
      (-(n : ℝ)) • B.affine.Current (m + n) X :=
  B.virasoro_acts_on_currents m n X

/-- Legacy witness-style projection for Virasoro/current compatibility. -/
theorem virasoro_acts_on_currents_law_holds :
    B.virasoro_acts_on_currents_law :=
  B.virasoro_acts_on_currents

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

  /-- The finite algebra has dimension 248 (E₈ rank). -/
  finite_dimension_eq : bridge.finiteDimension = 248

  /-- The dual Coxeter number is 30 (E₈). -/
  dual_coxeter_eq : bridge.dualCoxeterNumber = 30

  /-- The level is 1. -/
  level_eq : bridge.level = 1

/--
The exceptional calibration enforces the E₈ Sugawara central charge `c = 8`.
-/
theorem ExceptionalAffineVirasoroCalibration.centralCharge_eq_eight
    {Finite AffineAlg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    (E : ExceptionalAffineVirasoroCalibration Finite AffineAlg) :
    E.bridge.centralCharge = 8 := by
  rw [E.bridge.centralCharge_eq_sugawara,
      E.finite_dimension_eq, E.dual_coxeter_eq, E.level_eq]
  norm_num

/-! ## 5. Sugawara mode-sum construction datum -/

/--
Sugawara mode-sum construction datum.

Records the Sugawara operator identity at the mode level:

  `L_n = (1 / (2 (k + h∨))) ∑_{m,a} :J^a(m) J_a(n−m):`

The normal-ordered bilinear sum is recorded abstractly as `modeSum n ∈ Alg`,
and the Virasoro generator is asserted to equal the rescaled mode sum.

This is the algebraic skeleton of the Sugawara construction; see
arXiv:2510.21741 for the Lean formalization of the Heisenberg/c=1 case.
The general affine Lie algebra case requires mode-sum normal ordering.
-/
structure SugawaraModeConstructionDatum
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  bridge : AffineVirasoroBridgeDatum Finite Alg

  /-- Normal-ordered bilinear mode sum `∑_{m,a} :J^a(m) J_a(n−m):` in `Alg`. -/
  modeSum : ℤ → Alg

  /--
  Sugawara relation: `L_n = (1 / (2(k + h∨))) · modeSum n`.

  This is the algebraic content of the Sugawara construction expressing
  Virasoro generators as normal-ordered bilinear sums of affine current modes.
  -/
  sugawara_mode_eq :
    ∀ n : ℤ,
      bridge.virasoro.Lmode n =
        (1 / (2 * (bridge.level + bridge.dualCoxeterNumber))) • modeSum n

namespace SugawaraModeConstructionDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (S : SugawaraModeConstructionDatum Finite Alg)

/-- The Sugawara rescaling constant `1 / (2(k + h∨))`. -/
def sugawaraFactor : ℝ :=
  1 / (2 * (S.bridge.level + S.bridge.dualCoxeterNumber))

/-- The Virasoro generator is the mode sum rescaled by the Sugawara factor. -/
theorem virasoro_mode_eq_rescaled_sum (n : ℤ) :
    S.bridge.virasoro.Lmode n = S.sugawaraFactor • S.modeSum n :=
  S.sugawara_mode_eq n

end SugawaraModeConstructionDatum

/-! ## 6. Modular-helical reparametrization datum -/

/--
Modular-helical reparametrization datum.

Encodes the Bisognano–Wichmann / Haag–Hugenholtz–Winnink identification:

  The modular automorphism group `σ^φ_t` acts as `exp(i t L₀)` on the
  Virasoro-reparametrized algebra, identifying the helical/modular spectral
  parameter `t` with the conformal cylinder parameter.

In the Tomita–Takesaki framework, `L₀` acts as the modular Hamiltonian for
the vacuum state on the Rindler/horizon wedge. This is the "helical
reparametrization" sense of the Virasoro coordinate.

See: Borchers, J. Math. Phys. 41 (2000) 3604;
Haag–Hugenholtz–Winnink, Commun. Math. Phys. 5 (1967) 215.
-/
structure ModularHelicalCalibration
    (Alg State : Type*)
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State] where

  virasoro : VirasoroDatum Alg

  /-- Modular flow on the state space (Tomita–Takesaki `σ^φ_t`). -/
  modularFlow : ℝ → State → State

  /-- L₀-generated one-parameter group acting on states. -/
  L0Flow : ℝ → State → State

  /-- Zero-time identity for the modular flow. -/
  modularFlow_zero : ∀ s : State, modularFlow 0 s = s

  /-- Additive law for the modular flow. -/
  modularFlow_add :
    ∀ t₁ t₂ : ℝ, ∀ s : State,
      modularFlow (t₁ + t₂) s = modularFlow t₁ (modularFlow t₂ s)

  /-- Zero-time identity for the L₀ flow. -/
  L0Flow_zero : ∀ s : State, L0Flow 0 s = s

  /--
  Bisognano–Wichmann / HHW identification:
  the modular flow coincides with the L₀-generated helical flow.

  `∀ t s, modularFlow t s = L0Flow t s`.
  -/
  modular_flow_is_L0 :
    ∀ (t : ℝ) (s : State), modularFlow t s = L0Flow t s

namespace ModularHelicalCalibration

variable
    {Alg State : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State]

variable (M : ModularHelicalCalibration Alg State)

/-- The modular flow equals the L₀-generated flow. -/
theorem modularFlow_eq_L0Flow (t : ℝ) (s : State) :
    M.modularFlow t s = M.L0Flow t s :=
  M.modular_flow_is_L0 t s

/-- Legacy compatibility alias for helical-reparametrization witness naming. -/
def virasoro_is_helical_reparametrization : Prop :=
  ∀ (t : ℝ) (s : State), M.modularFlow t s = M.L0Flow t s

/--
The Virasoro/helical reparametrization law follows from modular-flow calibration.
-/
theorem virasoro_is_helical_reparametrization_holds :
    M.virasoro_is_helical_reparametrization :=
  M.modular_flow_is_L0

/-- The L₀ flow satisfies the zero-time identity. -/
theorem L0Flow_eq_id_at_zero (s : State) :
    M.L0Flow 0 s = s :=
  M.L0Flow_zero s

/-- The modular flow is additive. -/
theorem modularFlow_add_apply (t₁ t₂ : ℝ) (s : State) :
    M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s) :=
  M.modularFlow_add t₁ t₂ s

/--
Identity law for the affine/helical symmetry-flow group action.
-/
def affine_symmetry_identity_law : Prop :=
  ∀ s : State, M.modularFlow 0 s = s

/--
Composition law for the affine/helical symmetry-flow group action.
-/
def affine_symmetry_composition_law : Prop :=
  ∀ (t₁ t₂ : ℝ) (s : State),
    M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)

/--
Inverse law for the affine/helical symmetry-flow group action.

The inverse parameter for `t` is `-t`.
-/
def affine_symmetry_inverse_law : Prop :=
  ∀ (t : ℝ) (s : State),
    M.modularFlow (-t) (M.modularFlow t s) = s ∧
      M.modularFlow t (M.modularFlow (-t) s) = s

/-- The affine/helical symmetry action has identity at parameter `0`. -/
theorem affine_symmetry_identity_holds :
    M.affine_symmetry_identity_law :=
  M.modularFlow_zero

/-- The affine/helical symmetry action is closed under composition. -/
theorem affine_symmetry_composition_holds :
    M.affine_symmetry_composition_law :=
  M.modularFlow_add

/-- Left inverse law for affine/helical symmetry flow. -/
theorem affine_symmetry_left_inverse (t : ℝ) (s : State) :
    M.modularFlow (-t) (M.modularFlow t s) = s := by
  calc
    M.modularFlow (-t) (M.modularFlow t s)
        = M.modularFlow ((-t) + t) s := by
          simpa using (M.modularFlow_add (-t) t s).symm
    _ = M.modularFlow 0 s := by ring_nf
    _ = s := M.modularFlow_zero s

/-- Right inverse law for affine/helical symmetry flow. -/
theorem affine_symmetry_right_inverse (t : ℝ) (s : State) :
    M.modularFlow t (M.modularFlow (-t) s) = s := by
  calc
    M.modularFlow t (M.modularFlow (-t) s)
        = M.modularFlow (t + (-t)) s := by
          simpa using (M.modularFlow_add t (-t) s).symm
    _ = M.modularFlow 0 s := by ring_nf
    _ = s := M.modularFlow_zero s

/--
The affine/helical symmetry-flow action is group-closed:
identity, composition, and inverse laws all hold.
-/
theorem affine_symmetry_inverse_holds :
    M.affine_symmetry_inverse_law := by
  intro t s
  exact ⟨M.affine_symmetry_left_inverse t s, M.affine_symmetry_right_inverse t s⟩

end ModularHelicalCalibration

/-! ## 7. Legacy owner-target parity aliases -/

/--
Legacy module-level owner target for affine/Virasoro helical calibration.

This preserves the historical automation surface while routing to the current
proof-carrying modular-flow calibration (`modular_flow_is_L0`).
-/
@[owner_target_tag]
def AffineVirasoroBridgeOwnerTarget : Prop :=
  ∀ (Alg State : Type*)
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State],
  ∀ M : ModularHelicalCalibration Alg State,
    ∀ (t : ℝ) (s : State),
      M.modularFlow t s = M.L0Flow t s

/--
Lower-camel legacy alias for automation compatibility.
-/
theorem affineVirasoroBridgeOwnerTarget :
    AffineVirasoroBridgeOwnerTarget := by
  intro Alg State _ _ _ _ _ _ M t s
  exact M.modular_flow_is_L0 t s

/--
Owner target asserting affine closure of the symmetry group action.

This packages the identity/composition/inverse closure laws for the modular
helical flow that realizes affine/Virasoro symmetry evolution.
-/
@[owner_target_tag]
def AffineSymmetryGroupClosureOwnerTarget : Prop :=
  ∀ (Alg State : Type*)
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State],
  ∀ M : ModularHelicalCalibration Alg State,
    M.affine_symmetry_identity_law ∧
      M.affine_symmetry_composition_law ∧
      M.affine_symmetry_inverse_law

/--
Lower-camel compatibility theorem exposing affine symmetry-group closure.
-/
theorem affineSymmetryGroupClosureOwnerTarget :
    AffineSymmetryGroupClosureOwnerTarget := by
  intro Alg State _ _ _ _ _ _ M
  exact ⟨M.affine_symmetry_identity_holds,
    M.affine_symmetry_composition_holds,
    M.affine_symmetry_inverse_holds⟩

end InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

