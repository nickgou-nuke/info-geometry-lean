import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## 1. Virasoro data -/

/--
A Virasoro-like datum.

`Lmode n` is the Virasoro generator `L_n`.

`central` is the Virasoro central element.
-/
structure VirasoroDatum
    (Alg : Type*) [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  Lmode : ℤ → Alg
  central : Alg
  central_commutes_field : ∀ X : Alg, ⁅central, X⁆ = 0
  bracket_modes_field :
    ∀ m n : ℤ,
      ⁅Lmode m, Lmode n⁆ =
        (m - n : ℝ) • Lmode (m + n) +
          ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then central else 0)
  bracket_modes_normalized_field :
    ∀ m n : ℤ,
      ⁅Lmode m, Lmode n⁆ =
        (m - n : ℝ) • Lmode (m + n) +
          ((if m + n = 0 then (((m ^ 3 - m : ℤ) : ℚ) / 12) else 0 : ℚ) : ℝ) • central

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

/-- The central element commutes with everything. -/
theorem central_commutes (X : Alg) : ⁅V.central, X⁆ = 0 := by
  exact V.central_commutes_field X

/-- Explicit projection of the Virasoro bracket equation. -/
theorem bracket_modes
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then V.central else 0) := by
  exact V.bracket_modes_field m n

/-- Virasoro bracket in coefficient-normalized form. -/
theorem bracket_modes_normalized
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) • V.central := by
  simpa [virasoroCentralCoefficient] using V.bracket_modes_normalized_field m n

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
  centralCharge_eq_field : centralCharge = (level * dimG) / (level + hDual)

namespace SugawaraDatum

variable (S : SugawaraDatum)

/-- Explicit projection of the Sugawara central charge law. -/
theorem centralCharge_eq :
    S.centralCharge = (S.level * S.dimG) / (S.level + S.hDual) := by
  exact S.centralCharge_eq_field

/-- Compatibility alias for legacy witness naming of the Sugawara law. -/
def sugawara_law : Prop :=
  S.centralCharge = sugawaraCentralCharge S.level S.dimG S.hDual

/-- The Sugawara compatibility law is installed by the bridge calibration. -/
theorem sugawara_holds :
    S.sugawara_law := by
  simpa [sugawara_law, sugawaraCentralCharge] using S.centralCharge_eq

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

  /-- Killing form for the central-extension term. -/
  killingForm : Finite → Finite → ℝ
  current_mode_bracket_field :
    ∀ (m n : ℤ) (X Y : Finite),
      ⁅Current m X, Current n Y⁆ =
        Current (m + n) ⁅X, Y⁆ +
          ((m : ℝ) * killingForm X Y) • (if m + n = 0 then kCentral else 0)
  central_commutes_field : ∀ X : Alg, ⁅kCentral, X⁆ = 0

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
        ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0) := by
  exact A.current_mode_bracket_field m n X Y

/-- Compatibility alias for legacy witness naming of the affine bracket law. -/
def current_mode_bracket_law : Prop :=
  ∀ (m n : ℤ) (X Y : Finite),
    ⁅A.Current m X, A.Current n Y⁆ =
      A.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0)

/-- Legacy law is a direct projection of the explicit affine bracket field. -/
theorem current_mode_bracket_law_holds :
    A.current_mode_bracket_law := by
  intro m n X Y
  exact A.current_mode_bracket m n X Y

/-- The affine central element commutes with all algebra elements. -/
theorem central_commutes_with
    (X : Alg) :
    ⁅A.kCentral, X⁆ = 0 := by
  exact A.central_commutes_field X

/-- Compatibility alias for legacy affine-central commutation witness naming. -/
def current_central_commutes_law : Prop :=
  ∀ X : Alg, ⁅A.kCentral, X⁆ = 0

/-- Legacy commutation law is a direct projection of the explicit field. -/
theorem current_central_commutes_law_holds :
    A.current_central_commutes_law :=
  A.central_commutes_with

end AffineCurrentDatum

/-! ## 3. Affine-Virasoro bridge -/

/--
Affine-Virasoro bridge.

This records the two key facts:

1. Virasoro modes reparametrize affine current modes.
2. A Sugawara or stress-tensor construction may produce the Virasoro datum from
   the affine currents.
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
  Central charge readout of the Virasoro algebra.
  -/
  centralCharge : ℝ

  /-- Affine level `k` used by the Sugawara calibration. -/
  level : ℝ

  /-- Dimension of the finite current algebra. -/
  finiteDimension : ℝ

  /-- Dual Coxeter number `h∨` of the finite current algebra. -/
  dualCoxeterNumber : ℝ
  virasoro_acts_on_currents_field :
    ∀ (m n : ℤ) (X : Finite),
      ⁅virasoro.Lmode m, affine.Current n X⁆ =
        (-(n : ℝ)) • affine.Current (m + n) X
  centralCharge_calibrated_field :
    centralCharge = level * finiteDimension / (level + dualCoxeterNumber)

namespace AffineVirasoroBridgeDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : AffineVirasoroBridgeDatum Finite Alg)

/-- Reparametrization law: `[L_m, J(n,X)] = -n J(m+n, X)`. -/
theorem virasoro_acts_on_currents (m n : ℤ) (X : Finite) :
    ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
      (-(n : ℝ)) • B.affine.Current (m + n) X := by
  exact B.virasoro_acts_on_currents_field m n X

/-- The bridge's central charge is the explicit Sugawara value. -/
theorem centralCharge_calibrated :
    B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber) := by
  exact B.centralCharge_calibrated_field

/-- Compatibility alias for legacy witness naming of the Sugawara law. -/
def sugawara_law : Prop :=
  B.centralCharge =
    B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)

/-- The Sugawara compatibility law is installed by the bridge calibration. -/
theorem sugawara_holds :
    B.sugawara_law := by
  simpa [sugawara_law] using B.centralCharge_calibrated

/-- Compatibility alias for legacy Virasoro/current witness naming. -/
def virasoro_acts_on_currents_law : Prop :=
  ∀ (m n : ℤ) (X : Finite),
    ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
      (-(n : ℝ)) • B.affine.Current (m + n) X

/-- Legacy witness-style projection for Virasoro/current compatibility. -/
theorem virasoro_acts_on_currents_law_holds :
    B.virasoro_acts_on_currents_law := by
  intro m n X
  exact B.virasoro_acts_on_currents m n X

end AffineVirasoroBridgeDatum

/-! ## 4. E8/E9-style calibration socket -/

/--
Exceptional affine-Virasoro calibration.

`E8(8)` finite symmetry
    → affine `E9(9)` current symmetry
    → Virasoro reparametrization/stress-tensor ledger.
-/
structure ExceptionalAffineVirasoroCalibration
    (Finite AffineAlg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg] where

  bridge :
    AffineVirasoroBridgeDatum Finite AffineAlg
  finite_dimension_eq_field : bridge.finiteDimension = 248
  dual_coxeter_eq_field : bridge.dualCoxeterNumber = 30
  level_eq_field : bridge.level = 1

namespace ExceptionalAffineVirasoroCalibration

variable
    {Finite AffineAlg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    (E : ExceptionalAffineVirasoroCalibration Finite AffineAlg)

/-- The finite algebra has dimension 248 (E₈ rank). -/
theorem finite_dimension_eq : E.bridge.finiteDimension = 248 := by
  exact E.finite_dimension_eq_field

/-- The dual Coxeter number is 30 (E₈). -/
theorem dual_coxeter_eq : E.bridge.dualCoxeterNumber = 30 := by
  exact E.dual_coxeter_eq_field

/-- The level is 1. -/
theorem level_eq : E.bridge.level = 1 := by
  exact E.level_eq_field

/--
The exceptional calibration enforces the E₈ Sugawara central charge `c = 8`.
-/
theorem centralCharge_eq_eight :
    E.bridge.centralCharge = 8 := by
  rw [E.bridge.centralCharge_calibrated,
      E.finite_dimension_eq, E.dual_coxeter_eq, E.level_eq]
  norm_num

end ExceptionalAffineVirasoroCalibration

/-! ## 5. Sugawara mode-sum construction datum -/

/--
Sugawara mode-sum construction datum.

Records the Sugawara operator identity at the mode level:

  `L_n = (1 / (2 (k + h∨))) ∑_{m,a} :J^a(m) J_a(n−m):`
-/
structure SugawaraModeConstructionDatum
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  bridge : AffineVirasoroBridgeDatum Finite Alg

  /-- Normal-ordered bilinear mode sum `∑_{m,a} :J^a(m) J_a(n−m):` in `Alg`. -/
  modeSum : ℤ → Alg
  virasoro_mode_eq_rescaled_sum_field :
    ∀ n : ℤ, bridge.virasoro.Lmode n = (1 / (2 * (bridge.level + bridge.dualCoxeterNumber))) • modeSum n

namespace SugawaraModeConstructionDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (S : SugawaraModeConstructionDatum Finite Alg)

/-- The Sugawara rescaling constant `1 / (2(k + h∨))`. -/
def sugawaraFactor : ℝ :=
  1 / (2 * (S.bridge.level + S.bridge.dualCoxeterNumber))

/--
Sugawara relation: `L_n = (1 / (2(k + h∨))) · modeSum n`.

This is the algebraic content of the Sugawara construction expressing
Virasoro generators as normal-ordered bilinear sums of affine current modes.
-/
theorem virasoro_mode_eq_rescaled_sum (n : ℤ) :
    S.bridge.virasoro.Lmode n = S.sugawaraFactor • S.modeSum n := by
  simpa [sugawaraFactor] using S.virasoro_mode_eq_rescaled_sum_field n

end SugawaraModeConstructionDatum

/-! ## 6. Modular-helical reparametrization datum -/

/--
Modular-helical reparametrization datum.

Encodes the Bisognano–Wichmann / Haag–Hugenholtz–Winnink identification:

  The modular automorphism group `σ^φ_t` acts as `exp(i t L₀)` on the
  Virasoro-reparametrized algebra, identifying the helical/modular spectral
  parameter `t` with the conformal cylinder parameter.
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
  modularFlow_zero_field : ∀ s : State, modularFlow 0 s = s
  modularFlow_add_field :
    ∀ (t₁ t₂ : ℝ) (s : State), modularFlow (t₁ + t₂) s = modularFlow t₁ (modularFlow t₂ s)
  L0Flow_zero_field : ∀ s : State, L0Flow 0 s = s
  modular_flow_is_L0_field : ∀ (t : ℝ) (s : State), modularFlow t s = L0Flow t s

namespace ModularHelicalCalibration

variable
    {Alg State : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State]

variable (M : ModularHelicalCalibration Alg State)

/-- Zero-time identity for the modular flow. -/
theorem modularFlow_zero (s : State) : M.modularFlow 0 s = s := by
  exact M.modularFlow_zero_field s

/-- Additive law for the modular flow. -/
theorem modularFlow_add (t₁ t₂ : ℝ) (s : State) :
    M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s) := by
  exact M.modularFlow_add_field t₁ t₂ s

/-- Zero-time identity for the L₀ flow. -/
theorem L0Flow_zero (s : State) : M.L0Flow 0 s = s := by
  exact M.L0Flow_zero_field s

/--
Bisognano–Wichmann / HHW identification:
the modular flow coincides with the L₀-generated helical flow.

`∀ t s, modularFlow t s = L0Flow t s`.
-/
theorem modular_flow_is_L0 (t : ℝ) (s : State) :
    M.modularFlow t s = M.L0Flow t s := by
  exact M.modular_flow_is_L0_field t s

/-- Legacy compatibility alias for helical-reparametrization witness naming. -/
def virasoro_is_helical_reparametrization : Prop :=
  ∀ (t : ℝ) (s : State), M.modularFlow t s = M.L0Flow t s

/--
The Virasoro/helical reparametrization law follows from modular-flow calibration.
-/
theorem virasoro_is_helical_reparametrization_holds :
    M.virasoro_is_helical_reparametrization :=
  M.modular_flow_is_L0

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
            symm
            exact M.modularFlow_add (-t) t s
    _ = M.modularFlow 0 s := by ring_nf
    _ = s := M.modularFlow_zero s

/-- Right inverse law for affine/helical symmetry flow. -/
theorem affine_symmetry_right_inverse (t : ℝ) (s : State) :
    M.modularFlow t (M.modularFlow (-t) s) = s := by
  calc
    M.modularFlow t (M.modularFlow (-t) s)
        = M.modularFlow (t + (-t)) s := by
            symm
            exact M.modularFlow_add t (-t) s
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

end InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
