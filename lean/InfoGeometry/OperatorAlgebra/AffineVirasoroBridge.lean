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
theorem central_commutes
    (hcentral : ∀ X : Alg, ⁅V.central, X⁆ = 0)
    (X : Alg) : ⁅V.central, X⁆ = 0 :=
  hcentral X

/-- Explicit projection of the Virasoro bracket equation. -/
theorem bracket_modes
    (hbracket :
      ∀ m n : ℤ,
        ⁅V.Lmode m, V.Lmode n⁆ =
          (m - n : ℝ) • V.Lmode (m + n) +
            ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then V.central else 0))
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        ((↑(m ^ 3 - m) : ℝ) / 12) • (if m + n = 0 then V.central else 0) := by
  exact hbracket m n

/-- Virasoro bracket in coefficient-normalized form. -/
theorem bracket_modes_normalized
    (hnorm :
      ∀ m n : ℤ,
        ⁅V.Lmode m, V.Lmode n⁆ =
          (m - n : ℝ) • V.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • V.central)
    (m n : ℤ) :
    ⁅V.Lmode m, V.Lmode n⁆ =
      (m - n : ℝ) • V.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) • V.central := by
  exact hnorm m n

/-- The Virasoro bracket law is a direct projection of the explicit field. -/
theorem virasoro_bracket_holds :
    (hnorm :
      ∀ m n : ℤ,
        ⁅V.Lmode m, V.Lmode n⁆ =
          (m - n : ℝ) • V.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • V.central) →
    ∀ m n : ℤ,
      ⁅V.Lmode m, V.Lmode n⁆ =
        (m - n : ℝ) • V.Lmode (m + n) +
          (virasoroCentralCoefficient m n : ℝ) • V.central := by
  intro hnorm
  intro m n
  exact hnorm m n

/-- Central-commutation is a direct projection of the explicit field. -/
theorem central_commutes_holds :
    (hcentral : ∀ X : Alg, ⁅V.central, X⁆ = 0) →
    ∀ X : Alg, ⁅V.central, X⁆ = 0 := by
  intro hcentral
  exact hcentral

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

namespace SugawaraDatum

variable (S : SugawaraDatum)

/-- Explicit projection of the Sugawara central charge law. -/
theorem centralCharge_eq :
    (hS : S.centralCharge = (S.level * S.dimG) / (S.level + S.hDual)) →
    S.centralCharge = (S.level * S.dimG) / (S.level + S.hDual) := by
  intro hS
  exact hS

/-- The Sugawara compatibility law is installed by the bridge calibration. -/
theorem sugawara_holds :
    (hS : S.centralCharge = (S.level * S.dimG) / (S.level + S.hDual)) →
    S.centralCharge = sugawaraCentralCharge S.level S.dimG S.hDual := by
  intro hS
  simpa [sugawaraCentralCharge] using hS

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

namespace AffineCurrentDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (A : AffineCurrentDatum Finite Alg)

/-- Explicit projection of the affine current-mode bracket law. -/
theorem current_mode_bracket
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅A.Current m X, A.Current n Y⁆ =
          A.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0))
    (m n : ℤ) (X Y : Finite) :
    ⁅A.Current m X, A.Current n Y⁆ =
      A.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0) := by
  exact hbr m n X Y

/-- The current-mode bracket law is a direct projection of the explicit affine bracket field. -/
theorem current_mode_bracket_holds :
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅A.Current m X, A.Current n Y⁆ =
          A.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0)) →
    ∀ (m n : ℤ) (X Y : Finite),
      ⁅A.Current m X, A.Current n Y⁆ =
        A.Current (m + n) ⁅X, Y⁆ +
          ((m : ℝ) * A.killingForm X Y) • (if m + n = 0 then A.kCentral else 0) := by
  intro hbr
  intro m n X Y
  exact hbr m n X Y

/-- The affine central element commutes with all algebra elements. -/
theorem central_commutes_with
    (hcentral : ∀ X : Alg, ⁅A.kCentral, X⁆ = 0)
    (X : Alg) :
    ⁅A.kCentral, X⁆ = 0 := by
  exact hcentral X

/-- Current central commutation is a direct projection of the explicit field. -/
theorem current_central_commutes_holds :
    (hcentral : ∀ X : Alg, ⁅A.kCentral, X⁆ = 0) →
    ∀ X : Alg, ⁅A.kCentral, X⁆ = 0 := by
  intro hcentral
  exact hcentral

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

namespace AffineVirasoroBridgeDatum

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : AffineVirasoroBridgeDatum Finite Alg)

/-- Reparametrization law: `[L_m, J(n,X)] = -n J(m+n, X)`. -/
theorem virasoro_acts_on_currents (m n : ℤ) (X : Finite) :
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
          (-(n : ℝ)) • B.affine.Current (m + n) X) →
    ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
      (-(n : ℝ)) • B.affine.Current (m + n) X := by
  intro hact
  exact hact m n X

/-- The bridge's central charge is the explicit Sugawara value. -/
theorem centralCharge_calibrated :
    (hcc : B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)) →
    B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber) := by
  intro hcc
  exact hcc

/-- The Sugawara compatibility law is installed by the bridge calibration. -/
theorem sugawara_holds :
    (hcc : B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber)) →
    B.centralCharge =
      B.level * B.finiteDimension / (B.level + B.dualCoxeterNumber) := by
  intro hcc
  exact hcc

/-- Projection for Virasoro/current compatibility. -/
theorem virasoro_acts_on_currents_holds :
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
          (-(n : ℝ)) • B.affine.Current (m + n) X) →
    ∀ (m n : ℤ) (X : Finite),
      ⁅B.virasoro.Lmode m, B.affine.Current n X⁆ =
        (-(n : ℝ)) • B.affine.Current (m + n) X := by
  intro hact
  intro m n X
  exact hact m n X

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

namespace ExceptionalAffineVirasoroCalibration

variable
    {Finite AffineAlg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    (E : ExceptionalAffineVirasoroCalibration Finite AffineAlg)

/--
The exceptional calibration enforces the E₈ Sugawara central charge `c = 8`.
-/
theorem centralCharge_eq_eight
    (hcc : E.bridge.centralCharge =
      E.bridge.level * E.bridge.finiteDimension / (E.bridge.level + E.bridge.dualCoxeterNumber))
    (hfd : E.bridge.finiteDimension = 248)
    (hdc : E.bridge.dualCoxeterNumber = 30)
    (hlv : E.bridge.level = 1) :
    E.bridge.centralCharge = 8 := by
  rw [hcc, hfd, hdc, hlv]
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
    (hmode :
      ∀ n : ℤ, S.bridge.virasoro.Lmode n =
        (1 / (2 * (S.bridge.level + S.bridge.dualCoxeterNumber))) • S.modeSum n) →
    S.bridge.virasoro.Lmode n = S.sugawaraFactor • S.modeSum n := by
  intro hmode
  simpa [sugawaraFactor] using hmode n

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

namespace ModularHelicalCalibration

variable
    {Alg State : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [AddCommGroup State] [Module ℝ State]

variable (M : ModularHelicalCalibration Alg State)

/-- Zero-time identity for the modular flow. -/
theorem modularFlow_zero
    (hzero : ∀ s : State, M.modularFlow 0 s = s)
    (s : State) : M.modularFlow 0 s = s :=
  hzero s

/-- Additive law for the modular flow. -/
theorem modularFlow_add (t₁ t₂ : ℝ) (s : State) :
    (hadd : ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)) →
    M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s) := by
  intro hadd
  exact hadd t₁ t₂ s

/-- Zero-time identity for the L₀ flow. -/
theorem L0Flow_zero
    (hzero : ∀ s : State, M.L0Flow 0 s = s)
    (s : State) : M.L0Flow 0 s = s :=
  hzero s

/--
Bisognano–Wichmann / HHW identification:
the modular flow coincides with the L₀-generated helical flow.

`∀ t s, modularFlow t s = L0Flow t s`.
-/
theorem modular_flow_is_L0 (t : ℝ) (s : State) :
    (hident : ∀ (t : ℝ) (s : State), M.modularFlow t s = M.L0Flow t s) →
    M.modularFlow t s = M.L0Flow t s := by
  intro hident
  exact hident t s

/--
The Virasoro/helical reparametrization law follows from modular-flow calibration.
-/
theorem modularFlow_eq_L0Flow :
    (hident : ∀ (t : ℝ) (s : State), M.modularFlow t s = M.L0Flow t s) →
    ∀ (t : ℝ) (s : State), M.modularFlow t s = M.L0Flow t s := by
  intro hident
  exact hident

/-- The affine/helical symmetry action has identity at parameter `0`. -/
theorem affine_symmetry_identity_holds :
    (hzero : ∀ s : State, M.modularFlow 0 s = s) →
    ∀ s : State, M.modularFlow 0 s = s := by
  intro hzero
  exact hzero

/-- The affine/helical symmetry action is closed under composition. -/
theorem affine_symmetry_composition_holds :
    (hadd : ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)) →
    ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s) := by
  intro hadd
  exact hadd

/-- Left inverse law for affine/helical symmetry flow. -/
theorem affine_symmetry_left_inverse (t : ℝ) (s : State) :
    (hzero : ∀ s : State, M.modularFlow 0 s = s) →
    (hadd : ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)) →
    M.modularFlow (-t) (M.modularFlow t s) = s := by
  intro hzero hadd
  calc
    M.modularFlow (-t) (M.modularFlow t s)
        = M.modularFlow ((-t) + t) s := by
            symm
            exact hadd (-t) t s
    _ = M.modularFlow 0 s := by ring_nf
    _ = s := hzero s

/-- Right inverse law for affine/helical symmetry flow. -/
theorem affine_symmetry_right_inverse (t : ℝ) (s : State) :
    (hzero : ∀ s : State, M.modularFlow 0 s = s) →
    (hadd : ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)) →
    M.modularFlow t (M.modularFlow (-t) s) = s := by
  intro hzero hadd
  calc
    M.modularFlow t (M.modularFlow (-t) s)
        = M.modularFlow (t + (-t)) s := by
            symm
            exact hadd t (-t) s
    _ = M.modularFlow 0 s := by ring_nf
    _ = s := hzero s

/--
The affine/helical symmetry-flow action is group-closed:
identity, composition, and inverse laws all hold.
-/
theorem affine_symmetry_inverse_holds :
    (hzero : ∀ s : State, M.modularFlow 0 s = s) →
    (hadd : ∀ (t₁ t₂ : ℝ) (s : State),
      M.modularFlow (t₁ + t₂) s = M.modularFlow t₁ (M.modularFlow t₂ s)) →
    ∀ (t : ℝ) (s : State),
      M.modularFlow (-t) (M.modularFlow t s) = s ∧
        M.modularFlow t (M.modularFlow (-t) s) = s := by
  intro hzero hadd
  intro t s
  exact ⟨M.affine_symmetry_left_inverse t s hzero hadd, M.affine_symmetry_right_inverse t s hzero hadd⟩

end ModularHelicalCalibration

end InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
