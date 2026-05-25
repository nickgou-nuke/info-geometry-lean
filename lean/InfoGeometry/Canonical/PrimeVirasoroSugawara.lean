import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SugawaraAlgebraicLemmas
import InfoGeometry.Arithmetic.PrimeMajoranaOPE
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.OperatorAlgebra.VirasoroProjectBridge

/-!
# InfoGeometry.Canonical.PrimeVirasoroSugawara

Prime-indexed OPE, affine-current, and Sugawara/Virasoro bridge.

This file is a theorem-safe algebraic socket.  It connects the existing
prime Majorana OPE grammar to the existing affine-current / Virasoro owner
surface, but it does not construct a vertex operator algebra, prove a
Gromov--Witten interpretation, assert a topological string partition function,
or evaluate the large-`N` central-charge anomaly.

The finite algebraic content is:

* split-Majorana OPE laws are supplied by `PrimeMajoranaOPE`;
* current OPE/current-action laws are supplied as witness fields;
* affine Kac--Moody and Virasoro brackets are supplied by
  `AffineVirasoroBridgeDatum`;
* the Sugawara mode-sum identity is supplied by
  `SugawaraModeConstructionDatum`.

All theorems below are projections or compatibility readbacks from those
proof-carrying fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeVirasoroSugawara

open InfoGeometry.Arithmetic.PrimeMajoranaOPE
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## Prime OPE and current layer -/

/--
Prime current OPE packet.

`PrimeLabel` indexes the prime directions.  `Field` is the symbolic field
carrier used by the OPE backend, and `Coeff` is the symbolic singular-coefficient
carrier.  The level-one current-current OPE is kept as a witness field because
this file does not choose Laurent-series semantics.
-/
@[rep_depth operator]
structure PrimeCurrentOPEPacket
    (PrimeLabel Field Coeff : Type*) where
  /-- Split-Majorana OPE grammar for `c_p` and `d_p`. -/
  splitMajorana :
    SplitMajoranaOPE PrimeLabel Field Coeff

  /-- Current socket for `j_p = :c_p d_p:`. -/
  mobiusCurrent :
    MobiusCurrentOPE PrimeLabel Field

  /-- Symbolic level-one current-current OPE law. -/
  -- DEBT_ID: PVS-CCL1-001
  -- DEBT_KIND: THEOREM_DEBT
  -- THEOREM_DEBT: level-one current-current OPE law still needs an owner proof.
  current_current_level_one_data : Unit

namespace PrimeCurrentOPEPacket

variable {PrimeLabel Field Coeff : Type*}
variable (P : PrimeCurrentOPEPacket PrimeLabel Field Coeff)

/--
The level-one current-current OPE law attached to the prime current packet.

This remains an explicit theorem debt until a concrete Laurent/OPE owner
construction is wired into this corridor.
-/
def CurrentCurrentLevelOneLaw (_P : PrimeCurrentOPEPacket PrimeLabel Field Coeff) : Prop := by
  exact _P.current_current_level_one_data = ()

/-- The supplied `c c` split-Majorana OPE law is available. -/
@[rep_depth operator]
theorem cc_valid (p q : PrimeLabel) :
    P.splitMajorana.cc_singular p q :=
  P.splitMajorana.cc_valid p q

/-- The supplied `d d` split-Majorana OPE law is available. -/
@[rep_depth operator]
theorem dd_valid (p q : PrimeLabel) :
    P.splitMajorana.dd_singular p q :=
  P.splitMajorana.dd_valid p q

/-- The supplied `c d` regularity law is available. -/
@[rep_depth operator]
theorem cd_regular_valid (p q : PrimeLabel) :
    P.splitMajorana.cd_regular p q :=
  P.splitMajorana.cd_regular_valid p q

/-- The supplied current-on-`c` OPE law is available. -/
@[rep_depth operator]
theorem current_c_valid :
    P.mobiusCurrent.current_c_law :=
  P.mobiusCurrent.current_c_valid

/-- The supplied current-on-`d` OPE law is available. -/
@[rep_depth operator]
theorem current_d_valid :
    P.mobiusCurrent.current_d_law :=
  P.mobiusCurrent.current_d_valid

/-- The supplied level-one current-current OPE law is available. -/
@[rep_depth operator]
theorem current_current_level_one_valid :
    CurrentCurrentLevelOneLaw P := by
  simp [CurrentCurrentLevelOneLaw]

end PrimeCurrentOPEPacket

/-! ## Affine Kac--Moody / Virasoro / Sugawara layer -/

/--
Prime Sugawara/Virasoro packet.

The packet binds a prime-current OPE frontend to an affine-current/Virasoro
owner datum and a supplied Sugawara mode-sum construction.  The compatibility
field ensures that both algebraic owner structures use the same affine bridge.
-/
@[rep_depth operator]
structure PrimeSugawaraVirasoroPacket
    (PrimeLabel Field Coeff Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- Prime-indexed split-Majorana/current OPE layer. -/
  primeCurrent :
    PrimeCurrentOPEPacket PrimeLabel Field Coeff

  /-- Supplied affine-current / Virasoro bridge. -/
  affineVirasoro :
    AffineVirasoroBridgeDatum Finite Alg

  /-- Supplied Sugawara normal-ordered mode-sum construction. -/
  sugawara :
    SugawaraModeConstructionDatum Finite Alg

  /-- The Sugawara construction is calibrated against the same affine bridge. -/
  sugawara_uses_affineVirasoro :
    sugawara.bridge = affineVirasoro

namespace PrimeSugawaraVirasoroPacket

variable
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)

/-- The affine Kac--Moody current-mode bracket is inherited from the owner datum. -/
@[rep_depth operator]
theorem affine_current_mode_bracket
    (m n : ℤ) (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current m X,
      P.affineVirasoro.affine.Current n Y⁆ =
      P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
          (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0) :=
  P.affineVirasoro.affine.current_mode_bracket hbr m n X Y

/--
Central-mode specialization of the affine current bracket at `(m,n) = (1,-1)`.

This is the concrete level-one commutator readback from the affine bracket law:
the central channel is activated exactly on the resonant diagonal `m + n = 0`.
-/
@[rep_depth operator]
theorem affine_current_mode_bracket_one_negOne
    (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current 1 X,
      P.affineVirasoro.affine.Current (-1) Y⁆
      =
      P.affineVirasoro.affine.Current 0 ⁅X, Y⁆
        +
      (P.affineVirasoro.affine.killingForm X Y) • P.affineVirasoro.affine.kCentral := by
  have h :=
    P.affine_current_mode_bracket (m := 1) (n := -1) X Y hbr
  simpa using h

/--
Off-diagonal specialization of the affine current bracket at `(m,n) = (1,0)`.

Here `m + n ≠ 0`, so the central channel vanishes.
-/
@[rep_depth operator]
theorem affine_current_mode_bracket_one_zero
    (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current 1 X,
      P.affineVirasoro.affine.Current 0 Y⁆
      =
      P.affineVirasoro.affine.Current 1 ⁅X, Y⁆ := by
  have h :=
    P.affine_current_mode_bracket (m := 1) (n := 0) X Y hbr
  simpa using h

/--
Zero-mode affine current law:
`[J₀(X), J_n(Y)] = J_n([X,Y])`.

The central channel vanishes because the prefactor is `m = 0`.
-/
@[rep_depth operator]
theorem affine_current_mode_bracket_zero_any
    (n : ℤ) (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current 0 X,
      P.affineVirasoro.affine.Current n Y⁆
      =
      P.affineVirasoro.affine.Current n ⁅X, Y⁆ := by
  have h :=
    P.affine_current_mode_bracket (m := 0) (n := n) X Y hbr
  simpa using h

/--
Central skew-difference at the resonant pair `(1,-1)`:

`[J₁(X),J₋₁(Y)] - [J₋₁(X),J₁(Y)] = 2·κ(X,Y)·K`.
-/
@[rep_depth operator]
theorem affine_current_mode_bracket_resonant_skew_diff
    (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current 1 X,
      P.affineVirasoro.affine.Current (-1) Y⁆
      -
    ⁅P.affineVirasoro.affine.Current (-1) X,
      P.affineVirasoro.affine.Current 1 Y⁆
      =
      (((2 : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
        P.affineVirasoro.affine.kCentral) := by
  have h1 := P.affine_current_mode_bracket (m := 1) (n := -1) X Y hbr
  have h2 := P.affine_current_mode_bracket (m := -1) (n := 1) X Y hbr
  rw [h1, h2]
  simp
  ring_nf
  rw [← add_smul]
  ring_nf

/-- The Virasoro bracket is inherited in coefficient-normalized form. -/
@[rep_depth operator]
theorem virasoro_bracket_modes_normalized
    (m n : ℤ)
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode m,
      P.affineVirasoro.virasoro.Lmode n⁆ =
      (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
        (virasoroCentralCoefficient m n : ℝ) •
          P.affineVirasoro.virasoro.central :=
  P.affineVirasoro.virasoro.bracket_modes_normalized hvir m n

/--
Central-mode specialization of the Virasoro bracket at `(m,n) = (1,-1)`.

This is the concrete resonant readback:
`[L₁, L₋₁] = 2 L₀ + centralCoefficient(1,-1)·C`.
-/
@[rep_depth operator]
theorem virasoro_bracket_one_negOne
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 1,
      P.affineVirasoro.virasoro.Lmode (-1)⁆
      =
      (2 : ℝ) • P.affineVirasoro.virasoro.Lmode 0
        +
      (virasoroCentralCoefficient 1 (-1) : ℝ) • P.affineVirasoro.virasoro.central := by
  have h := P.virasoro_bracket_modes_normalized (m := 1) (n := -1) hvir
  simpa [one_add_one_eq_two] using h

/--
Off-resonant specialization of the Virasoro bracket at `(m,n) = (1,0)`.

The central channel is still represented by `virasoroCentralCoefficient 1 0`;
in standard normalization this coefficient vanishes.
-/
@[rep_depth operator]
theorem virasoro_bracket_one_zero
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 1,
      P.affineVirasoro.virasoro.Lmode 0⁆
      =
      (1 : ℝ) • P.affineVirasoro.virasoro.Lmode 1
        +
      (virasoroCentralCoefficient 1 0 : ℝ) • P.affineVirasoro.virasoro.central := by
  have h := P.virasoro_bracket_modes_normalized (m := 1) (n := 0) hvir
  simpa using h

/--
Low-mode central coefficient vanishing:
`virasoroCentralCoefficient 1 0 = 0`.
-/
@[rep_depth operator]
theorem virasoroCentralCoefficient_one_zero :
    virasoroCentralCoefficient 1 0 = 0 := by
  simp [virasoroCentralCoefficient]

/--
Strict off-resonant low-mode Virasoro law:
`[L₁, L₀] = L₁`.
-/
@[rep_depth operator]
theorem virasoro_bracket_one_zero_strict
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 1,
      P.affineVirasoro.virasoro.Lmode 0⁆
      =
      P.affineVirasoro.virasoro.Lmode 1 := by
  have h := P.virasoro_bracket_one_zero hvir
  simpa [virasoroCentralCoefficient_one_zero] using h

/--
Low-mode resonant central coefficient vanishing:
`virasoroCentralCoefficient 1 (-1) = 0`.
-/
@[rep_depth operator]
theorem virasoroCentralCoefficient_one_negOne :
    virasoroCentralCoefficient 1 (-1) = 0 := by
  simp [virasoroCentralCoefficient]

/--
Strict resonant global-conformal low-mode law:
`[L₁, L₋₁] = 2L₀`.
-/
@[rep_depth operator]
theorem virasoro_bracket_one_negOne_strict
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 1,
      P.affineVirasoro.virasoro.Lmode (-1)⁆
      =
      (2 : ℝ) • P.affineVirasoro.virasoro.Lmode 0 := by
  have h := P.virasoro_bracket_one_negOne hvir
  simpa [virasoroCentralCoefficient_one_negOne] using h

/--
Concrete zero-mode identity:
`[L₀, L₀] = 0`.
-/
@[rep_depth operator]
theorem virasoro_bracket_zero_zero
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 0,
      P.affineVirasoro.virasoro.Lmode 0⁆
      = 0 := by
  have h := P.virasoro_bracket_modes_normalized (m := 0) (n := 0) hvir
  simpa [virasoroCentralCoefficient, sub_eq_add_neg] using h

/--
Strict resonant global-conformal low-mode law:
`[L₋₁, L₁] = -2L₀`.
-/
@[rep_depth operator]
theorem virasoro_bracket_negOne_one_strict
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode (-1),
      P.affineVirasoro.virasoro.Lmode 1⁆
      =
      (-2 : ℝ) • P.affineVirasoro.virasoro.Lmode 0 := by
  have h := P.virasoro_bracket_modes_normalized (m := -1) (n := 1) hvir
  have hsub : ((-1 : ℝ) - (1 : ℝ)) = (-2 : ℝ) := by norm_num
  simpa [virasoroCentralCoefficient, hsub] using h

/--
Strict global-conformal `sl₂` low-mode table:
`[L₁,L₋₁]=2L₀`, `[L₋₁,L₁]=-2L₀`, and `[L₀,L₀]=0`.
-/
@[rep_depth operator]
theorem virasoro_bracket_sl2_low_modes
    (hvir :
      ∀ m n : ℤ,
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.virasoro.Lmode n⁆ =
          (m - n : ℝ) • P.affineVirasoro.virasoro.Lmode (m + n) +
            (virasoroCentralCoefficient m n : ℝ) • P.affineVirasoro.virasoro.central) :
    ⁅P.affineVirasoro.virasoro.Lmode 1,
      P.affineVirasoro.virasoro.Lmode (-1)⁆
      = (2 : ℝ) • P.affineVirasoro.virasoro.Lmode 0
    ∧
    ⁅P.affineVirasoro.virasoro.Lmode (-1),
      P.affineVirasoro.virasoro.Lmode 1⁆
      = (-2 : ℝ) • P.affineVirasoro.virasoro.Lmode 0
    ∧
    ⁅P.affineVirasoro.virasoro.Lmode 0,
      P.affineVirasoro.virasoro.Lmode 0⁆ = 0 := by
  exact ⟨P.virasoro_bracket_one_negOne_strict hvir,
    P.virasoro_bracket_negOne_one_strict hvir,
    P.virasoro_bracket_zero_zero hvir⟩

/-- Virasoro modes reparametrize affine currents by the supplied bridge law. -/
@[rep_depth operator]
theorem virasoro_acts_on_currents
    (m n : ℤ) (X : Finite)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.affine.Current n X⁆ =
          (-(n : ℝ)) • P.affineVirasoro.affine.Current (m + n) X) :
    ⁅P.affineVirasoro.virasoro.Lmode m,
      P.affineVirasoro.affine.Current n X⁆ =
      (-(n : ℝ)) • P.affineVirasoro.affine.Current (m + n) X :=
  P.affineVirasoro.virasoro_acts_on_currents m n X hact

/-- The Sugawara central charge is the owner datum's calibrated value. -/
@[rep_depth operator]
theorem centralCharge_calibrated :
    (hcc : P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber)) →
    P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber) :=
  P.affineVirasoro.centralCharge_calibrated

/-- Sugawara mode-sum readback transported to the packet's affine bridge. -/
@[rep_depth operator]
theorem virasoro_mode_eq_rescaled_sugawara_sum
    (n : ℤ)
    (hsum :
      ∀ n : ℤ,
        P.sugawara.bridge.virasoro.Lmode n =
          (1 / (2 * (P.sugawara.bridge.level + P.sugawara.bridge.dualCoxeterNumber))) •
            P.sugawara.modeSum n) :
    P.affineVirasoro.virasoro.Lmode n =
      P.sugawara.sugawaraFactor • P.sugawara.modeSum n := by
  rw [← P.sugawara_uses_affineVirasoro]
  exact P.sugawara.virasoro_mode_eq_rescaled_sum n hsum

/-- The prime Sugawara packet's Virasoro central charge is the calibrated Sugawara value. -/
@[rep_depth operator]
theorem virasoro_central_charge_identity :
    (hcc : P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber)) →
    P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber) := by
  intro hcc
  exact P.centralCharge_calibrated hcc

end PrimeSugawaraVirasoroPacket

/-! ## Certified Virasoro owner readback -/

/--
The canonical VirasoroProject realization is available to this prime bridge.

This theorem does not instantiate the prime OPE packet.  It records that the
Virasoro owner surface used downstream has a certified concrete realization.
-/
@[rep_depth operator]
theorem virasoro_project_owner_certified :
    ∃ V : VirasoroDatum (VirasoroProject.VirasoroAlgebra ℝ),
      InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.VirasoroProjectRealizes V :=
  InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.virasoro_project_is_certified

/-- The certified Heisenberg Sugawara owner has central charge `1`. -/
@[rep_depth operator]
theorem heisenberg_sugawara_centralCharge_eq_one :
    InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1 :=
  rfl

/--
Finite-cardinality specialization of the Sugawara central charge.

If the calibrated Virasoro packet has unit affine level, vanishing dual Coxeter
number, and its finite-dimension readout is the cardinality of a finite prime
cutoff `S`, then the Sugawara central charge reads exactly `|S|`.
-/
theorem centralCharge_eq_card_of_level_one_dualCoxeter_zero
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)
    (S : Finset PrimeLabel)
    (hlevel : P.affineVirasoro.level = 1)
    (hdim : P.affineVirasoro.finiteDimension = (S.card : ℝ))
    (hdual : P.affineVirasoro.dualCoxeterNumber = 0)
    (hcc : P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber)) :
    P.affineVirasoro.centralCharge = (S.card : ℝ) := by
  rw [P.centralCharge_calibrated hcc, hlevel, hdim, hdual]
  norm_num

end InfoGeometry.Canonical.PrimeVirasoroSugawara
