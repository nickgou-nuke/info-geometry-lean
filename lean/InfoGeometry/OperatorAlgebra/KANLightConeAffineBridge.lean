import InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge
import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
import InfoGeometry.OperatorAlgebra.WeylWeightBalance
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge

KAN-structured lightcone/affine socket.

This file fuses two existing owner surfaces:

* `NoncommutativeBogoliubovKANLift`, where KAN data are a representation/shadow
  readout of a doubled real Bogoliubov frame;
* `LightConeAffineCurrentBridge`, where selected lightcone directions are routed
  through the affine/Virasoro owner surface.

It does **not** prove a global Iwasawa theorem, does **not** assert that every
Drazin/Moore--Penrose mismatch is a KAN decomposition, and does **not** claim
that raw lightcone arrows are automatically Kac--Moody currents.  The affine
laws remain owned by `LightConeAffineCurrentBridge`; the KAN data remain a
shadow packet supplied by `NoncommutativeBogoliubovKANLift`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
open InfoGeometry.OperatorAlgebra.WeylWeightBalance

/--
KAN-organized lightcone affine bridge.

The `kanShadow` field supplies the compact/Cartan/nilpotent representation
shadow.  The `affineLightCone` field supplies the actual affine-current socket.
No equality or preservation law is bundled between them; the projections below
are the canonical readbacks used by later theorem-owner modules.
-/
@[rep_depth operator]
structure Bridge
    (E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- KAN/Bogoliubov representation shadow. -/
  kanShadow :
    BogoliubovKANShadowPacket E
      (Bog := Bog) (Korth := Korth) (Asplit := Asplit)
      (Nshear := Nshear) (CartanDiag := CartanDiag)

  /-- Lightcone directions routed through the affine/Virasoro owner socket. -/
  affineLightCone :
    LightConeAffineCurrentBridge Finite Alg

namespace Bridge

variable
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B :
  Bridge E Finite Alg Bog Korth Asplit Nshear CartanDiag)

/-! ## KAN projection readbacks -/

/-- Compact/metric `K` sector of the supplied KAN shadow. -/
@[rep_depth operator]
abbrev compactSector : Korth :=
  B.kanShadow.compactSector

/-- Abelian/Cartan/Weyl-scale `A` sector of the supplied KAN shadow. -/
@[rep_depth operator]
abbrev abelianScaleSector : Asplit :=
  B.kanShadow.cartanSector

/-- Nilpotent/shear `N` sector of the supplied KAN shadow. -/
@[rep_depth operator]
abbrev nilpotentSector : Nshear :=
  B.kanShadow.nilpotentSector

/-- Diagonal/Cartan readout remains a KAN shadow, not primitive owner data. -/
@[rep_depth operator]
abbrev diagonalShadow : CartanDiag :=
  B.kanShadow.diagonalShadow

/-- The KAN decomposition witness is whatever the supplied shadow packet carries. -/
@[rep_depth operator]
abbrev kanDecompositionWitness : Type* :=
  B.kanShadow.kanDecomposition

/-- Guard: diagonal data are only a representation/KAN shadow. -/
@[rep_depth operator]
abbrev diagonalIsOnlyShadow : Type* :=
  B.kanShadow.diagonalIsOnlyShadow

/-! ## Lightcone affine-current readbacks -/

/-- Positive lightcone root as routed through the affine-current socket. -/
@[rep_depth operator]
abbrev uPlusRoot : Finite :=
  B.affineLightCone.uPlusRoot

/-- Negative lightcone root as routed through the affine-current socket. -/
@[rep_depth operator]
abbrev uMinusRoot : Finite :=
  B.affineLightCone.uMinusRoot

/-- Positive lightcone affine current mode. -/
@[rep_depth operator]
def uPlusCurrent (n : ℤ) : Alg :=
  B.affineLightCone.uPlusCurrent n

/-- Negative lightcone affine current mode. -/
@[rep_depth operator]
def uMinusCurrent (n : ℤ) : Alg :=
  B.affineLightCone.uMinusCurrent n

/-- Positive current bracket law inherited from the lightcone affine owner. -/
@[rep_depth operator]
theorem uPlusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affineLightCone.affine.Current m X, B.affineLightCone.affine.Current n Y⁆ =
          B.affineLightCone.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affineLightCone.affine.killingForm X Y) •
              (if m + n = 0 then B.affineLightCone.affine.kCentral else 0)) :
    ⁅B.uPlusCurrent m, B.uPlusCurrent n⁆ =
      B.affineLightCone.affine.Current (m + n)
          ⁅B.affineLightCone.uPlusRoot, B.affineLightCone.uPlusRoot⁆ +
        ((m : ℝ) *
            B.affineLightCone.affine.killingForm
              B.affineLightCone.uPlusRoot B.affineLightCone.uPlusRoot) •
          (if m + n = 0 then B.affineLightCone.affine.kCentral else 0) := by
  unfold uPlusCurrent
  exact B.affineLightCone.uPlusCurrent_bracket m n hbr

/-- Negative current bracket law inherited from the lightcone affine owner. -/
@[rep_depth operator]
theorem uMinusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affineLightCone.affine.Current m X, B.affineLightCone.affine.Current n Y⁆ =
          B.affineLightCone.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affineLightCone.affine.killingForm X Y) •
              (if m + n = 0 then B.affineLightCone.affine.kCentral else 0)) :
    ⁅B.uMinusCurrent m, B.uMinusCurrent n⁆ =
      B.affineLightCone.affine.Current (m + n)
          ⁅B.affineLightCone.uMinusRoot, B.affineLightCone.uMinusRoot⁆ +
        ((m : ℝ) *
            B.affineLightCone.affine.killingForm
              B.affineLightCone.uMinusRoot B.affineLightCone.uMinusRoot) •
          (if m + n = 0 then B.affineLightCone.affine.kCentral else 0) := by
  unfold uMinusCurrent
  exact B.affineLightCone.uMinusCurrent_bracket m n hbr

/-- Mixed current bracket law inherited from the lightcone affine owner. -/
@[rep_depth operator]
theorem uPlus_uMinusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affineLightCone.affine.Current m X, B.affineLightCone.affine.Current n Y⁆ =
          B.affineLightCone.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affineLightCone.affine.killingForm X Y) •
              (if m + n = 0 then B.affineLightCone.affine.kCentral else 0)) :
    ⁅B.uPlusCurrent m, B.uMinusCurrent n⁆ =
      B.affineLightCone.affine.Current (m + n)
          ⁅B.affineLightCone.uPlusRoot, B.affineLightCone.uMinusRoot⁆ +
        ((m : ℝ) *
            B.affineLightCone.affine.killingForm
              B.affineLightCone.uPlusRoot B.affineLightCone.uMinusRoot) •
          (if m + n = 0 then B.affineLightCone.affine.kCentral else 0) := by
  unfold uPlusCurrent uMinusCurrent
  exact B.affineLightCone.uPlus_uMinusCurrent_bracket m n hbr

/-- Virasoro reparametrization of positive lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uPlusCurrent
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.affineLightCone.bridge.virasoro.Lmode m,
          B.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • B.affineLightCone.bridge.affine.Current (m + n) X) :
    ⁅B.affineLightCone.virasoro.Lmode m, B.uPlusCurrent n⁆ =
      (-(n : ℝ)) • B.uPlusCurrent (m + n) := by
  unfold uPlusCurrent
  exact B.affineLightCone.virasoro_acts_on_uPlusCurrent m n hact

/-- Virasoro reparametrization of negative lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uMinusCurrent
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.affineLightCone.bridge.virasoro.Lmode m,
          B.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • B.affineLightCone.bridge.affine.Current (m + n) X) :
    ⁅B.affineLightCone.virasoro.Lmode m, B.uMinusCurrent n⁆ =
      (-(n : ℝ)) • B.uMinusCurrent (m + n) := by
  unfold uMinusCurrent
  exact B.affineLightCone.virasoro_acts_on_uMinusCurrent m n hact

/-- Sugawara central-charge calibration inherited from the affine/Virasoro owner. -/
@[rep_depth operator]
theorem centralCharge_calibrated :
    (hcc : B.affineLightCone.bridge.centralCharge =
      B.affineLightCone.bridge.level * B.affineLightCone.bridge.finiteDimension /
        (B.affineLightCone.bridge.level + B.affineLightCone.bridge.dualCoxeterNumber)) →
    B.affineLightCone.bridge.centralCharge =
      B.affineLightCone.bridge.level * B.affineLightCone.bridge.finiteDimension /
        (B.affineLightCone.bridge.level + B.affineLightCone.bridge.dualCoxeterNumber) :=
  B.affineLightCone.centralCharge_calibrated

/-! ## Weight/mode balance interface -/

/--
The affine central selector is explicitly gated by mode balance.  This is the
mode-balance socket used by later Sugawara/Virasoro modules; no central term is
claimed away from `m+n=0`.
-/
@[rep_depth operator]
theorem centralSelector_eq_zero_of_not_modeBalanced
    {m n : ℤ}
    (hNot : ¬ IsModeBalanced m n) :
    (if m + n = 0 then B.affineLightCone.affine.kCentral else 0) = 0 := by
  unfold IsModeBalanced at hNot
  simp [hNot]

end Bridge

end InfoGeometry.OperatorAlgebra.KANLightConeAffineBridge
