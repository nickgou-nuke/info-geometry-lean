import Mathlib

/-!
# Split Majorana OPE bridge (witness-gated)

This module records a conservative Lean surface for the split-Majorana lane:

- finite-mode split Clifford/CAR witness data,
- local parity and global chirality witness data,
- chiral OPE witness data,
- finite Dirichlet/Witten character and Pfaffian readout packets.

It is deliberately witness-based: no RH/zero-location theorem is claimed here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebraic.SplitMajoranaOPEBridge

/--
Finite split-Majorana algebra packet over a mode index.

All algebraic equalities are exposed as witness fields so this remains model-agnostic.
-/
structure SplitMajoranaAlgebraPacket (Mode Operator : Type*) where
  c : Mode → Operator
  d : Mode → Operator
  epsilon : Mode → Operator
  iota : Mode → Operator
  numberOp : Mode → Operator
  localParity : Mode → Operator
  globalChirality : Operator

  anti_iota_epsilon : Mode → Mode → Prop
  anti_epsilon_epsilon : Mode → Mode → Prop
  anti_iota_iota : Mode → Mode → Prop
  anti_iota_epsilon_witness : ∀ p q : Mode, anti_iota_epsilon p q
  anti_epsilon_epsilon_witness : ∀ p q : Mode, anti_epsilon_epsilon p q
  anti_iota_iota_witness : ∀ p q : Mode, anti_iota_iota p q

  split_clifford_cc : Mode → Mode → Prop
  split_clifford_dd : Mode → Mode → Prop
  split_clifford_cd : Mode → Mode → Prop
  split_clifford_cc_witness : ∀ p q : Mode, split_clifford_cc p q
  split_clifford_dd_witness : ∀ p q : Mode, split_clifford_dd p q
  split_clifford_cd_witness : ∀ p q : Mode, split_clifford_cd p q

  localParity_eq_cd : Mode → Prop
  localParity_eq_cd_witness : ∀ p : Mode, localParity_eq_cd p
  localParity_eq_one_sub_twoN : Mode → Prop
  localParity_eq_one_sub_twoN_witness : ∀ p : Mode, localParity_eq_one_sub_twoN p
  globalChirality_eq_mobius_on_squareFree : Prop
  globalChirality_eq_mobius_on_squareFree_witness :
    globalChirality_eq_mobius_on_squareFree

/-- Re-export: local parity satisfies the declared `c·d` channel law. -/
theorem localParity_cd_channel
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator)
    (p : Mode) :
    P.localParity_eq_cd p :=
  P.localParity_eq_cd_witness p

/-- Re-export: split positive Majoranas satisfy the declared `cc` channel. -/
theorem split_clifford_cc_channel
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator)
    (p q : Mode) :
    P.split_clifford_cc p q :=
  P.split_clifford_cc_witness p q

/-- Re-export: split negative Majoranas satisfy the declared `dd` channel. -/
theorem split_clifford_dd_channel
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator)
    (p q : Mode) :
    P.split_clifford_dd p q :=
  P.split_clifford_dd_witness p q

/-- Re-export: the split `c` and `d` systems are mutually regular/orthogonal. -/
theorem split_clifford_cd_channel
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator)
    (p q : Mode) :
    P.split_clifford_cd p q :=
  P.split_clifford_cd_witness p q

/-- Re-export: local parity is the declared `1 - 2N` channel. -/
theorem localParity_one_sub_twoN_channel
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator)
    (p : Mode) :
    P.localParity_eq_one_sub_twoN p :=
  P.localParity_eq_one_sub_twoN_witness p

/-- Re-export: global chirality is square-free Möbius parity by packet witness. -/
theorem globalChirality_mobius_on_squareFree
    {Mode Operator : Type*}
    (P : SplitMajoranaAlgebraPacket Mode Operator) :
    P.globalChirality_eq_mobius_on_squareFree :=
  P.globalChirality_eq_mobius_on_squareFree_witness

/--
Split-Majorana chiral OPE packet.

This socket stores only the OPE calibration laws required downstream.
-/
structure SplitMajoranaOPEPacket (Mode Field : Type*) where
  cField : Mode → Field
  dField : Mode → Field
  jField : Mode → Field

  ope_cc : Mode → Mode → Prop
  ope_dd : Mode → Mode → Prop
  ope_cd_regular : Mode → Mode → Prop
  ope_cc_witness : ∀ p q : Mode, ope_cc p q
  ope_dd_witness : ∀ p q : Mode, ope_dd p q
  ope_cd_regular_witness : ∀ p q : Mode, ope_cd_regular p q

  j_on_c : Mode → Mode → Prop
  j_on_d : Mode → Mode → Prop
  j_on_c_witness : ∀ p q : Mode, j_on_c p q
  j_on_d_witness : ∀ p q : Mode, j_on_d p q

/-- Re-export: the mixed OPE channel is regular by packet witness. -/
theorem mixed_ope_regular
    {Mode Field : Type*}
    (P : SplitMajoranaOPEPacket Mode Field)
    (p q : Mode) :
    P.ope_cd_regular p q :=
  P.ope_cd_regular_witness p q

/-- Re-export: the `c_p(z)c_q(w)` singular OPE has the supplied split sign. -/
theorem cc_ope_channel
    {Mode Field : Type*}
    (P : SplitMajoranaOPEPacket Mode Field)
    (p q : Mode) :
    P.ope_cc p q :=
  P.ope_cc_witness p q

/-- Re-export: the `d_p(z)d_q(w)` singular OPE has the supplied negative split sign. -/
theorem dd_ope_channel
    {Mode Field : Type*}
    (P : SplitMajoranaOPEPacket Mode Field)
    (p q : Mode) :
    P.ope_dd p q :=
  P.ope_dd_witness p q

/-- Re-export: the local current sends `c` to the `d` channel. -/
theorem current_on_c_channel
    {Mode Field : Type*}
    (P : SplitMajoranaOPEPacket Mode Field)
    (p q : Mode) :
    P.j_on_c p q :=
  P.j_on_c_witness p q

/-- Re-export: the local current sends `d` to the negative `c` channel. -/
theorem current_on_d_channel
    {Mode Field : Type*}
    (P : SplitMajoranaOPEPacket Mode Field)
    (p q : Mode) :
    P.j_on_d p q :=
  P.j_on_d_witness p q

/-! ## Optional Euclidean lift through a real complex structure -/

/--
Optional lift from split-Majoranas to Euclidean Majoranas.

Without this packet the real form remains split, `Cl(n,n)`.  Supplying a real
complex structure `J` with `J² = -1` allows a model to treat `J d_p` as the
second Euclidean Majorana component.
-/
structure EuclideanMajoranaLiftPacket (Mode Operator : Type*) where
  split : SplitMajoranaAlgebraPacket Mode Operator
  complexStructure : Operator
  gammaOne : Mode → Operator
  gammaTwo : Mode → Operator
  complexStructure_sq_neg_one : Prop
  complexStructure_sq_neg_one_witness : complexStructure_sq_neg_one
  gammaOne_eq_c : ∀ p : Mode, gammaOne p = split.c p
  gammaTwo_eq_Jd : Mode → Prop
  gammaTwo_eq_Jd_witness : ∀ p : Mode, gammaTwo_eq_Jd p
  euclidean_clifford_law : Mode → Mode → Prop
  euclidean_clifford_witness : ∀ p q : Mode, euclidean_clifford_law p q

namespace EuclideanMajoranaLiftPacket

/-- Re-export: the real complex structure squares to `-1` in the supplied model. -/
theorem complexStructure_sq_neg_one_valid
    {Mode Operator : Type*}
    (P : EuclideanMajoranaLiftPacket Mode Operator) :
    P.complexStructure_sq_neg_one :=
  P.complexStructure_sq_neg_one_witness

/-- Re-export: the first Euclidean Majorana is the split `c` component. -/
theorem gammaOne_eq_split_c
    {Mode Operator : Type*}
    (P : EuclideanMajoranaLiftPacket Mode Operator)
    (p : Mode) :
    P.gammaOne p = P.split.c p :=
  P.gammaOne_eq_c p

/-- Re-export: the second Euclidean Majorana is the supplied `J d` component. -/
theorem gammaTwo_eq_complex_d
    {Mode Operator : Type*}
    (P : EuclideanMajoranaLiftPacket Mode Operator)
    (p : Mode) :
    P.gammaTwo_eq_Jd p :=
  P.gammaTwo_eq_Jd_witness p

/-- Re-export: the Euclidean Clifford law after the supplied lift. -/
theorem euclidean_clifford
    {Mode Operator : Type*}
    (P : EuclideanMajoranaLiftPacket Mode Operator)
    (p q : Mode) :
    P.euclidean_clifford_law p q :=
  P.euclidean_clifford_witness p q

end EuclideanMajoranaLiftPacket

/--
Finite Dirichlet/Witten character packet at spectral parameter `s`.

`character` is the finite product readout and may be interpreted as a finite
cutoff index/character.
-/
structure FiniteDirichletWittenCharacterPacket
    (Mode : Type*) [Fintype Mode] where
  s : ℝ
  primeWeight : Mode → ℕ
  localFactor : Mode → ℝ
  character : ℝ

  localFactor_eq_one_sub_prime_rpow_neg :
    ∀ p : Mode, localFactor p = 1 - Real.rpow (primeWeight p : ℝ) (-s)
  character_eq_prod_localFactor :
    character = ∏ p : Mode, localFactor p

namespace FiniteDirichletWittenCharacterPacket

/-- Re-export of the finite Euler-factor witness. -/
theorem localFactor_formula
    {Mode : Type*} [Fintype Mode]
    (P : FiniteDirichletWittenCharacterPacket Mode)
    (p : Mode) :
    P.localFactor p = 1 - Real.rpow (P.primeWeight p : ℝ) (-P.s) :=
  P.localFactor_eq_one_sub_prime_rpow_neg p

/-- Re-export of the finite character product witness. -/
theorem character_prod_formula
    {Mode : Type*} [Fintype Mode]
    (P : FiniteDirichletWittenCharacterPacket Mode) :
    P.character = ∏ p : Mode, P.localFactor p :=
  P.character_eq_prod_localFactor

end FiniteDirichletWittenCharacterPacket

/--
Pfaffian-character bridge packet at finite cutoff.

This keeps the finite identity `Pfaffian = character` witness-gated.
-/
structure FinitePfaffianCharacterBridgePacket
    (Mode : Type*) [Fintype Mode] where
  characterPacket : FiniteDirichletWittenCharacterPacket Mode
  pfaffianReadout : ℝ
  pfaffian_eq_character : pfaffianReadout = characterPacket.character

/-- Re-export of the finite Pfaffian/character bridge witness. -/
theorem pfaffian_eq_character_readout
    {Mode : Type*} [Fintype Mode]
    (P : FinitePfaffianCharacterBridgePacket Mode) :
    P.pfaffianReadout = P.characterPacket.character :=
  P.pfaffian_eq_character

end InfoGeometry.Algebraic.SplitMajoranaOPEBridge
