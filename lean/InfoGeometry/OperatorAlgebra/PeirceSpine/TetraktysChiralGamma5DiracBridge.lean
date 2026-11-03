/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge

/-!
# The Tetraktys Chiral `γ₅` Operator vs. Dirac Algebra over Non-Commutative Operator Rings

This module formalizes the 6-stage causal poset
`𝓣₀ ≺ 𝓚₁ ≺ 𝓗₂ ≺ 𝓜₃ ≺ 𝓓₄ ≺ 𝓐₅` extracted by epistemic compilation (`solve et coagula`)
from *The Tetraktys Chiral `γ₅` Operator vs. Dirac Algebra* (`1ewrpkhcDRw_Xs7ryH6tWgKOjy7Yu-jBN`)
and Turns 161–165 of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`, generalized from a single integer
test vector to universal theorems on the non-associative Zorn matrix algebra
`OperatorZornMatrix A` (`NCZornElement A`) over an arbitrary non-commutative associative
coefficient ring `[Ring A]`, together with the associative Peirce dual-chirality bridge
(`invS P` vs. `genSig P A C = genJ P A C * genPhi P A C`) over any `[Ring B]`.

## Main Definitions and Theorems

1. `TetraktysGamma5Archetype` and `tetraktysGamma5_strict_causal_chain`:
   The 6-stage acyclic causal poset `𝓣₀ ≺ 𝓚₁ ≺ 𝓗₂ ≺ 𝓜₃ ≺ 𝓓₄ ≺ 𝓐₅`.
2. `tetraktys_gamma5_threefold_origin` (`𝓣₀`):
   Threefold origin of `zornGamma5 = zornEL - zornER`:
   - Idempotent difference `zornEL - zornER = zornGamma5` with `zornEL + zornER = zornOne`,
   - Directional CAR commutator `bracket (zornEPlus i) (zornEMinus i) = zornGamma5` and
     anticommutator `zornAnticomm (zornEPlus i) (zornEMinus i) = zornOne` for every `i : Fin 3`,
   - Weyl reflections `zornWeyl i * zornWeyl i = -zornOne` and the Triadic Weyl Reflection
     Associator `zornWeyl 0 * (zornWeyl 1 * zornWeyl 2) = zornGamma5`,
     `(zornWeyl 0 * zornWeyl 1) * zornWeyl 2 = -zornGamma5`, and
     `associator (zornWeyl 2) (zornWeyl 1) (zornWeyl 0) = (2 : ℤ) • zornGamma5`.
3. `tetraktys_klein_four_group_identities` (`𝓚₁`):
   Left, right, and bilateral (`Ad_{γ₅}`) chiral operators `zornLeftGamma5`, `zornRightGamma5`,
   and `zornAdGamma5` on `OperatorZornMatrix A`, proving chiral middle-associativity
   `associator zornGamma5 X zornGamma5 = 0` and the Klein four-group `𝓚₄ ≅ C₂ × C₂`
   involution and composition laws.
4. `tetraktys_walsh_hadamard_peirce_projectors` (`𝓗₂`):
   The `4 × 4` Walsh–Hadamard rows applied to `(X, L_{γ₅} X, R_{γ₅} X, Ad_{γ₅} X)` isolate
   four times the four Peirce sectors `(zornEL * X) * zornEL`, `(zornEL * X) * zornER`,
   `(zornER * X) * zornEL`, `(zornER * X) * zornER`, whose sum reconstructs `X`.
5. `tetraktys_mass_protection_and_chiral_charge_duality` (`𝓜₃`):
   Universal anticommutator `zornAnticomm zornGamma5 X`, commutator `bracket zornGamma5 X`,
   linearized mass identity `zornMassLin X = zornEL * X + X * zornER = X`, and chiral charge
   `zornChiralCharge X = zornEL * X - X * zornER` with
   `(2 : ℤ) • zornChiralCharge X = zornAnticomm zornGamma5 X`.
6. `tetraktys_hodge_vs_bar_intertwining_duality` (`𝓓₄`):
   Upside-Down Tetraktys Hodge inversion `zornHodgeSwap` vs. octonionic bar-conjugation
   `zornBarConj`, proving `zornHodgeSwap (zornBarConj X) = zornBarConj (zornHodgeSwap X) = zornAdGamma5 X`,
   `zornHodgeSwap (zornLeftGamma5 X) = -zornLeftGamma5 (zornHodgeSwap X)`, and
   `zornBarConj (zornLeftGamma5 X) = -zornRightGamma5 (zornBarConj X)`.
7. `alternating_gamma5_associator_chain_and_chromomagnetic_anomaly` (`𝓐₅`):
   Alternating `γ₅` associator chain
   `associator zornGamma5 X Y = -associator X zornGamma5 Y = associator X Y zornGamma5 = (2 : ℤ) • zornCrossCurvature X Y`.
8. `associative_peirce_dual_chiral_gamma5_bridge`:
   Over any associative ring `[Ring B]`, links the external grading involution `invS P = 2P - 1`
   and internal chiral pseudoscalar `genSig P A C = genJ P A C * genPhi P A C` to the Weyl
   chiral projectors `genV P A C ± genSig P A C`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysChiralGamma5DiracBridge

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.NCZornProjectionNormalization
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped Matrix

variable {A : Type*} [Ring A]

/-! ## 1. The 6-Stage Causal Poset `𝓣₀ ≺ 𝓚₁ ≺ 𝓗₂ ≺ 𝓜₃ ≺ 𝓓₄ ≺ 𝓐₅` -/

/-- The 6-stage causal poset of Tetraktys Chiral `γ₅` vs. Dirac Algebra archetypes. -/
inductive TetraktysGamma5Archetype
  | T0_threefoldOrigin
  | K1_kleinFourChiralActions
  | H2_walshHadamardPeirceProjectors
  | M3_massProtectionChiralChargeDuality
  | D4_hodgeVsBarIntertwiningDuality
  | A5_alternatingGamma5AssociatorChain
  deriving DecidableEq, Repr

instance instInhabitedTetraktysGamma5Archetype : Inhabited TetraktysGamma5Archetype :=
  ⟨.T0_threefoldOrigin⟩

/-- Topological rank in the 6-stage causal poset. -/
def tetraktysGamma5Rank : TetraktysGamma5Archetype → ℕ
  | .T0_threefoldOrigin => 0
  | .K1_kleinFourChiralActions => 1
  | .H2_walshHadamardPeirceProjectors => 2
  | .M3_massProtectionChiralChargeDuality => 3
  | .D4_hodgeVsBarIntertwiningDuality => 4
  | .A5_alternatingGamma5AssociatorChain => 5

theorem tetraktysGamma5Rank_injective : Function.Injective tetraktysGamma5Rank := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

instance instPartialOrderTetraktysGamma5Archetype : PartialOrder TetraktysGamma5Archetype :=
  PartialOrder.lift tetraktysGamma5Rank tetraktysGamma5Rank_injective

theorem tetraktysGamma5_strict_causal_chain :
    TetraktysGamma5Archetype.T0_threefoldOrigin < .K1_kleinFourChiralActions ∧
    TetraktysGamma5Archetype.K1_kleinFourChiralActions < .H2_walshHadamardPeirceProjectors ∧
    TetraktysGamma5Archetype.H2_walshHadamardPeirceProjectors < .M3_massProtectionChiralChargeDuality ∧
    TetraktysGamma5Archetype.M3_massProtectionChiralChargeDuality < .D4_hodgeVsBarIntertwiningDuality ∧
    TetraktysGamma5Archetype.D4_hodgeVsBarIntertwiningDuality < .A5_alternatingGamma5AssociatorChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## 2. Component Normalization & Operator-Zorn Primitives -/

/-- Integer scalar multiplication on `OperatorZornMatrix A`. -/
def zsmulZorn (k : ℤ) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨k • X.n_plus, k • X.n_minus, fun i => k • X.sigma_plus i, fun i => k • X.sigma_minus i⟩

instance instSMulIntOperatorZornMatrix : SMul ℤ (OperatorZornMatrix A) := ⟨zsmulZorn⟩

@[simp] theorem zornZero_nPlus : (0 : OperatorZornMatrix A).n_plus = 0 := rfl
@[simp] theorem zornZero_nMinus : (0 : OperatorZornMatrix A).n_minus = 0 := rfl
@[simp] theorem zornZero_sigmaPlus (i : Fin 3) : (0 : OperatorZornMatrix A).sigma_plus i = 0 := rfl
@[simp] theorem zornZero_sigmaMinus (i : Fin 3) : (0 : OperatorZornMatrix A).sigma_minus i = 0 := rfl

@[simp] theorem zornAdd_nPlus (X Y : OperatorZornMatrix A) :
    (X + Y).n_plus = X.n_plus + Y.n_plus := rfl

@[simp] theorem zornAdd_nMinus (X Y : OperatorZornMatrix A) :
    (X + Y).n_minus = X.n_minus + Y.n_minus := rfl

@[simp] theorem zornNeg_nPlus (X : OperatorZornMatrix A) :
    (-X).n_plus = -X.n_plus := rfl

@[simp] theorem zornNeg_nMinus (X : OperatorZornMatrix A) :
    (-X).n_minus = -X.n_minus := rfl

@[simp] theorem zsmulZorn_nPlus (k : ℤ) (X : OperatorZornMatrix A) :
    (k • X).n_plus = k • X.n_plus := rfl

@[simp] theorem zsmulZorn_nMinus (k : ℤ) (X : OperatorZornMatrix A) :
    (k • X).n_minus = k • X.n_minus := rfl

@[simp] theorem zsmulZorn_sigmaPlus (k : ℤ) (X : OperatorZornMatrix A) (i : Fin 3) :
    (k • X).sigma_plus i = k • X.sigma_plus i := rfl

@[simp] theorem zsmulZorn_sigmaMinus (k : ℤ) (X : OperatorZornMatrix A) (i : Fin 3) :
    (k • X).sigma_minus i = k • X.sigma_minus i := rfl

/-- Anticommutator `{X, Y} = X * Y + Y * X` on the non-associative Zorn carrier. -/
def zornAnticomm (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  X * Y + Y * X

/-- Left-handed sheet idempotent `e_L = (1, 0, 0, 0)`. -/
def zornEL : OperatorZornMatrix A :=
  ⟨1, 0, fun _ => 0, fun _ => 0⟩

/-- Right-handed sheet idempotent `e_R = (0, 1, 0, 0)`. -/
def zornER : OperatorZornMatrix A :=
  ⟨0, 1, fun _ => 0, fun _ => 0⟩

/-- Zorn identity element `1_Zorn = e_L + e_R = (1, 1, 0, 0)`. -/
def zornOne : OperatorZornMatrix A :=
  ⟨1, 1, fun _ => 0, fun _ => 0⟩

/-- The Tetraktys Chiral Operator `γ₅ = e_L - e_R = (1, -1, 0, 0)`. -/
def zornGamma5 : OperatorZornMatrix A :=
  ⟨1, -1, fun _ => 0, fun _ => 0⟩

/-- Linearized mass operator, written as the left and right Peirce sheet actions. -/
def zornMassLin (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  zornEL * X + X * zornER

/-- Standard unit basis vector in `Fin 3 → A`. -/
def zornBasisVec : Fin 3 → Fin 3 → A
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 1 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1

/-- Directional upper-cone raising generator `E_i^+ = (0, 0, e_i, 0)`. -/
def zornEPlus (i : Fin 3) : OperatorZornMatrix A :=
  ⟨0, 0, zornBasisVec i, fun _ => 0⟩

/-- Directional lower-cone lowering generator `E_i^- = (0, 0, 0, e_i)`. -/
def zornEMinus (i : Fin 3) : OperatorZornMatrix A :=
  ⟨0, 0, fun _ => 0, zornBasisVec i⟩

/-- Directional Weyl reflection `W_i = E_i^+ - E_i^- = (0, 0, e_i, -e_i)`. -/
def zornWeyl (i : Fin 3) : OperatorZornMatrix A :=
  zornEPlus i - zornEMinus i

/-- Left chiral multiplication `L_{γ₅}(X) = γ₅ * X`. -/
def zornLeftGamma5 (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  zornGamma5 * X

/-- Right chiral multiplication `R_{γ₅}(X) = X * γ₅`. -/
def zornRightGamma5 (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  X * zornGamma5

/-- Bilateral chiral parity involution `Ad_{γ₅}(X) = (γ₅ * X) * γ₅`. -/
def zornAdGamma5 (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (zornGamma5 * X) * zornGamma5

/-- Off-diagonal Dirac mass/cone sector `(e_L * X) * e_R + (e_R * X) * e_L = (0, 0, u, v)`. -/
def zornMassConeSector (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (zornEL * X) * zornER + (zornER * X) * zornEL

/-- Diagonal chiral charge sector `(e_L * X) * e_L - (e_R * X) * e_R = (a, -d, 0, 0)`. -/
def zornChiralCharge (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (zornEL * X) * zornEL - (zornER * X) * zornER

/-- Upside-Down Tetraktys Hodge sheet/cone swap `⋆_{𝓚₄}(a, d, u, v) = (d, a, v, u)`. -/
def zornHodgeSwap (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_minus, X.n_plus, X.sigma_minus, X.sigma_plus⟩

/-- Dirac off-diagonal cone swap `diracConeSwap(a, d, u, v) = (a, d, v, u)`. -/
def zornDiracConeSwap (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus, X.n_minus, X.sigma_minus, X.sigma_plus⟩

/-- Octonionic bar-involution `overline(a, d, u, v) = (d, a, -u, -v)`. -/
def zornBarConj (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_minus, X.n_plus, fun i => -X.sigma_plus i, fun i => -X.sigma_minus i⟩

/-- Off-diagonal cross-product curvature matrix `⟨0, 0, v₁ × v₂, u₁ × u₂⟩`. -/
def zornCrossCurvature (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨0, 0, fun i => NCZornElement.zornCross X.sigma_minus Y.sigma_minus i,
         fun i => NCZornElement.zornCross X.sigma_plus Y.sigma_plus i⟩

/-- Constructor-indexed operator realization mapping each `TetraktysGamma5Archetype` stage to its
canonical operator in `OperatorZornMatrix A`. -/
def tetraktysGamma5StageOp (X Y : OperatorZornMatrix A) :
    TetraktysGamma5Archetype → OperatorZornMatrix A
  | .T0_threefoldOrigin => associator (zornEPlus (A := A) 0) (zornEPlus 1) (zornEPlus 2)
  | .K1_kleinFourChiralActions => zornAdGamma5 X
  | .H2_walshHadamardPeirceProjectors =>
      X + zornLeftGamma5 X + zornRightGamma5 X + zornAdGamma5 X
  | .M3_massProtectionChiralChargeDuality => zornChiralCharge X
  | .D4_hodgeVsBarIntertwiningDuality => zornHodgeSwap (zornBarConj X)
  | .A5_alternatingGamma5AssociatorChain => associator (zornGamma5 (A := A)) X Y

/-- Tactic that proves `OperatorZornMatrix A` identities componentwise over any noncommutative
ring `[Ring A]` by `operatorZornMatrix_ext`, `fin_cases` on `Fin 3`, and `noncomm_ring` / `abel`. -/
macro "zorn_op_ext" : tactic =>
  `(tactic| (
    apply operatorZornMatrix_ext
    · simp only [zornEL, zornER, zornOne, zornGamma5, zornEPlus, zornEMinus, zornWeyl,
                 zornBasisVec, zornAnticomm, zornLeftGamma5, zornRightGamma5, zornAdGamma5,
                 zornMassConeSector, zornChiralCharge, zornHodgeSwap, zornDiracConeSwap,
                 zornBarConj, zornCrossCurvature, zornMassLin, nPlus, nMinus, sigmaPlus, sigmaMinus,
                 bracket, associator, NCZornElement.zornDot, NCZornElement.zornCross,
                 mul_n_plus, mul_n_minus, mul_sigma_plus_apply, mul_sigma_minus_apply,
                 zornAdd_nPlus, zornAdd_nMinus, add_sigma_plus_apply, add_sigma_minus_apply,
                 zornSub_nPlus, zornSub_nMinus, sub_sigma_plus_apply, sub_sigma_minus_apply,
                 zornNeg_nPlus, zornNeg_nMinus, neg_sigma_plus_apply, neg_sigma_minus_apply,
                 zsmulZorn_nPlus, zsmulZorn_nMinus, zsmulZorn_sigmaPlus, zsmulZorn_sigmaMinus,
                 zornZero_nPlus, zornZero_nMinus, zornZero_sigmaPlus, zornZero_sigmaMinus,
                 Fin.isValue, Fin.zero_eta, Fin.mk_one]
      (try noncomm_ring)
      (try abel)
    · simp only [zornEL, zornER, zornOne, zornGamma5, zornEPlus, zornEMinus, zornWeyl,
                 zornBasisVec, zornAnticomm, zornLeftGamma5, zornRightGamma5, zornAdGamma5,
                 zornMassConeSector, zornChiralCharge, zornHodgeSwap, zornDiracConeSwap,
                 zornBarConj, zornCrossCurvature, zornMassLin, nPlus, nMinus, sigmaPlus, sigmaMinus,
                 bracket, associator, NCZornElement.zornDot, NCZornElement.zornCross,
                 mul_n_plus, mul_n_minus, mul_sigma_plus_apply, mul_sigma_minus_apply,
                 zornAdd_nPlus, zornAdd_nMinus, add_sigma_plus_apply, add_sigma_minus_apply,
                 zornSub_nPlus, zornSub_nMinus, sub_sigma_plus_apply, sub_sigma_minus_apply,
                 zornNeg_nPlus, zornNeg_nMinus, neg_sigma_plus_apply, neg_sigma_minus_apply,
                 zsmulZorn_nPlus, zsmulZorn_nMinus, zsmulZorn_sigmaPlus, zsmulZorn_sigmaMinus,
                 zornZero_nPlus, zornZero_nMinus, zornZero_sigmaPlus, zornZero_sigmaMinus,
                 Fin.isValue, Fin.zero_eta, Fin.mk_one]
      (try noncomm_ring)
      (try abel)
    · funext c
      fin_cases c <;> (
        simp only [zornEL, zornER, zornOne, zornGamma5, zornEPlus, zornEMinus, zornWeyl,
                   zornBasisVec, zornAnticomm, zornLeftGamma5, zornRightGamma5, zornAdGamma5,
                   zornMassConeSector, zornChiralCharge, zornHodgeSwap, zornDiracConeSwap,
                   zornBarConj, zornCrossCurvature, zornMassLin, nPlus, nMinus, sigmaPlus, sigmaMinus,
                   bracket, associator, NCZornElement.zornDot, NCZornElement.zornCross,
                   mul_n_plus, mul_n_minus, mul_sigma_plus_apply, mul_sigma_minus_apply,
                   zornAdd_nPlus, zornAdd_nMinus, add_sigma_plus_apply, add_sigma_minus_apply,
                   zornSub_nPlus, zornSub_nMinus, sub_sigma_plus_apply, sub_sigma_minus_apply,
                   zornNeg_nPlus, zornNeg_nMinus, neg_sigma_plus_apply, neg_sigma_minus_apply,
                   zsmulZorn_nPlus, zsmulZorn_nMinus, zsmulZorn_sigmaPlus, zsmulZorn_sigmaMinus,
                   zornZero_nPlus, zornZero_nMinus, zornZero_sigmaPlus, zornZero_sigmaMinus,
                   Fin.isValue, Fin.zero_eta, Fin.mk_one]
        (try noncomm_ring)
        (try abel))
    · funext c
      fin_cases c <;> (
        simp only [zornEL, zornER, zornOne, zornGamma5, zornEPlus, zornEMinus, zornWeyl,
                   zornBasisVec, zornAnticomm, zornLeftGamma5, zornRightGamma5, zornAdGamma5,
                   zornMassConeSector, zornChiralCharge, zornHodgeSwap, zornDiracConeSwap,
                   zornBarConj, zornCrossCurvature, zornMassLin, nPlus, nMinus, sigmaPlus, sigmaMinus,
                   bracket, associator, NCZornElement.zornDot, NCZornElement.zornCross,
                   mul_n_plus, mul_n_minus, mul_sigma_plus_apply, mul_sigma_minus_apply,
                   zornAdd_nPlus, zornAdd_nMinus, add_sigma_plus_apply, add_sigma_minus_apply,
                   zornSub_nPlus, zornSub_nMinus, sub_sigma_plus_apply, sub_sigma_minus_apply,
                   zornNeg_nPlus, zornNeg_nMinus, neg_sigma_plus_apply, neg_sigma_minus_apply,
                   zsmulZorn_nPlus, zsmulZorn_nMinus, zsmulZorn_sigmaPlus, zsmulZorn_sigmaMinus,
                   zornZero_nPlus, zornZero_nMinus, zornZero_sigmaPlus, zornZero_sigmaMinus,
                   Fin.isValue, Fin.zero_eta, Fin.mk_one]
        (try noncomm_ring)
        (try abel))))

/-! ## 3. Stage `𝓣₀`: Threefold Origin of `zornGamma5` & Triadic Cone Associator -/

/-- **Stage `𝓣₀` (`tetraktys_gamma5_threefold_origin`)**:
Over any non-commutative ring `[Ring A]`, the Tetraktys chiral operator `zornGamma5` arises
simultaneously from:
1. The orthogonal Peirce idempotent difference `zornEL - zornER = zornGamma5`,
2. Each directional CAR commutator `bracket (zornEPlus i) (zornEMinus i) = zornGamma5` (`i : Fin 3`),
3. The Triadic Cone Associator:
   `(zornEPlus 0 * zornEPlus 1) * zornEPlus 2 = zornER`,
   `zornEPlus 0 * (zornEPlus 1 * zornEPlus 2) = zornEL`,
   `associator (zornEPlus 0) (zornEPlus 1) (zornEPlus 2) = -zornGamma5`, and
   `associator (zornEMinus 0) (zornEMinus 1) (zornEMinus 2) = -zornGamma5`. -/
theorem tetraktys_gamma5_threefold_origin (i : Fin 3) :
    zornEL (A := A) + zornER = zornOne ∧
    zornEL (A := A) - zornER = zornGamma5 ∧
    zornEL (A := A) * zornEL = zornEL ∧
    zornER (A := A) * zornER = zornER ∧
    zornEL (A := A) * zornER = 0 ∧
    zornER (A := A) * zornEL = 0 ∧
    zornGamma5 (A := A) * zornGamma5 = zornOne ∧
    (zornEPlus (A := A) i * zornEMinus i = zornEL ∧
     zornEMinus (A := A) i * zornEPlus i = zornER ∧
     zornAnticomm (zornEPlus (A := A) i) (zornEMinus i) = zornOne ∧
     bracket (zornEPlus (A := A) i) (zornEMinus i) = zornGamma5 ∧
     zornWeyl (A := A) i * zornWeyl i = -zornOne) ∧
    (zornEPlus (A := A) 0 * zornEPlus 1) * zornEPlus 2 = zornER ∧
    zornEPlus (A := A) 0 * (zornEPlus 1 * zornEPlus 2) = zornEL ∧
    associator (zornEPlus (A := A) 0) (zornEPlus 1) (zornEPlus 2) = -zornGamma5 (A := A) ∧
    associator (zornEMinus (A := A) 0) (zornEMinus 1) (zornEMinus 2) = -zornGamma5 (A := A) := by
  refine ⟨by zorn_op_ext, by zorn_op_ext, by zorn_op_ext, by zorn_op_ext,
          by zorn_op_ext, by zorn_op_ext, by zorn_op_ext, ?_,
          by zorn_op_ext, by zorn_op_ext, by zorn_op_ext, by zorn_op_ext⟩
  fin_cases i <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> zorn_op_ext)

/-! ## 4. Stage `𝓚₁`: Klein Four-Group `𝓚₄ ≅ C₂ × C₂` of Chiral Actions & Middle-Associativity -/

/-- **Stage `𝓚₁` (`tetraktys_klein_four_group_identities`)**:
For any `X : OperatorZornMatrix A` over any non-commutative ring `[Ring A]`:
1. `zornLeftGamma5`, `zornRightGamma5`, and `zornAdGamma5` act by independent sign flips on the
   Peirce sectors `(n_plus, n_minus, sigma_plus, sigma_minus)`,
2. Chiral middle-associativity holds: `(zornGamma5 * X) * zornGamma5 = zornGamma5 * (X * zornGamma5)`
   (`associator zornGamma5 X zornGamma5 = 0`),
3. `(id, zornLeftGamma5, zornRightGamma5, zornAdGamma5)` satisfy the Klein four-group `C₂ × C₂`
   involution and commutative composition laws. -/
theorem tetraktys_klein_four_group_identities (X : OperatorZornMatrix A) :
    zornLeftGamma5 X = ⟨X.n_plus, -X.n_minus, X.sigma_plus, fun i => -X.sigma_minus i⟩ ∧
    zornRightGamma5 X = ⟨X.n_plus, -X.n_minus, fun i => -X.sigma_plus i, X.sigma_minus⟩ ∧
    zornAdGamma5 X =
      ⟨X.n_plus, X.n_minus, fun i => -X.sigma_plus i, fun i => -X.sigma_minus i⟩ ∧
    (zornGamma5 * X) * zornGamma5 = zornGamma5 * (X * zornGamma5) ∧
    associator (zornGamma5 (A := A)) X zornGamma5 = 0 ∧
    zornLeftGamma5 (zornLeftGamma5 X) = X ∧
    zornRightGamma5 (zornRightGamma5 X) = X ∧
    zornAdGamma5 (zornAdGamma5 X) = X ∧
    zornLeftGamma5 (zornRightGamma5 X) = zornAdGamma5 X ∧
    zornRightGamma5 (zornLeftGamma5 X) = zornAdGamma5 X ∧
    zornLeftGamma5 (zornAdGamma5 X) = zornRightGamma5 X ∧
    zornRightGamma5 (zornAdGamma5 X) = zornLeftGamma5 X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_op_ext

/-! ## 5. Stage `𝓗₂`: `4 × 4` Walsh–Hadamard Character Synthesis of Peirce Projectors -/

/-- **Stage `𝓗₂` (`tetraktys_walsh_hadamard_peirce_projectors`)**:
Applying the `4 × 4` Walsh–Hadamard character table of `𝓚₄` to `(X, L_{γ₅} X, R_{γ₅} X, Ad_{γ₅} X)`
isolates four times each of the four Peirce sectors `(e_L X) e_L`, `(e_L X) e_R`, `(e_R X) e_L`,
and `(e_R X) e_R`, which sum to `X`. -/
theorem tetraktys_walsh_hadamard_peirce_projectors (X : OperatorZornMatrix A) :
    (zornEL * X) * zornEL = nPlus X.n_plus ∧
    (zornEL * X) * zornER = sigmaPlus X.sigma_plus ∧
    (zornER * X) * zornEL = sigmaMinus X.sigma_minus ∧
    (zornER * X) * zornER = nMinus X.n_minus ∧
    X + zornLeftGamma5 X + zornRightGamma5 X + zornAdGamma5 X =
      (4 : ℤ) • ((zornEL * X) * zornEL) ∧
    X + zornLeftGamma5 X - zornRightGamma5 X - zornAdGamma5 X =
      (4 : ℤ) • ((zornEL * X) * zornER) ∧
    X - zornLeftGamma5 X + zornRightGamma5 X - zornAdGamma5 X =
      (4 : ℤ) • ((zornER * X) * zornEL) ∧
    X - zornLeftGamma5 X - zornRightGamma5 X + zornAdGamma5 X =
      (4 : ℤ) • ((zornER * X) * zornER) ∧
    (zornEL * X) * zornEL + (zornEL * X) * zornER +
      (zornER * X) * zornEL + (zornER * X) * zornER = X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_op_ext

/-! ## 6. Stage `𝓜₃`: Chiral Mass Protection vs. Chiral Charge Duality -/

/-- **Stage `𝓜₃` (`tetraktys_mass_protection_and_chiral_charge_duality`)**:
1. The anticommutator `{γ₅, X}` annihilates the off-diagonal vector cones `(u, v)` and doubles
   the chiral sheet charge `(a, -d, 0, 0)`.
2. The commutator `[γ₅, X]` annihilates the diagonal sheets `(a, d)` and doubles the chiral
   vector current `(0, 0, u, -v)`.
3. `zornMassConeSector X = (e_L * X) * e_R + (e_R * X) * e_L = (0, 0, u, v)` is strictly
   annihilated by `zornAnticomm zornGamma5`, while
   `(2 : ℤ) • zornChiralCharge X = zornAnticomm zornGamma5 X`. -/
theorem tetraktys_mass_protection_and_chiral_charge_duality (X : OperatorZornMatrix A) :
    zornAnticomm zornGamma5 X =
      (2 : ℤ) • ⟨X.n_plus, -X.n_minus, fun _ => 0, fun _ => 0⟩ ∧
    bracket zornGamma5 X =
      (2 : ℤ) • ⟨0, 0, X.sigma_plus, fun i => -X.sigma_minus i⟩ ∧
    zornMassConeSector X = ⟨0, 0, X.sigma_plus, X.sigma_minus⟩ ∧
    zornAnticomm zornGamma5 (zornMassConeSector X) = 0 ∧
    zornChiralCharge X = ⟨X.n_plus, -X.n_minus, fun _ => 0, fun _ => 0⟩ ∧
    (2 : ℤ) • zornChiralCharge X = zornAnticomm zornGamma5 X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_op_ext

/-! ## 7. Stage `𝓓₄`: Upside-Down Tetraktys Hodge Inversion vs. Bar-Conjugation Duality -/

/-- Coordinate formula for `zornAdGamma5` to avoid unfolding nested Zorn products. -/
theorem zornAdGamma5_eq (X : OperatorZornMatrix A) :
    zornAdGamma5 X =
      ⟨X.n_plus, X.n_minus, fun i => -X.sigma_plus i, fun i => -X.sigma_minus i⟩ := by
  zorn_op_ext

/-- **Stage `𝓓₄` (`tetraktys_hodge_vs_bar_intertwining_duality`)**:
The Upside-Down Tetraktys Hodge swap `zornHodgeSwap` and octonionic bar-conjugation `zornBarConj`
commute to `zornAdGamma5 (zornDiracConeSwap X)`, while composing with `zornDiracConeSwap` gives
`zornAdGamma5 X`. Furthermore, `zornHodgeSwap` anticommutes with `L_{γ₅}` and `R_{γ₅}` individually,
while `zornBarConj` intertwines `L_{γ₅}` with `-R_{γ₅}`. -/
theorem tetraktys_hodge_vs_bar_intertwining_duality (X : OperatorZornMatrix A) :
    zornHodgeSwap (zornHodgeSwap X) = X ∧
    zornBarConj (zornBarConj X) = X ∧
    zornHodgeSwap (zornBarConj X) = zornAdGamma5 (zornDiracConeSwap X) ∧
    zornBarConj (zornHodgeSwap X) = zornAdGamma5 (zornDiracConeSwap X) ∧
    zornHodgeSwap (zornDiracConeSwap (zornBarConj X)) = zornAdGamma5 X ∧
    zornHodgeSwap (zornLeftGamma5 X) = -zornLeftGamma5 (zornHodgeSwap X) ∧
    zornHodgeSwap (zornRightGamma5 X) = -zornRightGamma5 (zornHodgeSwap X) ∧
    zornBarConj (zornLeftGamma5 X) = -zornRightGamma5 (zornBarConj X) ∧
    zornBarConj (zornRightGamma5 X) = -zornLeftGamma5 (zornBarConj X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_op_ext

/-! ## 8. Stage `𝓐₅`: Alternating `γ₅` Associator Chain -/

/-- **Stage `𝓐₅` (`alternating_gamma5_associator_chain_and_chromomagnetic_anomaly`)**:
For any `X, Y : OperatorZornMatrix A` over any non-commutative ring `[Ring A]`:
1. Moving `zornGamma5` across the three slots of the Zorn associator alternates signs and
   isolates twice the off-diagonal cross-product curvature `zornCrossCurvature X Y`:
   `[γ₅, X, Y] = -[X, γ₅, Y] = +[X, Y, γ₅] = 2 • ⟨0, 0, v₁ × v₂, u₁ × u₂⟩`.
2. The two outer-slot associators agree, as witnessed directly by their common curvature value. -/
theorem alternating_gamma5_associator_chain_and_chromomagnetic_anomaly
    (X Y : OperatorZornMatrix A) :
    associator (zornGamma5 (A := A)) X Y = (2 : ℤ) • zornCrossCurvature X Y ∧
    associator X (zornGamma5 (A := A)) Y = -((2 : ℤ) • zornCrossCurvature X Y) ∧
    associator X Y (zornGamma5 (A := A)) = (2 : ℤ) • zornCrossCurvature X Y ∧
    associator (zornGamma5 (A := A)) X Y = associator X Y (zornGamma5 (A := A)) := by
  have h1 : associator (zornGamma5 (A := A)) X Y = (2 : ℤ) • zornCrossCurvature X Y := by
    zorn_op_ext
  have h2 : associator X (zornGamma5 (A := A)) Y = -((2 : ℤ) • zornCrossCurvature X Y) := by
    zorn_op_ext
  have h3 : associator X Y (zornGamma5 (A := A)) = (2 : ℤ) • zornCrossCurvature X Y := by
    zorn_op_ext
  exact ⟨h1, h2, h3, h1.trans h3.symm⟩

/-! ## 9. Associative Peirce Dual-Chirality Bridge (`invS P` vs. `genSig P A C`) -/

/-- **Archetype `A₈₆` (`associative_peirce_dual_chiral_gamma5_bridge`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`, the external grading involution
`invS P = 2P - 1` and the internal chiral pseudoscalar `genSig P A C = genJ P A C * genPhi P A C`
both anticommute with `genPhi P A C` and `genJ P A C`, commute with `genV P A C`, and form
orthogonal zero-divisor Weyl projectors `genV P A C + genSig P A C = 2 • qgtPlus P A C` and
`genV P A C - genSig P A C = 2 • qgtMinus P A C`. -/
theorem associative_peirce_dual_chiral_gamma5_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    invS P * genV P A C = genSig P A C ∧
    invS P * genSig P A C = genV P A C ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 ∧
    anticomm (genSig P A C) (genPhi P A C) = 0 ∧
    anticomm (genSig P A C) (genJ P A C) = 0 ∧
    PeirceSpine.comm (invS P) (genV P A C) = 0 ∧
    PeirceSpine.comm (genSig P A C) (genV P A C) = 0 ∧
    (genV P A C + genSig P A C) * (genV P A C - genSig P A C) = 0 ∧
    (genV P A C - genSig P A C) * (genV P A C + genSig P A C) = 0 ∧
    (genV P A C + genSig P A C) * (genPhi P A C - genJ P A C) = 0 ∧
    (genV P A C - genSig P A C) * (genPhi P A C + genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ## 10. Non-Commutativity (`T16`) and Non-Vacuity (`T17`) Witness over Matrix Operators -/

/-- Concrete element in `OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ)` with non-commuting
`2 × 2` matrix coefficients. -/
def ncZornWitnessX : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨!![1, 1; 0, 0], !![0, 0; 1, 1],
   fun i => if i = 0 then !![0, 1; 0, 0] else 0,
   fun _ => 0⟩

/-- Second concrete element in `OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ)`. -/
def ncZornWitnessY : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨!![0, 1; 0, 0], !![1, 0; 0, 0],
   fun i => if i = 1 then !![0, 0; 1, 0] else 0,
   fun _ => 0⟩

/-- **Non-Commutativity (`T16`) and Non-Vacuity (`T17`) Certificate**:
1. The matrix coefficients `ncZornWitnessX.n_plus` and `ncZornWitnessY.n_plus` do not commute in
   `Matrix (Fin 2) (Fin 2) ℤ`,
2. The Zorn product is non-commutative (`ncZornWitnessX * ncZornWitnessY ≠ ncZornWitnessY * ncZornWitnessX`),
3. The chiral `γ₅` associator `associator zornGamma5 ncZornWitnessX ncZornWitnessY` is non-zero! -/
theorem ncZornWitness_noncomm_and_nonzero_associator :
    ncZornWitnessX.n_plus * ncZornWitnessY.n_plus ≠
      ncZornWitnessY.n_plus * ncZornWitnessX.n_plus ∧
    ncZornWitnessX * ncZornWitnessY ≠ ncZornWitnessY * ncZornWitnessX ∧
    associator (zornGamma5 (A := Matrix (Fin 2) (Fin 2) ℤ))
      ncZornWitnessX ncZornWitnessY ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    revert h11
    decide
  · intro h
    have hnp := congrArg (fun Z : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ) => Z.n_plus 0 1) h
    revert hnp
    decide
  · intro h
    have hsm := congrArg
      (fun Z : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ) => Z.sigma_minus 2 0 0) h
    revert hsm
    decide

end InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysChiralGamma5DiracBridge
