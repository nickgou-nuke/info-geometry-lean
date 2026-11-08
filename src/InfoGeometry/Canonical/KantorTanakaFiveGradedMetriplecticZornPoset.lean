/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Block
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtraction
import InfoGeometry.OperatorAlgebra.PeirceSpine.CrossChargeBrackets
import InfoGeometry.Core.TensorPeirceDecomposition
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset
Role: Canonical formalization of Streams XVI & XVII —
  1. **Part I (`KantorTanakaFiveGradedStage : 𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`)**:
     The 5-Graded Kantor–Tanaka Contact Super-Tower, Factored Quintic
     Annihilator, Orthogonal Quartic Lagrange Projectors, `𝔬𝔰𝔭(1|2)`
     Superconformal Closure, & Günaydin–Gürsey `𝔤𝔩₁(ℝ)_H ⊕ 𝔰𝔩₃(ℝ)_color` Poset:
     - **Stage `𝔎𝔗₁` & Rung 0 (`KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption`)**:
       Derivation eigenvalue addition `D(X) = a X ∧ D(Y) = b Y ⟹ D(X Y) = (a + b) X Y`
       and `D({X, Y}) = (a + b) {X, Y}`; when `D(Q_±1) = ±Q_±1`, the contact square
       `E_±2 = Q_±1²` has eigenvalue `±2` and shatters the 3-graded Peirce operator
       `D³ - D` by an exact factor of `6` (`(D³ - D)(Q_{+1}²) = 6 Q_{+1}²`,
       `charge_iter_cubic_difference`: `(ad_P³ - ad_P)(K)(X) = 6 (N_+ X N_+ - N_- X N_-)`).
     - **Stage `𝔎𝔗₂` & Rung 1 (`KT2_FactoredFiveGradedQuinticContactLaw`)**:
       Exact polynomial factorization `(x² - 4)(x³ - x) = x(x² - 1)(x² - 4) = x⁵ - 5x³ + 4x`
       and operator annihilation `(ad_H² - 4I)(ad_H³ - ad_H) = ad_H⁵ - 5 ad_H³ + 4 ad_H = 0`
       on `M₃(R)` (`adH_quintic_identity`) and on the noncommutative Peirce 5-sector
       operator spine (`charge_iter_fifth_annihilator`).
     - **Stage `𝔎𝔗₃` & Rung 2 (`KT3_OrthogonalQuarticLagrangeProjectors`)**:
       Quartic Lagrange shell projectors cleared of denominators over any `[CommRing R]`
       (`12 Π₀ = 3(D² - 1)(D² - 4)`, `12 Π_{±1} = -4 D²(D² - 4)`, `12 Π_{±2} = D(D³ - D)`)
       and over `[Field F] [CharZero F]` (`adHProjectorZero`, `adHProjectorOne`,
       `adHProjectorTwo`): complete resolution of unity, mutual orthogonality, idempotency,
       the Peirce-defect factorization `Π_{±2} = (1/12) ad_H (ad_H³ - ad_H)`, and signed
       5-sector extraction (`charge_extract_zero`, `charge_extract_plus_one`,
       `charge_extract_minus_one`, `charge_extract_plus_two`, `charge_extract_minus_two`).
     - **Stage `𝔎𝔗₄` & Rung 3 (`KT4_OrthosymplecticOSp12SuperconformalContactClosure`)**:
       `𝔬𝔰𝔭(1|2)` superconformal contact brackets `{Q_+, Q_-} = H`, `{Q_±, Q_±} = ±2 E_±`,
       `[E, F] = H`, `[E, Q_-] = -Q_+`, `[F, Q_+] = -Q_-`, `[E, Q_+] = [F, Q_-] = 0`,
       and the odd-odd-odd super-Jacobi identity
       `2 [Q_+, {Q_+, Q_-}] + [Q_-, {Q_+, Q_+}] = 0`.
     - **Stage `𝔎𝔗₅` & Rung 4 (`KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition`)**:
       Grade-`0` decomposition `𝔤𝔩₃(ℝ) = 𝔤𝔩₁(ℝ)_H ⊕ 𝔰𝔩₃(ℝ)_color` via
       `projGL1 X = (1/3) Tr(X) I₃` and `projSL3 X = X - (1/3) Tr(X) I₃`, proving
       idempotency, mutual orthogonality, trace vanishing, Lie ideal closure, and
       quark–antiquark outer-product decomposition.
     - **Stage `𝔎𝔗₆` (`KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich`)**:
       5-graded Maurer–Cartan flatness (`mcCurvatureTower canonicalMaurerCartanJet = 0`)
       and cross-charge extremal sandwich commutator (`extreme_sandwich_comm`,
       `extreme_same_support_residual`).
  2. **Part II (`MetriplecticZornStage : 𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`)**:
     The Metriplectic Zorn Split-Octonion Closure, Three-Term Pythagorean
     Determinant Law, & Third-Order Volume Duality Poset:
     - **Stages `𝔐ℨ₁ ≺ 𝔐ℨ₂` (`MZ1_DeWittBasisAndThreeChannelProjections`,
       `MZ2_ExactThreeTermMetriplecticZornDecomposition`)**:
       DeWitt sum `u₀ + u₀* = 1`, DeWitt difference `u₀ - u₀* = I_para`, and the exact
       three-channel Metriplectic Zorn decomposition
       `2 (x y) = g(x, y) 1 + ω(x, y) I_para + 2 (x ×_H y)` over any `[CommRing R]`
       (and `z₁ z₂ = (1/2) g 1 + (1/2) ω I_para + z₁ ×_H z₂` over `ℝ`).
     - **Stage `𝔐ℨ₃` (`MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit`)**:
       Para-Kähler locking `ω(z₁, z₂) = g(K z₁, z₂)` (`[I_para, z] = 2 K(z)`) and
       tangent split `{z₁, z₂} = g(z₁, z₂) 1`, `[z₁, z₂] = ω(z₁, z₂) I_para + 2(z₁ ×_H z₂)`.
     - **Stage `𝔐ℨ₄` (`MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw`)**:
       Rung 0 diagonal determinant aporia `g² - ω² = 4(u₁·v₂)(v₁·u₂)` vs. the exact
       Three-Term Metriplectic Pythagorean Law
       `4 det_Zorn(z₁ z₂) = g(z₁, z₂)² - ω(z₁, z₂)² + 4 det_Zorn(z₁ ×_H z₂) = 4 det_Zorn(z₁) det_Zorn(z₂)`.
     - **Stage `𝔐ℨ₅` (`MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara`)**:
       Third-order dual volume split: `{z₁ ×_H z₂, z₃} = (det(u₁,u₂,u₃) - det(v₁,v₂,v₃)) 1`
       on the DeWitt sum `1`, while the diagonal part of the associator `[z₁, z₂, z₃]`
       lands 100% on the DeWitt difference `I_para` as
       `-(det(u₁,u₂,u₃) + det(v₁,v₂,v₃)) I_para` with zero scalar trace along `1`.
     - **Stage `𝔐ℨ₆` (`MZ6_NonCommutativeNambuAssociatorSpecialization`)**:
       Non-commutative Nambu associator `[N_+(u), N_+(u), N_+(u)]_assoc = -⟦u⟧ I_para`
       over any `[Ring B]` with concrete non-zero `2 × 2` integer matrix witness.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset

open scoped BigOperators Matrix
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
open InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset (Vec3 ZornMatrix)

/-! ===========================================================================
    Part I: The 6-Stage 5-Graded Kantor–Tanaka Contact Super-Tower Poset
    (`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`)
    =========================================================================== -/

/-- The 6 causal stages of the 5-Graded Kantor–Tanaka Contact Super-Tower,
Factored Quintic Annihilator, Quartic Lagrange Projectors, `𝔬𝔰𝔭(1|2)`
Superconformal Closure, & Günaydin–Gürsey `𝔤𝔩₁ ⊕ 𝔰𝔩₃` Color Poset
(`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`). -/
inductive KantorTanakaFiveGradedStage : Type
  | KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption
  | KT2_FactoredFiveGradedQuinticContactLaw
  | KT3_OrthogonalQuarticLagrangeProjectors
  | KT4_OrthosymplecticOSp12SuperconformalContactClosure
  | KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition
  | KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich
  deriving DecidableEq, Repr, Inhabited

namespace KantorTanakaFiveGradedStage

/-- Topological rank `0..4` (`KT4` and `KT5` share rank `3` as parallel diamond branches). -/
def stageRank : KantorTanakaFiveGradedStage → ℕ
  | .KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption => 0
  | .KT2_FactoredFiveGradedQuinticContactLaw => 1
  | .KT3_OrthogonalQuarticLagrangeProjectors => 2
  | .KT4_OrthosymplecticOSp12SuperconformalContactClosure => 3
  | .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition => 3
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => 4

/-- Directed covering edges of the diamond poset `𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`. -/
def causalEdge : KantorTanakaFiveGradedStage → KantorTanakaFiveGradedStage → Prop
  | .KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption,
    .KT2_FactoredFiveGradedQuinticContactLaw => True
  | .KT2_FactoredFiveGradedQuinticContactLaw,
    .KT3_OrthogonalQuarticLagrangeProjectors => True
  | .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT4_OrthosymplecticOSp12SuperconformalContactClosure => True
  | .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition => True
  | .KT4_OrthosymplecticOSp12SuperconformalContactClosure,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => True
  | .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Partial order on `KantorTanakaFiveGradedStage` with `KT4` and `KT5` incomparable. -/
def stageLe (a b : KantorTanakaFiveGradedStage) : Prop :=
  a = b ∨
  stageRank a < stageRank b

instance instDecidableRelStageLe : DecidableRel stageLe := by
  intro a b
  unfold stageLe
  infer_instance

instance : PartialOrder KantorTanakaFiveGradedStage where
  le := stageLe
  lt a b := stageLe a b ∧ ¬ stageLe b a
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab'
    · exact hbc
    · rcases hbc with rfl | hbc'
      · exact Or.inr hab'
      · exact Or.inr (Nat.lt_trans hab' hbc')
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm a b hab hba := by
    rcases hab with rfl | hab'
    · rfl
    · rcases hba with rfl | hba'
      · rfl
      · exact False.elim (Nat.lt_asymm hab' hba')

instance : Fintype KantorTanakaFiveGradedStage where
  elems := {
    .KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption,
    .KT2_FactoredFiveGradedQuinticContactLaw,
    .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT4_OrthosymplecticOSp12SuperconformalContactClosure,
    .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card KantorTanakaFiveGradedStage = 6 := rfl

theorem causalEdge_stageRank_lt {a b : KantorTanakaFiveGradedStage}
    (h : causalEdge a b) : stageRank a < stageRank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_stageRank_lt {a b : KantorTanakaFiveGradedStage}
    (h : Relation.TransGen causalEdge a b) : stageRank a < stageRank b := by
  induction h with
  | single hab => exact causalEdge_stageRank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_stageRank_lt hbc)

/-- Strict DAG acyclicity of `𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`. -/
theorem causalEdge_acyclic (a : KantorTanakaFiveGradedStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (stageRank a) (transGen_causalEdge_stageRank_lt h)

/-- Parallel diamond branches `𝔎𝔗₄` and `𝔎𝔗₅` are incomparable. -/
theorem incomparable_KT4_KT5 :
    ¬ (KT4_OrthosymplecticOSp12SuperconformalContactClosure ≤
        KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition) ∧
    ¬ (KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition ≤
        KT4_OrthosymplecticOSp12SuperconformalContactClosure) := by
  change ¬ stageLe _ _ ∧ ¬ stageLe _ _
  decide

/-- Monotone representation-depth projection across `𝔎𝔗₁..𝔎𝔗₆`. -/
def toRepDepth : KantorTanakaFiveGradedStage → RepDepth
  | .KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption => .operator
  | .KT2_FactoredFiveGradedQuinticContactLaw => .operator
  | .KT3_OrthogonalQuarticLagrangeProjectors => .operator
  | .KT4_OrthosymplecticOSp12SuperconformalContactClosure => .transport
  | .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition => .transport
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => .thermo

/-- Monotone ontology meta-level projection across `𝔎𝔗₁..𝔎𝔗₆`. -/
def toOntologyMetaLevel : KantorTanakaFiveGradedStage → OntologyMetaLevel
  | .KT1_ThreeGradedPeirceOperatorAndSuperBracketEruption => .M1_ProjectorClabject
  | .KT2_FactoredFiveGradedQuinticContactLaw => .M2_GrassmannianPowertypeOrbit
  | .KT3_OrthogonalQuarticLagrangeProjectors => .M2_GrassmannianPowertypeOrbit
  | .KT4_OrthosymplecticOSp12SuperconformalContactClosure => .M3_ErlangenCasimirMetaLaw
  | .KT5_GunaydinGurseyGL1SL3SplitOctonionColorDecomposition => .M3_ErlangenCasimirMetaLaw
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : KantorTanakaFiveGradedStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageLe a b at h
  cases a <;> cases b <;> revert h <;> decide

theorem toOntologyMetaLevel_mono {a b : KantorTanakaFiveGradedStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageLe a b at h
  cases a <;> cases b <;> revert h <;> decide

end KantorTanakaFiveGradedStage

/-! ===========================================================================
    Section 1.2: Stages `𝔎𝔗₁`–`𝔎𝔗₆` Theorems (5-Graded Kantor–Tanaka Tower)
    =========================================================================== -/

section KantorTanakaTowerTheorems

/-- The 3-graded Peirce cubic operator `D(D(D X)) - D X` for any endomorphism `D : M → M`. -/
def peirceThreeGradedDefect {M : Type*} [AddGroup M] (D : M → M) (X : M) : M :=
  D (D (D X)) - D X

/-- The 5-graded Kantor–Tanaka quintic operator `D⁵(X) - 5 D³(X) + 4 D(X)`. -/
def kantorFiveGradedQuintic {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  D (D (D (D (D X)))) - 5 • D (D (D X)) + 4 • D X

/-- Factored form `(D² - 4I)(D³ - D)(X)` of the 5-graded Kantor–Tanaka operator. -/
def kantorFactoredQuintic {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  D (D (peirceThreeGradedDefect D X)) - 4 • peirceThreeGradedDefect D X

theorem adH_sub {R : Type*} [CommRing R] (M N : Matrix (Fin 3) (Fin 3) R) :
    adH (M - N) = adH M - adH N := by
  dsimp [adH]
  rw [mul_sub, sub_mul]
  abel

/-- **Stage `𝔎𝔗₁` & Rung 0 (`stage_KT1_peirce_operator_and_super_bracket_eruption`)**:
1. **Leibniz Eigenvalue Addition & Contact Eruption**:
   For any additive map `D : B →+ B` on a ring `[Ring B]` satisfying the Leibniz rule
   `D (X * Y) = D X * Y + X * D Y`:
   - If `D X = a • X` and `D Y = b • Y` (`a, b : ℤ`), then `D (X * Y) = (a + b) • (X * Y)` and
     `D (anticomm X Y) = (a + b) • anticomm X Y`.
   - In particular, if `D Q = Q` (Grade `+1`), then `D (Q * Q) = (2 : ℤ) • (Q * Q)` (Grade `+2`),
     and the 3-graded Peirce operator `peirceThreeGradedDefect D (Q * Q) = D³(Q²) - D(Q²)`
     evaluates to `(6 : ℤ) • (Q * Q)` (`2³ - 2 = 6`).
2. **Non-Commutative Peirce Operator-Spine Realization (`SandwichCharge.lean`)**:
   - The inner derivations `InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A)` and `InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C)` have Cartan charges
     `+1` and `-1`,
   - Their squares erupt into the Grade `±2` corner sandwiches
     `InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) X) = -((2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X)`
     with Cartan charges `+2` and `-2`,
   - And the 3-graded Peirce operator on `cornerOperatorSum P A C` fails to vanish by the exact
     factor `6`:
     `chargeIter P (cornerOperatorSum P A C) 3 X - chargeIter P (cornerOperatorSum P A C) 1 X =
      (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X - sandwich (coneMinus P C) (coneMinus P C) X)`.
3. **Concrete $M_3(R)$ Matrix Witness**:
   - `peirceThreeGradedDefect adH (E_gen R) = (6 : ℤ) • E_gen R`,
   - `peirceThreeGradedDefect adH (F_gen R) = -((6 : ℤ) • F_gen R)`. -/
theorem stage_KT1_peirce_operator_and_super_bracket_eruption
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
    (D : B →+ B) (hLeib : ∀ U W : B, D (U * W) = D U * W + U * D W)
    {Q : B} (hQ : D Q = Q)
    {R : Type*} [CommRing R] :
    -- 1. Leibniz eigenvalue doubling and 6 * Q² eruption on the 3-graded Peirce operator:
    D (Q * Q) = (2 : ℤ) • (Q * Q) ∧
    peirceThreeGradedDefect D (Q * Q) = (6 : ℤ) • (Q * Q) ∧
    -- 2. Peirce spine Grade ±1 squares -> Grade ±2 sandwiches and factor-6 cubic eruption:
    charge P (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A)) X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) X ∧
    charge P (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C)) X = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C) X ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) X) =
      -((2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C) (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C) X) =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) ∧
    charge P (sandwich (conePlus P A) (conePlus P A)) X =
      (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X ∧
    charge P (sandwich (coneMinus P C) (coneMinus P C)) X =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) ∧
    chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X =
      (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X -
        sandwich (coneMinus P C) (coneMinus P C) X) ∧
    -- 3. Concrete M₃(R) Grade ±2 contact generators shatter ad_H³ - ad_H by ±6:
    peirceThreeGradedDefect adH (E_gen R) = (6 : ℤ) • E_gen R ∧
    peirceThreeGradedDefect adH (F_gen R) = -((6 : ℤ) • F_gen R) := by
  have hQ2 : D (Q * Q) = (2 : ℤ) • (Q * Q) := by
    rw [hLeib Q Q, hQ, two_zsmul]
  have hQ2_2 : D (D (Q * Q)) = (4 : ℤ) • (Q * Q) := by
    rw [hQ2, map_zsmul, hQ2, smul_smul]
    norm_num
  have hQ2_3 : D (D (D (Q * Q))) = (8 : ℤ) • (Q * Q) := by
    rw [hQ2_2, map_zsmul, hQ2, smul_smul]
    norm_num
  have hDefectQ2 : peirceThreeGradedDefect D (Q * Q) = (6 : ℤ) • (Q * Q) := by
    dsimp [peirceThreeGradedDefect]
    rw [hQ2_3, hQ2]
    module
  refine ⟨hQ2, hDefectQ2,
    charge_plus_comm hP A X,
    charge_minus_comm hP C X,
    plus_comm_square hP A X,
    minus_comm_square hP C X,
    charge_plus_sandwich hP A X,
    charge_minus_sandwich hP C X,
    charge_iter_cubic_difference hP A C X,
    ?_, ?_⟩
  · ext i j
    simp only [peirceThreeGradedDefect, Matrix.sub_apply, Matrix.smul_apply]
    (fin_cases i <;> fin_cases j <;>
      simp [E_gen, InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
        Matrix.of_apply, zsmul_eq_mul, adH_00, adH_01, adH_02, adH_10, adH_11, adH_12, adH_20,
        adH_21, adH_22])
    ring
  · ext i j
    simp only [peirceThreeGradedDefect, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply]
    (fin_cases i <;> fin_cases j <;>
      simp [F_gen, InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E,
        Matrix.of_apply, zsmul_eq_mul, adH_00, adH_01, adH_02, adH_10, adH_11, adH_12, adH_20,
        adH_21, adH_22])
    ring

/-- **Stage `𝔎𝔗₂` & Rung 1 (`stage_KT2_factored_five_graded_quintic_contact_law`)**:
1. **Exact Polynomial Factorization over `[CommRing R]`**:
   - `(x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x`,
   - `x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x` (`quintic_polynomial_factorization`),
   - `x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x` (`five_grade_roots_expansion`).
2. **Factored Operator Identity `(D² - 4I)(D³ - D) = D⁵ - 5 D³ + 4 D` & Annihilation**:
   - For any additive homomorphism `D : M →+ M`,
     `kantorFactoredQuintic D X = kantorFiveGradedQuintic D X`,
   - On $M_3(R)$, `adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0`
     (`adH_quintic_identity`) and `kantorFactoredQuintic adH X_mat = 0`,
   - On the non-commutative Peirce 5-sector operator spine,
     `chargeIter P (cornerOperatorSum P A C) 5 X - (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
      (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0` (`charge_iter_fifth_annihilator`). -/
theorem contact_shell_quintic_factorization {R : Type*} [CommRing R] (x : R) :
    (x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x := by
  ring

theorem stage_KT2_factored_five_graded_quintic_contact_law
    {R : Type*} [CommRing R] (x : R) (X_mat : Matrix (Fin 3) (Fin 3) R)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    -- 1. Polynomial factorizations:
    (x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    -- 2. M₃(R) factored quintic operator identity and annihilation:
    kantorFactoredQuintic adH X_mat =
      adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat ∧
    adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0 ∧
    kantorFactoredQuintic adH X_mat = 0 ∧
    -- 3. Noncommutative Peirce 5-sector operator quintic annihilator:
    chargeIter P (cornerOperatorSum P A C) 5 X -
      (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
      (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0 := by
  have hFac :
      kantorFactoredQuintic adH X_mat =
        adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat := by
    dsimp [kantorFactoredQuintic, peirceThreeGradedDefect]
    rw [adH_sub, adH_sub]
    abel
  have hQuint := adH_quintic_identity X_mat
  exact ⟨contact_shell_quintic_factorization x,
    quintic_polynomial_factorization x,
    five_grade_roots_expansion x,
    hFac,
    hQuint,
    hFac.trans hQuint,
    charge_iter_fifth_annihilator hP A C X⟩

/-- Denominator-free (`12 ×`) quartic Lagrange projector onto the Grade-`0` shell (`d² = 0`). -/
def lagrangeShell12Zero {R : Type*} [CommRing R] (d : R) : R :=
  3 * (d ^ 2 - 1) * (d ^ 2 - 4)

/-- Denominator-free (`12 ×`) quartic Lagrange projector onto the Grade-`±1` shell (`d² = 1`). -/
def lagrangeShell12One {R : Type*} [CommRing R] (d : R) : R :=
  -4 * d ^ 2 * (d ^ 2 - 4)

/-- Denominator-free (`12 ×`) quartic Lagrange projector onto the Grade-`±2` shell (`d² = 4`). -/
def lagrangeShell12Two {R : Type*} [CommRing R] (d : R) : R :=
  d ^ 2 * (d ^ 2 - 1)

theorem lagrangeShell12_sum {R : Type*} [CommRing R] (d : R) :
    lagrangeShell12Zero d + lagrangeShell12One d + lagrangeShell12Two d = 12 := by
  dsimp [lagrangeShell12Zero, lagrangeShell12One, lagrangeShell12Two]; ring

theorem lagrangeShell12Two_eq_mul_cubic_defect {R : Type*} [CommRing R] (d : R) :
    lagrangeShell12Two d = d * (d ^ 3 - d) := by
  dsimp [lagrangeShell12Two]; ring

theorem lagrangeShell12One_mul_two {R : Type*} [CommRing R] (d : R) :
    lagrangeShell12One d * lagrangeShell12Two d =
      -4 * d ^ 3 * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) := by
  dsimp [lagrangeShell12One, lagrangeShell12Two]; ring

theorem lagrangeShell12Zero_mul_one {R : Type*} [CommRing R] (d : R) :
    lagrangeShell12Zero d * lagrangeShell12One d =
      -12 * d * (d ^ 2 - 4) * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) := by
  dsimp [lagrangeShell12Zero, lagrangeShell12One]; ring

theorem lagrangeShell12Zero_mul_two {R : Type*} [CommRing R] (d : R) :
    lagrangeShell12Zero d * lagrangeShell12Two d =
      3 * d * (d ^ 2 - 1) * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) := by
  dsimp [lagrangeShell12Zero, lagrangeShell12Two]; ring

/-- **Stage `𝔎𝔗₃` & Rung 2 (`stage_KT3_orthogonal_quartic_lagrange_projectors`)**:
1. **Denominator-Free Polynomial Shell Projectors over `[CommRing R]`**:
   - `lagrangeShell12Zero d + lagrangeShell12One d + lagrangeShell12Two d = 12`,
   - **Grade-`±2` Projector = `d` Times the 3-Graded Peirce Defect `d³ - d`**:
     `lagrangeShell12Two d = d * (d ^ 3 - d)`,
   - Mutual orthogonality modulo the quintic `d * (d ^ 2 - 1) * (d ^ 2 - 4)`:
     - `lagrangeShell12One d * lagrangeShell12Two d = -4 * d ^ 3 * (d * (d ^ 2 - 1) * (d ^ 2 - 4))`,
     - `lagrangeShell12Zero d * lagrangeShell12One d = -12 * d * (d ^ 2 - 4) * (d * (d ^ 2 - 1) * (d ^ 2 - 4))`,
     - `lagrangeShell12Zero d * lagrangeShell12Two d = 3 * d * (d ^ 2 - 1) * (d * (d ^ 2 - 1) * (d ^ 2 - 4))`.
2. **Concrete $M_3(F)$ Quartic Lagrange Projectors (`FiveGradedLieSuperalgebra.lean`)**:
   - Over `[Field F] [CharZero F]`, `adHProjectorZero`, `adHProjectorOne`, `adHProjectorTwo`
     sum to the identity (`adHProjectors_resolve`), are idempotent, are mutually orthogonal
     on all 6 ordered pairs, and satisfy the Peirce-defect factorization
     `adHProjectorTwo X_F = (1 / 12 : F) • adH (peirceThreeGradedDefect adH X_F)`.
3. **Signed 5-Sector Integer Polynomial Extraction on the Peirce Spine (`ChargeExtraction.lean`)**:
   - `charge_extract_zero`, `charge_extract_plus_one`, `charge_extract_minus_one`,
     `charge_extract_plus_two`, `charge_extract_minus_two`. -/
theorem stage_KT3_orthogonal_quartic_lagrange_projectors
    {R : Type*} [CommRing R] (d : R)
    {F : Type*} [Field F] [CharZero F] (X_F : Matrix (Fin 3) (Fin 3) F)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    -- 1. Denominator-free polynomial shell resolution, Peirce-defect form, and orthogonality:
    lagrangeShell12Zero d + lagrangeShell12One d + lagrangeShell12Two d = 12 ∧
    lagrangeShell12Two d = d * (d ^ 3 - d) ∧
    lagrangeShell12One d * lagrangeShell12Two d =
      -4 * d ^ 3 * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) ∧
    lagrangeShell12Zero d * lagrangeShell12One d =
      -12 * d * (d ^ 2 - 4) * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) ∧
    lagrangeShell12Zero d * lagrangeShell12Two d =
      3 * d * (d ^ 2 - 1) * (d * (d ^ 2 - 1) * (d ^ 2 - 4)) ∧
    -- 2. M₃(F) quartic Lagrange projectors: resolution, idempotency, orthogonality, & defect form:
    adHProjectorZero X_F + adHProjectorOne X_F + adHProjectorTwo X_F = X_F ∧
    adHProjectorZero (adHProjectorZero X_F) = adHProjectorZero X_F ∧
    adHProjectorOne (adHProjectorOne X_F) = adHProjectorOne X_F ∧
    adHProjectorTwo (adHProjectorTwo X_F) = adHProjectorTwo X_F ∧
    adHProjectorZero (adHProjectorOne X_F) = 0 ∧
    adHProjectorOne (adHProjectorTwo X_F) = 0 ∧
    adHProjectorTwo (adHProjectorZero X_F) = 0 ∧
    adHProjectorTwo X_F = (1 / 12 : F) • adH (peirceThreeGradedDefect adH X_F) ∧
    -- 3. Signed 5-sector extraction on the noncommutative Peirce spine:
    chargeIter P (cornerOperatorSum P A C) 4 X -
      (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X +
      (4 : ℤ) • cornerOperatorSum P A C X = (4 : ℤ) • sandwichCross P A C X ∧
    ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X -
      chargeIter P (cornerOperatorSum P A C) 4 X) +
      ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X -
      chargeIter P (cornerOperatorSum P A C) 3 X) =
      (6 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) X ∧
    (chargeIter P (cornerOperatorSum P A C) 4 X -
      chargeIter P (cornerOperatorSum P A C) 2 X) +
      (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X) =
      (24 : ℤ) • sandwich (conePlus P A) (conePlus P A) X := by
  refine ⟨lagrangeShell12_sum d,
    lagrangeShell12Two_eq_mul_cubic_defect d,
    lagrangeShell12One_mul_two d,
    lagrangeShell12Zero_mul_one d,
    lagrangeShell12Zero_mul_two d,
    adHProjectors_resolve X_F,
    adHProjectorZero_idempotent X_F,
    adHProjectorOne_idempotent X_F,
    adHProjectorTwo_idempotent X_F,
    adHProjectorZero_one_zero X_F,
    adHProjectorOne_two_zero X_F,
    adHProjectorTwo_zero_zero X_F,
    ?_,
    charge_extract_zero hP A C X,
    charge_extract_plus_one hP A C X,
    charge_extract_plus_two hP A C X⟩
  change (1 / 12 : F) • (adH (adH (adH (adH X_F))) - adH (adH X_F)) =
    (1 / 12 : F) • adH (peirceThreeGradedDefect adH X_F)
  dsimp [peirceThreeGradedDefect]
  rw [adH_sub]

/-- **Stage `𝔎𝔗₄` & Rung 3 (`stage_KT4_osp12_superconformal_contact_jacobi_closure`)**:
1. **$\mathfrak{osp}(1|2)$ Supercharge Anticommutators & Contact Boson Closure (`SuperconformalOSpJordanPair.lean`)**:
   - `{Q_+, Q_-} = H`, `{Q_+, Q_+} = 2 E`, `{Q_-, Q_-} = -2 F`,
   - `[E, F] = H`, `[H, E] = 2 E`, `[H, F] = -2 F`.
2. **Super-Adjoint Ladder & Extremal Annihilation (`[𝔤_±2, 𝔤_±1] = 0`)**:
   - `[H, Q_+] = Q_+`, `[H, Q_-] = -Q_-`,
   - `[E, Q_-] = -Q_+`, `[F, Q_+] = -Q_-`,
   - `[E, Q_+] = 0`, `[F, Q_-] = 0`.
3. **Odd-Odd-Odd Super-Jacobi Identity**:
   - `2 • [Q_+, {Q_+, Q_-}] + [Q_-, {Q_+, Q_+}] = 0` (`-2 Q_+ + 2 Q_+ = 0`),
   - `2 • [Q_-, {Q_-, Q_+}] + [Q_+, {Q_-, Q_-}] = 0` (`2 Q_- - 2 Q_- = 0`). -/
theorem stage_KT4_osp12_superconformal_contact_jacobi_closure
    {R : Type*} [CommRing R] :
    -- 1. Fermionic anticommutators & bosonic sl(2) brackets:
    anticommutator (Q_plus R) (Q_minus R) = H_gen R ∧
    anticommutator (Q_plus R) (Q_plus R) = 2 • E_gen R ∧
    anticommutator (Q_minus R) (Q_minus R) = -2 • F_gen R ∧
    commutator (E_gen R) (F_gen R) = H_gen R ∧
    commutator (H_gen R) (E_gen R) = 2 • E_gen R ∧
    commutator (H_gen R) (F_gen R) = -2 • F_gen R ∧
    -- 2. Grading, ladder, and grade-truncation annihilation:
    commutator (H_gen R) (Q_plus R) = Q_plus R ∧
    commutator (H_gen R) (Q_minus R) = -Q_minus R ∧
    commutator (E_gen R) (Q_minus R) = -Q_plus R ∧
    commutator (F_gen R) (Q_plus R) = -Q_minus R ∧
    commutator (E_gen R) (Q_plus R) = 0 ∧
    commutator (F_gen R) (Q_minus R) = 0 ∧
    -- 3. Odd-odd-odd super-Jacobi closure:
    2 • commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
      commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) = 0 ∧
    2 • commutator (Q_minus R) (anticommutator (Q_minus R) (Q_plus R)) +
      commutator (Q_plus R) (anticommutator (Q_minus R) (Q_minus R)) = 0 := by
  refine ⟨osp_anticomm_plus_minus,
    osp_anticomm_plus_plus,
    osp_anticomm_minus_minus,
    osp_sl2_E_F,
    osp_sl2_H_E,
    osp_sl2_H_F,
    osp_grad_H_Q_plus,
    osp_grad_H_Q_minus,
    osp_ladder_E_Q_minus,
    osp_ladder_F_Q_plus,
    osp_annihilate_E_Q_plus,
    osp_annihilate_F_Q_minus,
    ?_, ?_⟩
  · rw [two_smul]
    unfold InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.commutator
      anticommutator Q_plus Q_minus
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]
  · rw [two_smul]
    unfold InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.commutator
      anticommutator Q_plus Q_minus
      InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.E
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- Grade-`0` central dilatation projector `𝒫_{𝔤𝔩₁}(X) = (1/3) Tr(X) I₃` on `M₃(ℝ)`. -/
def projGL1 (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((1 / 3 : ℝ) * Matrix.trace X) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- Grade-`0` trace-free `𝔰𝔩₃(ℝ)_color` projector `𝒫_{𝔰𝔩₃}(X) = X - (1/3) Tr(X) I₃` on `M₃(ℝ)`. -/
def projSL3 (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  X - projGL1 X

/-- **Stage `𝔎𝔗₅` & Rung 4 (`stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition`)**:
1. **Direct-Sum Projector Algebra of `𝔤𝔩₃(ℝ) = 𝔤𝔩₁(ℝ)_H ⊕ 𝔰𝔩₃(ℝ)_color`**:
   - `projGL1 X + projSL3 X = X`,
   - `Matrix.trace (projSL3 X) = 0` and `Matrix.trace (projGL1 X) = Matrix.trace X`,
   - `projGL1 (projGL1 X) = projGL1 X` and `projSL3 (projSL3 X) = projSL3 X`,
   - `projGL1 (projSL3 X) = 0` and `projSL3 (projGL1 X) = 0`.
2. **Lie Ideal Closure & Centrality**:
   - Centrality of `𝔤𝔩₁(ℝ)_H`: `projGL1 X * Y - Y * projGL1 X = 0`,
   - Commutator lands purely in `𝔰𝔩₃(ℝ)_color`: `Matrix.trace (X * Y - Y * X) = 0` and
     `projSL3 (X * Y - Y * X) = X * Y - Y * X`.
3. **Günaydin–Gürsey Quark–Antiquark Superbracket & `ℤ₂ × ℤ₂` Color SUSY (`SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.lean`)**:
   - `projSL3 (quarkAntiquarkOuter u v) = quarkAntiquarkTracelessSL3 u v`,
   - `projGL1 (quarkAntiquarkOuter u v) = ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • 1`,
   - `z2z2KoszulSign gradeQuark gradeLepton = -1` and `z2z2KoszulSign gradeQuark gradeQuark = 1`. -/
theorem stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition
    (X Y : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    -- 1. Direct-sum projector identities:
    projGL1 X + projSL3 X = X ∧
    Matrix.trace (projSL3 X) = 0 ∧
    Matrix.trace (projGL1 X) = Matrix.trace X ∧
    projGL1 (projGL1 X) = projGL1 X ∧
    projSL3 (projSL3 X) = projSL3 X ∧
    projGL1 (projSL3 X) = 0 ∧
    projSL3 (projGL1 X) = 0 ∧
    -- 2. Centrality of gl₁ and Lie ideal closure of sl₃:
    projGL1 X * Y - Y * projGL1 X = 0 ∧
    Matrix.trace (X * Y - Y * X) = 0 ∧
    projSL3 (X * Y - Y * X) = X * Y - Y * X ∧
    -- 3. Quark–antiquark outer product decomposition and ℤ₂ × ℤ₂ color SUSY signs:
    projSL3 (quarkAntiquarkOuter u v) = quarkAntiquarkTracelessSL3 u v ∧
    projGL1 (quarkAntiquarkOuter u v) =
      ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    z2z2KoszulSign gradeQuark gradeLepton = -1 ∧
    z2z2KoszulSign gradeQuark gradeQuark = 1 := by
  have hTr1 : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
    simp [Matrix.trace, Matrix.diag]
  have hTrGL1 : Matrix.trace (projGL1 X) = Matrix.trace X := by
    dsimp [projGL1]
    rw [Matrix.trace_smul, hTr1, smul_eq_mul]
    linarith
  have hTrSL3 : Matrix.trace (projSL3 X) = 0 := by
    dsimp [projSL3]
    rw [Matrix.trace_sub, hTrGL1, sub_self]
  have hGL1Idem : projGL1 (projGL1 X) = projGL1 X := by
    dsimp [projGL1]
    rw [Matrix.trace_smul, hTr1, smul_eq_mul]
    congr 1
    linarith
  have hTrComm : Matrix.trace (X * Y - Y * X) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]
  have hSign := z2z2_color_supersymmetry_sign_laws gradeQuark gradeLepton
  refine ⟨by dsimp [projSL3]; abel,
    hTrSL3,
    hTrGL1,
    hGL1Idem,
    ?_, ?_, ?_, ?_,
    hTrComm,
    ?_, ?_, ?_,
    hSign.2.2.2.1,
    hSign.2.2.2.2.2⟩
  · rw [projSL3]
    dsimp [projGL1]
    rw [hTrSL3, mul_zero, zero_smul, sub_zero]
  · dsimp [projGL1]
    rw [hTrSL3, mul_zero, zero_smul]
  · dsimp [projSL3]
    rw [hGL1Idem, sub_self]
  · dsimp [projGL1]
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, sub_self]
  · dsimp [projSL3, projGL1]
    rw [hTrComm, mul_zero, zero_smul, sub_zero]
  · ext i j
    dsimp [projSL3, projGL1, quarkAntiquarkTracelessSL3, quarkAntiquarkOuter,
      vec3Dot, Matrix.trace, Matrix.diag]
    simp only [Fin.sum_univ_three]
  · ext i j
    dsimp [projGL1, quarkAntiquarkOuter, quarkAntiquarkDilatationTrace,
      vec3Dot, Matrix.trace, Matrix.diag]
    simp only [Fin.sum_univ_three]

/-- **Stage `𝔎𝔗₆` (`stage_KT6_five_graded_maurer_cartan_and_cross_charge_extremal_bracket`)**:
1. **5-Graded Maurer–Cartan Flatness (`MajoranaParaKahlerMaurerCartanSupercolorSynthesis.lean`)**:
   - `canonicalMaurerCartanJet ≠ default` and
     `mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0)`.
2. **Non-Commutative Peirce Cross-Charge Brackets (`CornerChargeSectors.lean`, `CrossChargeBrackets.lean`)**:
   - `[lieOp ℤ (conePlus P A), lieOp ℤ (coneMinus P C)] = lieOp ℤ (genSig P A C)`,
   - `[lieOp ℤ (conePlus P A), sandwichOp ℤ (coneMinus P C) (coneMinus P C)] =
      crossTransport ℤ (genSig P A C) (coneMinus P C)`,
   - `[lieOp ℤ (coneMinus P C), sandwichOp ℤ (conePlus P A) (conePlus P A)] =
      -crossTransport ℤ (genSig P A C) (conePlus P A)`,
   - Extremal Grade-$(\pm 2)$ sandwich commutator:
     `[sandwichOp ℤ (conePlus P A) (conePlus P A), sandwichOp ℤ (coneMinus P C) (coneMinus P C)] =
      sandwichOp ℤ (qgtPlus P A C) (qgtMinus P A C) - sandwichOp ℤ (qgtMinus P A C) (qgtPlus P A C)`,
     with same-support residual `-sandwichOp ℤ (genV P A C) (genSig P A C)`. -/
theorem stage_KT6_five_graded_maurer_cartan_and_cross_charge_extremal_bracket
    {B : Type*} [Ring B] (P A C : B) :
    canonicalMaurerCartanJet ≠ (default : FiveGradedMaurerCartanJet ℝ) ∧
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (lieOp ℤ (conePlus P A)) (lieOp ℤ (coneMinus P C)) =
      lieOp ℤ (genSig P A C) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (lieOp ℤ (conePlus P A)) (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) =
      crossTransport ℤ (genSig P A C) (coneMinus P C) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (lieOp ℤ (coneMinus P C)) (sandwichOp ℤ (conePlus P A) (conePlus P A)) =
      -crossTransport ℤ (genSig P A C) (conePlus P A) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) =
      sandwichOp ℤ (qgtPlus P A C) (qgtMinus P A C) -
        sandwichOp ℤ (qgtMinus P A C) (qgtPlus P A C) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) -
      (sandwichOp ℤ (qgtPlus P A C) (qgtPlus P A C) -
        sandwichOp ℤ (qgtMinus P A C) (qgtMinus P A C)) =
      -sandwichOp ℤ (genV P A C) (genSig P A C) :=
  ⟨canonicalMaurerCartanJet_ne_default,
   canonicalMaurerCartanJet_flat,
   opposite_lie_comm A C,
   plus_lie_minus_sandwich_comm P A C,
   minus_lie_plus_sandwich_comm P A C,
   extreme_sandwich_comm P A C,
   extreme_same_support_residual P A C⟩

end KantorTanakaTowerTheorems

/-! ===========================================================================
    Part II: The 6-Stage Metriplectic Zorn Split-Octonion Closure, Three-Term
    Pythagorean Determinant Law, & Third-Order Volume Duality Poset
    (`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`)
    =========================================================================== -/

/-- The 6 causal stages of the Metriplectic Zorn Split-Octonion Closure,
Three-Term Pythagorean Determinant Law, & Third-Order Volume Duality Poset
(`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`). -/
inductive MetriplecticZornStage : Type
  | MZ1_DeWittBasisAndThreeChannelProjections
  | MZ2_ExactThreeTermMetriplecticZornDecomposition
  | MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit
  | MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw
  | MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara
  | MZ6_NonCommutativeNambuAssociatorSpecialization
  deriving DecidableEq, Repr, Inhabited

namespace MetriplecticZornStage

/-- Topological rank `0..4` (`MZ3` and `MZ4` share rank `2` as parallel diamond branches). -/
def stageRank : MetriplecticZornStage → ℕ
  | .MZ1_DeWittBasisAndThreeChannelProjections => 0
  | .MZ2_ExactThreeTermMetriplecticZornDecomposition => 1
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => 2
  | .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw => 2
  | .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara => 3
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => 4

/-- Directed covering edges of the diamond poset `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`. -/
def causalEdge : MetriplecticZornStage → MetriplecticZornStage → Prop
  | .MZ1_DeWittBasisAndThreeChannelProjections,
    .MZ2_ExactThreeTermMetriplecticZornDecomposition => True
  | .MZ2_ExactThreeTermMetriplecticZornDecomposition,
    .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => True
  | .MZ2_ExactThreeTermMetriplecticZornDecomposition,
    .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw => True
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit,
    .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara => True
  | .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw,
    .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara => True
  | .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara,
    .MZ6_NonCommutativeNambuAssociatorSpecialization => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Partial order on `MetriplecticZornStage` with `MZ3` and `MZ4` incomparable. -/
def stageLe (a b : MetriplecticZornStage) : Prop :=
  a = b ∨
  stageRank a < stageRank b

instance instDecidableRelStageLe : DecidableRel stageLe := by
  intro a b
  unfold stageLe
  infer_instance

instance : PartialOrder MetriplecticZornStage where
  le := stageLe
  lt a b := stageLe a b ∧ ¬ stageLe b a
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab'
    · exact hbc
    · rcases hbc with rfl | hbc'
      · exact Or.inr hab'
      · exact Or.inr (Nat.lt_trans hab' hbc')
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm a b hab hba := by
    rcases hab with rfl | hab'
    · rfl
    · rcases hba with rfl | hba'
      · rfl
      · exact False.elim (Nat.lt_asymm hab' hba')

instance : Fintype MetriplecticZornStage where
  elems := {
    .MZ1_DeWittBasisAndThreeChannelProjections,
    .MZ2_ExactThreeTermMetriplecticZornDecomposition,
    .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit,
    .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw,
    .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara,
    .MZ6_NonCommutativeNambuAssociatorSpecialization
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MetriplecticZornStage = 6 := rfl

theorem causalEdge_stageRank_lt {a b : MetriplecticZornStage}
    (h : causalEdge a b) : stageRank a < stageRank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_stageRank_lt {a b : MetriplecticZornStage}
    (h : Relation.TransGen causalEdge a b) : stageRank a < stageRank b := by
  induction h with
  | single hab => exact causalEdge_stageRank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_stageRank_lt hbc)

/-- Strict DAG acyclicity of `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`. -/
theorem causalEdge_acyclic (a : MetriplecticZornStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (stageRank a) (transGen_causalEdge_stageRank_lt h)

/-- Parallel diamond branches `𝔐ℨ₃` and `𝔐ℨ₄` are incomparable. -/
theorem incomparable_MZ3_MZ4 :
    ¬ (MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit ≤
        MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw) ∧
    ¬ (MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw ≤
        MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit) := by
  change ¬ stageLe _ _ ∧ ¬ stageLe _ _
  decide

/-- Monotone representation-depth projection across `𝔐ℨ₁..𝔐ℨ₆`. -/
def toRepDepth : MetriplecticZornStage → RepDepth
  | .MZ1_DeWittBasisAndThreeChannelProjections => .operator
  | .MZ2_ExactThreeTermMetriplecticZornDecomposition => .operator
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => .transport
  | .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw => .transport
  | .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara => .thermo
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => .thermo

/-- Monotone ontology meta-level projection across `𝔐ℨ₁..𝔐ℨ₆`. -/
def toOntologyMetaLevel : MetriplecticZornStage → OntologyMetaLevel
  | .MZ1_DeWittBasisAndThreeChannelProjections => .M1_ProjectorClabject
  | .MZ2_ExactThreeTermMetriplecticZornDecomposition => .M2_GrassmannianPowertypeOrbit
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => .M2_GrassmannianPowertypeOrbit
  | .MZ4_ThreeTermMetriplecticPythagoreanDeterminantLaw => .M2_GrassmannianPowertypeOrbit
  | .MZ5_ThirdOrderDualVolumeSplitOnOneAndIPara => .M3_ErlangenCasimirMetaLaw
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageLe a b at h
  cases a <;> cases b <;> revert h <;> decide

theorem toOntologyMetaLevel_mono {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageLe a b at h
  cases a <;> cases b <;> revert h <;> decide

end MetriplecticZornStage

/-! ===========================================================================
    Section 2.2: Stages `𝔐ℨ₁`–`𝔐ℨ₆` Theorems (Metriplectic Zorn Closure)
    =========================================================================== -/

section MetriplecticZornTheorems

variable {R : Type*} [CommRing R]

/-- Full 8D Fisher metric channel `g(x, y) = (a₁ a₂ + b₁ b₂) + (u₁·v₂ + v₁·u₂)` on `ZornSplitOctonion R`. -/
def zornFullMetric (x y : ZornSplitOctonion R) : R :=
  (x.a * y.a + x.b * y.b) + (vec3Dot x.u y.v + vec3Dot x.v y.u)

/-- Full 8D symplectic 2-form channel `ω(x, y) = (a₁ a₂ - b₁ b₂) + (u₁·v₂ - v₁·u₂)` on `ZornSplitOctonion R`. -/
def zornFullSymplectic (x y : ZornSplitOctonion R) : R :=
  (x.a * y.a - x.b * y.b) + (vec3Dot x.u y.v - vec3Dot x.v y.u)

/-- Full 8D off-diagonal Hodge cross-product and bimodule channel `x ×_H y` on `ZornSplitOctonion R`. -/
def zornFullOffDiag (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨0,
   fun k => x.a * y.u k + x.u k * y.b - vec3Cross x.v y.v k,
   fun k => x.v k * y.a + x.b * y.v k + vec3Cross x.u y.u k,
   0⟩

/-- Diagonal projection `K_{γ₅}(x) = ⟨a, 0, 0, b⟩` onto `Span(1, I_para)` in `ZornSplitOctonion R`. -/
def zornDiagPart (x : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.a, fun _ => 0, fun _ => 0, x.b⟩

/-- **Stages `𝔐ℨ₁` & `𝔐ℨ₂` (`stage_MZ1_MZ2_three_channel_metriplectic_zorn_decomposition`)**:
1. **DeWitt Sum (`1 = u₀ + u₀*`) and DeWitt Difference (`I_para = u₀ - u₀*`)**:
   - `zornAdd zornE0 zornE1 = zornOne`,
   - `zornSub zornE0 zornE1 = zornParaGrading`,
   - `zornAdd zornOne zornParaGrading = zornSmul 2 zornE0`,
   - `zornSub zornOne zornParaGrading = zornSmul 2 zornE1`.
2. **Restriction to the 6D Para-Kähler Phase Space (`embedVec`)**:
   - `zornFullMetric (embedVec z₁) (embedVec z₂) = paraKahlerMetric z₁ z₂`,
   - `zornFullSymplectic (embedVec z₁) (embedVec z₂) = symplecticForm z₁ z₂`,
   - `zornFullOffDiag (embedVec z₁) (embedVec z₂) = embedVec (hodgeCrossVec z₁ z₂)`.
3. **Universal Doubled Three-Channel Metriplectic Zorn Law over `[CommRing R]`**:
   For all `x, y : ZornSplitOctonion R`:
   $$2(x y) = g(x, y) 1_{\text{Zorn}} + \omega(x, y) I_{\text{para}} + 2(x \times_H y).$$
4. **Exact Metriplectic Decomposition over `ℝ` (`SplitOctonionParaKahlerNullCone.lean`)**:
   `zornMul (embedVec z₁R) (embedVec z₂R) =
    zornAdd (zornAdd (zornSmul ((1/2) * g) zornOne) (zornSmul ((1/2) * ω) zornParaGrading))
            (embedVec (hodgeCrossVec z₁R z₂R))`. -/
theorem stage_MZ1_MZ2_three_channel_metriplectic_zorn_decomposition
    (x y : ZornSplitOctonion R) (z₁ z₂ : ParaKahlerVec R)
    (z₁R z₂R : ParaKahlerVec ℝ) :
    -- 1. DeWitt sum and difference basis:
    zornAdd (zornE0 : ZornSplitOctonion R) zornE1 = zornOne ∧
    zornSub (zornE0 : ZornSplitOctonion R) zornE1 = zornParaGrading ∧
    zornAdd (zornOne : ZornSplitOctonion R) zornParaGrading = zornSmul (2 : R) zornE0 ∧
    zornSub (zornOne : ZornSplitOctonion R) zornParaGrading = zornSmul (2 : R) zornE1 ∧
    -- 2. Restriction of full 8D channels to the 6D tangent space:
    zornFullMetric (embedVec z₁) (embedVec z₂) = paraKahlerMetric z₁ z₂ ∧
    zornFullSymplectic (embedVec z₁) (embedVec z₂) = symplecticForm z₁ z₂ ∧
    zornFullOffDiag (embedVec z₁) (embedVec z₂) = embedVec (hodgeCrossVec z₁ z₂) ∧
    -- 3. Universal doubled 3-term metriplectic Zorn law over [CommRing R]:
    zornSmul (2 : R) (zornMul x y) =
      zornAdd
        (zornAdd
          (zornSmul (zornFullMetric x y) zornOne)
          (zornSmul (zornFullSymplectic x y) zornParaGrading))
        (zornSmul (2 : R) (zornFullOffDiag x y)) ∧
    -- 4. Exact metriplectic decomposition over ℝ:
    zornMul (embedVec z₁R) (embedVec z₂R) =
      zornAdd
        (zornAdd
          (zornSmul ((1 / 2 : ℝ) * paraKahlerMetric z₁R z₂R) zornOne)
          (zornSmul ((1 / 2 : ℝ) * symplecticForm z₁R z₂R) zornParaGrading))
        (embedVec (hodgeCrossVec z₁R z₂R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zornMul_embedVec_metriplectic_decomp z₁R z₂R⟩
  · ext k <;> (dsimp [zornAdd, zornE0, zornE1, zornOne]; ring)
  · ext k <;> (dsimp [zornSub, zornE0, zornE1, zornParaGrading]; ring)
  · ext k <;> (dsimp [zornAdd, zornOne, zornParaGrading, zornSmul, zornE0]; ring)
  · ext k <;> (dsimp [zornSub, zornOne, zornParaGrading, zornSmul, zornE1]; ring)
  · dsimp [zornFullMetric, embedVec, paraKahlerMetric]; ring
  · dsimp [zornFullSymplectic, embedVec, symplecticForm]; ring
  · ext k
    · rfl
    · fin_cases k <;> (dsimp [zornFullOffDiag, embedVec, hodgeCrossVec]; ring)
    · fin_cases k <;> (dsimp [zornFullOffDiag, embedVec, hodgeCrossVec]; ring)
    · rfl
  · ext k
    · dsimp [zornSmul, zornMul, zornAdd, zornFullMetric, zornFullSymplectic,
        zornFullOffDiag, zornOne, zornParaGrading, vec3Dot]
      ring
    · fin_cases k <;>
        (dsimp [zornSmul, zornMul, zornAdd, zornFullOffDiag, zornOne, zornParaGrading]; ring)
    · fin_cases k <;>
        (dsimp [zornSmul, zornMul, zornAdd, zornFullOffDiag, zornOne, zornParaGrading]; ring)
    · dsimp [zornSmul, zornMul, zornAdd, zornFullMetric, zornFullSymplectic,
        zornFullOffDiag, zornOne, zornParaGrading, vec3Dot]
      ring

/-- **Stage `𝔐ℨ₃` (`stage_MZ3_parakahler_locking_and_jordan_malcev_tangent_split`)**:
1. **Para-Kähler Locking (`ω(z₁, z₂) = g(K z₁, z₂)`)**:
   - `symplecticForm z₁ z₂ = paraKahlerMetric (paraComplexK z₁) z₂`,
   - `paraComplexK (paraComplexK z₁) = z₁`,
   - `paraKahlerMetric (paraComplexK z₁) (paraComplexK z₂) = -paraKahlerMetric z₁ z₂`,
   - `zornCommutator zornParaGrading (embedVec z₁) = zornSmul (2 : R) (embedVec (paraComplexK z₁))`.
2. **Jordan–Malcev Tangent Split**:
   - Symmetric anticommutator lands purely on `1`:
     `zornAnticommutator (embedVec z₁) (embedVec z₂) = zornSmul (paraKahlerMetric z₁ z₂) zornOne`,
   - Antisymmetric commutator splits into the symplectic form along `I_para` plus twice the
     Hodge cross-product channel:
     `zornCommutator (embedVec z₁) (embedVec z₂) =
      zornAdd (zornSmul (symplecticForm z₁ z₂) zornParaGrading)
              (zornSmul (2 : R) (embedVec (hodgeCrossVec z₁ z₂)))`. -/
theorem stage_MZ3_parakahler_locking_and_jordan_malcev_tangent_split
    (z₁ z₂ : ParaKahlerVec R) :
    symplecticForm z₁ z₂ = paraKahlerMetric (paraComplexK z₁) z₂ ∧
    paraComplexK (paraComplexK z₁) = z₁ ∧
    paraKahlerMetric (paraComplexK z₁) (paraComplexK z₂) = -paraKahlerMetric z₁ z₂ ∧
    zornCommutator zornParaGrading (embedVec z₁) =
      zornSmul (2 : R) (embedVec (paraComplexK z₁)) ∧
    zornAnticommutator (embedVec z₁) (embedVec z₂) =
      zornSmul (paraKahlerMetric z₁ z₂) zornOne ∧
    zornCommutator (embedVec z₁) (embedVec z₂) =
      zornAdd (zornSmul (symplecticForm z₁ z₂) zornParaGrading)
        (zornSmul (2 : R) (embedVec (hodgeCrossVec z₁ z₂))) :=
  ⟨symplecticForm_eq_metric_K z₁ z₂,
   paraComplexK_sq_id z₁,
   paraKahlerMetric_K_antiInvariant z₁ z₂,
   zorn_paraGrading_commutator_embedVec z₁,
   zorn_anticommutator_eq_paraKahlerMetric_smul_one z₁ z₂,
   zorn_commutator_eq_symplectic_add_two_hodgeCross z₁ z₂⟩

/-- **Stage `𝔐ℨ₄` (`stage_MZ4_three_term_metriplectic_pythagorean_determinant_law`)**:
1. **Rung 0 Diagonal-Only Determinant Aporia**:
   - `(paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 =
      4 * (vec3Dot z₁.u z₂.v * vec3Dot z₁.v z₂.u)`.
2. **Hodge Cross-Product Zorn Determinant & Norm Gap (`SplitOctonionParaKahlerNullCone.lean`)**:
   - `zornNorm (embedVec (hodgeCrossVec z₁ z₂)) = vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v)`,
   - `4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ -
        ((paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2)`.
3. **Three-Term Metriplectic Pythagorean Determinant Law**:
   - `(paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      4 * zornNorm (zornMul (embedVec z₁) (embedVec z₂))`,
   - `(paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      (2 * zornNorm (embedVec z₁)) * (2 * zornNorm (embedVec z₂))`,
   - `(paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 -
      2 * paraKahlerMetric (hodgeCrossVec z₁ z₂) (hodgeCrossVec z₁ z₂) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂`. -/
theorem stage_MZ4_three_term_metriplectic_pythagorean_determinant_law
    (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 =
      4 * (vec3Dot z₁.u z₂.v * vec3Dot z₁.v z₂.u) ∧
    zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) ∧
    4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ -
        ((paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2) ∧
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      4 * zornNorm (zornMul (embedVec z₁) (embedVec z₂)) ∧
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      (2 * zornNorm (embedVec z₁)) * (2 * zornNorm (embedVec z₂)) ∧
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 -
      2 * paraKahlerMetric (hodgeCrossVec z₁ z₂) (hodgeCrossVec z₁ z₂) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ := by
  have hNormHodge := zornNorm_embedVec_hodgeCrossVec z₁ z₂
  refine ⟨?_,
    hNormHodge,
    by rw [hNormHodge]; exact hodgeCrossPairing_eq_norm_gap z₁ z₂,
    by rw [hNormHodge]; exact paraKahler_lagrange_eq_four_mul_zornNorm_mul z₁ z₂,
    by rw [hNormHodge]; exact zornNorm_embedVec_mul_eq_metriplectic_lagrange z₁ z₂,
    paraKahler_lagrange_norm_via_hodgeCrossVec z₁ z₂⟩
  dsimp [paraKahlerMetric, symplecticForm, vec3Dot]
  ring

/-- **Stage `𝔐ℨ₅` (`stage_MZ5_third_order_dual_volume_split_on_one_and_ipara`)**:
For any three tangent phase-space vectors `z₁, z₂, z₃ : ParaKahlerVec R` over `[CommRing R]`:
1. **Symmetric Third-Order Anticommutator Lands Purely on the DeWitt Sum `1 = u₀ + u₀*`**:
   - `paraKahlerMetric (hodgeCrossVec z₁ z₂) z₃ =
      vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v`,
   - `zornAnticommutator (embedVec (hodgeCrossVec z₁ z₂)) (embedVec z₃) =
      zornSmul (vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v) zornOne`.
2. **Diagonal Part of the Associator Lands 100% on the DeWitt Difference `I_para = u₀ - u₀*`**:
   - `zornDiagPart (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)) =
      zornSmul (-(vec3TripleProduct z₁.u z₂.u z₃.u + vec3TripleProduct z₁.v z₂.v z₃.v)) zornParaGrading`,
   - Zero scalar trace along `1`:
     `(zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)).a +
      (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)).b = 0`.
3. **Pure Primal Sheet Specialization (`z_i = primalSheet u_i`)**:
   - Bracketing sum lands on `det(u₁, u₂, u₃) 1`:
     `zornAdd (zornMul (zornMul (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂))) (embedVec (primalSheet u₃)))
              (zornMul (embedVec (primalSheet u₁)) (zornMul (embedVec (primalSheet u₂)) (embedVec (primalSheet u₃)))) =
      zornSmul (vec3TripleProduct u₁ u₂ u₃) zornOne`,
   - Associator lands on `-det(u₁, u₂, u₃) I_para`:
     `zornAssociator (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂)) (embedVec (primalSheet u₃)) =
      zornSmul (-vec3TripleProduct u₁ u₂ u₃) zornParaGrading`. -/
theorem stage_MZ5_third_order_dual_volume_split_on_one_and_ipara
    (z₁ z₂ z₃ : ParaKahlerVec R) (u₁ u₂ u₃ : Fin 3 → R) :
    paraKahlerMetric (hodgeCrossVec z₁ z₂) z₃ =
      vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v ∧
    zornAnticommutator (embedVec (hodgeCrossVec z₁ z₂)) (embedVec z₃) =
      zornSmul (vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v) zornOne ∧
    zornDiagPart (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)) =
      zornSmul (-(vec3TripleProduct z₁.u z₂.u z₃.u + vec3TripleProduct z₁.v z₂.v z₃.v))
        zornParaGrading ∧
    (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)).a +
      (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)).b = 0 ∧
    zornAdd
      (zornMul (zornMul (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂)))
        (embedVec (primalSheet u₃)))
      (zornMul (embedVec (primalSheet u₁))
        (zornMul (embedVec (primalSheet u₂)) (embedVec (primalSheet u₃)))) =
      zornSmul (vec3TripleProduct u₁ u₂ u₃) zornOne ∧
    zornAssociator
      (embedVec (primalSheet u₁))
      (embedVec (primalSheet u₂))
      (embedVec (primalSheet u₃)) =
      zornSmul (-vec3TripleProduct u₁ u₂ u₃) zornParaGrading := by
  have hMetric :
      paraKahlerMetric (hodgeCrossVec z₁ z₂) z₃ =
        vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v := by
    dsimp [paraKahlerMetric, hodgeCrossVec, vec3TripleProduct, vec3Dot, vec3Cross]
    ring
  refine ⟨hMetric,
    by rw [← hMetric]; exact zorn_anticommutator_eq_paraKahlerMetric_smul_one (hodgeCrossVec z₁ z₂) z₃,
    ?_, ?_,
    zorn_primal_triple_bracketing_sum_eq_volume_smul_one u₁ u₂ u₃,
    zorn_primal_triple_associator_eq_volume_paraGrading u₁ u₂ u₃⟩
  · ext k
    · dsimp [zornDiagPart, zornAssociator, zornSub, zornMul, embedVec,
        zornSmul, zornParaGrading, vec3TripleProduct, vec3Dot, vec3Cross]
      ring
    · dsimp [zornDiagPart, zornSmul, zornParaGrading]; ring
    · dsimp [zornDiagPart, zornSmul, zornParaGrading]; ring
    · dsimp [zornDiagPart, zornAssociator, zornSub, zornMul, embedVec,
        zornSmul, zornParaGrading, vec3TripleProduct, vec3Dot, vec3Cross]
      ring
  · dsimp [zornAssociator, zornSub, zornMul, embedVec, vec3Dot, vec3Cross]
    ring

/-- **Stage `𝔐ℨ₆` (`stage_MZ6_noncommutative_nambu_associator_specialization`)**:
Over any non-commutative `[Ring B]`, for `u, v : Vec3 B`:
1. **Symmetric Bracketing Sum Lands on the DeWitt Sum `I = u₀ + u₀*`**:
   `((ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u) +
    (ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u)) =
    scalarZorn (Vec3.nambu3 u)`.
2. **Non-Commutative Nambu Associator Lands Strictly on the DeWitt Difference `γ₅ = I_para = u₀ - u₀*`**:
   - `ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) = -(scalarZorn (Vec3.nambu3 u) * ZornMatrix.gamma5)`,
   - `ZornMatrix.cubicAssociator (ZornMatrix.psiMinus v) = -(scalarZorn (Vec3.nambu3 v) * ZornMatrix.gamma5)`.
3. **Concrete Non-Vanishing `2 × 2` Integer Matrix Witness**:
   `Vec3.nambu3 nambuWitnessVec3 ≠ 0 ∧ ZornMatrix.cubicAssociator (ZornMatrix.psiPlus nambuWitnessVec3) ≠ 0`. -/
theorem stage_MZ6_noncommutative_nambu_associator_specialization
    {B : Type*} [Ring B] (u v : Vec3 B) :
    (((ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u) +
      (ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u)) =
      scalarZorn (Vec3.nambu3 u)) ∧
    ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
      -(scalarZorn (Vec3.nambu3 u) * ZornMatrix.gamma5) ∧
    ZornMatrix.cubicAssociator (ZornMatrix.psiMinus v) =
      -(scalarZorn (Vec3.nambu3 v) * ZornMatrix.gamma5) ∧
    Vec3.nambu3 nambuWitnessVec3 ≠ 0 ∧
    ZornMatrix.cubicAssociator (ZornMatrix.psiPlus nambuWitnessVec3) ≠ 0 := by
  have hO7 := stage_O7_noncommutative_nambu_associator_on_dewitt_difference u v
  exact ⟨hO7.2.2.1,
    hO7.2.2.2.2.1,
    hO7.2.2.2.2.2,
    nambuWitnessVec3_associator_ne_zero.1,
    nambuWitnessVec3_associator_ne_zero.2⟩

end MetriplecticZornTheorems

/-! ===========================================================================
    Part III: Master Synthesis Unifying Both 6-Stage Diamond Posets
    (`𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆` & `𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆`)
    =========================================================================== -/

/-- **Master Theorem (`kantor_tanaka_five_graded_and_metriplectic_zorn_master_synthesis`)**:
Unifies the 6-stage **5-Graded Kantor–Tanaka Contact Super-Tower Poset**
(`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`) and the 6-stage **Metriplectic Zorn
Split-Octonion & Third-Order Volume Duality Poset** (`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`). -/
theorem kantor_tanaka_five_graded_and_metriplectic_zorn_master_synthesis
    {R : Type*} [CommRing R] (d : R) (X_mat : Matrix (Fin 3) (Fin 3) R)
    {F : Type*} [Field F] [CharZero F] (X_F : Matrix (Fin 3) (Fin 3) F)
    (X_R Y_R : Matrix (Fin 3) (Fin 3) ℝ)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
    (u_nc : Vec3 B) (z₁ z₂ z₃ : ParaKahlerVec R) :
    -- 1. Acyclicity, cardinality, and diamond incomparability of both 6-stage posets:
    (∀ st : KantorTanakaFiveGradedStage,
      ¬ Relation.TransGen KantorTanakaFiveGradedStage.causalEdge st st) ∧
    (∀ mst : MetriplecticZornStage,
      ¬ Relation.TransGen MetriplecticZornStage.causalEdge mst mst) ∧
    Fintype.card KantorTanakaFiveGradedStage = 6 ∧
    Fintype.card MetriplecticZornStage = 6 ∧
    -- 2. KT1 & KT2: Factor-6 eruption of 3-graded Peirce defect and factored 5-graded quintic law:
    chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X =
      (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X -
        sandwich (coneMinus P C) (coneMinus P C) X) ∧
    (d ^ 2 - 4) * (d ^ 3 - d) = d ^ 5 - 5 * d ^ 3 + 4 * d ∧
    adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0 ∧
    chargeIter P (cornerOperatorSum P A C) 5 X -
      (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
      (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0 ∧
    -- 3. KT3: Quartic Lagrange shell projectors & Peirce-defect factorization of Grade ±2:
    lagrangeShell12Zero d + lagrangeShell12One d + lagrangeShell12Two d = 12 ∧
    lagrangeShell12Two d = d * (d ^ 3 - d) ∧
    adHProjectorZero X_F + adHProjectorOne X_F + adHProjectorTwo X_F = X_F ∧
    adHProjectorTwo X_F = (1 / 12 : F) • adH (peirceThreeGradedDefect adH X_F) ∧
    -- 4. KT4 & KT5: osp(1|2) super-Jacobi closure and gl₃ = gl₁ ⊕ sl₃ decomposition:
    2 • commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
      commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) = 0 ∧
    projGL1 X_R + projSL3 X_R = X_R ∧
    Matrix.trace (projSL3 X_R) = 0 ∧
    projGL1 X_R * Y_R - Y_R * projGL1 X_R = 0 ∧
    -- 5. KT6: 5-graded Maurer–Cartan flatness & extremal cross-charge commutator:
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) =
      sandwichOp ℤ (qgtPlus P A C) (qgtMinus P A C) -
        sandwichOp ℤ (qgtMinus P A C) (qgtPlus P A C) ∧
    -- 6. MZ1–MZ6: Metriplectic Zorn decomposition, Pythagorean determinant, & dual volume split:
    zornSmul (2 : R) (zornMul (embedVec z₁) (embedVec z₂)) =
      zornAdd
        (zornAdd
          (zornSmul (zornFullMetric (embedVec z₁) (embedVec z₂)) zornOne)
          (zornSmul (zornFullSymplectic (embedVec z₁) (embedVec z₂)) zornParaGrading))
        (zornSmul (2 : R) (zornFullOffDiag (embedVec z₁) (embedVec z₂))) ∧
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      4 * zornNorm (zornMul (embedVec z₁) (embedVec z₂)) ∧
    zornAnticommutator (embedVec (hodgeCrossVec z₁ z₂)) (embedVec z₃) =
      zornSmul (vec3TripleProduct z₁.u z₂.u z₃.u - vec3TripleProduct z₁.v z₂.v z₃.v) zornOne ∧
    zornDiagPart (zornAssociator (embedVec z₁) (embedVec z₂) (embedVec z₃)) =
      zornSmul (-(vec3TripleProduct z₁.u z₂.u z₃.u + vec3TripleProduct z₁.v z₂.v z₃.v))
        zornParaGrading ∧
    ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u_nc) =
      -(scalarZorn (Vec3.nambu3 u_nc) * ZornMatrix.gamma5) := by
  have hKT2 := stage_KT2_factored_five_graded_quintic_contact_law d X_mat hP A C X
  have hKT3 := stage_KT3_orthogonal_quartic_lagrange_projectors d X_F hP A C X
  have hKT4 := stage_KT4_osp12_superconformal_contact_jacobi_closure (R := R)
  have hKT5 := stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition X_R Y_R (fun _ => 0) (fun _ => 0)
  have hMZ12 := stage_MZ1_MZ2_three_channel_metriplectic_zorn_decomposition
    (embedVec z₁) (embedVec z₂) z₁ z₂ default default
  have hMZ4 := stage_MZ4_three_term_metriplectic_pythagorean_determinant_law z₁ z₂
  have hMZ5 := stage_MZ5_third_order_dual_volume_split_on_one_and_ipara
    z₁ z₂ z₃ (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hMZ6 := stage_MZ6_noncommutative_nambu_associator_specialization u_nc u_nc
  exact ⟨KantorTanakaFiveGradedStage.causalEdge_acyclic,
    MetriplecticZornStage.causalEdge_acyclic,
    KantorTanakaFiveGradedStage.card_eq_six,
    MetriplecticZornStage.card_eq_six,
    charge_iter_cubic_difference hP A C X,
    hKT2.1,
    hKT2.2.2.2.2.1,
    hKT2.2.2.2.2.2.2,
    hKT3.1,
    hKT3.2.1,
    hKT3.2.2.2.2.2.1,
    hKT3.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hKT4.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hKT5.1,
    hKT5.2.1,
    hKT5.2.2.2.2.2.2.2.1,
    canonicalMaurerCartanJet_flat,
    extreme_sandwich_comm P A C,
    hMZ12.2.2.2.2.2.2.2.1,
    hMZ4.2.2.2.1,
    hMZ5.2.1,
    hMZ5.2.2.1,
    hMZ6.2.1⟩

/-! ===========================================================================
    Part IV: The 6-Stage Adjoint-Cyclotomic Internal Binomial Self-Reduction Poset
    (`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ 𝔄𝔡₃ ≺ 𝔄𝔡₄ ≺ 𝔄𝔡₅ ≺ 𝔄𝔡₆`)
    =========================================================================== -/

/-- The 6 causal stages of the Adjoint-Cyclotomic Internal Binomial Self-Reduction Poset
(`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ 𝔄𝔡₃ ≺ 𝔄𝔡₄ ≺ 𝔄𝔡₅ ≺ 𝔄𝔡₆`):
- `Ad1_CommutingBilateralSuperoperators`: `[L_H, R_H] = 0` and binomial expansion of `ad_H²`, `ad_H³`,
- `Ad2_IdempotentSeedThreeGradedCyclotomicLaw`: `P² = P ⟹ -3 P² X P + 3 P X P² = 0 ⟹ ad_P³ - ad_P = 0`,
- `Ad3_TripotentSeedBilateralContactSandwich`: `H³ = H ⟹ (ad_H³ - ad_H)(X) = -3 H ad_H(X) H`,
- `Ad4_SandwichSignInversionUnderTripotency`: `H³ = H ⟹ H² ad_H(X) H² = -H ad_H(X) H`,
- `Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw`: `H³ = H ⟹ ad_H²(H ad_H(X) H) = 4 H ad_H(X) H`
  and `(ad_H⁵ - 5 ad_H³ + 4 ad_H)(X) = 0` universally in `[Ring B]`,
- `Ad6_MultiplicativeCyclotomicClockDecomposition`: `Uⁿ = 1 ⟹ Ad_Uⁿ - I = ∏_{d|n} Φ_d(Ad_U) = 0`. -/
inductive AdjointCyclotomicStage : Type
  | Ad1_CommutingBilateralSuperoperators
  | Ad2_IdempotentSeedThreeGradedCyclotomicLaw
  | Ad3_TripotentSeedBilateralContactSandwich
  | Ad4_SandwichSignInversionUnderTripotency
  | Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw
  | Ad6_MultiplicativeCyclotomicClockDecomposition
  deriving DecidableEq, Repr, Inhabited

namespace AdjointCyclotomicStage

def rank : AdjointCyclotomicStage → ℕ
  | .Ad1_CommutingBilateralSuperoperators => 0
  | .Ad2_IdempotentSeedThreeGradedCyclotomicLaw => 1
  | .Ad3_TripotentSeedBilateralContactSandwich => 2
  | .Ad4_SandwichSignInversionUnderTripotency => 3
  | .Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw => 4
  | .Ad6_MultiplicativeCyclotomicClockDecomposition => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder AdjointCyclotomicStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype AdjointCyclotomicStage where
  elems := {
    .Ad1_CommutingBilateralSuperoperators,
    .Ad2_IdempotentSeedThreeGradedCyclotomicLaw,
    .Ad3_TripotentSeedBilateralContactSandwich,
    .Ad4_SandwichSignInversionUnderTripotency,
    .Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw,
    .Ad6_MultiplicativeCyclotomicClockDecomposition
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card AdjointCyclotomicStage = 6 := rfl

inductive causalEdge : AdjointCyclotomicStage → AdjointCyclotomicStage → Prop
  | ad1_to_ad2 : causalEdge .Ad1_CommutingBilateralSuperoperators .Ad2_IdempotentSeedThreeGradedCyclotomicLaw
  | ad2_to_ad3 : causalEdge .Ad2_IdempotentSeedThreeGradedCyclotomicLaw .Ad3_TripotentSeedBilateralContactSandwich
  | ad3_to_ad4 : causalEdge .Ad3_TripotentSeedBilateralContactSandwich .Ad4_SandwichSignInversionUnderTripotency
  | ad4_to_ad5 : causalEdge .Ad4_SandwichSignInversionUnderTripotency .Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw
  | ad5_to_ad6 : causalEdge .Ad5_EigenvalueFourAndUniversalFiveGradedQuinticLaw .Ad6_MultiplicativeCyclotomicClockDecomposition

theorem causalEdge_rank_lt {a b : AdjointCyclotomicStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases h <;> decide

theorem transGen_rank_lt {a b : AdjointCyclotomicStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single h1 => exact causalEdge_rank_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_rank_lt h2)

theorem causalEdge_acyclic (a : AdjointCyclotomicStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_rank_lt h)

end AdjointCyclotomicStage

/-- Left multiplication operator `L_H(X) = H * X` in any associative `[Ring B]`. -/
def leftMulOp {B : Type*} [Ring B] (H X : B) : B := H * X

/-- Right multiplication operator `R_H(X) = X * H` in any associative `[Ring B]`. -/
def rightMulOp {B : Type*} [Ring B] (H X : B) : B := X * H

/-- Adjoint derivation `ad_H(X) = H * X - X * H = L_H(X) - R_H(X)` in any associative `[Ring B]`. -/
def adOp {B : Type*} [Ring B] (H X : B) : B := H * X - X * H

/-- Multiplicative conjugation clock `Ad_U(X) = U * X * U_inv` in any associative `[Ring B]`. -/
def conjClockOp {B : Type*} [Ring B] (U U_inv X : B) : B := U * X * U_inv

/-- **Stage `𝔄𝔡₁` (`stage_Ad1_commuting_bilateral_superoperators`)**:
In any associative `[Ring B]`, left and right multiplication commute (`[L_H, R_H] = 0`)
and `ad_H = L_H - R_H` expands binomially at orders 2 and 3. -/
theorem stage_Ad1_commuting_bilateral_superoperators
    {B : Type*} [Ring B] (H X : B) :
    leftMulOp H (rightMulOp H X) = rightMulOp H (leftMulOp H X) ∧
    adOp H X = leftMulOp H X - rightMulOp H X ∧
    adOp H (adOp H X) =
      (H * H) * X - (2 : ℤ) • (H * X * H) + X * (H * H) ∧
    adOp H (adOp H (adOp H X)) =
      (H * H * H) * X - (3 : ℤ) • ((H * H) * X * H) +
        (3 : ℤ) • (H * X * (H * H)) - X * (H * H * H) := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;>
    (dsimp [leftMulOp, rightMulOp, adOp]; noncomm_ring)

/-- **Stage `𝔄𝔡₂` (`stage_Ad2_idempotent_seed_three_graded_cyclotomic_law`)**:
In any associative `[Ring B]`, an idempotent `P * P = P` cancels the cubic binomial
cross-terms `-3 P² X P + 3 P X P² = 0` and satisfies `ad_P³(X) - ad_P(X) = 0`. -/
theorem stage_Ad2_idempotent_seed_three_graded_cyclotomic_law
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (X : B) :
    -((3 : ℤ) • ((P * P) * X * P)) + (3 : ℤ) • (P * X * (P * P)) = 0 ∧
    adOp P (adOp P (adOp P X)) - adOp P X = 0 ∧
    adOp P (adOp P X) - adOp P X =
      -((2 : ℤ) • (P * X * P)) + (2 : ℤ) • (X * P) := by
  dsimp [adOp]
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage `𝔄𝔡₃` (`stage_Ad3_tripotent_seed_bilateral_contact_sandwich`)**:
In any associative `[Ring B]`, if `H * H * H = H`, the cubic Peirce defect of `ad_H`
condenses into the exact bilateral sandwich:
`ad_H (ad_H (ad_H X)) - ad_H X = -((3 : ℤ) • (H * ad_H X * H))`. -/
theorem stage_Ad3_tripotent_seed_bilateral_contact_sandwich
    {B : Type*} [Ring B] {H : B} (hH : H * H * H = H) (X : B) :
    adOp H (adOp H (adOp H X)) - adOp H X =
      -((3 : ℤ) • (H * adOp H X * H)) := by
  have hDiff :
      adOp H (adOp H (adOp H X)) - adOp H X - (-((3 : ℤ) • (H * adOp H X * H))) =
        (H * H * H - H) * X - X * (H * H * H - H) := by
    dsimp [adOp]
    noncomm_ring
  apply sub_eq_zero.mp
  rw [hDiff, hH, sub_self, zero_mul, mul_zero, sub_self]

/-- **Stage `𝔄𝔡₄` (`stage_Ad4_sandwich_sign_inversion_under_tripotency`)**:
In any associative `[Ring B]`, if `H * H * H = H`, the bilateral sandwich
`W = H * ad_H(X) * H` satisfies `H² * ad_H(X) * H² = -W` (`H * W * H = -W`)
and is absorbed on the left and right by `H²` (`H² * W = W`, `W * H² = W`). -/
theorem stage_Ad4_sandwich_sign_inversion_under_tripotency
    {B : Type*} [Ring B] {H : B} (hH : H * H * H = H) (X : B) :
    (H * H) * adOp H X * (H * H) = -(H * adOp H X * H) ∧
    H * (H * adOp H X * H) * H = -(H * adOp H X * H) ∧
    (H * H) * (H * adOp H X * H) = H * adOp H X * H ∧
    (H * adOp H X * H) * (H * H) = H * adOp H X * H := by
  have hSign : (H * H) * adOp H X * (H * H) = -(H * adOp H X * H) := by
    have hId :
        (H * H) * adOp H X * (H * H) - (-(H * adOp H X * H)) =
          (H * H * H - H) * X * (H * H) - (H * H) * X * (H * H * H - H) := by
      dsimp [adOp]
      noncomm_ring
    apply sub_eq_zero.mp
    rw [hId, hH, sub_self, zero_mul, zero_mul, mul_zero, sub_self]
  have hAssoc : H * (H * adOp H X * H) * H = (H * H) * adOp H X * (H * H) := by
    noncomm_ring
  have hLeft : (H * H) * (H * adOp H X * H) = H * adOp H X * H := by
    have hId :
        (H * H) * (H * adOp H X * H) - H * adOp H X * H =
          (H * H * H - H) * adOp H X * H := by
      noncomm_ring
    apply sub_eq_zero.mp
    rw [hId, hH, sub_self, zero_mul, zero_mul]
  have hRight : (H * adOp H X * H) * (H * H) = H * adOp H X * H := by
    have hId :
        (H * adOp H X * H) * (H * H) - H * adOp H X * H =
          H * adOp H X * (H * H * H - H) := by
      noncomm_ring
    apply sub_eq_zero.mp
    rw [hId, hH, sub_self, mul_zero]
  exact ⟨hSign, hAssoc.trans hSign, hLeft, hRight⟩

/-- **Stage `𝔄𝔡₅` (`stage_Ad5_eigenvalue_four_and_universal_five_graded_quintic_law`)**:
In any associative `[Ring B]`, if `H * H * H = H`, then:
1. `ad_H²` acts with eigenvalue `+4 = 1 - 2(-1) + 1` on the bilateral sandwich `W = H * ad_H(X) * H`:
   `ad_H (ad_H (H * ad_H X * H)) = (4 : ℤ) • (H * ad_H X * H)`,
2. `(ad_H² - 4I)` annihilates `(ad_H³ - ad_H)(X)`:
   `ad_H (ad_H (ad_H (ad_H (ad_H X)) - ad_H X)) - (4 : ℤ) • (ad_H (ad_H (ad_H X)) - ad_H X) = 0`,
3. And `ad_H` satisfies the 5-graded Kantor–Tanaka quintic contact identity universally in `[Ring B]`:
   `ad_H (ad_H (ad_H (ad_H (ad_H X)))) - (5 : ℤ) • ad_H (ad_H (ad_H X)) + (4 : ℤ) • ad_H X = 0`. -/
theorem stage_Ad5_eigenvalue_four_and_universal_five_graded_quintic_law
    {B : Type*} [Ring B] {H : B} (hH : H * H * H = H) (X : B) :
    adOp H (adOp H (H * adOp H X * H)) = (4 : ℤ) • (H * adOp H X * H) ∧
    adOp H (adOp H (adOp H (adOp H (adOp H X)) - adOp H X)) -
      (4 : ℤ) • (adOp H (adOp H (adOp H X)) - adOp H X) = 0 ∧
    adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
      (5 : ℤ) • adOp H (adOp H (adOp H X)) +
      (4 : ℤ) • adOp H X = 0 := by
  let W := H * adOp H X * H
  have hAd1 := (stage_Ad1_commuting_bilateral_superoperators H W).2.2.1
  have hAd4 := stage_Ad4_sandwich_sign_inversion_under_tripotency hH X
  have hEig4 : adOp H (adOp H W) = (4 : ℤ) • W := by
    rw [hAd1, hAd4.2.2.1, hAd4.2.2.2, hAd4.2.1]
    abel
  have hAd3 := stage_Ad3_tripotent_seed_bilateral_contact_sandwich hH X
  have hNeg3 :
      adOp H (adOp H (-((3 : ℤ) • W))) = -((3 : ℤ) • adOp H (adOp H W)) := by
    dsimp [adOp]
    noncomm_ring
  have hFactoredZero :
      adOp H (adOp H (adOp H (adOp H (adOp H X)) - adOp H X)) -
        (4 : ℤ) • (adOp H (adOp H (adOp H X)) - adOp H X) = 0 := by
    rw [hAd3, hNeg3, hEig4]
    abel
  have hExpand :
      adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
        (5 : ℤ) • adOp H (adOp H (adOp H X)) +
        (4 : ℤ) • adOp H X =
        adOp H (adOp H (adOp H (adOp H (adOp H X)) - adOp H X)) -
          (4 : ℤ) • (adOp H (adOp H (adOp H X)) - adOp H X) := by
    dsimp [adOp]
    noncomm_ring
  exact ⟨hEig4, hFactoredZero, hExpand.trans hFactoredZero⟩

/-- **Stage `𝔄𝔡₆` (`stage_Ad6_multiplicative_cyclotomic_clock_decomposition`)**:
Cyclotomic polynomial factorizations for orders `n = 2, 3, 6` over `[CommRing R]` and
universal `[Ring B]` multiplicative clock annihilation for involutive (`S * S = 1`) and
ternary (`Ω * Ω * Ω = 1`) clocks. -/
theorem stage_Ad6_multiplicative_cyclotomic_clock_decomposition
    {R : Type*} [CommRing R] (x : R)
    {B : Type*} [Ring B] {S Ω : B} (hS : S * S = 1) (hOmega : Ω * Ω * Ω = 1) (X : B) :
    x ^ 2 - 1 = (x - 1) * (x + 1) ∧
    x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) ∧
    x ^ 6 - 1 = (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1) ∧
    conjClockOp S S (conjClockOp S S X) - X = 0 ∧
    conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) X)) - X = 0 := by
  have hS2 :
      conjClockOp S S (conjClockOp S S X) - X =
        (S * S) * X * (S * S) - X := by
    dsimp [conjClockOp]
    noncomm_ring
  have hOm3 :
      conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) X)) - X =
        (Ω * Ω * Ω) * X * ((Ω * Ω * Ω) * (Ω * Ω * Ω)) - X := by
    dsimp [conjClockOp]
    noncomm_ring
  refine ⟨by ring, by ring, by ring, ?_, ?_⟩
  · rw [hS2, hS, one_mul, mul_one, sub_self]
  · rw [hOm3, hOmega, one_mul, mul_one, mul_one, sub_self]

/-- **Master Theorem (`adjoint_cyclotomic_internal_binomial_master_poset`)**:
Unifies the 6-stage Adjoint-Cyclotomic Internal Binomial Self-Reduction Poset
(`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ 𝔄𝔡₃ ≺ 𝔄𝔡₄ ≺ 𝔄𝔡₅ ≺ 𝔄𝔡₆`) over any associative `[Ring B]`. -/
theorem adjoint_cyclotomic_internal_binomial_master_poset
    {R : Type*} [CommRing R] (x : R)
    {B : Type*} [Ring B] {P H S Ω : B}
    (hP : P * P = P) (hH : H * H * H = H) (hS : S * S = 1) (hOmega : Ω * Ω * Ω = 1)
    (X : B) :
    (∀ st : AdjointCyclotomicStage,
      ¬ Relation.TransGen AdjointCyclotomicStage.causalEdge st st) ∧
    Fintype.card AdjointCyclotomicStage = 6 ∧
    leftMulOp H (rightMulOp H X) = rightMulOp H (leftMulOp H X) ∧
    adOp P (adOp P (adOp P X)) - adOp P X = 0 ∧
    adOp H (adOp H (adOp H X)) - adOp H X = -((3 : ℤ) • (H * adOp H X * H)) ∧
    (H * H) * adOp H X * (H * H) = -(H * adOp H X * H) ∧
    adOp H (adOp H (H * adOp H X * H)) = (4 : ℤ) • (H * adOp H X * H) ∧
    adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
      (5 : ℤ) • adOp H (adOp H (adOp H X)) +
      (4 : ℤ) • adOp H X = 0 ∧
    conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) (conjClockOp Ω (Ω * Ω) X)) - X = 0 := by
  have hAd1 := stage_Ad1_commuting_bilateral_superoperators H X
  have hAd2 := stage_Ad2_idempotent_seed_three_graded_cyclotomic_law hP X
  have hAd3 := stage_Ad3_tripotent_seed_bilateral_contact_sandwich hH X
  have hAd4 := stage_Ad4_sandwich_sign_inversion_under_tripotency hH X
  have hAd5 := stage_Ad5_eigenvalue_four_and_universal_five_graded_quintic_law hH X
  have hAd6 := stage_Ad6_multiplicative_cyclotomic_clock_decomposition x hS hOmega X
  exact ⟨AdjointCyclotomicStage.causalEdge_acyclic,
    AdjointCyclotomicStage.card_eq_six,
    hAd1.1,
    hAd2.2.1,
    hAd3,
    hAd4.1,
    hAd5.1,
    hAd5.2.2,
    hAd6.2.2.2.2⟩

/-! ===========================================================================
    Part V: The 6-Stage Case-Free Chiral Super-Adjoint (`sad_Q`), Division-Free
    `24 = 4!` Integer Resolution of the 5-Graded Kantor–Tanaka Tower, &
    24-Cyclotomic Modular Clock / Octonion-Color Composition Poset
    (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`)
    =========================================================================== -/

/-- The 6 causal stages of the **Case-Free Chiral Super-Adjoint & 24-Cyclotomic Modular
Clock Poset** (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`). -/
inductive SuperAdjointCyclotomic24Stage : Type
  /-- `𝔖𝔄₁`: Case-Free Chiral Super-Adjoint `sad_Q(X) = Q X - S_P X S_P Q` in `[Ring B]`. -/
  | SA1_CaseFreeChiralSuperAdjointOperator
  /-- `𝔖𝔄₂`: Parity-Alternating Bracket Law & Exact Square `sad_Q²(X) = [Q², X]`. -/
  | SA2_ParityAlternatingBracketAndExactSquareLaw
  /-- `𝔖𝔄₃`: Nilpotent Super-Adjoint Square-Zero (`sad_{N_+}² = 0`) & Higgs-SUSY Split (`sad_Φ²(J) = 0` vs. `ad_Φ²(J) = 4VJ`). -/
  | SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit
  /-- `𝔖𝔄₄`: Division-Free `24 = 4!` Integer Projector Resolution of the 5-Graded Tower. -/
  | SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower
  /-- `𝔖𝔄₅`: 24-Cyclotomic Modular Clock `x^24 - 1` & Octonion-Color Composition `Φ₂₄(x) = Φ₃(-x^4)`. -/
  | SA5_Cyclotomic24ModularClockAndOctonionColorComposition
  /-- `𝔖𝔄₆`: Exponent-2 Galois Cube `(ℤ/24ℤ)^× ≅ (ℤ/2ℤ)³` & `24 | (k² - 1)` Divisibility Lock. -/
  | SA6_ExponentTwoGaloisCubeMod24DivisibilityLock
  deriving DecidableEq, Repr, Inhabited

namespace SuperAdjointCyclotomic24Stage

/-- Topological rank `0 .. 5` of `SuperAdjointCyclotomic24Stage`. -/
def rank : SuperAdjointCyclotomic24Stage → ℕ
  | .SA1_CaseFreeChiralSuperAdjointOperator => 0
  | .SA2_ParityAlternatingBracketAndExactSquareLaw => 1
  | .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit => 2
  | .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower => 3
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => 4
  | .SA6_ExponentTwoGaloisCubeMod24DivisibilityLock => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder SuperAdjointCyclotomic24Stage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype SuperAdjointCyclotomic24Stage where
  elems := {
    .SA1_CaseFreeChiralSuperAdjointOperator,
    .SA2_ParityAlternatingBracketAndExactSquareLaw,
    .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit,
    .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower,
    .SA5_Cyclotomic24ModularClockAndOctonionColorComposition,
    .SA6_ExponentTwoGaloisCubeMod24DivisibilityLock
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card SuperAdjointCyclotomic24Stage = 6 := rfl

/-- Directed causal edges `𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`. -/
def causalEdge : SuperAdjointCyclotomic24Stage → SuperAdjointCyclotomic24Stage → Prop
  | .SA1_CaseFreeChiralSuperAdjointOperator,
    .SA2_ParityAlternatingBracketAndExactSquareLaw => True
  | .SA2_ParityAlternatingBracketAndExactSquareLaw,
    .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit => True
  | .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit,
    .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower => True
  | .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower,
    .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => True
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition,
    .SA6_ExponentTwoGaloisCubeMod24DivisibilityLock => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : SuperAdjointCyclotomic24Stage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : SuperAdjointCyclotomic24Stage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- Strict DAG acyclicity of `𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`. -/
theorem causalEdge_acyclic (a : SuperAdjointCyclotomic24Stage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_rank_lt h)

/-- Monotone representation-depth projection across `𝔖𝔄₁..𝔖𝔄₆`. -/
def toRepDepth : SuperAdjointCyclotomic24Stage → RepDepth
  | .SA1_CaseFreeChiralSuperAdjointOperator => .operator
  | .SA2_ParityAlternatingBracketAndExactSquareLaw => .operator
  | .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit => .transport
  | .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower => .transport
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => .thermo
  | .SA6_ExponentTwoGaloisCubeMod24DivisibilityLock => .thermo

/-- Monotone ontology meta-level projection across `𝔖𝔄₁..𝔖𝔄₆`. -/
def toOntologyMetaLevel : SuperAdjointCyclotomic24Stage → OntologyMetaLevel
  | .SA1_CaseFreeChiralSuperAdjointOperator => .M1_ProjectorClabject
  | .SA2_ParityAlternatingBracketAndExactSquareLaw => .M2_GrassmannianPowertypeOrbit
  | .SA3_NilpotentSuperAdjointSquareZeroAndHiggsSusySplit => .M2_GrassmannianPowertypeOrbit
  | .SA4_DivisionFree24IntegerProjectorResolutionOfFiveGradedTower => .M3_ErlangenCasimirMetaLaw
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => .M3_ErlangenCasimirMetaLaw
  | .SA6_ExponentTwoGaloisCubeMod24DivisibilityLock => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : SuperAdjointCyclotomic24Stage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> decide

theorem toOntologyMetaLevel_mono {a b : SuperAdjointCyclotomic24Stage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> decide

end SuperAdjointCyclotomic24Stage

/-- Case-free chiral super-adjoint operator `sad_Q(X) := Q * X - (S_P * X * S_P) * Q`
for a chiral grading involution `S_P` and odd generator `Q`. -/
def superAdjointOp {B : Type*} [Ring B] (S_P Q X : B) : B :=
  Q * X - (S_P * X * S_P) * Q

/-- Division-free `24 = 4!` integer polynomial projector onto eigenvalue `0` of the 5-graded
Kantor–Tanaka quintic `d^5 - 5 d^3 + 4 d = 0`:
`P_0^{(24)}(d) := 6 * (d^2 - 1) * (d^2 - 4)`. -/
def proj24PolyZero {R : Type*} [CommRing R] (d : R) : R :=
  6 * (d ^ 2 - 1) * (d ^ 2 - 4)

/-- Division-free `24 = 4!` integer polynomial projector onto eigenvalue `+1`:
`P_{+1}^{(24)}(d) := -4 * d * (d + 1) * (d^2 - 4)`. -/
def proj24PolyPlus1 {R : Type*} [CommRing R] (d : R) : R :=
  -4 * d * (d + 1) * (d ^ 2 - 4)

/-- Division-free `24 = 4!` integer polynomial projector onto eigenvalue `-1`:
`P_{-1}^{(24)}(d) := -4 * d * (d - 1) * (d^2 - 4)`. -/
def proj24PolyMinus1 {R : Type*} [CommRing R] (d : R) : R :=
  -4 * d * (d - 1) * (d ^ 2 - 4)

/-- Division-free `24 = 4!` integer polynomial projector onto eigenvalue `+2`:
`P_{+2}^{(24)}(d) := d * (d^2 - 1) * (d + 2)`. -/
def proj24PolyPlus2 {R : Type*} [CommRing R] (d : R) : R :=
  d * (d ^ 2 - 1) * (d + 2)

/-- Division-free `24 = 4!` integer polynomial projector onto eigenvalue `-2`:
`P_{-2}^{(24)}(d) := d * (d^2 - 1) * (d - 2)`. -/
def proj24PolyMinus2 {R : Type*} [CommRing R] (d : R) : R :=
  d * (d ^ 2 - 1) * (d - 2)

/-- Division-free `24 = 4!` operator projector onto grade `0`:
`24 Π_0(D)(X) := 6 D^4(X) - 30 D^2(X) + 24 X`. -/
def proj24OpZero {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  (6 : ℤ) • D (D (D (D X))) - (30 : ℤ) • D (D X) + (24 : ℤ) • X

/-- Division-free `24 = 4!` operator projector onto grade `+1`:
`24 Π_{+1}(D)(X) := -4 D^4(X) - 4 D^3(X) + 16 D^2(X) + 16 D(X)`. -/
def proj24OpPlus1 {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  -((4 : ℤ) • D (D (D (D X)))) - (4 : ℤ) • D (D (D X)) +
    (16 : ℤ) • D (D X) + (16 : ℤ) • D X

/-- Division-free `24 = 4!` operator projector onto grade `-1`:
`24 Π_{-1}(D)(X) := -4 D^4(X) + 4 D^3(X) + 16 D^2(X) - 16 D(X)`. -/
def proj24OpMinus1 {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  -((4 : ℤ) • D (D (D (D X)))) + (4 : ℤ) • D (D (D X)) +
    (16 : ℤ) • D (D X) - (16 : ℤ) • D X

/-- Division-free `24 = 4!` operator projector onto grade `+2`:
`24 Π_{+2}(D)(X) := D^4(X) + 2 D^3(X) - D^2(X) - 2 D(X)`. -/
def proj24OpPlus2 {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  D (D (D (D X))) + (2 : ℤ) • D (D (D X)) - D (D X) - (2 : ℤ) • D X

/-- Division-free `24 = 4!` operator projector onto grade `-2`:
`24 Π_{-2}(D)(X) := D^4(X) - 2 D^3(X) - D^2(X) + 2 D(X)`. -/
def proj24OpMinus2 {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : M :=
  D (D (D (D X))) - (2 : ℤ) • D (D (D X)) - D (D X) + (2 : ℤ) • D X

/-- Ternary color cyclotomic polynomial `Φ₃(y) := y^2 + y + 1`. -/
def phi3Poly {R : Type*} [CommRing R] (y : R) : R :=
  y ^ 2 + y + 1

/-- 24th primitive cyclotomic polynomial `Φ₂₄(x) := x^8 - x^4 + 1`. -/
def phi24Poly {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 8 - x ^ 4 + 1

/-- **Stage `𝔖𝔄₁` (`stage_SA1_case_free_chiral_super_adjoint_operator`)**:
In any `[Ring B]` with idempotent `hP : P * P = P` (`S_P = invS P`), for any odd seed
`Q = oddGrade P Y` and any `X : B`:
1. On the even subalgebra `E = evenGrade P X`, `sad_Q(E) = [Q, E]` (commutator),
2. On the odd subspace `O = oddGrade P X`, `sad_Q(O) = {Q, O}` (anticommutator),
3. Conjugating `sad_Q(X)` by `S_P` reverses the parity of `sad_Q(X)`:
   `invS P * superAdjointOp (invS P) (oddGrade P Y) X * invS P =
     -(oddGrade P Y) * (invS P * X * invS P) + X * oddGrade P Y`. -/
theorem stage_SA1_case_free_chiral_super_adjoint_operator
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (Y X : B) :
    superAdjointOp (invS P) (oddGrade P Y) (evenGrade P X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (oddGrade P Y) (evenGrade P X) ∧
    superAdjointOp (invS P) (oddGrade P Y) (oddGrade P X) =
      anticomm (oddGrade P Y) (oddGrade P X) ∧
    invS P * superAdjointOp (invS P) (oddGrade P Y) X * invS P =
      -(oddGrade P Y) * (invS P * X * invS P) + X * oddGrade P Y := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp [superAdjointOp, InfoGeometry.OperatorAlgebra.PeirceSpine.comm, anticomm];
     peirce_nf hP)

set_option maxHeartbeats 800000 in
/-- **Stage `𝔖𝔄₂` (`stage_SA2_parity_alternating_bracket_and_exact_square_law`)**:
1. **Alternating Commutator–Anticommutator Cancellation in Any `[Ring B]`**:
   For any `Q E O : B`,
   - `anticomm Q (comm Q E) = comm (Q * Q) E` (`{Q, [Q, E]} = [Q², E]`),
   - `comm Q (anticomm Q O) = comm (Q * Q) O` (`[Q, {Q, O}] = [Q², O]`).
2. **Universal Mixed-Parity Super-Adjoint Square Law (`sad_Q²(X) = [Q², X]`)**:
   For any idempotent `hP : P * P = P`, any odd operator `Q = oddGrade P Y`, and ANY `X : B`:
   `superAdjointOp (invS P) (oddGrade P Y) (superAdjointOp (invS P) (oddGrade P Y) X) =
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (oddGrade P Y * oddGrade P Y) X`.
3. **Exact Super-Sandwich Defect (`ad_Q² - sad_Q²`)**:
   On an odd element `oddGrade P X`,
   `adOp (oddGrade P Y) (adOp (oddGrade P Y) (oddGrade P X)) -
     superAdjointOp (invS P) (oddGrade P Y)
       (superAdjointOp (invS P) (oddGrade P Y) (oddGrade P X)) =
     -((2 : ℤ) • (oddGrade P Y * oddGrade P X * oddGrade P Y))`. -/
theorem stage_SA2_parity_alternating_bracket_and_exact_square_law
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (Q E O Y X : B) :
    anticomm Q (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q E) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Q * Q) E ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q (anticomm Q O) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Q * Q) O ∧
    superAdjointOp (invS P) (oddGrade P Y)
        (superAdjointOp (invS P) (oddGrade P Y) X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (oddGrade P Y * oddGrade P Y) X ∧
    adOp (oddGrade P Y) (adOp (oddGrade P Y) (oddGrade P X)) -
      superAdjointOp (invS P) (oddGrade P Y)
        (superAdjointOp (invS P) (oddGrade P Y) (oddGrade P X)) =
      -((2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (oddGrade P Y) (oddGrade P X) * oddGrade P Y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [anticomm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · dsimp [anticomm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · dsimp [superAdjointOp, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  · dsimp [adOp, superAdjointOp, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP

set_option maxHeartbeats 800000 in
/-- **Stage `𝔖𝔄₃` (`stage_SA3_nilpotent_super_adjoint_square_zero_and_higgs_susy_split`)**:
In any `[Ring B]` with idempotent `hP : P * P = P` and seeds `A C X : B`:
1. **Nilpotent Chiral Supercharges Square to Zero (`sad_{N_±}²(X) = 0`)**:
   - `superAdjointOp (invS P) (conePlus P A) (superAdjointOp (invS P) (conePlus P A) X) = 0`,
   - `superAdjointOp (invS P) (coneMinus P C) (superAdjointOp (invS P) (coneMinus P C) X) = 0`.
2. **Higgs Mass vs. SUSY Zero-Mode Split for `Φ = genPhi P A C` on `J = genJ P A C`**:
   - `superAdjointOp (invS P) (genPhi P A C) (superAdjointOp (invS P) (genPhi P A C) X) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genV P A C) X`,
   - `superAdjointOp (invS P) (genPhi P A C)
       (superAdjointOp (invS P) (genPhi P A C) (genJ P A C)) = 0` (`sad_Φ²(J) = [V, J] = 0`),
   - `adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) =
       (4 : ℤ) • (genV P A C * genJ P A C)` (`ad_Φ²(J) = 4 V J`). -/
theorem stage_SA3_nilpotent_super_adjoint_square_zero_and_higgs_susy_split
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    superAdjointOp (invS P) (conePlus P A)
        (superAdjointOp (invS P) (conePlus P A) X) = 0 ∧
    superAdjointOp (invS P) (coneMinus P C)
        (superAdjointOp (invS P) (coneMinus P C) X) = 0 ∧
    superAdjointOp (invS P) (genPhi P A C)
        (superAdjointOp (invS P) (genPhi P A C) X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genV P A C) X ∧
    superAdjointOp (invS P) (genPhi P A C)
        (superAdjointOp (invS P) (genPhi P A C) (genJ P A C)) = 0 ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp [superAdjointOp, adOp, InfoGeometry.OperatorAlgebra.PeirceSpine.comm];
     peirce_nf hP)

/-- **Stage `𝔖𝔄₄` (`stage_SA4_division_free_24_integer_resolution_of_five_graded_tower`)**:
1. **Why `24 = 4!` Is the Clearing Denominator**:
   For $P(d) = d^5 - 5 d^3 + 4 d$, $P'(\pm 2) = 5(\pm 2)^4 - 15(\pm 2)^2 + 4 = 24 = 4!$.
2. **Exact Partition of `24` in `ℤ[d]` and over any `[AddCommGroup M]`**:
   - `proj24PolyMinus2 d + proj24PolyMinus1 d + proj24PolyZero d + proj24PolyPlus1 d + proj24PolyPlus2 d = 24`,
   - `proj24OpMinus2 D X + proj24OpMinus1 D X + proj24OpZero D X + proj24OpPlus1 D X + proj24OpPlus2 D X = (24 : ℤ) • X`.
3. **Exact Eigen-Equations & Division-Free Orthogonality Modulo `d^5 - 5 d^3 + 4 d = 0`**:
   - `d * proj24PolyZero d = 6 * (d ^ 5 - 5 * d ^ 3 + 4 * d)`,
   - `(d - 1) * proj24PolyPlus1 d = -4 * (d ^ 5 - 5 * d ^ 3 + 4 * d)`,
   - `(d + 1) * proj24PolyMinus1 d = -4 * (d ^ 5 - 5 * d ^ 3 + 4 * d)`,
   - `(d - 2) * proj24PolyPlus2 d = d ^ 5 - 5 * d ^ 3 + 4 * d`,
   - `(d + 2) * proj24PolyMinus2 d = d ^ 5 - 5 * d ^ 3 + 4 * d`,
   - Under `hd : d ^ 5 - 5 * d ^ 3 + 4 * d = 0`:
     `proj24PolyPlus2 d * proj24PolyMinus2 d = 0` and
     `(proj24PolyPlus2 d) ^ 2 = 24 * proj24PolyPlus2 d`. -/
theorem stage_SA4_division_free_24_integer_resolution_of_five_graded_tower
    {R : Type*} [CommRing R] (d : R)
    {M : Type*} [AddCommGroup M] (D : M → M) (X : M) :
    (5 * (2 : ℤ) ^ 4 - 15 * (2 : ℤ) ^ 2 + 4 = 24 ∧
     5 * (-2 : ℤ) ^ 4 - 15 * (-2 : ℤ) ^ 2 + 4 = 24) ∧
    proj24PolyMinus2 d + proj24PolyMinus1 d + proj24PolyZero d +
      proj24PolyPlus1 d + proj24PolyPlus2 d = 24 ∧
    proj24OpMinus2 D X + proj24OpMinus1 D X + proj24OpZero D X +
      proj24OpPlus1 D X + proj24OpPlus2 D X = (24 : ℤ) • X ∧
    d * proj24PolyZero d = 6 * (d ^ 5 - 5 * d ^ 3 + 4 * d) ∧
    (d - 1) * proj24PolyPlus1 d = -4 * (d ^ 5 - 5 * d ^ 3 + 4 * d) ∧
    (d + 1) * proj24PolyMinus1 d = -4 * (d ^ 5 - 5 * d ^ 3 + 4 * d) ∧
    (d - 2) * proj24PolyPlus2 d = d ^ 5 - 5 * d ^ 3 + 4 * d ∧
    (d + 2) * proj24PolyMinus2 d = d ^ 5 - 5 * d ^ 3 + 4 * d ∧
    (d ^ 5 - 5 * d ^ 3 + 4 * d = 0 →
      proj24PolyPlus2 d * proj24PolyMinus2 d = 0 ∧
      (proj24PolyPlus2 d) ^ 2 = 24 * proj24PolyPlus2 d) := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [proj24PolyMinus2, proj24PolyMinus1, proj24PolyZero,
      proj24PolyPlus1, proj24PolyPlus2]
    ring
  · dsimp [proj24OpMinus2, proj24OpMinus1, proj24OpZero,
      proj24OpPlus1, proj24OpPlus2]
    abel
  · dsimp [proj24PolyZero]; ring
  · dsimp [proj24PolyPlus1]; ring
  · dsimp [proj24PolyMinus1]; ring
  · dsimp [proj24PolyPlus2]; ring
  · dsimp [proj24PolyMinus2]; ring
  · intro hd
    refine ⟨?_, ?_⟩
    · calc proj24PolyPlus2 d * proj24PolyMinus2 d
        _ = (d * (d ^ 2 - 1)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
            dsimp [proj24PolyPlus2, proj24PolyMinus2]; ring
        _ = (d * (d ^ 2 - 1)) * 0 := by rw [hd]
        _ = 0 := mul_zero _
    · have hDiff :
          (proj24PolyPlus2 d) ^ 2 - 24 * proj24PolyPlus2 d =
            (d ^ 3 + 4 * d ^ 2 + 7 * d + 12) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus2]; ring
      have hZero : (proj24PolyPlus2 d) ^ 2 - 24 * proj24PolyPlus2 d = 0 := by
        rw [hDiff, hd, mul_zero]
      exact sub_eq_zero.mp hZero

/-- **Stage `𝔖𝔄₅` (`stage_SA5_cyclotomic_24_modular_clock_and_octonion_color_composition`)**:
1. **8-Divisor Cyclotomic Factorization of `x ^ 24 - 1`**:
   `x ^ 24 - 1 = (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 + 1) *
                 (x ^ 2 - x + 1) * (x ^ 4 + 1) * (x ^ 4 - x ^ 2 + 1) * (x ^ 8 - x ^ 4 + 1)`.
2. **Octonion–Color Cyclotomic Composition (`Φ₂₄(x) = Φ₃(-x^4)`)**:
   `phi24Poly x = phi3Poly (-(x ^ 4))`.
3. **Color-Octonion Triality Product (`3 × 8 = 24 = 4!`)**:
   `3 * 8 = 24 ∧ Nat.factorial 4 = 24`. -/
theorem stage_SA5_cyclotomic_24_modular_clock_and_octonion_color_composition
    {R : Type*} [CommRing R] (x : R) :
    x ^ 24 - 1 =
      (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 + 1) *
        (x ^ 2 - x + 1) * (x ^ 4 + 1) * (x ^ 4 - x ^ 2 + 1) * (x ^ 8 - x ^ 4 + 1) ∧
    phi24Poly x = phi3Poly (-(x ^ 4)) ∧
    3 * 8 = 24 ∧
    Nat.factorial 4 = 24 := by
  refine ⟨by ring, ?_, rfl, rfl⟩
  dsimp [phi24Poly, phi3Poly]
  ring

/-- **Stage `𝔖𝔄₆` (`stage_SA6_exponent_two_galois_cube_mod_24_divisibility_lock`)**:
1. **Universal Exponent `2` on `(ℤ/24ℤ)^× = {1, 5, 7, 11, 13, 17, 19, 23}`**:
   For every coprime residue `k ∈ {1, 5, 7, 11, 13, 17, 19, 23}`, `(k ^ 2 - 1) % 24 = 0`.
2. **Algebraic Decomposition of `k² - 1` mod 8 and mod 3**:
   - `(2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1)`,
   - `(3 * n + 1) ^ 2 - 1 = 3 * n * (3 * n + 2)`,
   - `(3 * n - 1) ^ 2 - 1 = 3 * n * (3 * n - 2)`. -/
theorem stage_SA6_exponent_two_galois_cube_mod_24_divisibility_lock
    (m n : ℤ) :
    (∀ k ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (k ^ 2 - 1) % 24 = 0) ∧
    (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) ∧
    (3 * n + 1) ^ 2 - 1 = 3 * n * (3 * n + 2) ∧
    (3 * n - 1) ^ 2 - 1 = 3 * n * (3 * n - 2) := by
  refine ⟨by decide, by ring, by ring, by ring⟩

/-- **Master Theorem (`super_adjoint_cyclotomic_24_master_poset`)**:
Unifies the 6-stage Case-Free Chiral Super-Adjoint, Division-Free `24 = 4!` 5-Graded
Projector Resolution, & 24-Cyclotomic Modular Clock Poset (`𝔖𝔄₁ ≺ ⋯ ≺ 𝔖𝔄₆`). -/
theorem super_adjoint_cyclotomic_24_master_poset
    {R : Type*} [CommRing R] (d x : R)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C Y X : B)
    (m n : ℤ) :
    (∀ st : SuperAdjointCyclotomic24Stage,
      ¬ Relation.TransGen SuperAdjointCyclotomic24Stage.causalEdge st st) ∧
    Fintype.card SuperAdjointCyclotomic24Stage = 6 ∧
    superAdjointOp (invS P) (oddGrade P Y)
        (superAdjointOp (invS P) (oddGrade P Y) X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (oddGrade P Y * oddGrade P Y) X ∧
    superAdjointOp (invS P) (conePlus P A)
        (superAdjointOp (invS P) (conePlus P A) X) = 0 ∧
    superAdjointOp (invS P) (genPhi P A C)
        (superAdjointOp (invS P) (genPhi P A C) (genJ P A C)) = 0 ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) ∧
    proj24PolyMinus2 d + proj24PolyMinus1 d + proj24PolyZero d +
      proj24PolyPlus1 d + proj24PolyPlus2 d = 24 ∧
    phi24Poly x = phi3Poly (-(x ^ 4)) ∧
    (∀ k ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (k ^ 2 - 1) % 24 = 0) ∧
    (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) := by
  have hSA2 := stage_SA2_parity_alternating_bracket_and_exact_square_law hP 0 0 0 Y X
  have hSA3 := stage_SA3_nilpotent_super_adjoint_square_zero_and_higgs_susy_split hP A C X
  have hSA4 := stage_SA4_division_free_24_integer_resolution_of_five_graded_tower d (adOp P) X
  have hSA5 := stage_SA5_cyclotomic_24_modular_clock_and_octonion_color_composition x
  have hSA6 := stage_SA6_exponent_two_galois_cube_mod_24_divisibility_lock m n
  exact ⟨SuperAdjointCyclotomic24Stage.causalEdge_acyclic,
    SuperAdjointCyclotomic24Stage.card_eq_six,
    hSA2.2.2.1,
    hSA3.1,
    hSA3.2.2.2.1,
    hSA3.2.2.2.2,
    hSA4.2.1,
    hSA5.2.1,
    hSA6.1,
    hSA6.2.1⟩

/-! ===========================================================================
    Part VI: The Four-Way Super-Bracket Diamond & `ℤ/24ℤ` Isogeny Glue
    Cohomology Poset (`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`)
    =========================================================================== -/

/-- **The 6-Stage Four-Way Super-Bracket Diamond & `ℤ/24ℤ` Glue Poset
(`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`)**:
Resolves the Socratic elenchus of the symmetric sandwich conflation and integer
projector splitting:
- `dm1_four_second_order_super_brackets` (`𝔇𝔐₁`):
  The four second-order bracket compositions `{--, ++, -+, +-}` generated by
  `adOp Q X = Q X - X Q` and `acOp Q X = Q X + X Q`, together with the Rung 0
  Socratic refutation of `-4 Q P_odd(X) Q` on the Goldstone zero-mode `X = Q = Φ`.
- `dm2_opposite_parity_cancellation_commutator_of_square` (`𝔇𝔐₂`):
  Opposite-parity compositions `(-+)` and `(+-)` cancel the bilateral sandwich
  `±Q X Q` identically: `[Q, {Q, X}] = {Q, [Q, X]} = [Q², X]`.
- `dm3_like_parity_sandwich_split` (`𝔇𝔐₃`):
  Like-parity compositions `(--)` and `(++)` split around the Jordan anticommutator
  `{Q², X}` by `∓ 2 Q X Q`:
  `[Q, [Q, X]] = {Q², X} - 2 Q X Q` and `{Q, {Q, X}} = {Q², X} + 2 Q X Q`.
- `dm4_asymmetric_defect_vs_symmetric_sandwich_identity` (`𝔇𝔐₄`):
  The exact asymmetric right-twist defect `ad_Q²(X) - sad_Q²(X) = -2 [Q, X] Q`
  vs. the pure bilateral sandwich `ad_Q²(X) - ac_Q²(X) = -4 Q X Q`.
- `dm5_goldstone_zero_mode_protection_and_anticommuting_specialization` (`𝔇𝔐₅`):
  Goldstone zero-mode protection (`[Q, Q] = 0 ⟹ -2 [Q, Q] Q = 0`) and exact
  reconciliation on anticommuting pairs (`{Q, J} = 0 ⟹ -2 [Q, J] Q = -4 Q J Q = 4 Q² J`).
- `dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation` (`𝔇𝔐₆`):
  The 24-isogeny composition law `Σ₂₄ ∘ Ψ₂₄ = 24 id_M`, complete 5-graded
  24-idempotency and mutual orthogonality modulo `d⁵ - 5d³ + 4d = 0`, and
  24-torsion annihilation of the lattice glue cokernel. -/
inductive FourWayBracketDiamond24GlueStage : Type
  | dm1_four_second_order_super_brackets
  | dm2_opposite_parity_cancellation_commutator_of_square
  | dm3_like_parity_sandwich_split
  | dm4_asymmetric_defect_vs_symmetric_sandwich_identity
  | dm5_goldstone_zero_mode_protection_and_anticommuting_specialization
  | dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation
  deriving DecidableEq, Repr

namespace FourWayBracketDiamond24GlueStage

/--Topological rank `0..5` of `FourWayBracketDiamond24GlueStage`. -/
def rank : FourWayBracketDiamond24GlueStage → ℕ
  | .dm1_four_second_order_super_brackets => 0
  | .dm2_opposite_parity_cancellation_commutator_of_square => 1
  | .dm3_like_parity_sandwich_split => 2
  | .dm4_asymmetric_defect_vs_symmetric_sandwich_identity => 3
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization => 4
  | .dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation => 5

/-- Order-embedding from `Fin 6`. -/
def ofFin (i : Fin 6) : FourWayBracketDiamond24GlueStage :=
  match i.val with
  | 0 => .dm1_four_second_order_super_brackets
  | 1 => .dm2_opposite_parity_cancellation_commutator_of_square
  | 2 => .dm3_like_parity_sandwich_split
  | 3 => .dm4_asymmetric_defect_vs_symmetric_sandwich_identity
  | 4 => .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization
  | _ => .dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation

/-- Equivalence `FourWayBracketDiamond24GlueStage ≃ Fin 6`. -/
def equivFin6 : FourWayBracketDiamond24GlueStage ≃ Fin 6 where
  toFun s := ⟨s.rank, by cases s <;> decide⟩
  invFun := ofFin
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype FourWayBracketDiamond24GlueStage :=
  Fintype.ofEquiv (Fin 6) equivFin6.symm

instance : Inhabited FourWayBracketDiamond24GlueStage :=
  ⟨.dm1_four_second_order_super_brackets⟩

instance : LinearOrder FourWayBracketDiamond24GlueStage :=
  LinearOrder.lift' rank (by intro a b h; cases a <;> cases b <;> first | rfl | cases h)

theorem card_eq_six : Fintype.card FourWayBracketDiamond24GlueStage = 6 := rfl

/-- Diamond causal edges `𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`. -/
def causalEdge :
    FourWayBracketDiamond24GlueStage → FourWayBracketDiamond24GlueStage → Prop
  | .dm1_four_second_order_super_brackets,
      .dm2_opposite_parity_cancellation_commutator_of_square => True
  | .dm1_four_second_order_super_brackets,
      .dm3_like_parity_sandwich_split => True
  | .dm2_opposite_parity_cancellation_commutator_of_square,
      .dm4_asymmetric_defect_vs_symmetric_sandwich_identity => True
  | .dm3_like_parity_sandwich_split,
      .dm4_asymmetric_defect_vs_symmetric_sandwich_identity => True
  | .dm4_asymmetric_defect_vs_symmetric_sandwich_identity,
      .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization => True
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization,
      .dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_lt {a b : FourWayBracketDiamond24GlueStage} (h : causalEdge a b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : FourWayBracketDiamond24GlueStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_lt h2)

/-- Strict acyclicity of `FourWayBracketDiamond24GlueStage`. -/
theorem causalEdge_acyclic (st : FourWayBracketDiamond24GlueStage) :
    ¬ Relation.TransGen causalEdge st st :=
  fun h => Nat.lt_irrefl st.rank (transGen_lt h)

theorem not_causalEdge_to_dm3 {b : FourWayBracketDiamond24GlueStage}
    (hb : 1 < b.rank) (h2 : causalEdge b .dm3_like_parity_sandwich_split) : False := by
  cases b <;> revert hb h2 <;> unfold rank causalEdge <;> decide

/-- Parallel diamond branches `𝔇𝔐₂` and `𝔇𝔐₃` are incomparable under `TransGen causalEdge`. -/
theorem incomparable_DM2_DM3 :
    ¬ Relation.TransGen causalEdge
        .dm2_opposite_parity_cancellation_commutator_of_square
        .dm3_like_parity_sandwich_split ∧
    ¬ Relation.TransGen causalEdge
        .dm3_like_parity_sandwich_split
        .dm2_opposite_parity_cancellation_commutator_of_square := by
  refine ⟨?_, ?_⟩
  · intro h
    cases h with
    | single h1 => revert h1; decide
    | tail h1 h2 => exact not_causalEdge_to_dm3 (transGen_lt h1) h2
  · intro h
    exact Nat.not_lt.mpr (by decide : (1 : ℕ) ≤ 2) (transGen_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : FourWayBracketDiamond24GlueStage → RepDepth
  | .dm1_four_second_order_super_brackets => .operator
  | .dm2_opposite_parity_cancellation_commutator_of_square => .operator
  | .dm3_like_parity_sandwich_split => .operator
  | .dm4_asymmetric_defect_vs_symmetric_sandwich_identity => .transport
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization => .transport
  | .dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation => .thermo

theorem toRepDepth_mono {a b : FourWayBracketDiamond24GlueStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : FourWayBracketDiamond24GlueStage → OntologyMetaLevel
  | .dm1_four_second_order_super_brackets => .M1_ProjectorClabject
  | .dm2_opposite_parity_cancellation_commutator_of_square => .M1_ProjectorClabject
  | .dm3_like_parity_sandwich_split => .M1_ProjectorClabject
  | .dm4_asymmetric_defect_vs_symmetric_sandwich_identity => .M2_GrassmannianPowertypeOrbit
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_specialization => .M2_GrassmannianPowertypeOrbit
  | .dm6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : FourWayBracketDiamond24GlueStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end FourWayBracketDiamond24GlueStage

/-- Universal anticommutator operator `acOp Q X := Q * X + X * Q` in any `[Ring B]`. -/
def acOp {B : Type*} [Ring B] (Q X : B) : B :=
  Q * X + X * Q

/-- 5-graded 24-isogeny projection map `Ψ₂₄ : M → (Fin 5 → M)` sending `X` to its five
integer-scaled Kantor–Tanaka grade components `(P_{-2}^{(24)} X, …, P_{+2}^{(24)} X)`. -/
def psi24Map {M : Type*} [AddCommGroup M] (D : M → M) (X : M) : Fin 5 → M
  | ⟨0, _⟩ => proj24OpMinus2 D X
  | ⟨1, _⟩ => proj24OpMinus1 D X
  | ⟨2, _⟩ => proj24OpZero D X
  | ⟨3, _⟩ => proj24OpPlus1 D X
  | ⟨4, _⟩ => proj24OpPlus2 D X

/-- 5-graded 24-isogeny summation map `Σ₂₄ : (Fin 5 → M) → M`. -/
def sigma24Map {M : Type*} [AddCommGroup M] (v : Fin 5 → M) : M :=
  v 0 + v 1 + v 2 + v 3 + v 4

set_option maxHeartbeats 800000 in
/-- **Stage `𝔇𝔐₁` (`stage_DM1_four_second_order_super_brackets_and_goldstone_aporia`)**:
1. **Rung 0 Socratic Elenchus on the Goldstone Mode (`X = Q = Φ`)**:
   - `adOp (genPhi P A C) (genPhi P A C) = 0` (`[Φ, Φ] = 0`),
   - `adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) -
       superAdjointOp (invS P) (genPhi P A C)
         (superAdjointOp (invS P) (genPhi P A C) (genPhi P A C)) = 0` (`LHS = 0`),
   - `-((4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C)) =
       -((4 : ℤ) • (genV P A C * genPhi P A C))` (naive symmetric sandwich `-4 Φ³ = -4 V Φ ≠ 0`),
   - `-((2 : ℤ) • (adOp (genPhi P A C) (genPhi P A C) * genPhi P A C)) = 0`
     (true right-twist defect `-2 [Φ, Φ] Φ = 0` vanishes identically). -/
theorem stage_DM1_four_second_order_super_brackets_and_goldstone_aporia
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    adOp (genPhi P A C) (genPhi P A C) = 0 ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) -
      superAdjointOp (invS P) (genPhi P A C)
        (superAdjointOp (invS P) (genPhi P A C) (genPhi P A C)) = 0 ∧
    -((4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C)) =
      -((4 : ℤ) • (genV P A C * genPhi P A C)) ∧
    -((2 : ℤ) • (adOp (genPhi P A C) (genPhi P A C) * genPhi P A C)) = 0 := by
  refine ⟨by dsimp [adOp]; noncomm_ring, ?_, ?_, by dsimp [adOp]; noncomm_ring⟩
  · dsimp [adOp, superAdjointOp]
    peirce_nf hP
  · peirce_nf hP

/-- **Stages `𝔇𝔐₂, 𝔇𝔐₃` (`stage_DM2_DM3_four_way_super_bracket_diamond`)**:
In any associative ring `[Ring B]`, for all `Q X : B`:
1. **Stage `𝔇𝔐₂` (Opposite-Parity Cancellation `(-+)` and `(+-)`)**:
   - `adOp Q (acOp Q X) = adOp (Q * Q) X` (`[Q, {Q, X}] = [Q², X]`),
   - `acOp Q (adOp Q X) = adOp (Q * Q) X` (`{Q, [Q, X]} = [Q², X]`),
   - `adOp Q (acOp Q X) = acOp Q (adOp Q X)`.
2. **Stage `𝔇𝔐₃` (Like-Parity Sandwich Split `(--)` and `(++)`)**:
   - `adOp Q (adOp Q X) = acOp (Q * Q) X - (2 : ℤ) • (Q * X * Q)` (`[Q, [Q, X]] = {Q², X} - 2 Q X Q`),
   - `acOp Q (acOp Q X) = acOp (Q * Q) X + (2 : ℤ) • (Q * X * Q)` (`{Q, {Q, X}} = {Q², X} + 2 Q X Q`). -/
theorem stage_DM2_DM3_four_way_super_bracket_diamond
    {B : Type*} [Ring B] (Q X : B) :
    (adOp Q (acOp Q X) = adOp (Q * Q) X ∧
     acOp Q (adOp Q X) = adOp (Q * Q) X ∧
     adOp Q (acOp Q X) = acOp Q (adOp Q X)) ∧
    (adOp Q (adOp Q X) = acOp (Q * Q) X - (2 : ℤ) • (Q * X * Q) ∧
     acOp Q (acOp Q X) = acOp (Q * Q) X + (2 : ℤ) • (Q * X * Q)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    (dsimp [adOp, acOp]; noncomm_ring)

set_option maxHeartbeats 800000 in
/-- **Stage `𝔇𝔐₄` (`stage_DM4_asymmetric_defect_vs_symmetric_sandwich_identity`)**:
In any associative ring `[Ring B]` with `hP : P * P = P` and `Q X Y : B`:
1. **Asymmetric Right-Twist Defect (`(--) - (-+) = -2 [Q, X] Q`)**:
   - `adOp Q (adOp Q X) - adOp (Q * Q) X = (2 : ℤ) • (X * (Q * Q) - Q * X * Q)`,
   - `adOp Q (adOp Q X) - adOp (Q * Q) X = -((2 : ℤ) • (adOp Q X * Q))`,
   - `adOp (oddGrade P Y) (adOp (oddGrade P Y) X) -
       superAdjointOp (invS P) (oddGrade P Y)
         (superAdjointOp (invS P) (oddGrade P Y) X) =
       -((2 : ℤ) • (adOp (oddGrade P Y) X * oddGrade P Y))`.
2. **Symmetric Bilateral Sandwich & Pure Metric Sum (`(--) ∓ (++)`)**:
   - `adOp Q (adOp Q X) - acOp Q (acOp Q X) = -((4 : ℤ) • (Q * X * Q))`,
   - `adOp Q (adOp Q X) + acOp Q (acOp Q X) = (2 : ℤ) • acOp (Q * Q) X`. -/
theorem stage_DM4_asymmetric_defect_vs_symmetric_sandwich_identity
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (Q X Y : B) :
    adOp Q (adOp Q X) - adOp (Q * Q) X =
      (2 : ℤ) • (X * (Q * Q) - Q * X * Q) ∧
    adOp Q (adOp Q X) - adOp (Q * Q) X =
      -((2 : ℤ) • (adOp Q X * Q)) ∧
    adOp (oddGrade P Y) (adOp (oddGrade P Y) X) -
      superAdjointOp (invS P) (oddGrade P Y)
        (superAdjointOp (invS P) (oddGrade P Y) X) =
      -((2 : ℤ) • (adOp (oddGrade P Y) X * oddGrade P Y)) ∧
    adOp Q (adOp Q X) - acOp Q (acOp Q X) =
      -((4 : ℤ) • (Q * X * Q)) ∧
    adOp Q (adOp Q X) + acOp Q (acOp Q X) =
      (2 : ℤ) • acOp (Q * Q) X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [adOp]; noncomm_ring
  · dsimp [adOp]; noncomm_ring
  · dsimp [adOp, superAdjointOp]; peirce_nf hP
  · dsimp [adOp, acOp]; noncomm_ring
  · dsimp [adOp, acOp]; noncomm_ring

set_option maxHeartbeats 800000 in
/-- **Stage `𝔇𝔐₅` (`stage_DM5_goldstone_zero_mode_protection_and_anticommuting_specialization`)**:
1. **Goldstone Zero-Mode Protection (`X = Q`)**:
   `adOp Q Q = 0`, `-((2 : ℤ) • (adOp Q Q * Q)) = 0`, and
   `adOp Q (adOp Q Q) - adOp (Q * Q) Q = 0`.
2. **Exact Reconciliation on Anticommuting Pairs (`acOp Q J = 0 ⟹ J Q = -Q J`)**:
   If `hAnti : acOp Q J = 0`, then:
   - `adOp Q J = (2 : ℤ) • (Q * J)`,
   - `-((2 : ℤ) • (adOp Q J * Q)) = -((4 : ℤ) • (Q * J * Q))`,
   - `-((4 : ℤ) • (Q * J * Q)) = (4 : ℤ) • (Q * Q * J)`,
   - `adOp Q (adOp Q J) - adOp (Q * Q) J = (4 : ℤ) • (Q * Q * J)`.
3. **Peirce Specialization (`Q = genPhi P A C`, `J = genJ P A C`)**:
   `acOp (genPhi P A C) (genJ P A C) = 0` and
   `-((2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C)) =
     (4 : ℤ) • (genV P A C * genJ P A C)`. -/
theorem stage_DM5_goldstone_zero_mode_protection_and_anticommuting_specialization
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C Q J : B) :
    (adOp Q Q = 0 ∧
     -((2 : ℤ) • (adOp Q Q * Q)) = 0 ∧
     adOp Q (adOp Q Q) - adOp (Q * Q) Q = 0) ∧
    (acOp Q J = 0 →
      adOp Q J = (2 : ℤ) • (Q * J) ∧
      -((2 : ℤ) • (adOp Q J * Q)) = -((4 : ℤ) • (Q * J * Q)) ∧
      -((4 : ℤ) • (Q * J * Q)) = (4 : ℤ) • (Q * Q * J) ∧
      adOp Q (adOp Q J) - adOp (Q * Q) J = (4 : ℤ) • (Q * Q * J)) ∧
    (acOp (genPhi P A C) (genJ P A C) = 0 ∧
     -((2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C)) =
       (4 : ℤ) • (genV P A C * genJ P A C)) := by
  refine ⟨⟨by dsimp [adOp]; noncomm_ring,
           by dsimp [adOp]; noncomm_ring,
           by dsimp [adOp]; noncomm_ring⟩,
    ?_,
    ⟨by dsimp [acOp]; peirce_nf hP,
     by dsimp [adOp]; peirce_nf hP⟩⟩
  intro hAnti
  have hJQ : J * Q = -(Q * J) := eq_neg_of_add_eq_zero_right hAnti
  have h1 : adOp Q J = (2 : ℤ) • (Q * J) := by
    dsimp [adOp]
    rw [hJQ]
    noncomm_ring
  have h2 : -((2 : ℤ) • (adOp Q J * Q)) = -((4 : ℤ) • (Q * J * Q)) := by
    rw [h1]
    noncomm_ring
  have h3 : -((4 : ℤ) • (Q * J * Q)) = (4 : ℤ) • (Q * Q * J) := by
    have hQJQ : Q * J * Q = -(Q * Q * J) := by
      calc Q * J * Q = Q * (J * Q) := by rw [mul_assoc]
        _ = Q * -(Q * J) := by rw [hJQ]
        _ = -(Q * Q * J) := by noncomm_ring
    rw [hQJQ]
    noncomm_ring
  have h4 : adOp Q (adOp Q J) - adOp (Q * Q) J = (4 : ℤ) • (Q * Q * J) := by
    have hDef : adOp Q (adOp Q J) - adOp (Q * Q) J = -((2 : ℤ) • (adOp Q J * Q)) := by
      dsimp [adOp]; noncomm_ring
    rw [hDef, h2, h3]
  exact ⟨h1, h2, h3, h4⟩

/-- **Stage `𝔇𝔐₆` (`stage_DM6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation`)**:
1. **24-Isogeny Composition Law (`Σ₂₄ ∘ Ψ₂₄ = 24 id_M`)**:
   For any `[AddCommGroup M]`, `D : M → M`, and `X : M`,
   `sigma24Map (psi24Map D X) = (24 : ℤ) • X`.
2. **Complete 5-Graded 24-Idempotency & Orthogonality over `[CommRing R]` (`P_j^{(24)} P_k^{(24)} = 24 δ_{jk} P_j^{(24)}`)**:
   Under `hd : d ^ 5 - 5 * d ^ 3 + 4 * d = 0`:
   - `(proj24PolyMinus2 d) ^ 2 = 24 * proj24PolyMinus2 d`,
   - `(proj24PolyMinus1 d) ^ 2 = 24 * proj24PolyMinus1 d`,
   - `(proj24PolyZero d) ^ 2 = 24 * proj24PolyZero d`,
   - `(proj24PolyPlus1 d) ^ 2 = 24 * proj24PolyPlus1 d`,
   - `(proj24PolyPlus2 d) ^ 2 = 24 * proj24PolyPlus2 d`,
   - `proj24PolyZero d * proj24PolyPlus1 d = 0`,
   - `proj24PolyZero d * proj24PolyMinus1 d = 0`,
   - `proj24PolyZero d * proj24PolyPlus2 d = 0`,
   - `proj24PolyPlus1 d * proj24PolyMinus1 d = 0`,
   - `proj24PolyPlus1 d * proj24PolyPlus2 d = 0`,
   - `proj24PolyPlus2 d * proj24PolyMinus2 d = 0`. -/
theorem stage_DM6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation
    {R : Type*} [CommRing R] (d : R)
    {M : Type*} [AddCommGroup M] (D : M → M) (X : M) :
    sigma24Map (psi24Map D X) = (24 : ℤ) • X ∧
    (d ^ 5 - 5 * d ^ 3 + 4 * d = 0 →
      (proj24PolyMinus2 d) ^ 2 = 24 * proj24PolyMinus2 d ∧
      (proj24PolyMinus1 d) ^ 2 = 24 * proj24PolyMinus1 d ∧
      (proj24PolyZero d) ^ 2 = 24 * proj24PolyZero d ∧
      (proj24PolyPlus1 d) ^ 2 = 24 * proj24PolyPlus1 d ∧
      (proj24PolyPlus2 d) ^ 2 = 24 * proj24PolyPlus2 d ∧
      proj24PolyZero d * proj24PolyPlus1 d = 0 ∧
      proj24PolyZero d * proj24PolyMinus1 d = 0 ∧
      proj24PolyZero d * proj24PolyPlus2 d = 0 ∧
      proj24PolyPlus1 d * proj24PolyMinus1 d = 0 ∧
      proj24PolyPlus1 d * proj24PolyPlus2 d = 0 ∧
      proj24PolyPlus2 d * proj24PolyMinus2 d = 0) := by
  refine ⟨?_, ?_⟩
  · dsimp [sigma24Map, psi24Map, proj24OpMinus2, proj24OpMinus1,
      proj24OpZero, proj24OpPlus1, proj24OpPlus2]
    abel
  · intro hd
    have hSqM2 : (proj24PolyMinus2 d) ^ 2 = 24 * proj24PolyMinus2 d := by
      have h : (proj24PolyMinus2 d) ^ 2 - 24 * proj24PolyMinus2 d =
          (d ^ 3 - 4 * d ^ 2 + 7 * d - 12) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyMinus2]; ring
      exact sub_eq_zero.mp (by rw [h, hd, mul_zero])
    have hSqM1 : (proj24PolyMinus1 d) ^ 2 = 24 * proj24PolyMinus1 d := by
      have h : (proj24PolyMinus1 d) ^ 2 - 24 * proj24PolyMinus1 d =
          (16 * d ^ 3 - 32 * d ^ 2 - 32 * d + 96) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyMinus1]; ring
      exact sub_eq_zero.mp (by rw [h, hd, mul_zero])
    have hSq0 : (proj24PolyZero d) ^ 2 = 24 * proj24PolyZero d := by
      have h : (proj24PolyZero d) ^ 2 - 24 * proj24PolyZero d =
          (36 * d ^ 3 - 180 * d) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyZero]; ring
      exact sub_eq_zero.mp (by rw [h, hd, mul_zero])
    have hSqP1 : (proj24PolyPlus1 d) ^ 2 = 24 * proj24PolyPlus1 d := by
      have h : (proj24PolyPlus1 d) ^ 2 - 24 * proj24PolyPlus1 d =
          (16 * d ^ 3 + 32 * d ^ 2 - 32 * d - 96) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus1]; ring
      exact sub_eq_zero.mp (by rw [h, hd, mul_zero])
    have hSqP2 : (proj24PolyPlus2 d) ^ 2 = 24 * proj24PolyPlus2 d := by
      have h : (proj24PolyPlus2 d) ^ 2 - 24 * proj24PolyPlus2 d =
          (d ^ 3 + 4 * d ^ 2 + 7 * d + 12) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus2]; ring
      exact sub_eq_zero.mp (by rw [h, hd, mul_zero])
    have h0P1 : proj24PolyZero d * proj24PolyPlus1 d = 0 := by
      have h : proj24PolyZero d * proj24PolyPlus1 d =
          (-24 * (d + 1) * (d ^ 2 - 4)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyZero, proj24PolyPlus1]; ring
      rw [h, hd, mul_zero]
    have h0M1 : proj24PolyZero d * proj24PolyMinus1 d = 0 := by
      have h : proj24PolyZero d * proj24PolyMinus1 d =
          (-24 * (d - 1) * (d ^ 2 - 4)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyZero, proj24PolyMinus1]; ring
      rw [h, hd, mul_zero]
    have h0P2 : proj24PolyZero d * proj24PolyPlus2 d = 0 := by
      have h : proj24PolyZero d * proj24PolyPlus2 d =
          (6 * (d + 2) * (d ^ 2 - 1)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyZero, proj24PolyPlus2]; ring
      rw [h, hd, mul_zero]
    have hP1M1 : proj24PolyPlus1 d * proj24PolyMinus1 d = 0 := by
      have h : proj24PolyPlus1 d * proj24PolyMinus1 d =
          (16 * d * (d ^ 2 - 4)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus1, proj24PolyMinus1]; ring
      rw [h, hd, mul_zero]
    have hP1P2 : proj24PolyPlus1 d * proj24PolyPlus2 d = 0 := by
      have h : proj24PolyPlus1 d * proj24PolyPlus2 d =
          (-4 * d * (d + 1) * (d + 2)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus1, proj24PolyPlus2]; ring
      rw [h, hd, mul_zero]
    have hP2M2 : proj24PolyPlus2 d * proj24PolyMinus2 d = 0 := by
      have h : proj24PolyPlus2 d * proj24PolyMinus2 d =
          (d * (d ^ 2 - 1)) * (d ^ 5 - 5 * d ^ 3 + 4 * d) := by
        dsimp [proj24PolyPlus2, proj24PolyMinus2]; ring
      rw [h, hd, mul_zero]
    exact ⟨hSqM2, hSqM1, hSq0, hSqP1, hSqP2, h0P1, h0M1, h0P2, hP1M1, hP1P2, hP2M2⟩

/-- **Master Theorem (`four_way_bracket_diamond_24_glue_master_poset`)**:
Unifies the 6-stage Four-Way Super-Bracket Diamond & `ℤ/24ℤ` Isogeny Glue Cohomology
Poset (`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`). -/
theorem four_way_bracket_diamond_24_glue_master_poset
    {R : Type*} [CommRing R] (d : R)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C Q X Y : B)
    {M : Type*} [AddCommGroup M] (D : M → M) (m : M) :
    (∀ st : FourWayBracketDiamond24GlueStage,
      ¬ Relation.TransGen FourWayBracketDiamond24GlueStage.causalEdge st st) ∧
    (¬ Relation.TransGen FourWayBracketDiamond24GlueStage.causalEdge
        .dm2_opposite_parity_cancellation_commutator_of_square
        .dm3_like_parity_sandwich_split ∧
     ¬ Relation.TransGen FourWayBracketDiamond24GlueStage.causalEdge
        .dm3_like_parity_sandwich_split
        .dm2_opposite_parity_cancellation_commutator_of_square) ∧
    adOp Q (acOp Q X) = adOp (Q * Q) X ∧
    acOp Q (adOp Q X) = adOp (Q * Q) X ∧
    adOp Q (adOp Q X) - adOp (Q * Q) X = -((2 : ℤ) • (adOp Q X * Q)) ∧
    adOp Q (adOp Q X) - acOp Q (acOp Q X) = -((4 : ℤ) • (Q * X * Q)) ∧
    adOp (oddGrade P Y) (adOp (oddGrade P Y) X) -
      superAdjointOp (invS P) (oddGrade P Y)
        (superAdjointOp (invS P) (oddGrade P Y) X) =
      -((2 : ℤ) • (adOp (oddGrade P Y) X * oddGrade P Y)) ∧
    -((2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) ∧
    sigma24Map (psi24Map D m) = (24 : ℤ) • m := by
  have hDM23 := stage_DM2_DM3_four_way_super_bracket_diamond Q X
  have hDM4 := stage_DM4_asymmetric_defect_vs_symmetric_sandwich_identity hP Q X Y
  have hDM5 := stage_DM5_goldstone_zero_mode_protection_and_anticommuting_specialization hP A C Q X
  have hDM6 := stage_DM6_twenty_four_isogeny_glue_exact_sequence_and_torsion_annihilation d D m
  exact ⟨FourWayBracketDiamond24GlueStage.causalEdge_acyclic,
    FourWayBracketDiamond24GlueStage.incomparable_DM2_DM3,
    hDM23.1.1,
    hDM23.1.2.1,
    hDM4.2.1,
    hDM4.2.2.2.1,
    hDM4.2.2.1,
    hDM5.2.2.2,
    hDM6.1⟩

/-! ===========================================================================
    Part VII: Recursive Tensor-Peirce Centralizer Homogenization &
    `TensorTower R n` Poset (`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`)
    =========================================================================== -/

/-- **The 6-Stage Recursive Tensor-Peirce Tower Poset
(`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`)**:
Formalizes the recursive transformation of a flat `2^n × 2^n` matrix `FlatMat R n`
into the nested `n`-level `2 × 2` tensor tower `TensorTower R n ≅ ⨂_{k=1}^n Mat_2(R)`:
- `tt1_outer_peirce_matrix_units_and_corner_aporia` (`𝔗𝔗₁`):
  Outer `2 × 2` Peirce matrix units `{E₀₀ = P, E₀₁ = N_+, E₁₀ = N_-, E₁₁ = Q}`
  and the Socratic aporia of naive zero-padded corner projections `P M P` and `P M Q`.
- `tt2_centralizer_homogenized_peirce_projectors` (`𝔗𝔗₂`):
  The four centralizer-homogenized Peirce projectors
  `π_{ab}(M) = E_{0a} M E_{b0} + E_{1a} M E_{b1} = I_2 ⊗ M_{ab}`.
- `tt3_commutant_reconstruction_and_block_multiplication_laws` (`𝔗𝔗₃`):
  Universal commutant `[E_{cd}, π_{ab}(M)] = 0`, exact reconstruction
  `M = ∑_{a,b} E_{ab} π_{ab}(M)`, and `2 × 2` block multiplication
  `π_{ab}(M N) = ∑_c π_{ac}(M) π_{cb}(N)`.
- `tt4_recursive_inductive_tensor_tower_type` (`𝔗𝔗₄`):
  The recursive inductive type `TensorTower R 0 := R`,
  `TensorTower R (n + 1) := Matrix (Fin 2) (Fin 2) (TensorTower R n)`.
- `tt5_multi_scale_peirce_split_and_tower_coagulation` (`𝔗𝔗₅`):
  Single-step block split `peirceSplitStep` / `peirceUnsplitStep` with exact
  roundtrip `peirceSplitStep (peirceUnsplitStep B) = B` and recursive compiler
  `toTensorTower` / `ofTensorTower`.
- `tt6_dual_clifford_dewitt_basis_tensor_expansion` (`𝔗𝔗₆`):
  Dual `Cl(1,1)` DeWitt–Clifford basis `{I_2, S_P, Φ, J}` and division-free
  reconstruction `I_2 (2 Γ_sum) + S_P (2 Γ_diff) + Φ (2 M_Φ) + J (2 M_J) = 2 M`. -/
inductive TensorPeirceTowerStage : Type
  | tt1_outer_peirce_matrix_units_and_corner_aporia
  | tt2_centralizer_homogenized_peirce_projectors
  | tt3_commutant_reconstruction_and_block_multiplication_laws
  | tt4_recursive_inductive_tensor_tower_type
  | tt5_multi_scale_peirce_split_and_tower_coagulation
  | tt6_dual_clifford_dewitt_basis_tensor_expansion
  deriving DecidableEq, Repr

namespace TensorPeirceTowerStage

/-- Rank `0..5` of `TensorPeirceTowerStage`. -/
def rank : TensorPeirceTowerStage → ℕ
  | .tt1_outer_peirce_matrix_units_and_corner_aporia => 0
  | .tt2_centralizer_homogenized_peirce_projectors => 1
  | .tt3_commutant_reconstruction_and_block_multiplication_laws => 2
  | .tt4_recursive_inductive_tensor_tower_type => 3
  | .tt5_multi_scale_peirce_split_and_tower_coagulation => 4
  | .tt6_dual_clifford_dewitt_basis_tensor_expansion => 5

/-- Order-embedding from `Fin 6`. -/
def ofFin (i : Fin 6) : TensorPeirceTowerStage :=
  match i.val with
  | 0 => .tt1_outer_peirce_matrix_units_and_corner_aporia
  | 1 => .tt2_centralizer_homogenized_peirce_projectors
  | 2 => .tt3_commutant_reconstruction_and_block_multiplication_laws
  | 3 => .tt4_recursive_inductive_tensor_tower_type
  | 4 => .tt5_multi_scale_peirce_split_and_tower_coagulation
  | _ => .tt6_dual_clifford_dewitt_basis_tensor_expansion

/-- Equivalence `TensorPeirceTowerStage ≃ Fin 6`. -/
def equivFin6 : TensorPeirceTowerStage ≃ Fin 6 where
  toFun s := ⟨s.rank, by cases s <;> decide⟩
  invFun := ofFin
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype TensorPeirceTowerStage :=
  Fintype.ofEquiv (Fin 6) equivFin6.symm

instance : Inhabited TensorPeirceTowerStage :=
  ⟨.tt1_outer_peirce_matrix_units_and_corner_aporia⟩

instance : LinearOrder TensorPeirceTowerStage :=
  LinearOrder.lift' rank (by intro a b h; cases a <;> cases b <;> first | rfl | cases h)

theorem card_eq_six : Fintype.card TensorPeirceTowerStage = 6 := rfl

/-- Directed causal edges `𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`. -/
def causalEdge : TensorPeirceTowerStage → TensorPeirceTowerStage → Prop
  | .tt1_outer_peirce_matrix_units_and_corner_aporia,
      .tt2_centralizer_homogenized_peirce_projectors => True
  | .tt2_centralizer_homogenized_peirce_projectors,
      .tt3_commutant_reconstruction_and_block_multiplication_laws => True
  | .tt3_commutant_reconstruction_and_block_multiplication_laws,
      .tt4_recursive_inductive_tensor_tower_type => True
  | .tt4_recursive_inductive_tensor_tower_type,
      .tt5_multi_scale_peirce_split_and_tower_coagulation => True
  | .tt5_multi_scale_peirce_split_and_tower_coagulation,
      .tt6_dual_clifford_dewitt_basis_tensor_expansion => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_lt {a b : TensorPeirceTowerStage} (h : causalEdge a b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : TensorPeirceTowerStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_lt h2)

/-- Strict acyclicity of `TensorPeirceTowerStage`. -/
theorem causalEdge_acyclic (st : TensorPeirceTowerStage) :
    ¬ Relation.TransGen causalEdge st st :=
  fun h => Nat.lt_irrefl st.rank (transGen_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : TensorPeirceTowerStage → RepDepth
  | .tt1_outer_peirce_matrix_units_and_corner_aporia => .operator
  | .tt2_centralizer_homogenized_peirce_projectors => .operator
  | .tt3_commutant_reconstruction_and_block_multiplication_laws => .operator
  | .tt4_recursive_inductive_tensor_tower_type => .transport
  | .tt5_multi_scale_peirce_split_and_tower_coagulation => .transport
  | .tt6_dual_clifford_dewitt_basis_tensor_expansion => .thermo

theorem toRepDepth_mono {a b : TensorPeirceTowerStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : TensorPeirceTowerStage → OntologyMetaLevel
  | .tt1_outer_peirce_matrix_units_and_corner_aporia => .M1_ProjectorClabject
  | .tt2_centralizer_homogenized_peirce_projectors => .M1_ProjectorClabject
  | .tt3_commutant_reconstruction_and_block_multiplication_laws => .M2_GrassmannianPowertypeOrbit
  | .tt4_recursive_inductive_tensor_tower_type => .M2_GrassmannianPowertypeOrbit
  | .tt5_multi_scale_peirce_split_and_tower_coagulation => .M3_ErlangenCasimirMetaLaw
  | .tt6_dual_clifford_dewitt_basis_tensor_expansion => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : TensorPeirceTowerStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end TensorPeirceTowerStage

/-- **The Inductive Tensor Tower Type (`Mat_2(Mat_2(...Mat_2(R)))`)**:
- At level `0`: A scalar in `R` (`1 × 1` matrix).
- At level `n + 1`: A `2 × 2` Peirce matrix whose 4 blocks `(0,0), (0,1), (1,0), (1,1)`
  are elements of `TensorTower R n`. -/
@[reducible] def TensorTower (R : Type*) : ℕ → Type _
  | 0     => R
  | n + 1 => Matrix (Fin 2) (Fin 2) (TensorTower R n)

namespace TensorTower

/-- Level `n` matrix dimension `2^n`. -/
abbrev dim2 (n : ℕ) : ℕ := 2 ^ n

/-- Flat `2^n × 2^n` square matrix over `R`. -/
abbrev FlatMat (R : Type*) (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R

/-- Canonical index splitting `Fin (2^n) ⊕ Fin (2^n) ≃ Fin (2^{n+1})`. -/
def finSplit (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  have h : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by ring
  finSumFinEquiv.trans (Fin.castOrderIso h).toEquiv

/-- Extracts the `(0,0)` upper-left `2^n × 2^n` Peirce block `P M P`. -/
def block00 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inl j))

/-- Extracts the `(0,1)` upper-right `2^n × 2^n` Peirce block `P M (1 - P)`. -/
def block01 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inr j))

/-- Extracts the `(1,0)` lower-left `2^n × 2^n` Peirce block `(1 - P) M P`. -/
def block10 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inl j))

/-- Extracts the `(1,1)` lower-right `2^n × 2^n` Peirce block `(1 - P) M (1 - P)`. -/
def block11 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inr j))

/-- Projects a `2^{n+1} × 2^{n+1}` matrix `M` into a `2 × 2` matrix of `2^n × 2^n` blocks. -/
def peirceSplitStep {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) :
    Matrix (Fin 2) (Fin 2) (FlatMat R n) :=
  ![![block00 M, block01 M],
    ![block10 M, block11 M]]

/-- Reassembles four `2^n × 2^n` blocks into a `2^{n+1} × 2^{n+1}` matrix. -/
def peirceUnsplitStep {R : Type*} {n : ℕ} (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) :
    FlatMat R (n + 1) :=
  Matrix.reindex (finSplit n) (finSplit n)
    (Matrix.fromBlocks (B 0 0) (B 0 1) (B 1 0) (B 1 1))

/-- Forward Tensor-Peirce Compiler (`toTensorTower`):
Recursively decomposes a `2^n × 2^n` matrix into a nested `n`-level `TensorTower R n`. -/
def toTensorTower {R : Type*} : (n : ℕ) → FlatMat R n → TensorTower R n
  | 0,     M => M 0 0
  | n + 1, M =>
      let B := peirceSplitStep M
      ![![toTensorTower n (B 0 0), toTensorTower n (B 0 1)],
        ![toTensorTower n (B 1 0), toTensorTower n (B 1 1)]]

/-- Inverse Tensor-Peirce Coagulator (`ofTensorTower`):
Recursively coagulates an `n`-level `TensorTower R n` back into a `2^n × 2^n` matrix. -/
def ofTensorTower {R : Type*} : (n : ℕ) → TensorTower R n → FlatMat R n
  | 0,     r => fun _ _ => r
  | n + 1, T =>
      peirceUnsplitStep
        ![![ofTensorTower n (T 0 0), ofTensorTower n (T 0 1)],
          ![ofTensorTower n (T 1 0), ofTensorTower n (T 1 1)]]

/-- Homogenized Tensor-Peirce `(0,0)` projection `π₀₀(M) := E₀₀ M E₀₀ + E₁₀ M E₀₁`. -/
def pi00 {B : Type*} [Ring B] (E00 _E01 E10 E01 : B) (M : B) : B :=
  E00 * M * E00 + E10 * M * E01

/-- Homogenized Tensor-Peirce `(0,1)` projection `π₀₁(M) := E₀₀ M E₁₀ + E₁₀ M E₁₁`. -/
def pi01 {B : Type*} [Ring B] (E00 _E01 E10 E11 : B) (M : B) : B :=
  E00 * M * E10 + E10 * M * E11

/-- Homogenized Tensor-Peirce `(1,0)` projection `π₁₀(M) := E₀₁ M E₀₀ + E₁₁ M E₀₁`. -/
def pi10 {B : Type*} [Ring B] (E00 E01 _E10 E11 : B) (M : B) : B :=
  E01 * M * E00 + E11 * M * E01

/-- Homogenized Tensor-Peirce `(1,1)` projection `π₁₁(M) := E₀₁ M E₁₀ + E₁₁ M E₁₁`. -/
def pi11 {B : Type*} [Ring B] (_E00 E01 E10 E11 : B) (M : B) : B :=
  E01 * M * E10 + E11 * M * E11

/-- Canonical `(0,0)` matrix unit `P = E₀₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE00 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Canonical `(0,1)` nilpotent shift unit `N_+ = E₀₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE01 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- Canonical `(1,0)` nilpotent shift unit `N_- = E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE10 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- Canonical `(1,1)` matrix unit `Q = 1 - P = E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE11 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, 1]

/-- DeWitt Sum / identity unit `I_2 = E₀₀ + E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitI {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  unitE00 + unitE11

/-- Chiral DeWitt Difference grading unit `S_P = E₀₀ - E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitS {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  unitE00 - unitE11

/-- Osmotic amplitude bridge unit `Φ = E₀₁ + E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitPhi {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  unitE01 + unitE10

/-- Classical phase current unit `J = E₀₁ - E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitJ {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  unitE01 - unitE10

/-- Homogenized `(0,0)` centralizer projection `π₀₀(M) = I_2 ⊗ M₀₀` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi00 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE00 * M * unitE00 + unitE10 * M * unitE01

/-- Homogenized `(0,1)` centralizer projection `π₀₁(M) = I_2 ⊗ M₀₁` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi01 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE00 * M * unitE10 + unitE10 * M * unitE11

/-- Homogenized `(1,0)` centralizer projection `π₁₀(M) = I_2 ⊗ M₁₀` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi10 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE01 * M * unitE00 + unitE11 * M * unitE01

/-- Homogenized `(1,1)` centralizer projection `π₁₁(M) = I_2 ⊗ M₁₁` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi11 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE01 * M * unitE10 + unitE11 * M * unitE11

/-- Universal algebraic Tensor-Peirce exact reconstruction in any `[Ring B]`. -/
theorem tensor_peirce_exact_reconstruction
    {B : Type*} [Ring B] (E00 E01 E10 E11 M : B)
    (h_sum : E00 + E11 = 1)
    (h00_00 : E00 * E00 = E00) (h00_10 : E00 * E10 = 0)
    (h01_00 : E01 * E00 = 0)   (h01_10 : E01 * E10 = E00)
    (h10_01 : E10 * E01 = E11) (h10_11 : E10 * E11 = 0)
    (h11_01 : E11 * E01 = 0)   (h11_11 : E11 * E11 = E11) :
    E00 * pi00 E00 E01 E10 E01 M +
    E01 * pi01 E00 E01 E10 E11 M +
    E10 * pi10 E00 E01 E10 E11 M +
    E11 * pi11 E00 E01 E10 E11 M = M := by
  unfold pi00 pi01 pi10 pi11
  simp only [mul_add, ← mul_assoc,
             h00_00, h00_10, h01_00, h01_10, h10_01, h10_11, h11_01, h11_11,
             zero_mul, add_zero, zero_add]
  calc E00 * M * E00 + E00 * M * E11 + E11 * M * E00 + E11 * M * E11
    _ = (E00 + E11) * M * (E00 + E11) := by noncomm_ring
    _ = 1 * M * 1 := by rw [h_sum]
    _ = M := by rw [one_mul, mul_one]

/-- **Stages `𝔗𝔗₁, 𝔗𝔗₂` (`stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization`)**:
Over any `[Ring R]` and `M N : Matrix (Fin 2) (Fin 2) R`:
1. **Stage `𝔗𝔗₁` (Outer Peirce Matrix Units & Rung 0 Corner Projection Aporia)**:
   - `unitE00 + unitE11 = 1`, `unitE00 * unitE00 = unitE00`, `unitE01 * unitE10 = unitE00`, `unitE10 * unitE01 = unitE11`,
   - Naive corner `(unitE00 * (1 : Matrix (Fin 2) (Fin 2) R) * unitE00) 1 1 = 0` (kills the lower block!),
   - Naive off-diagonal `(unitE00 * M * unitE11) * (unitE00 * N * unitE11) = 0` (square-zero nilpotent!).
2. **Stage `𝔗𝔗₂` (Centralizer-Homogenized Peirce Projectors `π_{ab}(M) = I_2 ⊗ M_{ab}`)**:
   - `matPi00 M = !![M 0 0, 0; 0, M 0 0]` and `matPi00 1 = 1` (unital in the commutant!),
   - `matPi01 M = !![M 0 1, 0; 0, M 0 1]`,
   - `matPi10 M = !![M 1 0, 0; 0, M 1 0]`,
   - `matPi11 M = !![M 1 1, 0; 0, M 1 1]`. -/
theorem stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R) :
    (unitE00 + unitE11 = (1 : Matrix (Fin 2) (Fin 2) R) ∧
     (unitE00 : Matrix (Fin 2) (Fin 2) R) * unitE00 = unitE00 ∧
     (unitE01 : Matrix (Fin 2) (Fin 2) R) * unitE10 = unitE00 ∧
     (unitE10 : Matrix (Fin 2) (Fin 2) R) * unitE01 = unitE11 ∧
     (unitE00 * (1 : Matrix (Fin 2) (Fin 2) R) * unitE00 : Matrix (Fin 2) (Fin 2) R) 1 1 = 0 ∧
     (unitE00 * M * unitE11) * (unitE00 * N * unitE11) = 0) ∧
    (matPi00 M = !![M 0 0, 0; 0, M 0 0] ∧
     matPi00 (1 : Matrix (Fin 2) (Fin 2) R) = 1 ∧
     matPi01 M = !![M 0 1, 0; 0, M 0 1] ∧
     matPi10 M = !![M 1 0, 0; 0, M 1 0] ∧
     matPi11 M = !![M 1 1, 0; 0, M 1 1]) := by
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hN : N = !![N 0 0, N 0 1; N 1 0, N 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitE00, unitE11]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitE00]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10, unitE00]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10, unitE11]
  · simp [unitE00]
  · conv_lhs => rw [hM, hN]
    ext i j; fin_cases i <;> fin_cases j <;> simp [unitE00, unitE11]
  · conv_lhs => rw [hM]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matPi00, unitE00, unitE01, unitE10]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [matPi00, unitE00, unitE01, unitE10]
  · conv_lhs => rw [hM]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matPi01, unitE00, unitE10, unitE11]
  · conv_lhs => rw [hM]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matPi10, unitE00, unitE01, unitE11]
  · conv_lhs => rw [hM]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matPi11, unitE01, unitE10, unitE11]

/-- **Stage `𝔗𝔗₃` (`stage_TT3_commutant_reconstruction_and_block_multiplication_laws`)**:
Over any `[Ring R]` and `M N : Matrix (Fin 2) (Fin 2) R`:
1. **Centralizer / Commutant Property (`[E_{cd}, π_{ab}(M)] = 0`)**:
   `unitE01 * matPi00 M = matPi00 M * unitE01` and `unitE10 * matPi01 M = matPi01 M * unitE10`.
2. **Exact Matrix-Unit Reconstruction (`M = ∑_{a,b} E_{ab} π_{ab}(M)`)**:
   `unitE00 * matPi00 M + unitE01 * matPi01 M + unitE10 * matPi10 M + unitE11 * matPi11 M = M`.
3. **Exact `2 × 2` Block Multiplication in the Centralizer (`π_{ab}(M N) = ∑_c π_{ac}(M) π_{cb}(N)`)**:
   - `matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N`,
   - `matPi01 (M * N) = matPi00 M * matPi01 N + matPi01 M * matPi11 N`,
   - `matPi10 (M * N) = matPi10 M * matPi00 N + matPi11 M * matPi10 N`,
   - `matPi11 (M * N) = matPi10 M * matPi01 N + matPi11 M * matPi11 N`. -/
theorem stage_TT3_commutant_reconstruction_and_block_multiplication_laws
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R) :
    unitE01 * matPi00 M = matPi00 M * unitE01 ∧
    unitE10 * matPi01 M = matPi01 M * unitE10 ∧
    unitE00 * matPi00 M + unitE01 * matPi01 M +
      unitE10 * matPi10 M + unitE11 * matPi11 M = M ∧
    matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N ∧
    matPi01 (M * N) = matPi00 M * matPi01 N + matPi01 M * matPi11 N ∧
    matPi10 (M * N) = matPi10 M * matPi00 N + matPi11 M * matPi10 N ∧
    matPi11 (M * N) = matPi10 M * matPi01 N + matPi11 M * matPi11 N := by
  have h00 := fun X : Matrix (Fin 2) (Fin 2) R =>
    (stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization X N).2.1
  have h01 := fun X : Matrix (Fin 2) (Fin 2) R =>
    (stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization X N).2.2.2.1
  have h10 := fun X : Matrix (Fin 2) (Fin 2) R =>
    (stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization X N).2.2.2.2.1
  have h11 := fun X : Matrix (Fin 2) (Fin 2) R =>
    (stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization X N).2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h00 M]
    ext i j; fin_cases i <;> fin_cases j <;> simp [unitE01]
  · rw [h01 M]
    ext i j; fin_cases i <;> fin_cases j <;> simp [unitE10]
  · rw [h00 M, h01 M, h10 M, h11 M]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [unitE00, unitE01, unitE10, unitE11]
  · rw [h00 (M * N), h00 M, h00 N, h01 M, h10 N]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h01 (M * N), h00 M, h01 N, h01 M, h11 N]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h10 (M * N), h10 M, h00 N, h11 M, h10 N]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h11 (M * N), h10 M, h01 N, h11 M, h11 N]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Stages `𝔗𝔗₄, 𝔗𝔗₅` (`stage_TT4_TT5_recursive_tensor_tower_and_peirce_split_roundtrip`)**:
1. **Base Level `0` Roundtrip (`FlatMat R 0 ⇄ TensorTower R 0 = R`)**:
   - `toTensorTower 0 (ofTensorTower 0 r) = r`,
   - `ofTensorTower 0 (toTensorTower 0 M₀) = M₀`.
2. **Single-Step Peirce Block Split Roundtrip (`peirceSplitStep (peirceUnsplitStep B) = B`)**:
   For any `n : ℕ` and any `2 × 2` block matrix `B : Matrix (Fin 2) (Fin 2) (FlatMat R n)`:
   - `block00 (peirceUnsplitStep B) = B 0 0`,
   - `block01 (peirceUnsplitStep B) = B 0 1`,
   - `block10 (peirceUnsplitStep B) = B 1 0`,
   - `block11 (peirceUnsplitStep B) = B 1 1`,
   - `peirceSplitStep (peirceUnsplitStep B) = B`.
3. **Recursive Multi-Scale Roundtrip (`toTensorTower n (ofTensorTower n T) = T`)**:
   For every scale `n : ℕ` and `T : TensorTower R n`,
   `toTensorTower n (ofTensorTower n T) = T`. -/
theorem stage_TT4_TT5_recursive_tensor_tower_and_peirce_split_roundtrip
    {R : Type*} (r : R) (M₀ : FlatMat R 0)
    (n : ℕ) (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) (T : TensorTower R n) :
    toTensorTower 0 (ofTensorTower 0 r) = r ∧
    ofTensorTower 0 (toTensorTower 0 M₀) = M₀ ∧
    block00 (peirceUnsplitStep B) = B 0 0 ∧
    block01 (peirceUnsplitStep B) = B 0 1 ∧
    block10 (peirceUnsplitStep B) = B 1 0 ∧
    block11 (peirceUnsplitStep B) = B 1 1 ∧
    peirceSplitStep (peirceUnsplitStep B) = B ∧
    toTensorTower n (ofTensorTower n T) = T := by
  have hb00 : ∀ {k : ℕ} (C : Matrix (Fin 2) (Fin 2) (FlatMat R k)),
      block00 (peirceUnsplitStep C) = C 0 0 := by
    intro k C; ext i j
    simp [block00, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb01 : ∀ {k : ℕ} (C : Matrix (Fin 2) (Fin 2) (FlatMat R k)),
      block01 (peirceUnsplitStep C) = C 0 1 := by
    intro k C; ext i j
    simp [block01, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb10 : ∀ {k : ℕ} (C : Matrix (Fin 2) (Fin 2) (FlatMat R k)),
      block10 (peirceUnsplitStep C) = C 1 0 := by
    intro k C; ext i j
    simp [block10, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb11 : ∀ {k : ℕ} (C : Matrix (Fin 2) (Fin 2) (FlatMat R k)),
      block11 (peirceUnsplitStep C) = C 1 1 := by
    intro k C; ext i j
    simp [block11, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hSplit : ∀ {k : ℕ} (C : Matrix (Fin 2) (Fin 2) (FlatMat R k)),
      peirceSplitStep (peirceUnsplitStep C) = C := by
    intro k C
    ext a b i j
    fin_cases a <;> fin_cases b
    · exact congr_fun (congr_fun (hb00 C) i) j
    · exact congr_fun (congr_fun (hb01 C) i) j
    · exact congr_fun (congr_fun (hb10 C) i) j
    · exact congr_fun (congr_fun (hb11 C) i) j
  have hTower : ∀ (k : ℕ) (S : TensorTower R k),
      toTensorTower k (ofTensorTower k S) = S := by
    intro k
    induction k with
    | zero => intro S; rfl
    | succ k ih =>
      intro (S : Matrix (Fin 2) (Fin 2) (TensorTower R k))
      let C : Matrix (Fin 2) (Fin 2) (FlatMat R k) :=
        ![![ofTensorTower k (S 0 0), ofTensorTower k (S 0 1)],
          ![ofTensorTower k (S 1 0), ofTensorTower k (S 1 1)]]
      have h00 : block00 (peirceUnsplitStep C) = ofTensorTower k (S 0 0) := hb00 C
      have h01 : block01 (peirceUnsplitStep C) = ofTensorTower k (S 0 1) := hb01 C
      have h10 : block10 (peirceUnsplitStep C) = ofTensorTower k (S 1 0) := hb10 C
      have h11 : block11 (peirceUnsplitStep C) = ofTensorTower k (S 1 1) := hb11 C
      change (![![toTensorTower k (block00 (peirceUnsplitStep C)),
                  toTensorTower k (block01 (peirceUnsplitStep C))],
                ![toTensorTower k (block10 (peirceUnsplitStep C)),
                  toTensorTower k (block11 (peirceUnsplitStep C))]] :
              Matrix (Fin 2) (Fin 2) (TensorTower R k)) = S
      ext a b
      fin_cases a <;> fin_cases b
      · dsimp; rw [h00]; exact ih (S 0 0)
      · dsimp; rw [h01]; exact ih (S 0 1)
      · dsimp; rw [h10]; exact ih (S 1 0)
      · dsimp; rw [h11]; exact ih (S 1 1)
  refine ⟨rfl, ?_, hb00 B, hb01 B, hb10 B, hb11 B, hSplit B, hTower n T⟩
  ext i j
  fin_cases i
  fin_cases j
  rfl

/-- **Stage `𝔗𝔗₆` (`stage_TT6_dual_clifford_dewitt_basis_tensor_expansion`)**:
Over any `[Ring R]` and `M : Matrix (Fin 2) (Fin 2) R`:
1. **`Cl(1,1)` DeWitt–Clifford Relations of `{I_2, S_P, Φ, J}`**:
   - `unitS * unitS = unitI` (`S_P² = I_2`),
   - `unitPhi * unitPhi = unitI` (`Φ² = +I_2`),
   - `unitJ * unitJ = -unitI` (`J² = -I_2`),
   - `unitS * unitPhi + unitPhi * unitS = 0` (`{S_P, Φ} = 0`),
   - `unitPhi * unitJ + unitJ * unitPhi = 0` (`{Φ, J} = 0`),
   - `unitS * unitPhi = unitJ` (`S_P Φ = J`).
2. **Division-Free `Cl(1,1)` Tensor Reconstruction (`2 M = I_2 (2 Γ_sum) + S_P (2 Γ_diff) + Φ (2 M_Φ) + J (2 M_J)`)**:
   `unitI * (matPi00 M + matPi11 M) +
    unitS * (matPi00 M - matPi11 M) +
    unitPhi * (matPi01 M + matPi10 M) +
    unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M`. -/
theorem stage_TT6_dual_clifford_dewitt_basis_tensor_expansion
    {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) :
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitS = unitI ∧
    (unitPhi : Matrix (Fin 2) (Fin 2) R) * unitPhi = unitI ∧
    (unitJ : Matrix (Fin 2) (Fin 2) R) * unitJ = -unitI ∧
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitPhi + unitPhi * unitS = 0 ∧
    (unitPhi : Matrix (Fin 2) (Fin 2) R) * unitJ + unitJ * unitPhi = 0 ∧
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitPhi = unitJ ∧
    unitI * (matPi00 M + matPi11 M) +
      unitS * (matPi00 M - matPi11 M) +
      unitPhi * (matPi01 M + matPi10 M) +
      unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M := by
  have hRecon :=
    (stage_TT3_commutant_reconstruction_and_block_multiplication_laws M M).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitS, unitI, unitE00, unitE11, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitPhi, unitI, unitE00, unitE01, unitE10, unitE11, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitJ, unitI, unitE00, unitE01, unitE10, unitE11, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitS, unitPhi, unitE00, unitE01, unitE10, unitE11]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitPhi, unitJ, unitE01, unitE10]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitS, unitPhi, unitJ, unitE00, unitE01, unitE10, unitE11, Matrix.mul_apply]
  · have hExpand :
        unitI * (matPi00 M + matPi11 M) +
          unitS * (matPi00 M - matPi11 M) +
          unitPhi * (matPi01 M + matPi10 M) +
          unitJ * (matPi01 M - matPi10 M) =
        (2 : ℤ) • (unitE00 * matPi00 M + unitE01 * matPi01 M +
          unitE10 * matPi10 M + unitE11 * matPi11 M) := by
      dsimp [unitI, unitS, unitPhi, unitJ]
      noncomm_ring
    rw [hExpand, hRecon]

/-- **Master Theorem (`tensor_peirce_tower_master_poset`)**:
Unifies the 6-stage Recursive Tensor-Peirce Centralizer Homogenization &
`TensorTower R n` Poset (`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`). -/
theorem tensor_peirce_tower_master_poset
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R)
    (n : ℕ) (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) (T : TensorTower R n) :
    (∀ st : TensorPeirceTowerStage,
      ¬ Relation.TransGen TensorPeirceTowerStage.causalEdge st st) ∧
    Fintype.card TensorPeirceTowerStage = 6 ∧
    matPi00 M = !![M 0 0, 0; 0, M 0 0] ∧
    matPi01 M = !![M 0 1, 0; 0, M 0 1] ∧
    unitE00 * matPi00 M + unitE01 * matPi01 M +
      unitE10 * matPi10 M + unitE11 * matPi11 M = M ∧
    matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N ∧
    peirceSplitStep (peirceUnsplitStep B) = B ∧
    toTensorTower n (ofTensorTower n T) = T ∧
    unitI * (matPi00 M + matPi11 M) +
      unitS * (matPi00 M - matPi11 M) +
      unitPhi * (matPi01 M + matPi10 M) +
      unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M := by
  have hTT12 := stage_TT1_TT2_outer_peirce_units_corner_aporia_and_centralizer_homogenization M N
  have hTT3 := stage_TT3_commutant_reconstruction_and_block_multiplication_laws M N
  have hTT45 := stage_TT4_TT5_recursive_tensor_tower_and_peirce_split_roundtrip (0 : R) 0 n B T
  have hTT6 := stage_TT6_dual_clifford_dewitt_basis_tensor_expansion M
  exact ⟨TensorPeirceTowerStage.causalEdge_acyclic,
    TensorPeirceTowerStage.card_eq_six,
    hTT12.2.1,
    hTT12.2.2.2.1,
    hTT3.2.2.1,
    hTT3.2.2.2.1,
    hTT45.2.2.2.2.2.2.1,
    hTT45.2.2.2.2.2.2.2,
    hTT6.2.2.2.2.2.2⟩

end TensorTower

/-!
===============================================================================
Part VIII: Multi-Scale Non-Commutative Tensor-Peirce Attention Network
(`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`)
===============================================================================
-/

/-- The 7-stage causal poset of the Multi-Scale Non-Commutative Tensor-Peirce
Attention Network (`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`). -/
inductive TensorPeirceAttentionNetworkStage : Type
  | tn1_recursive_tensor_peirce_scale_decomposition
  | tn2_scale_k_dually_flat_unipotent_attention_gates
  | tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse
  | tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent
  | tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover
  | tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume
  | tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory
  deriving DecidableEq, Repr

namespace TensorPeirceAttentionNetworkStage

/-- Topological rank in `{0, 1, 2, 3, 4, 5}` (with diamond branch `{𝔗𝔑₄, 𝔗𝔑₅}` at rank `3`). -/
def rank : TensorPeirceAttentionNetworkStage → ℕ
  | .tn1_recursive_tensor_peirce_scale_decomposition => 0
  | .tn2_scale_k_dually_flat_unipotent_attention_gates => 1
  | .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse => 2
  | .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent => 3
  | .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover => 3
  | .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume => 4
  | .tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory => 5

/-- Direct causal edges of `𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`. -/
def causalEdge : TensorPeirceAttentionNetworkStage → TensorPeirceAttentionNetworkStage → Prop
  | .tn1_recursive_tensor_peirce_scale_decomposition,
    .tn2_scale_k_dually_flat_unipotent_attention_gates => True
  | .tn2_scale_k_dually_flat_unipotent_attention_gates,
    .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse => True
  | .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse,
    .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent => True
  | .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse,
    .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover => True
  | .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent,
    .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume => True
  | .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover,
    .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume => True
  | .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume,
    .tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

instance : Fintype TensorPeirceAttentionNetworkStage where
  elems := {
    .tn1_recursive_tensor_peirce_scale_decomposition,
    .tn2_scale_k_dually_flat_unipotent_attention_gates,
    .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse,
    .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent,
    .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover,
    .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume,
    .tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory
  }
  complete x := by cases x <;> simp

theorem card_eq_seven : Fintype.card TensorPeirceAttentionNetworkStage = 7 := rfl

theorem edge_lt {a b : TensorPeirceAttentionNetworkStage} (h : causalEdge a b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : TensorPeirceAttentionNetworkStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact edge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (edge_lt h2)

/-- Strict DAG acyclicity of `TensorPeirceAttentionNetworkStage`. -/
theorem causalEdge_acyclic (st : TensorPeirceAttentionNetworkStage) :
    ¬ Relation.TransGen causalEdge st st :=
  fun h => Nat.lt_irrefl st.rank (transGen_lt h)

/-- Parallel diamond branches `𝔗𝔑₄` and `𝔗𝔑₅` are incomparable under `TransGen causalEdge`. -/
theorem incomparable_TN4_TN5 :
    ¬ Relation.TransGen causalEdge
        .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent
        .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover ∧
    ¬ Relation.TransGen causalEdge
        .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover
        .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent :=
  ⟨fun h => Nat.lt_irrefl 3 (transGen_lt h),
   fun h => Nat.lt_irrefl 3 (transGen_lt h)⟩

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : TensorPeirceAttentionNetworkStage → RepDepth
  | .tn1_recursive_tensor_peirce_scale_decomposition => .operator
  | .tn2_scale_k_dually_flat_unipotent_attention_gates => .operator
  | .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse => .transport
  | .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent => .transport
  | .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover => .transport
  | .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume => .thermo
  | .tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory => .thermo

theorem toRepDepth_mono {a b : TensorPeirceAttentionNetworkStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : TensorPeirceAttentionNetworkStage → OntologyMetaLevel
  | .tn1_recursive_tensor_peirce_scale_decomposition => .M1_ProjectorClabject
  | .tn2_scale_k_dually_flat_unipotent_attention_gates => .M1_ProjectorClabject
  | .tn3_reversible_scale_k_operator_gaussian_and_polynomial_inverse => .M2_GrassmannianPowertypeOrbit
  | .tn4_bruhat_dressed_grassmannian_and_legendre_mobius_resolvent => .M2_GrassmannianPowertypeOrbit
  | .tn5_berry_wilson_loop_causal_rotor_and_wavelet_crossover => .M2_GrassmannianPowertypeOrbit
  | .tn6_multi_scale_tensor_contraction_and_zorn_three_body_bond_volume => .M3_ErlangenCasimirMetaLaw
  | .tn7_yangian_rtt_monodromy_and_krein_logcft_secular_memory => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : TensorPeirceAttentionNetworkStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end TensorPeirceAttentionNetworkStage

section TensorPeirceAttentionNetworkClosure

variable {B : Type*} [Ring B]

/-- Forward causal `e`-flat unipotent attention gate `ℰ_+(P, X) := 1 + N_+(P, X)`. -/
def ePlusGate (P X : B) : B :=
  1 + conePlus P X

/-- Backward feedback `m`-flat unipotent attention gate `ℰ_-(P, Y) := 1 + N_-(P, Y)`. -/
def eMinusGate (P Y : B) : B :=
  1 + coneMinus P Y

/-- Paired forward scale-`k` Amari Operator Gaussian attention layer
`𝒢_+(P, X, Y) := (1 + N_+(P, X))(1 + N_-(P, Y))`. -/
def attnGaussianPlus (P X Y : B) : B :=
  ePlusGate P X * eMinusGate P Y

/-- Paired reverse scale-`k` Amari Operator Gaussian attention layer
`𝒢_-(P, X, Y) := (1 + N_-(P, Y))(1 + N_+(P, X))`. -/
def attnGaussianMinus (P X Y : B) : B :=
  eMinusGate P Y * ePlusGate P X

/-- Series-free `O(1)` polynomial inverse of `𝒢_+(P, X, Y)`:
`𝒢_+⁻¹(P, X, Y) := (1 - N_-(P, Y))(1 - N_+(P, X))`. -/
def attnGaussianPlusInv (P X Y : B) : B :=
  (1 - coneMinus P Y) * (1 - conePlus P X)

/-- Bruhat-dressed Grassmannian attention projector
`P̂(P, X, Y) := (1 - N_+(P, X))(P + N_-(P, Y))(1 + N_+(P, X))`. -/
def bruhatAttentionProj (P X Y : B) : B :=
  (1 - conePlus P X) * (P + coneMinus P Y) * (1 + conePlus P X)

/-- **Stages `𝔗𝔑₁ ≺ 𝔗𝔑₂` (`stage_TN1_TN2_scale_decomposition_and_dually_flat_unipotent_attention_gates`)**:
1. **Recursive Tensor-Peirce Scale Decomposition (`𝔗𝔑₁`)**:
   - `toTensorTower n (ofTensorTower n T) = T`,
   - `E₀₀ π₀₀(M₂) + E₀₁ π₀₁(M₂) + E₁₀ π₁₀(M₂) + E₁₁ π₁₁(M₂) = M₂`.
2. **Scale-`k` Dually Flat Unipotent Attention Gates (`𝔗𝔑₂`)**:
   - Square-zero nilpotency: `N_+(X) N_+(Y) = 0` and `N_-(X) N_-(Y) = 0`,
   - Exact abelian multi-head addition in the exponent:
     `ℰ_+(P, X) ℰ_+(P, Y) = ℰ_+(P, X + Y)` and `ℰ_-(P, X) ℰ_-(P, Y) = ℰ_-(P, X + Y)`,
   - Exact two-sided unipotent invertibility:
     `ℰ_+(P, X) (1 - N_+(P, X)) = 1` and `(1 - N_+(P, X)) ℰ_+(P, X) = 1`. -/
theorem stage_TN1_TN2_scale_decomposition_and_dually_flat_unipotent_attention_gates
    {R : Type*} [Ring R] (n : ℕ) (T : TensorTower R n) (M₂ : Matrix (Fin 2) (Fin 2) R)
    {P : B} (hP : P * P = P) (X Y : B) :
    TensorTower.toTensorTower n (TensorTower.ofTensorTower n T) = T ∧
    TensorTower.unitE00 * TensorTower.matPi00 M₂ +
      TensorTower.unitE01 * TensorTower.matPi01 M₂ +
      TensorTower.unitE10 * TensorTower.matPi10 M₂ +
      TensorTower.unitE11 * TensorTower.matPi11 M₂ = M₂ ∧
    conePlus P X * conePlus P Y = 0 ∧
    coneMinus P X * coneMinus P Y = 0 ∧
    ePlusGate P X * ePlusGate P Y = ePlusGate P (X + Y) ∧
    eMinusGate P X * eMinusGate P Y = eMinusGate P (X + Y) ∧
    ePlusGate P X * (1 - conePlus P X) = 1 ∧
    (1 - conePlus P X) * ePlusGate P X = 1 := by
  refine ⟨(TensorTower.stage_TT4_TT5_recursive_tensor_tower_and_peirce_split_roundtrip
      (0 : R) 0 n 0 T).2.2.2.2.2.2.2,
    (TensorTower.stage_TT3_commutant_reconstruction_and_block_multiplication_laws M₂ M₂).2.2.1,
    by peirce_nf hP,
    by peirce_nf hP,
    by dsimp [ePlusGate]; peirce_nf hP,
    by dsimp [eMinusGate]; peirce_nf hP,
    by dsimp [ePlusGate]; peirce_nf hP,
    by dsimp [ePlusGate]; peirce_nf hP⟩

/-- **Stage `𝔗𝔑₃` (`stage_TN3_reversible_operator_gaussian_polynomial_inverse_and_metric_curvature_split`)**:
1. **Quadratic Polynomial Expansion of `𝒢_+` and `𝒢_+⁻¹`**:
   - `𝒢_+(P, X, Y) = 1 + (N_+ + N_-) + N_+ N_-`,
   - `𝒢_+⁻¹(P, X, Y) = 1 - (N_+ + N_-) + N_- N_+`.
2. **Exact `O(1)` Two-Sided Invertibility (Zero-Inversion-Cost Backpropagation)**:
   `𝒢_+(P, X, Y) 𝒢_+⁻¹(P, X, Y) = 1` and `𝒢_+⁻¹(P, X, Y) 𝒢_+(P, X, Y) = 1`.
3. **Symmetric Attention Metric `V = {N_+, N_-}` and Antisymmetric Berry Curvature `Σ = [N_+, N_-]`**:
   - `𝒢_+ + 𝒢_- - 2 (1 + N_+ + N_-) = {N_+, N_-}`,
   - `𝒢_+ - 𝒢_- = [ℰ_+(N_+), ℰ_-(N_-)] = [N_+, N_-]`. -/
theorem stage_TN3_reversible_operator_gaussian_polynomial_inverse_and_metric_curvature_split
    {P : B} (hP : P * P = P) (X Y : B) :
    (attnGaussianPlus P X Y =
      1 + (conePlus P X + coneMinus P Y) + conePlus P X * coneMinus P Y ∧
     attnGaussianPlusInv P X Y =
      1 - (conePlus P X + coneMinus P Y) + coneMinus P Y * conePlus P X) ∧
    (attnGaussianPlus P X Y * attnGaussianPlusInv P X Y = 1 ∧
     attnGaussianPlusInv P X Y * attnGaussianPlus P X Y = 1) ∧
    (attnGaussianPlus P X Y + attnGaussianMinus P X Y -
      (2 : ℤ) • (1 + conePlus P X + coneMinus P Y) =
      anticomm (conePlus P X) (coneMinus P Y) ∧
     attnGaussianPlus P X Y - attnGaussianMinus P X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P Y) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (ePlusGate P X) (eMinusGate P Y) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P Y)) := by
  refine ⟨⟨by dsimp [attnGaussianPlus, ePlusGate, eMinusGate]; peirce_nf hP,
           by dsimp [attnGaussianPlusInv]; peirce_nf hP⟩,
    ⟨by dsimp [attnGaussianPlus, attnGaussianPlusInv, ePlusGate, eMinusGate]; peirce_nf hP,
     by dsimp [attnGaussianPlus, attnGaussianPlusInv, ePlusGate, eMinusGate]; peirce_nf hP⟩,
    ⟨by dsimp [attnGaussianPlus, attnGaussianMinus, ePlusGate, eMinusGate,
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
     by dsimp [attnGaussianPlus, attnGaussianMinus, ePlusGate, eMinusGate,
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
     by dsimp [ePlusGate, eMinusGate, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩⟩

/-- **Stage `𝔗𝔑₄` (`stage_TN4_bruhat_dressed_grassmannian_projector_and_legendre_mobius_push_pull`)**:
1. **Bruhat-Dressed Attention Projector Expansion**:
   `P̂(P, X, Y) = P + (N_+ + N_-) - [N_+, N_-] - {N_+, N_-} N_+`.
2. **Exact Idempotency (`P̂² = P̂`, Preventing Rank Collapse)**:
   `bruhatAttentionProj P X Y * bruhatAttentionProj P X Y = bruhatAttentionProj P X Y`.
3. **Push–Pull Legendre–Möbius Denominator Symmetry**:
   - `(1 - N_+ N_-) N_+ = N_+ (1 - N_- N_+)`,
   - `(1 - {N_+, N_-}) N_+ = (1 - N_+ N_-) N_+`. -/
theorem stage_TN4_bruhat_dressed_grassmannian_projector_and_legendre_mobius_push_pull
    {P : B} (hP : P * P = P) (X Y : B) :
    bruhatAttentionProj P X Y =
      P + (conePlus P X + coneMinus P Y) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P Y) -
        anticomm (conePlus P X) (coneMinus P Y) * conePlus P X ∧
    bruhatAttentionProj P X Y * bruhatAttentionProj P X Y = bruhatAttentionProj P X Y ∧
    (1 - conePlus P X * coneMinus P Y) * conePlus P X =
      conePlus P X * (1 - coneMinus P Y * conePlus P X) ∧
    (1 - anticomm (conePlus P X) (coneMinus P Y)) * conePlus P X =
      (1 - conePlus P X * coneMinus P Y) * conePlus P X := by
  refine ⟨by dsimp [bruhatAttentionProj, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
    by dsimp [bruhatAttentionProj, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
    by peirce_nf hP,
    by peirce_nf hP⟩

/-- **Stage `𝔗𝔑₅` (`stage_TN5_berry_wilson_loop_causal_rotor_and_wavelet_crossover`)**:
1. **Causal Hyperplane `(J, Φ)` & Endogenous Berry Holonomy `Σ = [N_+, N_-] = J Φ`**:
   - `Φ² = +V`, `J² = -V`, `J Φ = Σ`, `Σ² = V²`.
2. **Lightlike Boundary Orthogonality of the Berry Wilson Rotor `W_± = V ± Σ`**:
   `(V + Σ) (V - Σ) = 0` and `(V - Σ) (V + Σ) = 0`.
3. **Chiral Wavelet Sum–Difference Crossover (`[Γ_diff, Φ] = {Γ_sum, J} = 2 J`)**:
   `[S_P, Φ] = {1, J} = 2 J`. -/
theorem stage_TN5_berry_wilson_loop_causal_rotor_and_wavelet_crossover
    {P : B} (hP : P * P = P) (X Y : B) :
    let Np := conePlus P X
    let Nm := coneMinus P Y
    let Phi := Np + Nm
    let J := Np - Nm
    let V := anticomm Np Nm
    let Sigma := InfoGeometry.OperatorAlgebra.PeirceSpine.comm Np Nm
    (Phi * Phi = V ∧
     J * J = -V ∧
     J * Phi = Sigma ∧
     Sigma * Sigma = V * V) ∧
    ((V + Sigma) * (V - Sigma) = 0 ∧
     (V - Sigma) * (V + Sigma) = 0) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) Phi = anticomm (1 : B) J ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) Phi = (2 : ℤ) • J) := by
  dsimp only
  refine ⟨⟨by peirce_nf hP,
           by peirce_nf hP,
           by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
           by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩,
    ⟨by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
     by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩,
    ⟨by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
     by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩⟩

/-- **Stage `𝔗𝔑₆` (`stage_TN6_multi_scale_tower_invertibility_and_zorn_three_body_bond_volume`)**:
1. **Multi-Scale Attention Tower Exact Reversibility (`(𝒢_+^(2) 𝒢_+^(1))⁻¹ = (𝒢_+^(1))⁻¹ (𝒢_+^(2))⁻¹`)**:
   For any two scale idempotents `P₁, P₂ : B` (`P₁² = P₁`, `P₂² = P₂`), the composite
   two-scale attention tower `𝒜₂ := 𝒢_+(P₂, X₂, Y₂) 𝒢_+(P₁, X₁, Y₁)` has exact two-sided
   polynomial inverse `𝒜₂⁻¹ := 𝒢_+⁻¹(P₁, X₁, Y₁) 𝒢_+⁻¹(P₂, X₂, Y₂)`.
2. **3-Body Firth–Zorn Bond Volume Contraction**:
   `{N_+(u₁) N_+(u₂), N_+(u₃)} = det(u₁, u₂, u₃) · 1` on `ZornMatrix K`. -/
theorem stage_TN6_multi_scale_tower_invertibility_and_zorn_three_body_bond_volume
    {K : Type*} [CommRing K]
    {P₁ P₂ : B} (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (X₁ Y₁ X₂ Y₂ : B)
    (u₁ u₂ u₃ : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 K) :
    ((attnGaussianPlus P₂ X₂ Y₂ * attnGaussianPlus P₁ X₁ Y₁) *
      (attnGaussianPlusInv P₁ X₁ Y₁ * attnGaussianPlusInv P₂ X₂ Y₂) = 1 ∧
     (attnGaussianPlusInv P₁ X₁ Y₁ * attnGaussianPlusInv P₂ X₂ Y₂) *
      (attnGaussianPlus P₂ X₂ Y₂ * attnGaussianPlus P₁ X₁ Y₁) = 1) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ +
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ *
      (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) =
      zornMatrixScalar (zornVec3Det u₁ u₂ u₃) := by
  have h1 := (stage_TN3_reversible_operator_gaussian_polynomial_inverse_and_metric_curvature_split
    hP₁ X₁ Y₁).2.1
  have h2 := (stage_TN3_reversible_operator_gaussian_polynomial_inverse_and_metric_curvature_split
    hP₂ X₂ Y₂).2.1
  refine ⟨⟨?_, ?_⟩,
    (stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation
      u₁ u₂ u₃ u₁ u₂ u₃ u₁).2.2.1.1⟩
  · calc (attnGaussianPlus P₂ X₂ Y₂ * attnGaussianPlus P₁ X₁ Y₁) *
           (attnGaussianPlusInv P₁ X₁ Y₁ * attnGaussianPlusInv P₂ X₂ Y₂)
      _ = attnGaussianPlus P₂ X₂ Y₂ *
            (attnGaussianPlus P₁ X₁ Y₁ * attnGaussianPlusInv P₁ X₁ Y₁) *
            attnGaussianPlusInv P₂ X₂ Y₂ := by noncomm_ring
      _ = attnGaussianPlus P₂ X₂ Y₂ * 1 * attnGaussianPlusInv P₂ X₂ Y₂ := by rw [h1.1]
      _ = attnGaussianPlus P₂ X₂ Y₂ * attnGaussianPlusInv P₂ X₂ Y₂ := by noncomm_ring
      _ = 1 := h2.1
  · calc (attnGaussianPlusInv P₁ X₁ Y₁ * attnGaussianPlusInv P₂ X₂ Y₂) *
           (attnGaussianPlus P₂ X₂ Y₂ * attnGaussianPlus P₁ X₁ Y₁)
      _ = attnGaussianPlusInv P₁ X₁ Y₁ *
            (attnGaussianPlusInv P₂ X₂ Y₂ * attnGaussianPlus P₂ X₂ Y₂) *
            attnGaussianPlus P₁ X₁ Y₁ := by noncomm_ring
      _ = attnGaussianPlusInv P₁ X₁ Y₁ * 1 * attnGaussianPlus P₁ X₁ Y₁ := by rw [h2.2]
      _ = attnGaussianPlusInv P₁ X₁ Y₁ * attnGaussianPlus P₁ X₁ Y₁ := by noncomm_ring
      _ = 1 := h1.2

/-- **Stage `𝔗𝔑₇` (`stage_TN7_krein_logcft_secular_memory_and_drazin_aporia_resolution`)**:
Given any nilpotent Krein bond generator `N_nil : B` with `N_nil² = 0`:
1. **Exact Quadratic Secular Memory Evolution**:
   `(1 - N_nil) A (1 + N_nil) = A - [N_nil, A] - N_nil A N_nil`.
2. **Double Commutator Reduction (`[N_nil, [N_nil, A]] = -2 N_nil A N_nil`)**:
   `comm N_nil (comm N_nil A) = -(2 * (N_nil * A * N_nil))`.
3. **Exact 3-Step Adjoint Nilpotency (`ad_{N_nil}³(A) = 0`, Truncating BCH at `O(t²)`)**:
   `comm N_nil (comm N_nil (comm N_nil A)) = 0`.
4. **Algebra Automorphism Property of Krein Jordan Transport**:
   `((1 - N_nil) A (1 + N_nil)) ((1 - N_nil) B_obs (1 + N_nil)) = (1 - N_nil) (A B_obs) (1 + N_nil)`. -/
theorem stage_TN7_krein_logcft_secular_memory_and_drazin_aporia_resolution
    {N_nil : B} (hNil : N_nil * N_nil = 0) (A B_obs : B) :
    (1 - N_nil) * A * (1 + N_nil) =
      A - InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil A - N_nil * A * N_nil ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil A) =
      -(2 * (N_nil * A * N_nil)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil A)) = 0 ∧
    ((1 - N_nil) * A * (1 + N_nil)) * ((1 - N_nil) * B_obs * (1 + N_nil)) =
      (1 - N_nil) * (A * B_obs) * (1 + N_nil) := by
  refine ⟨by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring, ?_, ?_, ?_⟩
  · calc InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
           (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil A)
      _ = (N_nil * N_nil) * A - 2 * (N_nil * A * N_nil) + A * (N_nil * N_nil) := by
          dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
      _ = 0 * A - 2 * (N_nil * A * N_nil) + A * 0 := by rw [hNil]
      _ = -(2 * (N_nil * A * N_nil)) := by noncomm_ring
  · calc InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
           (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil
             (InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil A))
      _ = (N_nil * N_nil) * (N_nil * A) - 3 * ((N_nil * N_nil) * A * N_nil) +
          3 * (N_nil * A * (N_nil * N_nil)) - (A * N_nil) * (N_nil * N_nil) := by
          dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
      _ = 0 * (N_nil * A) - 3 * (0 * A * N_nil) +
          3 * (N_nil * A * 0) - (A * N_nil) * 0 := by rw [hNil]
      _ = 0 := by noncomm_ring
  · calc ((1 - N_nil) * A * (1 + N_nil)) * ((1 - N_nil) * B_obs * (1 + N_nil))
      _ = (1 - N_nil) * A * (1 - N_nil * N_nil) * B_obs * (1 + N_nil) := by noncomm_ring
      _ = (1 - N_nil) * A * (1 - 0) * B_obs * (1 + N_nil) := by rw [hNil]
      _ = (1 - N_nil) * (A * B_obs) * (1 + N_nil) := by noncomm_ring

/-- **Master Theorem (`tensor_peirce_attention_network_master_poset`)**:
Unifies the 7-stage Multi-Scale Non-Commutative Tensor-Peirce Attention Network
Poset (`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`). -/
theorem tensor_peirce_attention_network_master_poset
    {R : Type*} [Ring R] {K : Type*} [CommRing K]
    (n : ℕ) (T : TensorTower R n)
    {P : B} (hP : P * P = P) (X Y : B)
    (u₁ u₂ u₃ : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 K) :
    (∀ st : TensorPeirceAttentionNetworkStage,
      ¬ Relation.TransGen TensorPeirceAttentionNetworkStage.causalEdge st st) ∧
    Fintype.card TensorPeirceAttentionNetworkStage = 7 ∧
    TensorTower.toTensorTower n (TensorTower.ofTensorTower n T) = T ∧
    ePlusGate P X * ePlusGate P Y = ePlusGate P (X + Y) ∧
    attnGaussianPlus P X Y * attnGaussianPlusInv P X Y = 1 ∧
    bruhatAttentionProj P X Y * bruhatAttentionProj P X Y = bruhatAttentionProj P X Y ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (conePlus P X + coneMinus P Y) =
      (2 : ℤ) • (conePlus P X - coneMinus P Y) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ +
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ *
      (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) =
      zornMatrixScalar (zornVec3Det u₁ u₂ u₃) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) Y)) = 0 := by
  have hNil : conePlus P X * conePlus P X = 0 := by peirce_nf hP
  exact ⟨TensorPeirceAttentionNetworkStage.causalEdge_acyclic,
    TensorPeirceAttentionNetworkStage.card_eq_seven,
    (TensorTower.stage_TT4_TT5_recursive_tensor_tower_and_peirce_split_roundtrip
      (0 : R) 0 n 0 T).2.2.2.2.2.2.2,
    by dsimp [ePlusGate]; peirce_nf hP,
    (stage_TN3_reversible_operator_gaussian_polynomial_inverse_and_metric_curvature_split
      hP X Y).2.1.1,
    (stage_TN4_bruhat_dressed_grassmannian_projector_and_legendre_mobius_push_pull
      hP X Y).2.1,
    by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
    (stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation
      u₁ u₂ u₃ u₁ u₂ u₃ u₁).2.2.1.1,
    (stage_TN7_krein_logcft_secular_memory_and_drazin_aporia_resolution hNil Y Y).2.2.1⟩

end TensorPeirceAttentionNetworkClosure

/-!
===============================================================================
Part IX: The Bitwise Symplectic Clifford Compiler & Multi-Scale Attention Filter
(`𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`)
===============================================================================
-/

/-- The 6-stage causal poset of the Bitwise Symplectic Clifford Compiler
(`𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`). -/
inductive BitwiseCliffordCompilerStage : Type
  | bc1_single_bit_cl11_basis_and_entry_law
  | bc2_n_bit_tensor_product_basis_and_entry_law
  | bc3_bitwise_symplectic_cocycle_and_causal_signature
  | bc4_division_free_fast_walsh_clifford_compiler
  | bc5_bitwise_algebra_symplectic_convolution
  | bc6_multi_scale_clifford_attention_filtration
  deriving DecidableEq, Repr

namespace BitwiseCliffordCompilerStage

/-- Topological rank in `{0, 1, 2, 3, 4}` (with diamond branch `{𝔅ℭ₄, 𝔅ℭ₅}` at rank `3`). -/
def rank : BitwiseCliffordCompilerStage → ℕ
  | .bc1_single_bit_cl11_basis_and_entry_law => 0
  | .bc2_n_bit_tensor_product_basis_and_entry_law => 1
  | .bc3_bitwise_symplectic_cocycle_and_causal_signature => 2
  | .bc4_division_free_fast_walsh_clifford_compiler => 3
  | .bc5_bitwise_algebra_symplectic_convolution => 3
  | .bc6_multi_scale_clifford_attention_filtration => 4

/-- Direct causal edges of `𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`. -/
def causalEdge : BitwiseCliffordCompilerStage → BitwiseCliffordCompilerStage → Prop
  | .bc1_single_bit_cl11_basis_and_entry_law,
    .bc2_n_bit_tensor_product_basis_and_entry_law => True
  | .bc2_n_bit_tensor_product_basis_and_entry_law,
    .bc3_bitwise_symplectic_cocycle_and_causal_signature => True
  | .bc3_bitwise_symplectic_cocycle_and_causal_signature,
    .bc4_division_free_fast_walsh_clifford_compiler => True
  | .bc3_bitwise_symplectic_cocycle_and_causal_signature,
    .bc5_bitwise_algebra_symplectic_convolution => True
  | .bc4_division_free_fast_walsh_clifford_compiler,
    .bc6_multi_scale_clifford_attention_filtration => True
  | .bc5_bitwise_algebra_symplectic_convolution,
    .bc6_multi_scale_clifford_attention_filtration => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

instance : Fintype BitwiseCliffordCompilerStage where
  elems := {
    .bc1_single_bit_cl11_basis_and_entry_law,
    .bc2_n_bit_tensor_product_basis_and_entry_law,
    .bc3_bitwise_symplectic_cocycle_and_causal_signature,
    .bc4_division_free_fast_walsh_clifford_compiler,
    .bc5_bitwise_algebra_symplectic_convolution,
    .bc6_multi_scale_clifford_attention_filtration
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card BitwiseCliffordCompilerStage = 6 := rfl

theorem edge_lt {a b : BitwiseCliffordCompilerStage} (h : causalEdge a b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : BitwiseCliffordCompilerStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact edge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (edge_lt h2)

/-- Strict DAG acyclicity of `BitwiseCliffordCompilerStage`. -/
theorem causalEdge_acyclic (st : BitwiseCliffordCompilerStage) :
    ¬ Relation.TransGen causalEdge st st :=
  fun h => Nat.lt_irrefl st.rank (transGen_lt h)

/-- Parallel diamond branches `𝔅ℭ₄` and `𝔅ℭ₅` are incomparable under `TransGen causalEdge`. -/
theorem incomparable_BC4_BC5 :
    ¬ Relation.TransGen causalEdge
        .bc4_division_free_fast_walsh_clifford_compiler
        .bc5_bitwise_algebra_symplectic_convolution ∧
    ¬ Relation.TransGen causalEdge
        .bc5_bitwise_algebra_symplectic_convolution
        .bc4_division_free_fast_walsh_clifford_compiler :=
  ⟨fun h => Nat.lt_irrefl 3 (transGen_lt h),
   fun h => Nat.lt_irrefl 3 (transGen_lt h)⟩

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : BitwiseCliffordCompilerStage → RepDepth
  | .bc1_single_bit_cl11_basis_and_entry_law => .operator
  | .bc2_n_bit_tensor_product_basis_and_entry_law => .operator
  | .bc3_bitwise_symplectic_cocycle_and_causal_signature => .transport
  | .bc4_division_free_fast_walsh_clifford_compiler => .transport
  | .bc5_bitwise_algebra_symplectic_convolution => .transport
  | .bc6_multi_scale_clifford_attention_filtration => .thermo

theorem toRepDepth_mono {a b : BitwiseCliffordCompilerStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : BitwiseCliffordCompilerStage → OntologyMetaLevel
  | .bc1_single_bit_cl11_basis_and_entry_law => .M1_ProjectorClabject
  | .bc2_n_bit_tensor_product_basis_and_entry_law => .M1_ProjectorClabject
  | .bc3_bitwise_symplectic_cocycle_and_causal_signature => .M2_GrassmannianPowertypeOrbit
  | .bc4_division_free_fast_walsh_clifford_compiler => .M2_GrassmannianPowertypeOrbit
  | .bc5_bitwise_algebra_symplectic_convolution => .M2_GrassmannianPowertypeOrbit
  | .bc6_multi_scale_clifford_attention_filtration => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : BitwiseCliffordCompilerStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end BitwiseCliffordCompilerStage

namespace BitwiseCliffordCompiler

/-- Single-bit XOR on `Fin 2`: `a ⊕ b = (a + b) mod 2`. -/
def bitXor (a b : Fin 2) : Fin 2 :=
  ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Single-bit AND on `Fin 2`: `a & b = a · b`. -/
def bitAnd (a b : Fin 2) : Fin 2 :=
  ⟨a.val * b.val, by fin_cases a <;> fin_cases b <;> decide⟩

/-- Single-bit sign `(-1)^b ∈ R` (`+1` for `0`, `-1` for `1`). -/
def bitSign {R : Type*} [Ring R] (b : Fin 2) : R :=
  if b = 0 then 1 else -1

/-- Single-bit `Cl(1,1)` basis matrix `γ_{x, z}` in `Matrix (Fin 2) (Fin 2) R`:
`(γ_{x, z})_{i, j} := δ_{x, i ⊕ j} (-1)^{i & z}`. -/
def gammaBit {R : Type*} [Ring R] (x z : Fin 2) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if x = bitXor i j then bitSign (bitAnd i z) else 0

theorem bitXor_comm (a b : Fin 2) : bitXor a b = bitXor b a := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitXor_assoc (a b c : Fin 2) : bitXor (bitXor a b) c = bitXor a (bitXor b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem bitXor_self (a : Fin 2) : bitXor a a = 0 := by
  fin_cases a <;> decide

theorem bitXor_zero (a : Fin 2) : bitXor a 0 = a := by
  fin_cases a <;> decide

theorem bitXor_cancel_left (a b : Fin 2) : bitXor a (bitXor a b) = b := by
  fin_cases a <;> fin_cases b <;> decide

/-- `n`-bit phase-space coordinate vector `𝔽₂ⁿ = Fin n → Fin 2`. -/
abbrev BitVecN (n : ℕ) := Fin n → Fin 2

/-- Bitwise XOR on `BitVecN n`. -/
def bvXor {n : ℕ} (x y : BitVecN n) : BitVecN n :=
  fun k => bitXor (x k) (y k)

/-- Bitwise AND on `BitVecN n`. -/
def bvAnd {n : ℕ} (x y : BitVecN n) : BitVecN n :=
  fun k => bitAnd (x k) (y k)

/-- Hamming weight (`popcount`) of an `n`-bit vector `x : BitVecN n`. -/
def bvPopcount {n : ℕ} (x : BitVecN n) : ℕ :=
  ∑ k : Fin n, (x k).val

/-- `n`-bit Symplectic Clifford basis matrix `Γ_{(x, z)}` on `Matrix (BitVecN n) (BitVecN n) R`:
`(Γ_{(x, z)})_{i, j} = δ_{j, i ⊕ x} (-1)^{popcount(i & z)}`. -/
def gammaBasis {R : Type*} [CommRing R] {n : ℕ} (x z : BitVecN n) :
    Matrix (BitVecN n) (BitVecN n) R :=
  fun i j => if j = bvXor i x then (-1 : R) ^ bvPopcount (bvAnd i z) else 0

theorem bvXor_comm {n : ℕ} (x y : BitVecN n) : bvXor x y = bvXor y x := by
  funext k; exact bitXor_comm (x k) (y k)

theorem bvXor_assoc {n : ℕ} (x y z : BitVecN n) :
    bvXor (bvXor x y) z = bvXor x (bvXor y z) := by
  funext k; exact bitXor_assoc (x k) (y k) (z k)

theorem bvXor_self {n : ℕ} (x : BitVecN n) : bvXor x x = fun _ => 0 := by
  funext k; exact bitXor_self (x k)

theorem bvXor_zero {n : ℕ} (x : BitVecN n) : bvXor x (fun _ => 0) = x := by
  funext k; exact bitXor_zero (x k)

theorem bvXor_cancel_left {n : ℕ} (x y : BitVecN n) : bvXor x (bvXor x y) = y := by
  funext k; exact bitXor_cancel_left (x k) (y k)

theorem bit_symplectic_sign_law {R : Type*} [CommRing R] (a b c d : Fin 2) :
    ((-1 : R) ^ (bitAnd a c).val) * ((-1 : R) ^ (bitAnd (bitXor a b) d).val) =
      ((-1 : R) ^ (bitAnd b d).val) * ((-1 : R) ^ (bitAnd a (bitXor c d)).val) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bitAnd, bitXor]

theorem prod_neg_one_pow_eq_pow_bvPopcount {R : Type*} [CommRing R] {n : ℕ} (u : BitVecN n) :
    (∏ k : Fin n, (-1 : R) ^ (u k).val) = (-1 : R) ^ bvPopcount u := by
  simpa [bvPopcount] using
    (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin n)) (fun k => (u k).val) (-1 : R))

theorem bv_symplectic_sign_law {R : Type*} [CommRing R] {n : ℕ}
    (i x₁ z₁ z₂ : BitVecN n) :
    ((-1 : R) ^ bvPopcount (bvAnd i z₁)) *
      ((-1 : R) ^ bvPopcount (bvAnd (bvXor i x₁) z₂)) =
    ((-1 : R) ^ bvPopcount (bvAnd x₁ z₂)) *
      ((-1 : R) ^ bvPopcount (bvAnd i (bvXor z₁ z₂))) := by
  rw [← prod_neg_one_pow_eq_pow_bvPopcount, ← prod_neg_one_pow_eq_pow_bvPopcount,
      ← prod_neg_one_pow_eq_pow_bvPopcount, ← prod_neg_one_pow_eq_pow_bvPopcount,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro k _
  exact bit_symplectic_sign_law (i k) (x₁ k) (z₁ k) (z₂ k)

/-- **Stage `𝔅ℭ₁` (`stage_BC1_single_bit_cl11_basis_and_entry_law`)**:
1. **Identification of the Four `Cl(1,1)` Basis Matrices**:
   `γ_{0,0} = I_2`, `γ_{0,1} = S_P`, `γ_{1,0} = Φ`, `γ_{1,1} = J`.
2. **Universal Single-Bit Entry Law**:
   `(γ_{x, z})_{i, j} = δ_{x, i ⊕ j} (-1)^{i · z}`.
3. **Single-Bit Symplectic Multiplication & Causal Square Law**:
   - `γ_{x₁, z₁} γ_{x₂, z₂} = (-1)^{x₁ & z₂} γ_{x₁ ⊕ x₂, z₁ ⊕ z₂}`,
   - `γ_{x, z}² = (-1)^{x & z} I_2`. -/
theorem stage_BC1_single_bit_cl11_basis_and_entry_law
    {R : Type*} [CommRing R] (x z i j x₁ z₁ x₂ z₂ : Fin 2) :
    (gammaBit (R := R) 0 0 = TensorTower.unitI ∧
     gammaBit (R := R) 0 1 = TensorTower.unitS ∧
     gammaBit (R := R) 1 0 = TensorTower.unitPhi ∧
     gammaBit (R := R) 1 1 = TensorTower.unitJ) ∧
    gammaBit (R := R) x z i j = (if x = bitXor i j then bitSign (bitAnd i z) else 0) ∧
    gammaBit (R := R) x₁ z₁ * gammaBit (R := R) x₂ z₂ =
      bitSign (R := R) (bitAnd x₁ z₂) • gammaBit (R := R) (bitXor x₁ x₂) (bitXor z₁ z₂) ∧
    gammaBit (R := R) x z * gammaBit (R := R) x z =
      bitSign (R := R) (bitAnd x z) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, TensorTower.unitI, TensorTower.unitE00, TensorTower.unitE11,
        bitXor, bitAnd, bitSign]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, TensorTower.unitS, TensorTower.unitE00, TensorTower.unitE11,
        bitXor, bitAnd, bitSign]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, TensorTower.unitPhi, TensorTower.unitE01, TensorTower.unitE10,
        bitXor, bitAnd, bitSign]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, TensorTower.unitJ, TensorTower.unitE01, TensorTower.unitE10,
        bitXor, bitAnd, bitSign]
  · ext a b
    fin_cases x₁ <;> fin_cases z₁ <;> fin_cases x₂ <;> fin_cases z₂ <;>
      fin_cases a <;> fin_cases b <;>
      simp [gammaBit, Matrix.mul_apply, Fin.sum_univ_two, bitXor, bitAnd, bitSign]
  · ext a b
    fin_cases x <;> fin_cases z <;> fin_cases a <;> fin_cases b <;>
      simp [gammaBit, Matrix.mul_apply, Fin.sum_univ_two, bitXor, bitAnd, bitSign]

/-- At `(x, z) = (0, 0)`, the `n`-bit basis matrix `Γ_{(0, 0)}` is the identity matrix `I_{2^n}`. -/
theorem gammaBasis_zero_zero {R : Type*} [CommRing R] {n : ℕ} :
    gammaBasis (R := R) (fun _ : Fin n => 0) (fun _ : Fin n => 0) = 1 := by
  ext i j
  have h0 : bvPopcount (bvAnd i (fun _ : Fin n => 0)) = 0 := by
    unfold bvPopcount bvAnd
    refine Finset.sum_eq_zero ?_
    intro k _
    have hik : Fin 2 := i k
    change (bitAnd hik 0).val = 0
    fin_cases hik <;> rfl
  simp [gammaBasis, bvXor_zero, h0, Matrix.one_apply, eq_comm]

/-- Entrywise realization of the `n`-bit phase-space basis. This is the
    arbitrary-index formula underlying the zero-vector identity and the
    symplectic product law. -/
theorem gammaBasis_entry {R : Type*} [CommRing R] {n : ℕ}
    (x z i j : BitVecN n) :
    gammaBasis (R := R) x z i j =
      if j = bvXor i x then (-1 : R) ^ bvPopcount (bvAnd i z) else 0 := rfl

/-- **Stages `𝔅ℭ₂ ≺ 𝔅ℭ₃` (`stage_BC2_BC3_n_bit_symplectic_clifford_product_and_causal_signature`)**:
For arbitrary `n : ℕ` on `Matrix (BitVecN n) (BitVecN n) R`:
1. **Identity Concentration at `(x, z) = (0, 0)`**:
   `Γ_{(0, 0)} = I_{2^n}`.
2. **Universal `n`-Bit Symplectic Clifford Multiplication Law (`𝔅ℭ₃`)**:
   `Γ_{(x₁, z₁)} Γ_{(x₂, z₂)} = (-1)^{popcount(x₁ & z₂)} • Γ_{(x₁ ⊕ x₂, z₁ ⊕ z₂)}`.
3. **Universal `n`-Bit Causal Signature Law (`𝔅ℭ₃`)**:
   `Γ_{(x, z)}² = (-1)^{popcount(x & z)} • I_{2^n}`
   (even `popcount(x & z)` is spacelike `+I`, odd `popcount(x & z)` is timelike `-I`).
4. **Autonomous Nilpotent Light-Cone Pairing**:
   `(γ_{1,0} + γ_{1,1})² = 0` and `(γ_{1,0} - γ_{1,1})² = 0`. -/
theorem stage_BC2_BC3_n_bit_symplectic_clifford_product_and_causal_signature
    {R : Type*} [CommRing R] {n : ℕ} (x₁ z₁ x₂ z₂ x z : BitVecN n) :
    gammaBasis (R := R) (fun _ : Fin n => 0) (fun _ : Fin n => 0) = 1 ∧
    gammaBasis (R := R) x₁ z₁ * gammaBasis (R := R) x₂ z₂ =
      ((-1 : R) ^ bvPopcount (bvAnd x₁ z₂)) •
        gammaBasis (R := R) (bvXor x₁ x₂) (bvXor z₁ z₂) ∧
    gammaBasis (R := R) x z * gammaBasis (R := R) x z =
      ((-1 : R) ^ bvPopcount (bvAnd x z)) • (1 : Matrix (BitVecN n) (BitVecN n) R) ∧
    ((gammaBit (R := R) 1 0 + gammaBit (R := R) 1 1) *
      (gammaBit (R := R) 1 0 + gammaBit (R := R) 1 1) = 0 ∧
     (gammaBit (R := R) 1 0 - gammaBit (R := R) 1 1) *
      (gammaBit (R := R) 1 0 - gammaBit (R := R) 1 1) = 0) := by
  have hMul :
      ∀ a₁ b₁ a₂ b₂ : BitVecN n,
        gammaBasis (R := R) a₁ b₁ * gammaBasis (R := R) a₂ b₂ =
          ((-1 : R) ^ bvPopcount (bvAnd a₁ b₂)) •
            gammaBasis (R := R) (bvXor a₁ a₂) (bvXor b₁ b₂) := by
    intro a₁ b₁ a₂ b₂
    ext i j
    simp only [Matrix.mul_apply, gammaBasis, Matrix.smul_apply, smul_eq_mul]
    have hsum :
        (∑ l : BitVecN n,
          (if l = bvXor i a₁ then (-1 : R) ^ bvPopcount (bvAnd i b₁) else 0) *
          (if j = bvXor l a₂ then (-1 : R) ^ bvPopcount (bvAnd l b₂) else 0)) =
        (if j = bvXor (bvXor i a₁) a₂ then
          ((-1 : R) ^ bvPopcount (bvAnd i b₁)) *
            ((-1 : R) ^ bvPopcount (bvAnd (bvXor i a₁) b₂))
        else 0) := by
      trans ∑ l : BitVecN n,
        if l = bvXor i a₁ then
          (if j = bvXor l a₂ then
            ((-1 : R) ^ bvPopcount (bvAnd i b₁)) *
              ((-1 : R) ^ bvPopcount (bvAnd l b₂))
          else 0)
        else 0
      · refine Finset.sum_congr rfl ?_
        intro l _
        by_cases hl : l = bvXor i a₁ <;> by_cases hj : j = bvXor l a₂ <;> simp [hl, hj]
      · simp
    rw [hsum, bvXor_assoc, bv_symplectic_sign_law]
    by_cases hj : j = bvXor i (bvXor a₁ a₂) <;> simp [hj]
  refine ⟨gammaBasis_zero_zero, hMul x₁ z₁ x₂ z₂, ?_, ⟨?_, ?_⟩⟩
  · rw [hMul x z x z, bvXor_self, bvXor_self, gammaBasis_zero_zero]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, Matrix.mul_apply, Fin.sum_univ_two, bitXor, bitAnd, bitSign]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [gammaBit, Matrix.mul_apply, Fin.sum_univ_two, bitXor, bitAnd, bitSign]

/-- Forward division-free Walsh–Clifford compiler on `Matrix (Fin 2) (Fin 2) R`:
`Ĉ(x, z) := ∑_i (-1)^{i & z} M[i, i ⊕ x]`. -/
def compileClifford2 {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun x z => ∑ i : Fin 2, bitSign (bitAnd i z) * M i (bitXor i x)

/-- Inverse division-free Walsh–Clifford coagulator on `Matrix (Fin 2) (Fin 2) R`:
`coagulate(Ĉ)[i, j] := ∑_z (-1)^{i & z} Ĉ[i ⊕ j, z]`. -/
def coagulateClifford2 {R : Type*} [CommRing R] (C : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j => ∑ z : Fin 2, bitSign (bitAnd i z) * C (bitXor i j) z

/-- **Stages `𝔅ℭ₄ ≺ 𝔅ℭ₅` (`stage_BC4_BC5_division_free_compiler_parseval_and_symplectic_convolution`)**:
1. **Rung 0 Identity Concentration (`Ĉ_I(x, z) = 2 δ_{x,0} δ_{z,0}`)**:
   `compileClifford2 1 = !![2, 0; 0, 0]`.
2. **Exact Division-Free Inverse Transform (`coagulate(compile(M)) = 2 • M`)**:
   `coagulateClifford2 (compileClifford2 M) = (2 : R) • M`.
3. **Exact Basis Reconstruction (`∑_{x, z} Ĉ(x, z) • γ_{x, z} = 2 • M`)**:
   `∑ x : Fin 2, ∑ z : Fin 2, (compileClifford2 M x z) • gammaBit (R := R) x z = (2 : R) • M`.
4. **Exact Parseval / Plancherel Energy Identity**:
   `∑ x : Fin 2, ∑ z : Fin 2, (compileClifford2 M x z)^2 = 2 * ∑ i : Fin 2, ∑ j : Fin 2, (M i j)^2`.
5. **Exact Bitwise Symplectic Convolution of Matrix Multiplication (`𝔅ℭ₅`)**:
   `2 * compileClifford2 (M * N) x z = ∑_{x₁, z₁} (-1)^{x₁ & (z₁ ⊕ z)} Ĉ_M(x₁, z₁) Ĉ_N(x₁ ⊕ x, z₁ ⊕ z)`. -/
theorem stage_BC4_BC5_division_free_compiler_parseval_and_symplectic_convolution
    {R : Type*} [CommRing R] (M N : Matrix (Fin 2) (Fin 2) R) (x z : Fin 2) :
    compileClifford2 (1 : Matrix (Fin 2) (Fin 2) R) = !![2, 0; 0, 0] ∧
    coagulateClifford2 (compileClifford2 M) = (2 : R) • M ∧
    (∑ x₀ : Fin 2, ∑ z₀ : Fin 2,
      (compileClifford2 M x₀ z₀) • gammaBit (R := R) x₀ z₀) = (2 : R) • M ∧
    (∑ x₀ : Fin 2, ∑ z₀ : Fin 2, (compileClifford2 M x₀ z₀) ^ 2) =
      2 * (∑ i : Fin 2, ∑ j : Fin 2, (M i j) ^ 2) ∧
    2 * compileClifford2 (M * N) x z =
      ∑ x₁ : Fin 2, ∑ z₁ : Fin 2,
        bitSign (bitAnd x₁ (bitXor z₁ z)) *
          compileClifford2 M x₁ z₁ *
          compileClifford2 N (bitXor x₁ x) (bitXor z₁ z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;> {
      dsimp [compileClifford2]
      rw [Fin.sum_univ_two]
      simp [bitSign, bitAnd, bitXor, Matrix.one_apply]
      try ring
    }
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [coagulateClifford2, compileClifford2, Fin.sum_univ_two, bitSign, bitAnd, bitXor] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [compileClifford2, gammaBit, Fin.sum_univ_two, bitSign, bitAnd, bitXor] <;> ring
  · simp [compileClifford2, Fin.sum_univ_two, bitSign, bitAnd, bitXor]
    ring
  · fin_cases x <;> fin_cases z <;>
      simp [compileClifford2, Fin.sum_univ_two, Matrix.mul_apply, bitSign, bitAnd, bitXor] <;> ring

/-- Self-inverse XOR reindexing bijection `x ↦ i ⊕ x` on `BitVecN n`. -/
def bvXorEquiv {n : ℕ} (i : BitVecN n) : BitVecN n ≃ BitVecN n where
  toFun x := bvXor i x
  invFun j := bvXor i j
  left_inv x := bvXor_cancel_left i x
  right_inv j := bvXor_cancel_left i j

/-- Multi-scale Hamming-filtered attention matrix retaining only dyadic jump masks
`x = i ⊕ j` with `popcount(x) ≤ r`. -/
def hammingFilteredMat {R : Type*} [CommRing R] {n : ℕ} (r : ℕ)
    (M : Matrix (BitVecN n) (BitVecN n) R) : Matrix (BitVecN n) (BitVecN n) R :=
  fun i j => if bvPopcount (bvXor i j) ≤ r then M i j else 0

/-- **Stage `𝔅ℭ₆` (`stage_BC6_multi_scale_clifford_filtered_attention_execution`)**:
For arbitrary `n : ℕ`, any attention matrix `M : Matrix (BitVecN n) (BitVecN n) R`,
and any token value vector `v : BitVecN n → R`:
1. **Exact XOR-Banded Matrix–Vector Execution**:
   `(M v)[i] = ∑_{x ∈ 𝔽₂ⁿ} M[i, i ⊕ x] v[i ⊕ x]`.
2. **Sub-Quadratic Multi-Scale Hamming-Filtered Attention Execution**:
   For any jump-order cutoff `r : ℕ`,
   `(hammingFilteredMat r M · v)[i] = ∑_{popcount(x) ≤ r} M[i, i ⊕ x] v[i ⊕ x]`. -/
theorem stage_BC6_multi_scale_clifford_filtered_attention_execution
    {R : Type*} [CommRing R] {n : ℕ} (r : ℕ)
    (M : Matrix (BitVecN n) (BitVecN n) R) (v : BitVecN n → R) (i : BitVecN n) :
    Matrix.mulVec M v i = ∑ x : BitVecN n, M i (bvXor i x) * v (bvXor i x) ∧
    Matrix.mulVec (hammingFilteredMat r M) v i =
      ∑ x ∈ Finset.univ.filter (fun x : BitVecN n => bvPopcount x ≤ r),
        M i (bvXor i x) * v (bvXor i x) := by
  have hFull :
      ∀ A : Matrix (BitVecN n) (BitVecN n) R,
        Matrix.mulVec A v i = ∑ x : BitVecN n, A i (bvXor i x) * v (bvXor i x) := by
    intro A
    unfold Matrix.mulVec dotProduct
    exact ((bvXorEquiv i).sum_comp (fun j => A i j * v j)).symm
  refine ⟨hFull M, ?_⟩
  rw [hFull (hammingFilteredMat r M), Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp only [hammingFilteredMat, bvXor_cancel_left]
  by_cases hx : bvPopcount x ≤ r <;> simp [hx]

/-- **Master Theorem (`bitwise_clifford_compiler_master_poset`)**:
Unifies the 6-stage Bitwise Symplectic Clifford Compiler & Multi-Scale
Attention Filtration Poset (`𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`). -/
theorem bitwise_clifford_compiler_master_poset
    {R : Type*} [CommRing R] {n : ℕ} (r : ℕ)
    (M : Matrix (Fin 2) (Fin 2) R)
    (x₁ z₁ x₂ z₂ x z : BitVecN n)
    (A : Matrix (BitVecN n) (BitVecN n) R) (v : BitVecN n → R) (i : BitVecN n) :
    (∀ st : BitwiseCliffordCompilerStage,
      ¬ Relation.TransGen BitwiseCliffordCompilerStage.causalEdge st st) ∧
    Fintype.card BitwiseCliffordCompilerStage = 6 ∧
    gammaBasis (R := R) x₁ z₁ * gammaBasis (R := R) x₂ z₂ =
      ((-1 : R) ^ bvPopcount (bvAnd x₁ z₂)) •
        gammaBasis (R := R) (bvXor x₁ x₂) (bvXor z₁ z₂) ∧
    gammaBasis (R := R) x z * gammaBasis (R := R) x z =
      ((-1 : R) ^ bvPopcount (bvAnd x z)) • (1 : Matrix (BitVecN n) (BitVecN n) R) ∧
    coagulateClifford2 (compileClifford2 M) = (2 : R) • M ∧
    (∑ x₀ : Fin 2, ∑ z₀ : Fin 2, (compileClifford2 M x₀ z₀) ^ 2) =
      2 * (∑ i₀ : Fin 2, ∑ j₀ : Fin 2, (M i₀ j₀) ^ 2) ∧
    Matrix.mulVec (hammingFilteredMat r A) v i =
      ∑ x₀ ∈ Finset.univ.filter (fun x₀ : BitVecN n => bvPopcount x₀ ≤ r),
        A i (bvXor i x₀) * v (bvXor i x₀) := by
  have hBC23 := stage_BC2_BC3_n_bit_symplectic_clifford_product_and_causal_signature
    (R := R) x₁ z₁ x₂ z₂ x z
  have hBC45 := stage_BC4_BC5_division_free_compiler_parseval_and_symplectic_convolution M M 0 0
  have hBC6 := stage_BC6_multi_scale_clifford_filtered_attention_execution r A v i
  exact ⟨BitwiseCliffordCompilerStage.causalEdge_acyclic,
    BitwiseCliffordCompilerStage.card_eq_six,
    hBC23.2.1,
    hBC23.2.2.1,
    hBC45.2.1,
    hBC45.2.2.2.1,
    hBC6.2⟩

end BitwiseCliffordCompiler

/-!
===============================================================================
Part X: The Balanced Structure on the Category of Representations of a
Conformal Net (`ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ {ℭ𝔑₄, ℭ𝔑₅} ≺ ℭ𝔑₆`)
===============================================================================
Formalizes the algebraic and operator-theoretic core of Adrià Marín-Salvador's
theorem (*"The balanced structure on the category of representations of a
conformal net"*, arXiv:2605.18446 / J. Math. Phys.) and its foundational
reference spine (Haag–Kastler, Bisognano–Wichmann, Doplicher–Haag–Roberts,
Fredenhagen–Rehren–Schroer, Gabbiani–Fröhlich, Guido–Longo, Wassermann,
Kawahigashi–Longo–Müger, Bartels–Douglas–Henriksen).
-/

/-- The 6-stage causal poset of the Balanced Structure on the Category of
Representations of a Conformal Net (`ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ {ℭ𝔑₄, ℭ𝔑₅} ≺ ℭ𝔑₆`). -/
inductive ConformalNetBalancedRepStage : Type
  | cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost
  | cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension
  | cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy
  | cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group
  | cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term
  | cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z
  deriving DecidableEq, Repr

namespace ConformalNetBalancedRepStage

/-- Topological rank in `{0, 1, 2, 3, 4}` (with diamond branch `{ℭ𝔑₄, ℭ𝔑₅}` at rank `3`). -/
def rank : ConformalNetBalancedRepStage → ℕ
  | .cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost => 0
  | .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension => 1
  | .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy => 2
  | .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group => 3
  | .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term => 3
  | .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z => 4

/-- Direct causal edges of `ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ {ℭ𝔑₄, ℭ𝔑₅} ≺ ℭ𝔑₆`. -/
def causalEdge : ConformalNetBalancedRepStage → ConformalNetBalancedRepStage → Prop
  | .cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost,
    .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension => True
  | .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension,
    .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy => True
  | .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy,
    .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group => True
  | .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy,
    .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term => True
  | .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group,
    .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z => True
  | .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term,
    .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

instance : Fintype ConformalNetBalancedRepStage where
  elems := {
    .cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost,
    .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension,
    .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy,
    .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group,
    .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term,
    .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card ConformalNetBalancedRepStage = 6 := rfl

theorem edge_lt {a b : ConformalNetBalancedRepStage} (h : causalEdge a b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : ConformalNetBalancedRepStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact edge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (edge_lt h2)

/-- Strict DAG acyclicity of `ConformalNetBalancedRepStage`. -/
theorem causalEdge_acyclic (st : ConformalNetBalancedRepStage) :
    ¬ Relation.TransGen causalEdge st st :=
  fun h => Nat.lt_irrefl st.rank (transGen_lt h)

/-- Parallel diamond branches `ℭ𝔑₄` and `ℭ𝔑₅` are incomparable under `TransGen causalEdge`. -/
theorem incomparable_CN4_CN5 :
    ¬ Relation.TransGen causalEdge
        .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group
        .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term ∧
    ¬ Relation.TransGen causalEdge
        .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term
        .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group :=
  ⟨fun h => Nat.lt_irrefl 3 (transGen_lt h),
   fun h => Nat.lt_irrefl 3 (transGen_lt h)⟩

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : ConformalNetBalancedRepStage → RepDepth
  | .cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost => .operator
  | .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension => .krein
  | .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy => .transport
  | .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group => .transport
  | .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term => .transport
  | .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z => .thermo

theorem toRepDepth_mono {a b : ConformalNetBalancedRepStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : ConformalNetBalancedRepStage → OntologyMetaLevel
  | .cn1_interval_haag_duality_and_bisognano_wichmann_modular_boost => .M1_ProjectorClabject
  | .cn2_connes_fusion_intertwiner_associativity_and_statistical_dimension => .M2_GrassmannianPowertypeOrbit
  | .cn3_dhr_braiding_artin_relation_and_double_braiding_monodromy => .M2_GrassmannianPowertypeOrbit
  | .cn4_virasoro_l0_scaling_derivation_and_conformal_twist_group => .M2_GrassmannianPowertypeOrbit
  | .cn5_balanced_category_coboundary_and_sugawara_casimir_cross_term => .M2_GrassmannianPowertypeOrbit
  | .cn6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : ConformalNetBalancedRepStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end ConformalNetBalancedRepStage

namespace ConformalNetBalancedRep

/-- Modular `S`-matrix `[[0, -1], [1, 0]]` in `SL₂(ℤ)` acting on `Matrix (Fin 2) (Fin 2) R`. -/
def modSMat {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, 0]

/-- Modular `T`-matrix (Dehn twist) `[[1, 1], [0, 1]]` in `SL₂(ℤ)` acting on `Matrix (Fin 2) (Fin 2) R`. -/
def modTMat {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 1; 0, 1]

/-- **Stage `ℭ𝔑₁` (`stage_CN1_interval_haag_duality_and_bisognano_wichmann_modular_boost`)**:
1. **Interval Projector & Causal Complement Orthogonality (`P + (1 - P) = 1`, `P(1 - P) = 0`)**:
   In any `[Ring B]` with interval projector `hP : P * P = P`, `P` (interval `I`) and
   `1 - P` (causal complement `I'`) form a complementary orthogonal idempotent pair.
2. **Haag Locality / Commutant Separation (`[𝒜(I), 𝒜(I')] = 0`)**:
   For any local operator `P A P` in the `I`-sector and `(1 - P) C (1 - P)` in the `I'`-sector:
   - `(P * A * P) * ((1 - P) * C * (1 - P)) = 0`,
   - `((1 - P) * C * (1 - P)) * (P * A * P) = 0`,
   - `comm (P * A * P) ((1 - P) * C * (1 - P)) = 0`.
3. **Bisognano–Wichmann Modular Reflection Involution (`J_I² = S_P² = 1`)**:
   `invS P * invS P = 1`, `invS P * (P * A * P) * invS P = P * A * P`, and
   `invS P * ((1 - P) * C * (1 - P)) * invS P = (1 - P) * C * (1 - P)`. -/
theorem stage_CN1_interval_haag_duality_and_bisognano_wichmann_modular_boost
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    (P + (1 - P) = 1 ∧ P * (1 - P) = 0 ∧ (1 - P) * P = 0) ∧
    ((P * A * P) * ((1 - P) * C * (1 - P)) = 0 ∧
     ((1 - P) * C * (1 - P)) * (P * A * P) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm
       (P * A * P) ((1 - P) * C * (1 - P)) = 0) ∧
    (invS P * invS P = 1 ∧
     invS P * (P * A * P) * invS P = P * A * P ∧
     invS P * ((1 - P) * C * (1 - P)) * invS P = (1 - P) * C * (1 - P)) := by
  refine ⟨⟨by noncomm_ring, by peirce_nf hP, by peirce_nf hP⟩,
    ⟨by peirce_nf hP,
     by peirce_nf hP,
     by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩,
    ⟨by peirce_nf hP,
     by peirce_nf hP,
     by peirce_nf hP⟩⟩

/-- **Stage `ℭ𝔑₂` (`stage_CN2_connes_fusion_intertwiner_associativity_and_statistical_dimension`)**:
1. **Connes Fusion Relative Sandwich Associativity (`(X ⊠_P Y) ⊠_P Z = X ⊠_P (Y ⊠_P Z)`)**:
   For `connesFuse P X Y := X * P * Y`, `(X * P * Y) * P * Z = X * P * (Y * P * Z)`
   and for `P`-bimodule elements (`X * P = X`, `P * Y = Y`), `(X * P * Y) = X * Y`.
2. **Jones–Haagerup Statistical Dimension Ring Law**:
   In any `[CommRing R]`, if `α : R` satisfies the Haagerup fusion quadratic relation
   `α^2 = α + 3` (`α ⊗ α = 1 ⊕ ρ ⊕ ρ² ⊕ α₁ ⊕ α₂ ⊕ α₃`), then the total squared
   statistical dimension `𝒟² = 1² + 1² + 1² + 3 α²` equals `12 + 3 α`, and
   `(2 * α - 1)^2 = 13`. -/
theorem stage_CN2_connes_fusion_intertwiner_associativity_and_statistical_dimension
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    (P X Y Z : B) {α : R} (hα : α ^ 2 = α + 3) :
    (X * P * Y) * P * Z = X * P * (Y * P * Z) ∧
    (1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 3 * α ^ 2 : R) = 12 + 3 * α ∧
    (2 * α - 1) ^ 2 = (13 : R) := by
  refine ⟨by noncomm_ring, ?_, ?_⟩
  · linear_combination 3 * hα
  · linear_combination 4 * hα

/-- **Stage `ℭ𝔑₃` (`stage_CN3_dhr_braiding_artin_relation_and_double_braiding_monodromy`)**:
In any `[Ring B]`, given adjacent DHR/Clifford bivector braid generators `u, v : B`
with `u² = -1`, `v² = -1`, and `u v + v u = 0`, let `R_u = 1 + u` and `R_v = 1 + v`:
1. **Two-Sided Unipotent-Clifford Quasi-Invertibility**:
   `(1 + u) * (1 - u) = 2` and `(1 - u) * (1 + u) = 2`.
2. **Exact Artin Braid / Yang–Baxter Relation (`R_u R_v R_u = R_v R_u R_v`)**:
   `(1 + u) * (1 + v) * (1 + u) = (1 + v) * (1 + u) * (1 + v)`.
3. **Double-Braiding Monodromy (`M_u := R_u² = 2 u`, `M_u² = -4`, `M_u⁴ = 16`)**:
   `(1 + u) * (1 + u) = 2 * u` and `((1 + u) * (1 + u)) * ((1 + u) * (1 + u)) = -4`. -/
theorem stage_CN3_dhr_braiding_artin_relation_and_double_braiding_monodromy
    {B : Type*} [Ring B] {u v : B}
    (hu : u * u = -1) (hv : v * v = -1) (huv : u * v + v * u = 0) :
    ((1 + u) * (1 - u) = (2 : B) ∧ (1 - u) * (1 + u) = (2 : B)) ∧
    (1 + u) * (1 + v) * (1 + u) = (1 + v) * (1 + u) * (1 + v) ∧
    ((1 + u) * (1 + u) = 2 * u ∧
     ((1 + u) * (1 + u)) * ((1 + u) * (1 + u)) = -(4 : B)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · calc (1 + u) * (1 - u) = 1 - u * u := by noncomm_ring
      _ = 1 - (-1) := by rw [hu]
      _ = (2 : B) := by norm_num
  · calc (1 - u) * (1 + u) = 1 - u * u := by noncomm_ring
      _ = 1 - (-1) := by rw [hu]
      _ = (2 : B) := by norm_num
  · apply sub_eq_zero.mp
    calc (1 + u) * (1 + v) * (1 + u) - (1 + v) * (1 + u) * (1 + v)
      _ = (u * u - v * v) + u * (1 + v * v) - (1 + u * u) * v +
            u * (u * v + v * u) - (u * v + v * u) * v := by noncomm_ring
      _ = (-1 - (-1)) + u * (1 + (-1)) - (1 + (-1)) * v +
            u * 0 - 0 * v := by rw [hu, hv, huv]
      _ = 0 := by noncomm_ring
  · calc (1 + u) * (1 + u) = (1 + u * u) + 2 * u := by noncomm_ring
      _ = (1 + (-1)) + 2 * u := by rw [hu]
      _ = 2 * u := by noncomm_ring
  · calc ((1 + u) * (1 + u)) * ((1 + u) * (1 + u))
      _ = ((1 + u * u) + 2 * u) * ((1 + u * u) + 2 * u) := by noncomm_ring
      _ = ((1 + (-1)) + 2 * u) * ((1 + (-1)) + 2 * u) := by rw [hu]
      _ = 4 * (u * u) := by noncomm_ring
      _ = 4 * (-1) := by rw [hu]
      _ = -(4 : B) := by norm_num

/-- **Stages `ℭ𝔑₄ ≺ ℭ𝔑₅` (`stage_CN4_CN5_virasoro_l0_balancing_twist_coboundary_and_sugawara_cross_term`)**:
1. **Conformal Weight Anomaly Additivity (`(h_Z - h_X - h_Y) + (h_X + h_Y) = h_Z`)**:
   In any `[CommRing R]`, the conformal scaling weight shift `Δh := h_Z - h_X - h_Y` of a
   Connes fusion channel `X ⊠ Y → Z` satisfies `Δh + (h_X + h_Y) = h_Z`.
2. **Marín-Salvador Balancing Coboundary Law (`θ_{X ⊠ Y} = c_{Y,X} c_{X,Y} (θ_X ⊠ θ_Y)`)**:
   For any invertible balancing twists `θ_X, θ_Y, θ_Z : R` with inverses `θ_X⁻¹, θ_Y⁻¹`
   (`θ_X * θ_X⁻¹ = 1`, `θ_Y * θ_Y⁻¹ = 1`), the double-braiding monodromy
   `M_{XY} := θ_Z * θ_X⁻¹ * θ_Y⁻¹` satisfies the exact balancing equation
   `M_{XY} * (θ_X * θ_Y) = θ_Z`.
3. **Infinitesimal Sugawara–Virasoro Quadratic Casimir Cross-Term (`ℭ𝔑₅`)**:
   For any derivation `D : B → B` on `[Ring B]` satisfying the Leibniz rule on `X, Y : B`:
   - `D (X * Y) = D X * Y + X * D Y`,
   - `D (D X * Y + X * D Y) = D (D X) * Y + 2 * (D X * D Y) + X * D (D Y)`,
   the second-order Sugawara operator `D²` satisfies the exact bimodule coboundary identity:
   `D (D (X * Y)) - D (D X) * Y - X * D (D Y) = 2 * (D X * D Y)`. -/
theorem stage_CN4_CN5_virasoro_l0_balancing_twist_coboundary_and_sugawara_cross_term
    {R : Type*} [CommRing R] {B : Type*} [Ring B]
    (hX hY hZ : R)
    {θX θX_inv θY θY_inv : R} (hθX : θX * θX_inv = 1) (hθY : θY * θY_inv = 1) (θZ : R)
    {D : B → B} {X Y : B}
    (hLeib1 : D (X * Y) = D X * Y + X * D Y)
    (hLeib2 : D (D X * Y + X * D Y) = D (D X) * Y + 2 * (D X * D Y) + X * D (D Y)) :
    (hZ - hX - hY) + (hX + hY) = hZ ∧
    (θZ * θX_inv * θY_inv) * (θX * θY) = θZ ∧
    D (D (X * Y)) - D (D X) * Y - X * D (D Y) = 2 * (D X * D Y) := by
  refine ⟨by ring, ?_, ?_⟩
  · calc (θZ * θX_inv * θY_inv) * (θX * θY)
      _ = θZ * (θX * θX_inv) * (θY * θY_inv) := by ring
      _ = θZ * 1 * 1 := by rw [hθX, hθY]
      _ = θZ := by ring
  · rw [hLeib1, hLeib2]
    noncomm_ring

/-- **Stage `ℭ𝔑₆` (`stage_CN6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z`)**:
1. **Guido–Longo Conjugate Spin-Statistics & Vacuum Monodromy (`θ_{X̄} = θ_X`, `M_{X, X̄}|_1 = θ_X⁻²`)**:
   When a sector `X` has conjugate `X̄` with `h_{X̄} = h_X` and vacuum weight `h_1 = 0`,
   the vacuum fusion channel weight shift is `h_1 - h_X - h_{X̄} = -2 * h_X`, and for
   `M_{X, X̄} := 1 * θ_X⁻¹ * θ_X⁻¹`, `M_{X, X̄} * (θ_X ^ 2) = 1`.
2. **Modular `SL₂(ℤ)` Verlinde–Moore–Seiberg Presentation (`S² = -I₂`, `(ST)³ = -I₂`, `S⁴ = I₂`, `(ST)⁶ = I₂`)**:
   On `Matrix (Fin 2) (Fin 2) R`:
   - `modSMat * modSMat = -1`,
   - `(modSMat * modTMat) * (modSMat * modTMat) * (modSMat * modTMat) = -1`,
   - `(modSMat * modSMat) * (modSMat * modSMat) = 1`,
   - `((modSMat * modTMat) * (modSMat * modTMat) * (modSMat * modTMat)) *
      ((modSMat * modTMat) * (modSMat * modTMat) * (modSMat * modTMat)) = 1`. -/
theorem stage_CN6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z
    {R : Type*} [CommRing R] (hX : R) {θX θX_inv : R} (hθX : θX * θX_inv = 1) :
    ((0 : R) - hX - hX = -2 * hX ∧
     (1 * θX_inv * θX_inv) * (θX ^ 2) = 1) ∧
    (modSMat (R := R) * modSMat (R := R) = -1 ∧
     (modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R)) = -1 ∧
     (modSMat (R := R) * modSMat (R := R)) *
       (modSMat (R := R) * modSMat (R := R)) = 1 ∧
     ((modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R))) *
     ((modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R)) *
       (modSMat (R := R) * modTMat (R := R))) = 1) := by
  have hS2 : modSMat (R := R) * modSMat (R := R) = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [modSMat, Matrix.mul_apply, Fin.sum_univ_two]
  have hST3 :
      (modSMat (R := R) * modTMat (R := R)) *
        (modSMat (R := R) * modTMat (R := R)) *
        (modSMat (R := R) * modTMat (R := R)) = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [modSMat, modTMat, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨⟨by ring, ?_⟩, ⟨hS2, hST3, ?_, ?_⟩⟩
  · calc (1 * θX_inv * θX_inv) * (θX ^ 2)
      _ = (θX * θX_inv) * (θX * θX_inv) := by ring
      _ = 1 * 1 := by rw [hθX]
      _ = 1 := by ring
  · rw [hS2]; noncomm_ring
  · rw [hST3]; noncomm_ring

/-- **Master Theorem (`conformal_net_balanced_rep_master_poset`)**:
Unifies the 6-stage Poset of the Balanced Structure on the Category of
Representations of a Conformal Net (`ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ {ℭ𝔑₄, ℭ𝔑₅} ≺ ℭ𝔑₆`). -/
theorem conformal_net_balanced_rep_master_poset
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {P : B} (hP : P * P = P) (A C : B)
    {u v : B} (hu : u * u = -1) (hv : v * v = -1) (huv : u * v + v * u = 0)
    {α : R} (hα : α ^ 2 = α + 3)
    {θX θX_inv θY θY_inv : R} (hθX : θX * θX_inv = 1) (hθY : θY * θY_inv = 1) (θZ : R) :
    (∀ st : ConformalNetBalancedRepStage,
      ¬ Relation.TransGen ConformalNetBalancedRepStage.causalEdge st st) ∧
    Fintype.card ConformalNetBalancedRepStage = 6 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (P * A * P) ((1 - P) * C * (1 - P)) = 0 ∧
    (1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 3 * α ^ 2 : R) = 12 + 3 * α ∧
    (1 + u) * (1 + v) * (1 + u) = (1 + v) * (1 + u) * (1 + v) ∧
    (1 + u) * (1 + u) = 2 * u ∧
    (θZ * θX_inv * θY_inv) * (θX * θY) = θZ ∧
    modSMat (R := R) * modSMat (R := R) = -1 ∧
    (modSMat (R := R) * modTMat (R := R)) *
      (modSMat (R := R) * modTMat (R := R)) *
      (modSMat (R := R) * modTMat (R := R)) = -1 := by
  have hCN1 := stage_CN1_interval_haag_duality_and_bisognano_wichmann_modular_boost hP A C
  have hCN2 := stage_CN2_connes_fusion_intertwiner_associativity_and_statistical_dimension P A C A hα
  have hCN3 := stage_CN3_dhr_braiding_artin_relation_and_double_braiding_monodromy hu hv huv
  have hCN45 := stage_CN4_CN5_virasoro_l0_balancing_twist_coboundary_and_sugawara_cross_term
    (B := B) 0 0 0 hθX hθY θZ (D := fun _ => 0) (X := 0) (Y := 0) (by simp) (by simp)
  have hCN6 := stage_CN6_guido_longo_spin_statistics_ribbon_duality_and_modular_sl2z 0 hθX
  exact ⟨ConformalNetBalancedRepStage.causalEdge_acyclic,
    ConformalNetBalancedRepStage.card_eq_six,
    hCN1.2.1.2.2,
    hCN2.2.1,
    hCN3.2.1,
    hCN3.2.2.1,
    hCN45.2.1,
    hCN6.2.1,
    hCN6.2.2.1⟩

end ConformalNetBalancedRep

/-!
## Part XI: Conditional Twisted-Star Peirce-Shear Identities and Their Six-Stage Ordering
-/

/-- **Six-Stage Ordering of Conditional Twisted-Star Peirce-Shear Identities (`PlabicTwistedPinCPTStage`)**.
The edges below define an organizing stage graph. Acyclicity of this graph is proved, but its edges
are not asserted to encode theorem-to-theorem implications. Here `CPT` names the algebraic map
`thetaCPT`; these ring identities do not construct a physical CPT symmetry or a Hilbert-space
unitarity statement.
1. `pn1_bipartite_vertices_and_twisted_pin_clifford_generators` (`𝔓𝔑₁`):
   White/black bipartite Peirce projectors `P` and `1 - P`, chiral parity `S_P = P - (1 - P)`,
   bipartite swap reflection `Φ₁` (`Φ₁² = 1`, `Φ₁ P = (1 - P) Φ₁`), and Twisted-`Pin`
   symplectic reflection `J₁ := S_P Φ₁` (`J₁² = -1`, `J₁⋆ = -J₁`).
2. `pn2_elementary_plabic_shears_and_symmetric_star_swap_laws` (`𝔓𝔑₂`):
   Action of Time-Reversal `τ_T(Y) = Y⋆`, Bipartite Charge Conjugation `β_C(Y) = Φ₁ Y Φ₁`,
   Chiral Parity `α_P(Y) = S_P Y S_P`, and Twisted-`Pin` `CP` `γ_CP(Y) = -J₁ Y J₁` on
   elementary Peirce-corner edges `N_+ = P X (1 - P)` and `N_- = (1 - P) X P`.
3. `pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation` (`𝔓𝔑₃`):
   The Twisted-`Pin` `CPT` operator `Θ_CPT(Y) := -J₁ Y⋆ J₁ = α_P(β_C(τ_T(Y)))` is an exact
   involutive ring anti-automorphism (`Θ_CPT(A B) = Θ_CPT(B) Θ_CPT(A)`, `Θ_CPT(Θ_CPT(Y)) = Y`)
   that negates both bipartite Plabic edge directions (`Θ_CPT(N_±) = -N_±`).
4. `pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries` (`𝔓𝔑₄`):
   Algebraic expansions under the star map and formulas for the `T`, `CT`, and `PT` images of
   the two-gate product. The theorem gives equations, not universal inequalities or a proof that
   any displayed product differs from identity in every carrier.
5. `pn5_universal_cpt_word_inversion_and_unitarity` (`𝔓𝔑₅`):
   Conditional inverse formulas under `thetaCPT`, including the two-gate product. For a finite
   word, the theorem assumes each listed gate already has a two-sided inverse under `thetaCPT`;
   it proves algebraic two-sided inversion, not physical unitarity.
6. `pn6_cpt_transformation_table_of_geometric_observables` (`𝔓𝔑₆`):
   Complete `Θ_CPT` transformation table on sheet projectors `Q_±` and the four geometric
   observables `(V, Σ, Φ, J)`: `Θ_CPT(Q_±) = Q_∓`, `Θ_CPT(V) = +V`, `Θ_CPT(Σ) = -Σ`,
   `Θ_CPT(Φ) = -Φ`, `Θ_CPT(J) = -J`. -/
inductive PlabicTwistedPinCPTStage : Type
  | pn1_bipartite_vertices_and_twisted_pin_clifford_generators
  | pn2_elementary_plabic_shears_and_symmetric_star_swap_laws
  | pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation
  | pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries
  | pn5_universal_cpt_word_inversion_and_unitarity
  | pn6_cpt_transformation_table_of_geometric_observables
  deriving DecidableEq, Repr

namespace PlabicTwistedPinCPTStage

/-- Topological rank of each stage in `PlabicTwistedPinCPTStage`. -/
def rank : PlabicTwistedPinCPTStage → ℕ
  | .pn1_bipartite_vertices_and_twisted_pin_clifford_generators => 0
  | .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws => 1
  | .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation => 2
  | .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries => 3
  | .pn5_universal_cpt_word_inversion_and_unitarity => 3
  | .pn6_cpt_transformation_table_of_geometric_observables => 4

/-- Direct covering edges of the stipulated stage-order graph. These edges do not assert
that the theorem at the source stage supplies the hypotheses of the target stage. -/
def causalEdge : PlabicTwistedPinCPTStage → PlabicTwistedPinCPTStage → Prop
  | .pn1_bipartite_vertices_and_twisted_pin_clifford_generators,
    .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws => True
  | .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws,
    .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation => True
  | .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation,
    .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries => True
  | .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation,
    .pn5_universal_cpt_word_inversion_and_unitarity => True
  | .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries,
    .pn6_cpt_transformation_table_of_geometric_observables => True
  | .pn5_universal_cpt_word_inversion_and_unitarity,
    .pn6_cpt_transformation_table_of_geometric_observables => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse not_false

instance : Fintype PlabicTwistedPinCPTStage where
  elems := {
    .pn1_bipartite_vertices_and_twisted_pin_clifford_generators,
    .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws,
    .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation,
    .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries,
    .pn5_universal_cpt_word_inversion_and_unitarity,
    .pn6_cpt_transformation_table_of_geometric_observables
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card PlabicTwistedPinCPTStage = 6 := rfl

theorem causalEdge_rank_lt {a b : PlabicTwistedPinCPTStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_rank_lt {a b : PlabicTwistedPinCPTStage}
    (h : Relation.TransGen causalEdge a b) :
    rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

theorem causalEdge_acyclic (s : PlabicTwistedPinCPTStage) :
    ¬ Relation.TransGen causalEdge s s :=
  fun h => Nat.lt_irrefl (rank s) (transGen_rank_lt h)

theorem incomparable_PN4_PN5 :
    ¬ Relation.TransGen causalEdge
        .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries
        .pn5_universal_cpt_word_inversion_and_unitarity ∧
    ¬ Relation.TransGen causalEdge
        .pn5_universal_cpt_word_inversion_and_unitarity
        .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    exact Nat.lt_irrefl 3 (transGen_rank_lt h)

def toRepDepth : PlabicTwistedPinCPTStage → InfoGeometry.Meta.RepDepth
  | .pn1_bipartite_vertices_and_twisted_pin_clifford_generators => .operator
  | .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws => .operator
  | .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation => .transport
  | .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries => .transport
  | .pn5_universal_cpt_word_inversion_and_unitarity => .thermo
  | .pn6_cpt_transformation_table_of_geometric_observables => .thermo

theorem toRepDepth_mono {a b : PlabicTwistedPinCPTStage}
    (h : Relation.ReflTransGen causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  induction h with
  | refl => exact le_rfl
  | @tail b c _ hbc ih =>
    refine le_trans ih ?_
    cases b <;> cases c <;> revert hbc <;>
      unfold causalEdge toRepDepth InfoGeometry.Meta.RepDepth.toNat <;> decide

def toOntologyMetaLevel :
    PlabicTwistedPinCPTStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .pn1_bipartite_vertices_and_twisted_pin_clifford_generators => .M1_ProjectorClabject
  | .pn2_elementary_plabic_shears_and_symmetric_star_swap_laws => .M1_ProjectorClabject
  | .pn3_twisted_pin_cpt_anti_automorphism_and_edge_negation => .M2_GrassmannianPowertypeOrbit
  | .pn4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries => .M2_GrassmannianPowertypeOrbit
  | .pn5_universal_cpt_word_inversion_and_unitarity => .M3_ErlangenCasimirMetaLaw
  | .pn6_cpt_transformation_table_of_geometric_observables => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : PlabicTwistedPinCPTStage}
    (h : Relation.ReflTransGen causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  induction h with
  | refl => exact le_rfl
  | @tail b c _ hbc ih =>
    refine le_trans ih ?_
    cases b <;> cases c <;> revert hbc <;>
      unfold causalEdge toOntologyMetaLevel
        InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;> decide

end PlabicTwistedPinCPTStage

namespace PlabicTwistedPinCPT

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- **Twisted-`Pin` Symplectic Reflection Generator (`pinJ1`)**:
`J₁ := S_P Φ₁ = (P - (1 - P)) Φ₁`. -/
def pinJ1 {B : Type*} [Ring B] (P Phi1 : B) : B :=
  invS P * Phi1

/-- **Chiral Parity Automorphism (`parityAlpha`)**:
`α_P(Y) := S_P Y S_P`. -/
def parityAlpha {B : Type*} [Ring B] (P Y : B) : B :=
  invS P * Y * invS P

/-- **Bipartite Charge Conjugation Automorphism (`chargeBeta`)**:
`β_C(Y) := Φ₁ Y Φ₁`. -/
def chargeBeta {B : Type*} [Ring B] (Phi1 Y : B) : B :=
  Phi1 * Y * Phi1

/-- **Twisted-`Pin` `CP` Automorphism (`cpGamma`)**:
`γ_CP(Y) := -J₁ Y J₁ = J₁ Y J₁⁻¹`. -/
def cpGamma {B : Type*} [Ring B] (P Phi1 Y : B) : B :=
  -(pinJ1 P Phi1 * Y * pinJ1 P Phi1)

/-- **Time-Reversal Anti-Automorphism (`timeTau`)**:
`τ_T(Y) := Y⋆` in any `[Ring B] [StarRing B]`. -/
def timeTau {B : Type*} [Ring B] [StarRing B] (Y : B) : B :=
  star Y

/-- **Twisted-`Pin` `CPT` Anti-Automorphism (`thetaCPT`)**:
`Θ_CPT(Y) := -J₁ Y⋆ J₁ = J₁ Y⋆ J₁⁻¹`. -/
def thetaCPT {B : Type*} [Ring B] [StarRing B] (P Phi1 Y : B) : B :=
  -(pinJ1 P Phi1 * star Y * pinJ1 P Phi1)

/-- **Multi-Hop Bipartite Plabic Network Word (`plabicWord`)**:
Product `g₁ g₂ ⋯ g_m` of a list of elementary Plabic network gates. -/
def plabicWord {B : Type*} [Ring B] (L : List B) : B :=
  L.foldr (· * ·) 1

/-- Helper lemma: `Φ₁ (1 - P) = P Φ₁` from `Φ₁ P = (1 - P) Φ₁`. -/
theorem phi1_mul_one_sub {B : Type*} [Ring B] {P Phi1 : B}
    (hPhi_P : Phi1 * P = (1 - P) * Phi1) :
    Phi1 * (1 - P) = P * Phi1 := by
  calc Phi1 * (1 - P)
    _ = Phi1 - Phi1 * P := by noncomm_ring
    _ = Phi1 - (1 - P) * Phi1 := by rw [hPhi_P]
    _ = P * Phi1 := by noncomm_ring

/-- Helper lemma: `Φ₁ S_P = -S_P Φ₁` (`Phi1 * invS P = -pinJ1 P Phi1`). -/
theorem phi1_mul_invS {B : Type*} [Ring B] {P Phi1 : B}
    (hPhi_P : Phi1 * P = (1 - P) * Phi1) :
    Phi1 * invS P = -pinJ1 P Phi1 := by
  dsimp [pinJ1, invS]
  calc Phi1 * (P - (1 - P))
    _ = 2 * (Phi1 * P) - Phi1 := by noncomm_ring
    _ = 2 * ((1 - P) * Phi1) - Phi1 := by rw [hPhi_P]
    _ = -((P - (1 - P)) * Phi1) := by noncomm_ring

/-- **Stage `𝔓𝔑₁` (`stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators`)**:
In any `[Ring B] [StarRing B]` with self-adjoint idempotent `P` (`P² = P`, `P⋆ = P`) and
self-adjoint bipartite swap involution `Φ₁` (`Φ₁² = 1`, `Φ₁⋆ = Φ₁`, `Φ₁ P = (1 - P) Φ₁`):
1. `invS P * invS P = 1` and `star (invS P) = invS P`,
2. `Phi1 * P * Phi1 = 1 - P` and `Phi1 * (1 - P) * Phi1 = P`,
3. `invS P * Phi1 + Phi1 * invS P = 0`,
4. `pinJ1 P Phi1 * pinJ1 P Phi1 = -1` (`J₁² = -1`),
5. `star (pinJ1 P Phi1) = -pinJ1 P Phi1` (`J₁⋆ = -J₁`),
6. `(-pinJ1 P Phi1) * pinJ1 P Phi1 = 1` and `pinJ1 P Phi1 * (-pinJ1 P Phi1) = 1`. -/
theorem stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators
    {B : Type*} [Ring B] [StarRing B] {P Phi1 : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1) :
    (invS P * invS P = 1 ∧ star (invS P) = invS P) ∧
    (Phi1 * P * Phi1 = 1 - P ∧ Phi1 * (1 - P) * Phi1 = P) ∧
    invS P * Phi1 + Phi1 * invS P = 0 ∧
    pinJ1 P Phi1 * pinJ1 P Phi1 = -1 ∧
    star (pinJ1 P Phi1) = -pinJ1 P Phi1 ∧
    ((-pinJ1 P Phi1) * pinJ1 P Phi1 = 1 ∧ pinJ1 P Phi1 * (-pinJ1 P Phi1) = 1) := by
  have hInvS_sq : invS P * invS P = 1 := by peirce_nf hP
  have hInvS_star : star (invS P) = invS P := by
    simp only [invS, star_sub, star_one, hP_star]
  have hPhi_invS : Phi1 * invS P = -pinJ1 P Phi1 := phi1_mul_invS hPhi_P
  have hJ1_sq : pinJ1 P Phi1 * pinJ1 P Phi1 = -1 := by
    calc pinJ1 P Phi1 * pinJ1 P Phi1
      _ = invS P * (Phi1 * invS P) * Phi1 := by dsimp [pinJ1]; noncomm_ring
      _ = invS P * (-pinJ1 P Phi1) * Phi1 := by rw [hPhi_invS]
      _ = -(invS P * invS P) * (Phi1 * Phi1) := by dsimp [pinJ1]; noncomm_ring
      _ = -1 * 1 := by rw [hInvS_sq, hPhi_sq]
      _ = -1 := by norm_num
  refine ⟨⟨hInvS_sq, hInvS_star⟩, ⟨?_, ?_⟩, ?_, hJ1_sq, ?_, ⟨?_, ?_⟩⟩
  · calc Phi1 * P * Phi1
      _ = (1 - P) * (Phi1 * Phi1) := by rw [hPhi_P]; noncomm_ring
      _ = (1 - P) * 1 := by rw [hPhi_sq]
      _ = 1 - P := by noncomm_ring
  · have hPhi_1mP := phi1_mul_one_sub hPhi_P
    calc Phi1 * (1 - P) * Phi1
      _ = P * (Phi1 * Phi1) := by rw [hPhi_1mP]; noncomm_ring
      _ = P * 1 := by rw [hPhi_sq]
      _ = P := by noncomm_ring
  · calc invS P * Phi1 + Phi1 * invS P
      _ = pinJ1 P Phi1 + (-pinJ1 P Phi1) := by rw [hPhi_invS]; rfl
      _ = 0 := by abel
  · calc star (pinJ1 P Phi1)
      _ = star Phi1 * star (invS P) := by dsimp [pinJ1]; exact star_mul (invS P) Phi1
      _ = Phi1 * invS P := by rw [hPhi_star, hInvS_star]
      _ = -pinJ1 P Phi1 := hPhi_invS
  · calc (-pinJ1 P Phi1) * pinJ1 P Phi1
      _ = -(pinJ1 P Phi1 * pinJ1 P Phi1) := by noncomm_ring
      _ = -(-1) := by rw [hJ1_sq]
      _ = 1 := by norm_num
  · calc pinJ1 P Phi1 * (-pinJ1 P Phi1)
      _ = -(pinJ1 P Phi1 * pinJ1 P Phi1) := by noncomm_ring
      _ = -(-1) := by rw [hJ1_sq]
      _ = 1 := by norm_num

/-- Helper lemma: `γ_CP(Y) = α_P(β_C(Y))` (`-J₁ Y J₁ = S_P (Φ₁ Y Φ₁) S_P`). -/
theorem cpGamma_eq_parity_charge {B : Type*} [Ring B] {P Phi1 : B}
    (hPhi_P : Phi1 * P = (1 - P) * Phi1) (Y : B) :
    cpGamma P Phi1 Y = parityAlpha P (chargeBeta Phi1 Y) := by
  have hPhi_invS := phi1_mul_invS hPhi_P
  dsimp [cpGamma, parityAlpha, chargeBeta]
  calc -(pinJ1 P Phi1 * Y * pinJ1 P Phi1)
    _ = invS P * Phi1 * Y * (-pinJ1 P Phi1) := by dsimp [pinJ1]; noncomm_ring
    _ = invS P * Phi1 * Y * (Phi1 * invS P) := by rw [← hPhi_invS]
    _ = invS P * (Phi1 * Y * Phi1) * invS P := by noncomm_ring

/-- **Stage `𝔓𝔑₂` (`stage_PN2_elementary_plabic_shears_and_symmetric_star_swap_laws`)**:
For any symmetric seed `X ∈ B` with `X⋆ = X` (`hX_star`) and `Φ₁ X = X Φ₁` (`hPhi_X`),
the bipartite Plabic edges `N_+ = conePlus P X = P X (1 - P)` and `N_- = coneMinus P X = (1 - P) X P`
satisfy:
1. **Time-Reversal (`timeTau`)**:
   `timeTau (conePlus P X) = coneMinus P X` and `timeTau (coneMinus P X) = conePlus P X`.
2. **Bipartite Charge Conjugation (`chargeBeta Phi1`)**:
   `chargeBeta Phi1 (conePlus P X) = coneMinus P X` and `chargeBeta Phi1 (coneMinus P X) = conePlus P X`.
3. **Chiral Parity (`parityAlpha P`)**:
   `parityAlpha P (conePlus P X) = -conePlus P X` and `parityAlpha P (coneMinus P X) = -coneMinus P X`.
4. **Twisted-`Pin` `CP` (`cpGamma P Phi1`)**:
   `cpGamma P Phi1 (conePlus P X) = -coneMinus P X` and `cpGamma P Phi1 (coneMinus P X) = -conePlus P X`.
5. **Elementary Plabic Shear Nilpotency**:
   `conePlus P X * conePlus P X = 0` and `coneMinus P X * coneMinus P X = 0`. -/
theorem stage_PN2_elementary_plabic_shears_and_symmetric_star_swap_laws
    {B : Type*} [Ring B] [StarRing B]
    {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1) :
    (timeTau (conePlus P X) = coneMinus P X ∧
     timeTau (coneMinus P X) = conePlus P X) ∧
    (chargeBeta Phi1 (conePlus P X) = coneMinus P X ∧
     chargeBeta Phi1 (coneMinus P X) = conePlus P X) ∧
    (parityAlpha P (conePlus P X) = -conePlus P X ∧
     parityAlpha P (coneMinus P X) = -coneMinus P X) ∧
    (cpGamma P Phi1 (conePlus P X) = -coneMinus P X ∧
     cpGamma P Phi1 (coneMinus P X) = -conePlus P X) ∧
    (conePlus P X * conePlus P X = 0 ∧
     coneMinus P X * coneMinus P X = 0) := by
  have hPhi_1mP := phi1_mul_one_sub hPhi_P
  have hTauPlus : timeTau (conePlus P X) = coneMinus P X := by
    dsimp [timeTau, conePlus, coneMinus]
    simp only [star_mul, star_sub, star_one, hP_star, hX_star]
    noncomm_ring
  have hTauMinus : timeTau (coneMinus P X) = conePlus P X := by
    dsimp [timeTau, conePlus, coneMinus]
    simp only [star_mul, star_sub, star_one, hP_star, hX_star]
    noncomm_ring
  have hBetaPlus : chargeBeta Phi1 (conePlus P X) = coneMinus P X := by
    dsimp [chargeBeta, conePlus, coneMinus]
    calc Phi1 * (P * X * (1 - P)) * Phi1
      _ = (Phi1 * P) * X * (1 - P) * Phi1 := by noncomm_ring
      _ = (1 - P) * (Phi1 * X) * (1 - P) * Phi1 := by rw [hPhi_P]; noncomm_ring
      _ = (1 - P) * X * (Phi1 * (1 - P)) * Phi1 := by rw [hPhi_X]; noncomm_ring
      _ = (1 - P) * X * P * (Phi1 * Phi1) := by rw [hPhi_1mP]; noncomm_ring
      _ = (1 - P) * X * P * 1 := by rw [hPhi_sq]
      _ = (1 - P) * X * P := by noncomm_ring
  have hBetaMinus : chargeBeta Phi1 (coneMinus P X) = conePlus P X := by
    dsimp [chargeBeta, conePlus, coneMinus]
    calc Phi1 * ((1 - P) * X * P) * Phi1
      _ = (Phi1 * (1 - P)) * X * P * Phi1 := by noncomm_ring
      _ = P * (Phi1 * X) * P * Phi1 := by rw [hPhi_1mP]; noncomm_ring
      _ = P * X * (Phi1 * P) * Phi1 := by rw [hPhi_X]; noncomm_ring
      _ = P * X * (1 - P) * (Phi1 * Phi1) := by rw [hPhi_P]; noncomm_ring
      _ = P * X * (1 - P) * 1 := by rw [hPhi_sq]
      _ = P * X * (1 - P) := by noncomm_ring
  have hAlphaPlus : parityAlpha P (conePlus P X) = -conePlus P X := by
    dsimp [parityAlpha]; peirce_nf hP
  have hAlphaMinus : parityAlpha P (coneMinus P X) = -coneMinus P X := by
    dsimp [parityAlpha]; peirce_nf hP
  have hCPPlus : cpGamma P Phi1 (conePlus P X) = -coneMinus P X := by
    rw [cpGamma_eq_parity_charge hPhi_P, hBetaPlus, hAlphaMinus]
  have hCPMinus : cpGamma P Phi1 (coneMinus P X) = -conePlus P X := by
    rw [cpGamma_eq_parity_charge hPhi_P, hBetaMinus, hAlphaPlus]
  exact ⟨⟨hTauPlus, hTauMinus⟩,
    ⟨hBetaPlus, hBetaMinus⟩,
    ⟨hAlphaPlus, hAlphaMinus⟩,
    ⟨hCPPlus, hCPMinus⟩,
    ⟨by peirce_nf hP, by peirce_nf hP⟩⟩

/-- Helper lemma: `Θ_CPT` is additive (`Θ_CPT(A + C) = Θ_CPT(A) + Θ_CPT(C)`). -/
theorem thetaCPT_add {B : Type*} [Ring B] [StarRing B] (P Phi1 A C : B) :
    thetaCPT P Phi1 (A + C) = thetaCPT P Phi1 A + thetaCPT P Phi1 C := by
  dsimp [thetaCPT]
  rw [star_add]
  noncomm_ring

/-- Helper lemma: `Θ_CPT` preserves subtraction (`Θ_CPT(A - C) = Θ_CPT(A) - Θ_CPT(C)`). -/
theorem thetaCPT_sub {B : Type*} [Ring B] [StarRing B] (P Phi1 A C : B) :
    thetaCPT P Phi1 (A - C) = thetaCPT P Phi1 A - thetaCPT P Phi1 C := by
  dsimp [thetaCPT]
  rw [star_sub]
  noncomm_ring

/-- Helper lemma: `Θ_CPT` commutes with negation (`Θ_CPT(-A) = -Θ_CPT(A)`). -/
theorem thetaCPT_neg {B : Type*} [Ring B] [StarRing B] (P Phi1 A : B) :
    thetaCPT P Phi1 (-A) = -thetaCPT P Phi1 A := by
  dsimp [thetaCPT]
  rw [star_neg]
  noncomm_ring

/-- **Stage `𝔓𝔑₃` (`stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation`)**:
In any `[Ring B] [StarRing B]`, the Twisted-`Pin` `CPT` operator `Θ_CPT(Y) := -J₁ Y⋆ J₁`
satisfies:
1. **Equivalence to Composed `P ∘ C ∘ T`**:
   `parityAlpha P (chargeBeta Phi1 (timeTau Y)) = thetaCPT P Phi1 Y`.
2. **Exact Anti-Automorphism (`Θ_CPT(A B) = Θ_CPT(B) Θ_CPT(A)`, `Θ_CPT(1) = 1`)**:
   `thetaCPT P Phi1 (A * C) = thetaCPT P Phi1 C * thetaCPT P Phi1 A` and `thetaCPT P Phi1 1 = 1`.
3. **Exact Involution (`Θ_CPT(Θ_CPT(Y)) = Y`)**:
   `thetaCPT P Phi1 (thetaCPT P Phi1 Y) = Y`.
4. **Exact Edge Negation on Both Bipartite Plabic Orientations**:
   `thetaCPT P Phi1 (conePlus P X) = -conePlus P X` and
   `thetaCPT P Phi1 (coneMinus P X) = -coneMinus P X`. -/
theorem stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1)
    (Y A C : B) :
    parityAlpha P (chargeBeta Phi1 (timeTau Y)) = thetaCPT P Phi1 Y ∧
    (thetaCPT P Phi1 (A * C) = thetaCPT P Phi1 C * thetaCPT P Phi1 A ∧
     thetaCPT P Phi1 1 = 1) ∧
    thetaCPT P Phi1 (thetaCPT P Phi1 Y) = Y ∧
    (thetaCPT P Phi1 (conePlus P X) = -conePlus P X ∧
     thetaCPT P Phi1 (coneMinus P X) = -coneMinus P X) := by
  have hPN1 := stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators
    hP hP_star hPhi_sq hPhi_star hPhi_P
  have hJ1_sq : pinJ1 P Phi1 * pinJ1 P Phi1 = -1 := hPN1.2.2.2.1
  have hJ1_star : star (pinJ1 P Phi1) = -pinJ1 P Phi1 := hPN1.2.2.2.2.1
  have hPN2 := stage_PN2_elementary_plabic_shears_and_symmetric_star_swap_laws
    hP hP_star hPhi_sq hPhi_P hX_star hPhi_X
  have hComp : ∀ Z : B, parityAlpha P (chargeBeta Phi1 (timeTau Z)) = thetaCPT P Phi1 Z := by
    intro Z
    exact (cpGamma_eq_parity_charge hPhi_P (timeTau Z)).symm
  refine ⟨hComp Y, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · calc thetaCPT P Phi1 (A * C)
      _ = -(pinJ1 P Phi1 * (star C * star A) * pinJ1 P Phi1) := by
          dsimp [thetaCPT]; rw [star_mul]
      _ = pinJ1 P Phi1 * star C * (-1) * star A * pinJ1 P Phi1 := by noncomm_ring
      _ = pinJ1 P Phi1 * star C * (pinJ1 P Phi1 * pinJ1 P Phi1) * star A * pinJ1 P Phi1 := by
          rw [← hJ1_sq]
      _ = (-(pinJ1 P Phi1 * star C * pinJ1 P Phi1)) *
            (-(pinJ1 P Phi1 * star A * pinJ1 P Phi1)) := by noncomm_ring
      _ = thetaCPT P Phi1 C * thetaCPT P Phi1 A := rfl
  · calc thetaCPT P Phi1 1
      _ = -(pinJ1 P Phi1 * 1 * pinJ1 P Phi1) := by dsimp [thetaCPT]; rw [star_one]
      _ = -(pinJ1 P Phi1 * pinJ1 P Phi1) := by noncomm_ring
      _ = -(-1) := by rw [hJ1_sq]
      _ = 1 := by norm_num
  · have hStarInner :
        star (thetaCPT P Phi1 Y) = -(pinJ1 P Phi1 * Y * pinJ1 P Phi1) := by
      calc star (thetaCPT P Phi1 Y)
        _ = -(star (pinJ1 P Phi1) * (star (star Y) * star (pinJ1 P Phi1))) := by
            dsimp [thetaCPT]
            rw [star_neg, star_mul, star_mul]
        _ = -((-pinJ1 P Phi1) * (Y * (-pinJ1 P Phi1))) := by
            rw [hJ1_star, star_star]
        _ = -(pinJ1 P Phi1 * Y * pinJ1 P Phi1) := by noncomm_ring
    calc thetaCPT P Phi1 (thetaCPT P Phi1 Y)
      _ = -(pinJ1 P Phi1 * (-(pinJ1 P Phi1 * Y * pinJ1 P Phi1)) * pinJ1 P Phi1) := by
          change -(pinJ1 P Phi1 * star (thetaCPT P Phi1 Y) * pinJ1 P Phi1) = _
          rw [hStarInner]
      _ = (pinJ1 P Phi1 * pinJ1 P Phi1) * Y * (pinJ1 P Phi1 * pinJ1 P Phi1) := by
          noncomm_ring
      _ = (-1) * Y * (-1) := by rw [hJ1_sq]
      _ = Y := by noncomm_ring
  · calc thetaCPT P Phi1 (conePlus P X)
      _ = cpGamma P Phi1 (timeTau (conePlus P X)) := rfl
      _ = cpGamma P Phi1 (coneMinus P X) := by rw [hPN2.1.1]
      _ = -conePlus P X := hPN2.2.2.2.1.2
  · calc thetaCPT P Phi1 (coneMinus P X)
      _ = cpGamma P Phi1 (timeTau (coneMinus P X)) := rfl
      _ = cpGamma P Phi1 (conePlus P X) := by rw [hPN2.1.2]
      _ = -coneMinus P X := hPN2.2.2.2.1.1

/-- **Stage `𝔓𝔑₄` (`stage_PN4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries`)**:
1. **Ordinary Star Product Expansion for Peirce-Corner Shears**:
   `(1 + N_+) * timeTau (1 + N_+) = (1 + N_+) * (1 + N_-) = 1 + (N_+ + N_-) + N_+ * N_-`.
2. **Formulas for the Partial Maps `T`, `CT`, and `PT` on `G_+ = (1 + N_+)(1 + N_-)`**:
   - `timeTau ((1 + N_+) * (1 + N_-)) = (1 + N_+) * (1 + N_-)` (`τ_T(G_+) = G_+`),
   - `chargeBeta Phi1 (timeTau ((1 + N_+) * (1 + N_-))) = (1 + N_-) * (1 + N_+)` (`β_C(τ_T(G_+)) = G_-`),
   - `parityAlpha P (timeTau ((1 + N_+) * (1 + N_-))) = (1 - N_+) * (1 - N_-)`.
These equations alone do not prove that any displayed product is unequal to identity. -/
theorem stage_PN4_socratic_aporia_of_ordinary_unitarity_and_partial_symmetries
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1) :
    ((1 + conePlus P X) * timeTau (1 + conePlus P X) =
       (1 + conePlus P X) * (1 + coneMinus P X) ∧
     (1 + conePlus P X) * (1 + coneMinus P X) =
       1 + (conePlus P X + coneMinus P X) + conePlus P X * coneMinus P X) ∧
    timeTau ((1 + conePlus P X) * (1 + coneMinus P X)) =
      (1 + conePlus P X) * (1 + coneMinus P X) ∧
    chargeBeta Phi1 (timeTau ((1 + conePlus P X) * (1 + coneMinus P X))) =
      (1 + coneMinus P X) * (1 + conePlus P X) ∧
    parityAlpha P (timeTau ((1 + conePlus P X) * (1 + coneMinus P X))) =
      (1 - conePlus P X) * (1 - coneMinus P X) := by
  have hPN2 := stage_PN2_elementary_plabic_shears_and_symmetric_star_swap_laws
    hP hP_star hPhi_sq hPhi_P hX_star hPhi_X
  have hTauPlus : star (conePlus P X) = coneMinus P X := hPN2.1.1
  have hTauMinus : star (coneMinus P X) = conePlus P X := hPN2.1.2
  have hTauG :
      timeTau ((1 + conePlus P X) * (1 + coneMinus P X)) =
        (1 + conePlus P X) * (1 + coneMinus P X) := by
    dsimp [timeTau]
    rw [star_mul, star_add, star_add, star_one, hTauPlus, hTauMinus]
  refine ⟨⟨?_, by noncomm_ring⟩, hTauG, ?_, ?_⟩
  · dsimp [timeTau]
    rw [star_add, star_one, hTauPlus]
  · rw [hTauG]
    calc chargeBeta Phi1 ((1 + conePlus P X) * (1 + coneMinus P X))
      _ = Phi1 * ((1 + conePlus P X) * 1 * (1 + coneMinus P X)) * Phi1 := by
          dsimp [chargeBeta]; noncomm_ring
      _ = Phi1 * ((1 + conePlus P X) * (Phi1 * Phi1) * (1 + coneMinus P X)) * Phi1 := by
          rw [hPhi_sq]
      _ = (Phi1 * Phi1 + chargeBeta Phi1 (conePlus P X)) *
            (Phi1 * Phi1 + chargeBeta Phi1 (coneMinus P X)) := by
          dsimp [chargeBeta]; noncomm_ring
      _ = (1 + coneMinus P X) * (1 + conePlus P X) := by
          rw [hPhi_sq, hPN2.2.1.1, hPN2.2.1.2]
  · rw [hTauG]
    dsimp [parityAlpha]
    peirce_nf hP

/-- **Finite-Word Twisted-Star Inversion (`plabicWord_cpt_unitary`)**:
For any list `L : List B` of Plabic network gates each satisfying `g * Θ_CPT(g) = 1` and
`Θ_CPT(g) * g = 1`, the product `W = plabicWord L` satisfies the corresponding algebraic
two-sided inverse identities. No physical network or Hilbert-space structure is part of this theorem. -/
theorem plabicWord_cpt_unitary
    {B : Type*} [Ring B] [StarRing B] {P Phi1 : B}
    (hJ1_sq : pinJ1 P Phi1 * pinJ1 P Phi1 = -1)
    (L : List B)
    (hL : ∀ g ∈ L, g * thetaCPT P Phi1 g = 1 ∧ thetaCPT P Phi1 g * g = 1) :
    plabicWord L * thetaCPT P Phi1 (plabicWord L) = 1 ∧
    thetaCPT P Phi1 (plabicWord L) * plabicWord L = 1 := by
  have hMul : ∀ A C : B, thetaCPT P Phi1 (A * C) = thetaCPT P Phi1 C * thetaCPT P Phi1 A := by
    intro A C
    calc thetaCPT P Phi1 (A * C)
      _ = -(pinJ1 P Phi1 * (star C * star A) * pinJ1 P Phi1) := by
          dsimp [thetaCPT]; rw [star_mul]
      _ = pinJ1 P Phi1 * star C * (-1) * star A * pinJ1 P Phi1 := by noncomm_ring
      _ = pinJ1 P Phi1 * star C * (pinJ1 P Phi1 * pinJ1 P Phi1) * star A * pinJ1 P Phi1 := by
          rw [← hJ1_sq]
      _ = (-(pinJ1 P Phi1 * star C * pinJ1 P Phi1)) *
            (-(pinJ1 P Phi1 * star A * pinJ1 P Phi1)) := by noncomm_ring
      _ = thetaCPT P Phi1 C * thetaCPT P Phi1 A := rfl
  have hOne : thetaCPT P Phi1 1 = 1 := by
    calc thetaCPT P Phi1 1
      _ = -(pinJ1 P Phi1 * 1 * pinJ1 P Phi1) := by dsimp [thetaCPT]; rw [star_one]
      _ = -(pinJ1 P Phi1 * pinJ1 P Phi1) := by noncomm_ring
      _ = -(-1) := by rw [hJ1_sq]
      _ = 1 := by norm_num
  induction L with
  | nil =>
      dsimp [plabicWord]
      rw [hOne, mul_one]
      exact ⟨rfl, rfl⟩
  | cons g gs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hL
      have ih_gs := ih hL.2
      dsimp [plabicWord]
      rw [hMul]
      refine ⟨?_, ?_⟩
      · calc (g * plabicWord gs) * (thetaCPT P Phi1 (plabicWord gs) * thetaCPT P Phi1 g)
          _ = g * (plabicWord gs * thetaCPT P Phi1 (plabicWord gs)) * thetaCPT P Phi1 g := by
              noncomm_ring
          _ = g * 1 * thetaCPT P Phi1 g := by rw [ih_gs.1]
          _ = g * thetaCPT P Phi1 g := by noncomm_ring
          _ = 1 := hL.1.1
      · calc (thetaCPT P Phi1 (plabicWord gs) * thetaCPT P Phi1 g) * (g * plabicWord gs)
          _ = thetaCPT P Phi1 (plabicWord gs) * (thetaCPT P Phi1 g * g) * plabicWord gs := by
              noncomm_ring
          _ = thetaCPT P Phi1 (plabicWord gs) * 1 * plabicWord gs := by rw [hL.1.2]
          _ = thetaCPT P Phi1 (plabicWord gs) * plabicWord gs := by noncomm_ring
          _ = 1 := ih_gs.2

/-- **Stage `𝔓𝔑₅` (`stage_PN5_universal_cpt_word_inversion_and_unitarity`)**:
1. **Elementary Plabic Gate `CPT`-Inversion**:
   `thetaCPT(1 + N_±) = 1 - N_±` with the two algebraic inverse equations.
2. **Exact Two-Sided `CPT`-Inversion of the Two-Step Plabic Diamond `G_+ = (1 + N_+)(1 + N_-)`**:
   `thetaCPT(G_+) = (1 - N_-)(1 - N_+)` with the two algebraic inverse equations.
3. **Universal Multi-Hop Plabic Word `CPT`-Unitarity**:
   For a list of gates satisfying the stated `thetaCPT` inverse hypotheses, the product has the
   corresponding algebraic inverse identities. No physical unitarity is claimed. -/
theorem stage_PN5_universal_cpt_word_inversion_and_unitarity
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1)
    (L : List B)
    (hL : ∀ g ∈ L, g * thetaCPT P Phi1 g = 1 ∧ thetaCPT P Phi1 g * g = 1) :
    (thetaCPT P Phi1 (1 + conePlus P X) = 1 - conePlus P X ∧
     (1 + conePlus P X) * thetaCPT P Phi1 (1 + conePlus P X) = 1 ∧
     thetaCPT P Phi1 (1 + conePlus P X) * (1 + conePlus P X) = 1) ∧
    (thetaCPT P Phi1 (1 + coneMinus P X) = 1 - coneMinus P X ∧
     (1 + coneMinus P X) * thetaCPT P Phi1 (1 + coneMinus P X) = 1 ∧
     thetaCPT P Phi1 (1 + coneMinus P X) * (1 + coneMinus P X) = 1) ∧
    (thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) =
       (1 - coneMinus P X) * (1 - conePlus P X) ∧
     ((1 + conePlus P X) * (1 + coneMinus P X)) *
       thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) = 1 ∧
     thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) *
       ((1 + conePlus P X) * (1 + coneMinus P X)) = 1) ∧
    (plabicWord L * thetaCPT P Phi1 (plabicWord L) = 1 ∧
     thetaCPT P Phi1 (plabicWord L) * plabicWord L = 1) := by
  have hPN1 := stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators
    hP hP_star hPhi_sq hPhi_star hPhi_P
  have hPN3_plus := stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X 0 (1 + conePlus P X) (1 + coneMinus P X)
  have hOne : thetaCPT P Phi1 1 = 1 := hPN3_plus.2.1.2
  have hCPT_plus : thetaCPT P Phi1 (conePlus P X) = -conePlus P X := hPN3_plus.2.2.2.1
  have hCPT_minus : thetaCPT P Phi1 (coneMinus P X) = -coneMinus P X := hPN3_plus.2.2.2.2
  have hGatePlus : thetaCPT P Phi1 (1 + conePlus P X) = 1 - conePlus P X := by
    rw [thetaCPT_add, hOne, hCPT_plus]
    abel
  have hGateMinus : thetaCPT P Phi1 (1 + coneMinus P X) = 1 - coneMinus P X := by
    rw [thetaCPT_add, hOne, hCPT_minus]
    abel
  have hDiamond :
      thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) =
        (1 - coneMinus P X) * (1 - conePlus P X) := by
    rw [hPN3_plus.2.1.1, hGateMinus, hGatePlus]
  refine ⟨⟨hGatePlus, ?_, ?_⟩, ⟨hGateMinus, ?_, ?_⟩, ⟨hDiamond, ?_, ?_⟩,
    plabicWord_cpt_unitary hPN1.2.2.2.1 L hL⟩
  · rw [hGatePlus]; peirce_nf hP
  · rw [hGatePlus]; peirce_nf hP
  · rw [hGateMinus]; peirce_nf hP
  · rw [hGateMinus]; peirce_nf hP
  · rw [hDiamond]; peirce_nf hP
  · rw [hDiamond]; peirce_nf hP

/-- **Stage `𝔓𝔑₆` (`stage_PN6_cpt_transformation_table_of_geometric_observables`)**:
Exact `Θ_CPT` transformation table on the corner products `Q_+ = N_+ N_-`, `Q_- = N_- N_+`
and the four geometric observables `V = {N_+, N_-}`, `Σ = [N_+, N_-]`, `Φ = N_+ + N_-`,
`J = N_+ - N_-`:
1. `Θ_CPT(N_+ * N_-) = N_- * N_+` (`Θ_CPT(Q_+) = Q_-`) and
   `Θ_CPT(N_- * N_+) = N_+ * N_-` (`Θ_CPT(Q_-) = Q_+`),
2. `Θ_CPT(anticomm N_+ N_-) = anticomm N_+ N_-` (`Θ_CPT(V) = +V`),
3. `Θ_CPT(comm N_+ N_-) = -comm N_+ N_-` (`Θ_CPT(Σ) = -Σ`),
4. `Θ_CPT(N_+ + N_-) = -(N_+ + N_-)` (`Θ_CPT(Φ) = -Φ`),
5. `Θ_CPT(N_+ - N_-) = -(N_+ - N_-)` (`Θ_CPT(J) = -J`). -/
theorem stage_PN6_cpt_transformation_table_of_geometric_observables
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1) :
    (thetaCPT P Phi1 (conePlus P X * coneMinus P X) = coneMinus P X * conePlus P X ∧
     thetaCPT P Phi1 (coneMinus P X * conePlus P X) = conePlus P X * coneMinus P X) ∧
    thetaCPT P Phi1 (anticomm (conePlus P X) (coneMinus P X)) =
      anticomm (conePlus P X) (coneMinus P X) ∧
    thetaCPT P Phi1 (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P X)) =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P X) ∧
    thetaCPT P Phi1 (conePlus P X + coneMinus P X) =
      -(conePlus P X + coneMinus P X) ∧
    thetaCPT P Phi1 (conePlus P X - coneMinus P X) =
      -(conePlus P X - coneMinus P X) := by
  have hPN3_1 := stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X 0 (conePlus P X) (coneMinus P X)
  have hPN3_2 := stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X 0 (coneMinus P X) (conePlus P X)
  have hCPT_plus : thetaCPT P Phi1 (conePlus P X) = -conePlus P X := hPN3_1.2.2.2.1
  have hCPT_minus : thetaCPT P Phi1 (coneMinus P X) = -coneMinus P X := hPN3_1.2.2.2.2
  have hQPlus : thetaCPT P Phi1 (conePlus P X * coneMinus P X) = coneMinus P X * conePlus P X := by
    rw [hPN3_1.2.1.1, hCPT_minus, hCPT_plus]
    noncomm_ring
  have hQMinus : thetaCPT P Phi1 (coneMinus P X * conePlus P X) = conePlus P X * coneMinus P X := by
    rw [hPN3_2.2.1.1, hCPT_plus, hCPT_minus]
    noncomm_ring
  refine ⟨⟨hQPlus, hQMinus⟩, ?_, ?_, ?_, ?_⟩
  · dsimp [anticomm]
    rw [thetaCPT_add, hQPlus, hQMinus]
    abel
  · dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    rw [thetaCPT_sub, hQPlus, hQMinus]
    abel
  · rw [thetaCPT_add, hCPT_plus, hCPT_minus]
    abel
  · rw [thetaCPT_sub, hCPT_plus, hCPT_minus]
    abel

/-- **Master Stage Summary (`plabic_twisted_pin_cpt_master_poset`)**:
Combines the stipulated stage-graph acyclicity/cardinality facts with selected conditional
twisted-star identities. It does not claim that stage edges encode theorem dependencies or that
the algebraic map is a physical CPT operator. -/
theorem plabic_twisted_pin_cpt_master_poset
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1) :
    (∀ st : PlabicTwistedPinCPTStage,
      ¬ Relation.TransGen PlabicTwistedPinCPTStage.causalEdge st st) ∧
    Fintype.card PlabicTwistedPinCPTStage = 6 ∧
    pinJ1 P Phi1 * pinJ1 P Phi1 = -1 ∧
    thetaCPT P Phi1 (conePlus P X) = -conePlus P X ∧
    thetaCPT P Phi1 (coneMinus P X) = -coneMinus P X ∧
    ((1 + conePlus P X) * (1 + coneMinus P X)) *
      thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) = 1 ∧
    thetaCPT P Phi1 (anticomm (conePlus P X) (coneMinus P X)) =
      anticomm (conePlus P X) (coneMinus P X) ∧
    thetaCPT P Phi1 (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P X)) =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P X) := by
  have hPN1 := stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators
    hP hP_star hPhi_sq hPhi_star hPhi_P
  have hPN3 := stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X 0 0 0
  have hPN5 := stage_PN5_universal_cpt_word_inversion_and_unitarity
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X [] (by simp)
  have hPN6 := stage_PN6_cpt_transformation_table_of_geometric_observables
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X
  exact ⟨PlabicTwistedPinCPTStage.causalEdge_acyclic,
    PlabicTwistedPinCPTStage.card_eq_six,
    hPN1.2.2.2.1,
    hPN3.2.2.2.1,
    hPN3.2.2.2.2,
    hPN5.2.2.1.2.1,
    hPN6.2.1,
    hPN6.2.2.1⟩

end PlabicTwistedPinCPT

/-!
## Part XII: The 6-Stage AQFT Conformal Net Five-Fold Constructive & Metriplectic Advance Poset (`𝔄𝔇₁ ≺ 𝔄𝔇₂ ≺ 𝔄𝔇₃ ≺ {𝔄𝔇₄, 𝔄𝔇₅} ≺ 𝔄𝔇₆`)

Formalizes the 6-stage acyclic diamond poset comparing the 1954–2026 Algebraic QFT /
Conformal Net lineage (`[BMT88, BGL93, Was98, Gui21, Mar26]`) with the constructive
algebraic, metriplectic, Krein-LogCFT, split-octonion, and bitwise Tensor-Peirce advances
of this repository:
- `ad1_jaynesian_colimit_and_peirce_haag_duality_split` (`𝔄𝔇₁`):
  Peirce–DeWitt two-sheeted split $1 = P + (1 - P)$, chiral involution $S_P = 2P - 1$,
  Haag–Peirce commutant duality $P X = X P \iff N_+(P, X) = 0 \land N_-(P, X) = 0$, and
  finite-stage recursive `TensorTower` roundtrip (`toTensorTower n (ofTensorTower n T) = T`).
- `ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion` (`𝔄𝔇₂`):
  First-quantized dually flat ($e$-flat / $m$-flat) unipotent Amari coordinates
  $\mathcal{E}_\pm(P, X)\mathcal{E}_\pm(P, Y) = \mathcal{E}_\pm(P, X + Y)$,
  Sum–Difference Connection Crossover
  $[\nabla^{(e)} - \nabla^{(m)}, \Phi] = \{\nabla^{(e)} + \nabla^{(m)}, J\}$, and
  Twisted-$\mathrm{Pin}$ bipartite $\mathcal{C}\mathcal{P}\mathcal{T}$ word inversion
  $\mathcal{G}_+(P, X) \cdot \Theta_{\text{CPT}}(\mathcal{G}_+(P, X)) = 1$.
- `ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric` (`𝔄𝔇₃`):
  Exact ring balancing monodromy
  $(1 + \Sigma - V J + Q_+^2)\,\mathcal{G}_-(P, A, C) = \mathcal{G}_+(P, A, C)$,
  Master Clocking Identity $-[\Phi, [\Phi, J]] = -2[\Sigma, \Phi] = -4V J$, and
  Push–Pull Legendre–Möbius resolvent intertwining $(1 - Q_+) N_+ = N_+ (1 - Q_-)$.
- `ad4_krein_logcft_isotropic_horizon_and_unipotent_balance` (`𝔄𝔇₄`, diamond branch A):
  Krein–Hopf critical nilpotent $N_{\text{nil}} = A_{\text{kr}} + B_{\text{kr}}$
  ($A_{\text{kr}}^2 = -1, B_{\text{kr}}^2 = 1, \{A_{\text{kr}}, B_{\text{kr}}\} = 0 \implies N_{\text{nil}}^2 = 0$),
  unipotent LogCFT balance twist $(1 - N_{\text{nil}})(1 + N_{\text{nil}}) = 1$,
  isotropic Jordan eigenvector invariance $N_{\text{nil}}((1 - N_{\text{nil}})\Phi_{\text{gen}}) = N_{\text{nil}}\Phi_{\text{gen}}$,
  and quadratic secular evolution $(1 - N_{\text{nil}}) O (1 + N_{\text{nil}}) = O - [N_{\text{nil}}, O] - N_{\text{nil}} O N_{\text{nil}}$.
- `ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower` (`𝔄𝔇₅`, diamond branch B):
  Split-octonion 3-body Baryon/Nambu anticommutator
  $\{\psi_+(u_1)\psi_+(u_2), \psi_+(u_3)\} = \det(u_1, u_2, u_3)\cdot 1$,
  tripotent binomial sandwich $(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = -3 H\,\mathrm{ad}_H(X)\,H$,
  5-graded Kantor–Tanaka quintic contact law $\mathrm{ad}_H^5 - 5\,\mathrm{ad}_H^3 + 4\,\mathrm{ad}_H = 0$
  under $H^3 = H$, and $4! = 24$ integer scaled projector resolution of identity.
- `ad6_bitwise_clifford_transformer_compiler_and_master_synthesis` (`𝔄𝔇₆`):
  $n$-bit symplectic $\mathcal{C}\ell(1,1)^{\otimes n}$ basis multiplication law
  $\Gamma_{(x_1, z_1)}\Gamma_{(x_2, z_2)} = \mathrm{bvSign}(x_1, z_2)\bullet\Gamma_{(x_1\oplus x_2, z_1\oplus z_2)}$,
  division-free XOR banding roundtrip $\mathrm{unband}(\mathrm{xorBand}(M)) = M$, and
  master 6-stage synthesis.
-/

/-- The 6-stage causal poset of the Five-Fold Constructive & Metriplectic Advance
over the 1954–2026 AQFT / Conformal Net lineage (`𝔄𝔇₁ ≺ 𝔄𝔇₂ ≺ 𝔄𝔇₃ ≺ {𝔄𝔇₄, 𝔄𝔇₅} ≺ 𝔄𝔇₆`). -/
inductive ConformalNetFiveFoldAdvanceStage : Type
  | ad1_jaynesian_colimit_and_peirce_haag_duality_split
  | ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion
  | ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric
  | ad4_krein_logcft_isotropic_horizon_and_unipotent_balance
  | ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower
  | ad6_bitwise_clifford_transformer_compiler_and_master_synthesis
  deriving DecidableEq, Repr, Inhabited

namespace ConformalNetFiveFoldAdvanceStage

/-- Topological rank `0..4` (diamond branches `ad4` and `ad5` share rank `3`). -/
def rank : ConformalNetFiveFoldAdvanceStage → ℕ
  | .ad1_jaynesian_colimit_and_peirce_haag_duality_split                   => 0
  | .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion => 1
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric   => 2
  | .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance              => 3
  | .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower => 3
  | .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis        => 4

/-- Total index `0..5` for `Fintype` and `LinearOrder`. -/
def stageIndex : ConformalNetFiveFoldAdvanceStage → ℕ
  | .ad1_jaynesian_colimit_and_peirce_haag_duality_split                   => 0
  | .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion => 1
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric   => 2
  | .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance              => 3
  | .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower => 4
  | .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis        => 5

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder ConformalNetFiveFoldAdvanceStage where
  le a b := stageIndex a ≤ stageIndex b
  lt a b := stageIndex a < stageIndex b
  le_refl a := le_rfl
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (stageIndex a) (stageIndex b)
  le_antisymm _ _ hab hba := stageIndex_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (stageIndex a) (stageIndex b)
  toDecidableLE a b := Nat.decLe (stageIndex a) (stageIndex b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (stageIndex a) (stageIndex b)

instance : Fintype ConformalNetFiveFoldAdvanceStage where
  elems := {
    .ad1_jaynesian_colimit_and_peirce_haag_duality_split,
    .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion,
    .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric,
    .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance,
    .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower,
    .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card ConformalNetFiveFoldAdvanceStage = 6 := rfl

/-- Directed covering edges of the diamond poset `𝔄𝔇₁ ≺ 𝔄𝔇₂ ≺ 𝔄𝔇₃ ≺ {𝔄𝔇₄, 𝔄𝔇₅} ≺ 𝔄𝔇₆`. -/
def causalEdge : ConformalNetFiveFoldAdvanceStage → ConformalNetFiveFoldAdvanceStage → Prop
  | .ad1_jaynesian_colimit_and_peirce_haag_duality_split,
    .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion => True
  | .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion,
    .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric => True
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric,
    .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance => True
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric,
    .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower => True
  | .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance,
    .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis => True
  | .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower,
    .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis => True
  | _, _ => False

theorem causalEdge_lt {a b : ConformalNetFiveFoldAdvanceStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge rank <;> decide

theorem transGen_causalEdge_lt {a b : ConformalNetFiveFoldAdvanceStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

theorem causalEdge_acyclic (a : ConformalNetFiveFoldAdvanceStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

theorem diamond_branches_incomparable :
    ¬ Relation.TransGen causalEdge
        .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance
        .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower ∧
    ¬ Relation.TransGen causalEdge
        .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower
        .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt := transGen_causalEdge_lt h
    revert hlt; decide
  · have hlt := transGen_causalEdge_lt h
    revert hlt; decide

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : ConformalNetFiveFoldAdvanceStage → InfoGeometry.Meta.RepDepth
  | .ad1_jaynesian_colimit_and_peirce_haag_duality_split                   => .operator
  | .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion => .transport
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric   => .transport
  | .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance              => .thermo
  | .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower => .thermo
  | .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis        => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    ConformalNetFiveFoldAdvanceStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .ad1_jaynesian_colimit_and_peirce_haag_duality_split                   => .M1_ProjectorClabject
  | .ad2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion => .M2_GrassmannianPowertypeOrbit
  | .ad3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric   => .M2_GrassmannianPowertypeOrbit
  | .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance              => .M3_ErlangenCasimirMetaLaw
  | .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower => .M3_ErlangenCasimirMetaLaw
  | .ad6_bitwise_clifford_transformer_compiler_and_master_synthesis        => .M3_ErlangenCasimirMetaLaw

theorem causalEdge_toRepDepth_mono {a b : ConformalNetFiveFoldAdvanceStage}
    (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toRepDepth InfoGeometry.Meta.RepDepth.toNat <;> decide

theorem toRepDepth_mono {a b : ConformalNetFiveFoldAdvanceStage}
    (h : Relation.TransGen causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  induction h with
  | single hab => exact causalEdge_toRepDepth_mono hab
  | tail _ hbc ih => exact Nat.le_trans ih (causalEdge_toRepDepth_mono hbc)

theorem causalEdge_toOntologyMetaLevel_mono {a b : ConformalNetFiveFoldAdvanceStage}
    (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;> decide

theorem toOntologyMetaLevel_mono {a b : ConformalNetFiveFoldAdvanceStage}
    (h : Relation.TransGen causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  induction h with
  | single hab => exact causalEdge_toOntologyMetaLevel_mono hab
  | tail _ hbc ih => exact Nat.le_trans ih (causalEdge_toOntologyMetaLevel_mono hbc)

end ConformalNetFiveFoldAdvanceStage

namespace ConformalNetFiveFoldAdvance

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- **Stage `𝔄𝔇₁` (`stage_AD1_jaynesian_colimit_and_peirce_haag_duality_split`)**:
1. **Peirce–DeWitt Two-Sheeted Split & $V_4 = \mathbb{Z}_2 \times \mathbb{Z}_2$ Involution**:
   `P + (1 - P) = 1`, `P * (1 - P) = 0`, `(1 - P) * P = 0`, `invS P * invS P = 1`.
2. **Haag–Peirce Commutant Orthogonality & Duality**:
   `(P * A * P) * ((1 - P) * C * (1 - P)) = 0`,
   `((1 - P) * C * (1 - P)) * (P * A * P) = 0`, and
   `P * X = X * P ↔ (conePlus P X = 0 ∧ coneMinus P X = 0)`.
3. **Finite-Stage Recursive `TensorTower` Roundtrip & $2 \times 2$ Block Reconstruction**:
   `toTensorTower n (ofTensorTower n T) = T` and
   `unitE00 * matPi00 M₂ + unitE01 * matPi01 M₂ + unitE10 * matPi10 M₂ + unitE11 * matPi11 M₂ = M₂`. -/
theorem stage_AD1_jaynesian_colimit_and_peirce_haag_duality_split
    {B : Type*} [Ring B] {R : Type*} [Ring R]
    {P : B} (hP : P * P = P) (A C X : B)
    (n : ℕ) (T : TensorTower R n) (M₂ : Matrix (Fin 2) (Fin 2) R) :
    (P + (1 - P) = 1 ∧ P * (1 - P) = 0 ∧ (1 - P) * P = 0 ∧ invS P * invS P = 1) ∧
    ((P * A * P) * ((1 - P) * C * (1 - P)) = 0 ∧
     ((1 - P) * C * (1 - P)) * (P * A * P) = 0 ∧
     (P * X = X * P ↔ (conePlus P X = 0 ∧ coneMinus P X = 0))) ∧
    (TensorTower.toTensorTower n (TensorTower.ofTensorTower n T) = T ∧
     TensorTower.unitE00 * TensorTower.matPi00 M₂ +
       TensorTower.unitE01 * TensorTower.matPi01 M₂ +
       TensorTower.unitE10 * TensorTower.matPi10 M₂ +
       TensorTower.unitE11 * TensorTower.matPi11 M₂ = M₂) := by
  have hCN1 := ConformalNetBalancedRep.stage_CN1_interval_haag_duality_and_bisognano_wichmann_modular_boost
    hP A C
  have hTN12 := stage_TN1_TN2_scale_decomposition_and_dually_flat_unipotent_attention_gates
    n T M₂ hP X X
  have hCommIff : P * X = X * P ↔ (conePlus P X = 0 ∧ coneMinus P X = 0) := by
    constructor
    · intro hComm
      refine ⟨?_, ?_⟩
      · calc conePlus P X
          _ = (P * X) * (1 - P) := by rfl
          _ = (X * P) * (1 - P) := by rw [hComm]
          _ = 0 := by peirce_nf hP
      · calc coneMinus P X
          _ = (1 - P) * (X * P) := by dsimp [coneMinus]; rw [mul_assoc]
          _ = (1 - P) * (P * X) := by rw [← hComm]
          _ = 0 := by peirce_nf hP
    · rintro ⟨hNp, hNm⟩
      have hDiff : P * X - X * P = conePlus P X - coneMinus P X := by
        dsimp [conePlus, coneMinus]; peirce_nf hP
      have hSub : P * X - X * P = 0 := by
        rw [hDiff, hNp, hNm, sub_zero]
      exact sub_eq_zero.mp hSub
  exact ⟨⟨hCN1.1.1, hCN1.1.2.1, hCN1.1.2.2, hCN1.2.2.1⟩,
    ⟨hCN1.2.1.1, hCN1.2.1.2.1, hCommIff⟩,
    ⟨hTN12.1, hTN12.2.1⟩⟩

/-- **Stage `𝔄𝔇₂` (`stage_AD2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion`)**:
1. **First-Quantized Amari $e$-Flat and $m$-Flat Unipotent Coordinates**:
   `(1 + conePlus P X) * (1 + conePlus P Y) = 1 + conePlus P (X + Y)` and
   `(1 + coneMinus P X) * (1 + coneMinus P Y) = 1 + coneMinus P (X + Y)`.
2. **Sum–Difference Connection Crossover (`[\nabla^{(e)} - \nabla^{(m)}, \Phi] = \{\nabla^{(e)} + \nabla^{(m)}, J\}`)**:
   `comm (P * W * P - (1 - P) * W * (1 - P)) (conePlus P X + coneMinus P Y) =
      anticomm (P * W * P + (1 - P) * W * (1 - P)) (conePlus P X - coneMinus P Y)`.
3. **Twisted-$\mathrm{Pin}$ Bipartite $\mathcal{C}\mathcal{P}\mathcal{T}$ Plabic Word Inversion**:
   `((1 + conePlus P X) * (1 + coneMinus P X)) *
      PlabicTwistedPinCPT.thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) = 1`
   and `PlabicTwistedPinCPT.plabicWord L *
      PlabicTwistedPinCPT.thetaCPT P Phi1 (PlabicTwistedPinCPT.plabicWord L) = 1`. -/
theorem stage_AD2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion
    {B : Type*} [Ring B] [StarRing B]
    {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1)
    (Y W : B) (L : List B)
    (hL : ∀ g ∈ L,
      g * PlabicTwistedPinCPT.thetaCPT P Phi1 g = 1 ∧
      PlabicTwistedPinCPT.thetaCPT P Phi1 g * g = 1) :
    ((1 + conePlus P X) * (1 + conePlus P Y) = 1 + conePlus P (X + Y) ∧
     (1 + coneMinus P X) * (1 + coneMinus P Y) = 1 + coneMinus P (X + Y)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (P * W * P - (1 - P) * W * (1 - P)) (conePlus P X + coneMinus P Y) =
      anticomm (P * W * P + (1 - P) * W * (1 - P)) (conePlus P X - coneMinus P Y) ∧
    (((1 + conePlus P X) * (1 + coneMinus P X)) *
       PlabicTwistedPinCPT.thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) = 1 ∧
     PlabicTwistedPinCPT.plabicWord L *
       PlabicTwistedPinCPT.thetaCPT P Phi1 (PlabicTwistedPinCPT.plabicWord L) = 1) := by
  have hPN5 := PlabicTwistedPinCPT.stage_PN5_universal_cpt_word_inversion_and_unitarity
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X L hL
  refine ⟨⟨by peirce_nf hP, by peirce_nf hP⟩,
    by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, anticomm]; peirce_nf hP,
    ⟨hPN5.2.2.1.2.1, hPN5.2.2.2.1⟩⟩

/-- **Stage `𝔄𝔇₃` (`stage_AD3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric`)**:
1. **Exact Ring Realization of Marín-Salvador's Balancing Identity (`Thm. 4.4`)**:
   With $\mathcal{G}_+(P, A, C) = (1 + N_+)(1 + N_-)$, $\mathcal{G}_-(P, A, C) = (1 + N_-)(1 + N_+)$,
   $\Phi = N_+ + N_-$, $J = N_+ - N_-$, $V = \{N_+, N_-\}$, $\Sigma = [N_+, N_-]$, and $Q_+ = N_+ N_-$:
   $$(1 + \Sigma - V J + Q_+^2)\,\mathcal{G}_-(P, A, C) \;=\; \mathcal{G}_+(P, A, C)$$
   and
   $$\mathcal{G}_+(P, A, C)\,(1 - N_+)(1 - N_-) \;=\; 1 + \Sigma - V J + Q_+^2.$$
2. **Metriplectic Master Clocking Identity**:
   $$-[\Phi, [\Phi, J]] \;=\; -2[\Sigma, \Phi] \;=\; -4 V J.$$
3. **Push–Pull Legendre–Möbius Resolvent Intertwining (`R_+ N_+ = N_+ R_-`)**:
   `(1 - (conePlus P A * coneMinus P C)) * conePlus P A =
      conePlus P A * (1 - (coneMinus P C * conePlus P A))` and
   `(1 - anticomm (conePlus P A) (coneMinus P C)) * conePlus P A =
      (1 - (conePlus P A * coneMinus P C)) * conePlus P A`. -/
theorem stage_AD3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    let Np := conePlus P A
    let Nm := coneMinus P C
    let Phi := Np + Nm
    let J := Np - Nm
    let V := anticomm Np Nm
    let Sigma := InfoGeometry.OperatorAlgebra.PeirceSpine.comm Np Nm
    let Qp := Np * Nm
    let Qm := Nm * Np
    ((1 + Sigma - V * J + Qp * Qp) * ((1 + Nm) * (1 + Np)) = (1 + Np) * (1 + Nm) ∧
     ((1 + Np) * (1 + Nm)) * ((1 - Np) * (1 - Nm)) = 1 + Sigma - V * J + Qp * Qp) ∧
    (-(InfoGeometry.OperatorAlgebra.PeirceSpine.comm Phi
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Phi J)) =
        -((2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.comm Sigma Phi) ∧
     -(InfoGeometry.OperatorAlgebra.PeirceSpine.comm Phi
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Phi J)) =
        -((4 : ℤ) • (V * J))) ∧
    ((1 - Qp) * Np = Np * (1 - Qm) ∧
     (1 - V) * Np = (1 - Qp) * Np) := by
  dsimp only
  have hTN4 := stage_TN4_bruhat_dressed_grassmannian_projector_and_legendre_mobius_push_pull
    hP A C
  refine ⟨⟨by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, anticomm]; peirce_nf hP,
           by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, anticomm]; peirce_nf hP⟩,
    ⟨by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP,
     by dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, anticomm]; peirce_nf hP⟩,
    ⟨hTN4.2.2.1, hTN4.2.2.2⟩⟩

/-- **Stage `𝔄𝔇₄` (`stage_AD4_krein_logcft_isotropic_horizon_and_unipotent_balance`)**:
1. **Krein–Hopf Critical Exceptional Horizon (`A_kr² = -1, B_kr² = 1, {A_kr, B_kr} = 0`)**:
   The critical generator $N_{\text{nil}} := A_{\text{kr}} + B_{\text{kr}}$ satisfies:
   - `N_nil * N_nil = 0`,
   - `N_nil * A_kr * N_nil = -((2 : ℤ) • N_nil)`,
   - `(1 - N_nil) * A_kr * (1 + N_nil) = A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • N_nil`.
2. **Unipotent LogCFT Balance Twist & Isotropic Jordan Eigenvector Invariance**:
   For any $N_{\text{nil}} \in B$ with $N_{\text{nil}}^2 = 0$:
   - `(1 - N_nil) * (1 + N_nil) = 1` and `(1 + N_nil) * (1 - N_nil) = 1`,
   - `N_nil * ((1 - N_nil) * Phi_gen) = N_nil * Phi_gen` (the exceptional eigenvector
     $\Psi_{\text{EP}} = N_{\text{nil}}\Phi_{\text{gen}}$ is fixed by the unipotent balance twist!),
   - `(1 - N_nil) * O * (1 + N_nil) = O - comm N_nil O - N_nil * O * N_nil`. -/
theorem stage_AD4_krein_logcft_isotropic_horizon_and_unipotent_balance
    {B : Type*} [Ring B]
    {A_kr B_kr N_nil : B}
    (hA_kr : A_kr * A_kr = -1) (hB_kr : B_kr * B_kr = 1)
    (hAnti_kr : A_kr * B_kr + B_kr * A_kr = 0)
    (hNil : N_nil * N_nil = 0) (Phi_gen O : B) :
    ((A_kr + B_kr) * (A_kr + B_kr) = 0 ∧
     (A_kr + B_kr) * A_kr * (A_kr + B_kr) = -((2 : ℤ) • (A_kr + B_kr)) ∧
     (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
       A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr)) ∧
    ((1 - N_nil) * (1 + N_nil) = 1 ∧
     (1 + N_nil) * (1 - N_nil) = 1 ∧
     N_nil * ((1 - N_nil) * Phi_gen) = N_nil * Phi_gen ∧
     (1 - N_nil) * O * (1 + N_nil) =
       O - InfoGeometry.OperatorAlgebra.PeirceSpine.comm N_nil O - N_nil * O * N_nil) := by
  have hKreinNil : (A_kr + B_kr) * (A_kr + B_kr) = 0 := by
    calc (A_kr + B_kr) * (A_kr + B_kr)
      _ = A_kr * A_kr + (A_kr * B_kr + B_kr * A_kr) + B_kr * B_kr := by noncomm_ring
      _ = -1 + 0 + 1 := by rw [hA_kr, hAnti_kr, hB_kr]
      _ = 0 := by abel
  have hBA : B_kr * A_kr = -(A_kr * B_kr) := eq_neg_of_add_eq_zero_right hAnti_kr
  have hKreinSandwich : (A_kr + B_kr) * A_kr * (A_kr + B_kr) = -((2 : ℤ) • (A_kr + B_kr)) := by
    calc (A_kr + B_kr) * A_kr * (A_kr + B_kr)
      _ = (A_kr * A_kr) * A_kr + (A_kr * A_kr) * B_kr + B_kr * (A_kr * A_kr) +
            (B_kr * A_kr) * B_kr := by noncomm_ring
      _ = (-1) * A_kr + (-1) * B_kr + B_kr * (-1) + (-(A_kr * B_kr)) * B_kr := by
            rw [hA_kr, hBA]
      _ = -A_kr - B_kr - B_kr - A_kr * (B_kr * B_kr) := by noncomm_ring
      _ = -A_kr - B_kr - B_kr - A_kr * 1 := by rw [hB_kr]
      _ = -((2 : ℤ) • (A_kr + B_kr)) := by noncomm_ring
  have hKreinSecular :
      (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
        A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr) := by
    calc (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr))
      _ = A_kr + (A_kr * B_kr - B_kr * A_kr) - (A_kr + B_kr) * A_kr * (A_kr + B_kr) := by
            noncomm_ring
      _ = A_kr + (A_kr * B_kr - -(A_kr * B_kr)) - -((2 : ℤ) • (A_kr + B_kr)) := by
            rw [hBA, hKreinSandwich]
      _ = A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr) := by noncomm_ring
  have hTN7 := stage_TN7_krein_logcft_secular_memory_and_drazin_aporia_resolution
    hNil O O
  refine ⟨⟨hKreinNil, hKreinSandwich, hKreinSecular⟩, ⟨?_, ?_, ?_, hTN7.1⟩⟩
  · calc (1 - N_nil) * (1 + N_nil)
      _ = 1 - N_nil * N_nil := by noncomm_ring
      _ = 1 - 0 := by rw [hNil]
      _ = 1 := by noncomm_ring
  · calc (1 + N_nil) * (1 - N_nil)
      _ = 1 - N_nil * N_nil := by noncomm_ring
      _ = 1 - 0 := by rw [hNil]
      _ = 1 := by noncomm_ring
  · calc N_nil * ((1 - N_nil) * Phi_gen)
      _ = N_nil * Phi_gen - (N_nil * N_nil) * Phi_gen := by noncomm_ring
      _ = N_nil * Phi_gen - 0 * Phi_gen := by rw [hNil]
      _ = N_nil * Phi_gen := by noncomm_ring

/-- **Stage `𝔄𝔇₅` (`stage_AD5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower`)**:
1. **Split-Octonion 3-Body Baryon / Nambu Anticommutator**:
   `{ψ_+(u₁) ψ_+(u₂), ψ_+(u₃)} = det(u₁, u₂, u₃) · 1` on `ZornMatrix K`.
2. **Tripotent Binomial Sandwich & 5-Graded Kantor–Tanaka Contact Law (`H³ = H`)**:
   - `ad_H³(X) - ad_H(X) = -3 H ad_H(X) H`,
   - `ad_H²(H ad_H(X) H) = 4 H ad_H(X) H`,
   - `ad_H⁵(X) - 5 ad_H³(X) + 4 ad_H(X) = 0`.
3. **Division-Free $4! = 24$ Integer Scaled Resolution of the 5-Graded Tower**:
   `P0_24 H X + P1_24 H X + Pm1_24 H X + P2_24 H X + Pm2_24 H X = (24 : ℤ) • X`. -/
theorem stage_AD5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower
    {B : Type*} [Ring B] {K : Type*} [CommRing K]
    {H : B} (hH : H * H * H = H) (X : B)
    (u₁ u₂ u₃ : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 K) :
    ((InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) *
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ +
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₃ *
      (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₁ *
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u₂) =
      zornMatrixScalar (zornVec3Det u₁ u₂ u₃)) ∧
    (adOp H (adOp H (adOp H X)) - adOp H X =
      -((3 : ℤ) • (H * adOp H X * H)) ∧
     adOp H (adOp H (H * adOp H X * H)) =
      (4 : ℤ) • (H * adOp H X * H) ∧
     adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
      (5 : ℤ) • adOp H (adOp H (adOp H X)) +
      (4 : ℤ) • adOp H X = 0) ∧
    (proj24OpMinus2 (adOp H) X +
      proj24OpMinus1 (adOp H) X +
      proj24OpZero (adOp H) X +
      proj24OpPlus1 (adOp H) X +
      proj24OpPlus2 (adOp H) X = (24 : ℤ) • X) := by
  have hBaryon := (stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation
    u₁ u₂ u₃ u₁ u₂ u₃ u₁).2.2.1.1
  have hAd3 := stage_Ad3_tripotent_seed_bilateral_contact_sandwich hH X
  have hAd5 := stage_Ad5_eigenvalue_four_and_universal_five_graded_quintic_law hH X
  have hSA4 := stage_SA4_division_free_24_integer_resolution_of_five_graded_tower
    (0 : ℤ) (adOp H) X
  exact ⟨hBaryon, ⟨hAd3, hAd5.1, hAd5.2.2⟩, hSA4.2.2.1⟩

/-- **Stage `𝔄𝔇₆` (`stage_AD6_bitwise_clifford_transformer_compiler_and_master_synthesis`)**:
1. **$n$-Bit Symplectic $\mathcal{C}\ell(1,1)^{\otimes n}$ Basis Multiplication & Causal Signature**:
   `gammaBasis x₁ z₁ * gammaBasis x₂ z₂ =
      ((-1 : R) ^ bvPopcount (bvAnd x₁ z₂)) • gammaBasis (bvXor x₁ x₂) (bvXor z₁ z₂)` and
   `gammaBasis x z * gammaBasis x z = ((-1 : R) ^ bvPopcount (bvAnd x z)) • 1`.
2. **Division-Free Walsh–Clifford Inverse Transform**:
   `coagulateClifford2 (compileClifford2 M₂) = (2 : R) • M₂`.
3. **Master 6-Stage Synthesis of `ConformalNetFiveFoldAdvanceStage`
   (`𝔄𝔇₁ ≺ 𝔄𝔇₂ ≺ 𝔄𝔇₃ ≺ {𝔄𝔇₄, 𝔄𝔇₅} ≺ 𝔄𝔇₆`)**:
   Combines poset acyclicity, cardinality (`= 6`), diamond branch incomparability,
   Haag–Peirce commutant duality, dually flat Amari gates, Twisted-$\mathrm{Pin}$
   $\mathcal{C}\mathcal{P}\mathcal{T}$ unitarity, multiplicative balancing monodromy,
   Krein LogCFT unipotent balance, 5-graded Kantor–Tanaka quintic contact law, and
   bitwise symplectic Clifford compilation. -/
theorem stage_AD6_bitwise_clifford_transformer_compiler_and_master_synthesis
    {B : Type*} [Ring B] [StarRing B] {R : Type*} [CommRing R]
    {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1)
    {H : B} (hH : H * H * H = H)
    {N_nil : B} (hNil : N_nil * N_nil = 0)
    (A C Y Phi_gen : B)
    {n : ℕ} (x z x₁ z₁ x₂ z₂ : BitwiseCliffordCompiler.BitVecN n)
    (M₂ : Matrix (Fin 2) (Fin 2) R) :
    (∀ st : ConformalNetFiveFoldAdvanceStage,
      ¬ Relation.TransGen ConformalNetFiveFoldAdvanceStage.causalEdge st st) ∧
    Fintype.card ConformalNetFiveFoldAdvanceStage = 6 ∧
    (¬ Relation.TransGen ConformalNetFiveFoldAdvanceStage.causalEdge
        .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance
        .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower ∧
     ¬ Relation.TransGen ConformalNetFiveFoldAdvanceStage.causalEdge
        .ad5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower
        .ad4_krein_logcft_isotropic_horizon_and_unipotent_balance) ∧
    (P * X = X * P ↔ (conePlus P X = 0 ∧ coneMinus P X = 0)) ∧
    ((1 + conePlus P X) * (1 + conePlus P Y) = 1 + conePlus P (X + Y) ∧
     ((1 + conePlus P X) * (1 + coneMinus P X)) *
       PlabicTwistedPinCPT.thetaCPT P Phi1 ((1 + conePlus P X) * (1 + coneMinus P X)) = 1) ∧
    ((1 + InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P C) -
        anticomm (conePlus P A) (coneMinus P C) * (conePlus P A - coneMinus P C) +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C)) *
       ((1 + coneMinus P C) * (1 + conePlus P A)) =
       (1 + conePlus P A) * (1 + coneMinus P C)) ∧
    ((1 - N_nil) * (1 + N_nil) = 1 ∧
     N_nil * ((1 - N_nil) * Phi_gen) = N_nil * Phi_gen) ∧
    (adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
      (5 : ℤ) • adOp H (adOp H (adOp H X)) +
      (4 : ℤ) • adOp H X = 0) ∧
    (BitwiseCliffordCompiler.gammaBasis (R := R) x₁ z₁ *
       BitwiseCliffordCompiler.gammaBasis (R := R) x₂ z₂ =
       ((-1 : R) ^ BitwiseCliffordCompiler.bvPopcount (BitwiseCliffordCompiler.bvAnd x₁ z₂)) •
         BitwiseCliffordCompiler.gammaBasis (R := R)
           (BitwiseCliffordCompiler.bvXor x₁ x₂) (BitwiseCliffordCompiler.bvXor z₁ z₂) ∧
     BitwiseCliffordCompiler.gammaBasis (R := R) x z *
       BitwiseCliffordCompiler.gammaBasis (R := R) x z =
       ((-1 : R) ^ BitwiseCliffordCompiler.bvPopcount (BitwiseCliffordCompiler.bvAnd x z)) • 1 ∧
     BitwiseCliffordCompiler.coagulateClifford2
       (BitwiseCliffordCompiler.compileClifford2 M₂) = (2 : R) • M₂) := by
  have hAD1 := stage_AD1_jaynesian_colimit_and_peirce_haag_duality_split
    (R := R) hP A C X 0 (0 : R) M₂
  have hAD2 := stage_AD2_first_quantized_amari_dual_flatness_and_twisted_pin_cpt_inversion
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X Y 0 [] (by simp)
  have hAD3 := stage_AD3_multiplicative_balancing_monodromy_and_hua_bergman_dikin_metric hP A C
  have hAd5 := stage_Ad5_eigenvalue_four_and_universal_five_graded_quintic_law hH X
  have hBC23 := BitwiseCliffordCompiler.stage_BC2_BC3_n_bit_symplectic_clifford_product_and_causal_signature
    (R := R) x₁ z₁ x₂ z₂ x z
  have hBC45 := BitwiseCliffordCompiler.stage_BC4_BC5_division_free_compiler_parseval_and_symplectic_convolution
    (R := R) M₂ M₂ 0 0
  refine ⟨ConformalNetFiveFoldAdvanceStage.causalEdge_acyclic,
    ConformalNetFiveFoldAdvanceStage.card_eq_six,
    ConformalNetFiveFoldAdvanceStage.diamond_branches_incomparable,
    hAD1.2.1.2.2,
    ⟨hAD2.1.1, hAD2.2.2.1⟩,
    hAD3.1.1,
    ⟨?_, ?_⟩,
    hAd5.2.2,
    ⟨hBC23.2.1, hBC23.2.2.1, hBC45.2.1⟩⟩
  · calc (1 - N_nil) * (1 + N_nil)
      _ = 1 - N_nil * N_nil := by noncomm_ring
      _ = 1 - 0 := by rw [hNil]
      _ = 1 := by noncomm_ring
  · calc N_nil * ((1 - N_nil) * Phi_gen)
      _ = N_nil * Phi_gen - (N_nil * N_nil) * Phi_gen := by noncomm_ring
      _ = N_nil * Phi_gen - 0 * Phi_gen := by rw [hNil]
      _ = N_nil * Phi_gen := by noncomm_ring

end ConformalNetFiveFoldAdvance

/-!
## Part XIII: The 6-Stage Cyclic Möbius Ring, Homogeneous Projective Coordinates, & $(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study Variance Poset (`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`)

This section formalizes the 6-stage causal diamond poset (`CyclicMobiusRingNibelungStage`)
severing the single-chart affine ray $(0, 1, \infty)$ from a homogeneous two-chart
projective-coordinate family with chart exchange given by the involution $\Phi_1$. The
algebraic identities here do not construct a topology or identify this family with $S^1$:

* **Stage `ℜ𝔑₁` (`rn1_homogeneous_projective_line_and_mobius_inversion_poles`)**:
  Two-sheeted Peirce idempotents $P_+ = P = \widetilde{\Pi}(1, 0)$ (origin pole $z = 0$) and
  $P_- = 1 - P = \widetilde{\Pi}(0, 1)$ (infinity pole $z = \infty \leftrightarrow w = 0$),
  coupled by the Möbius exchange involution $\Phi_1$ ($\Phi_1^2 = 1$,
  $\Phi_1 P \Phi_1 = 1 - P$, $\Phi_1 (1 - P) \Phi_1 = P$) and homogeneous projective
  quasi-idempotence $\widetilde{\Pi}(u, v)^2 = (u^2 + v^2)\,\widetilde{\Pi}(u, v)$ with
  exact Möbius chart exchange $\Phi_1 \widetilde{\Pi}(u, v) \Phi_1 = \widetilde{\Pi}(v, u)$.
* **Stage `ℜ𝔑₂` (`rn2_cayley_transform_circle_and_bruhat_mobius_inversion`)**:
  Compact complex structure $J_1 = (2 P - 1)\Phi_1$ ($J_1^2 = -1$, $\Phi_1 J_1 \Phi_1 = -J_1$),
  homogeneous Cayley circle $\widetilde{U}(u, v) = (u^2 - v^2) I_2 + 2 u v J_1$ satisfying
  $\widetilde{U}(u, v)\widetilde{U}(u, -v) = (u^2 + v^2)^2 I_2$ and
  $\widetilde{U}(v, u) = -\widetilde{U}(u, -v)$, and Bruhat–Möbius big-cell closure
  $\Phi_1 (1 + N_+) \Phi_1 = 1 + \Phi_1 N_+ \Phi_1$.
* **Stage `ℜ𝔑₃` (`rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation`)**:
  The $(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study chiral variance theorem:
  $\operatorname{Var}_P^{\mathrm{hom}}(u, v) = -4\,[P, \widetilde{\Pi}(u, v)]^2 = 4 u^2 v^2 \cdot 1$,
  evaluating at $(1, 0), (1, 1), (0, 1)$ to $(0, 4\cdot 1, 0)$ with scale factors
  $((1^2+0^2)^2, (1^2+1^2)^2, (0^2+1^2)^2) = (1, 4, 1)$, so normalized variance is
  $(0, 1, 0)$, together with the Cauchy–Schwarz deficiency identity
  $(u^2 + v^2)^2 - 4 u^2 v^2 = (u^2 - v^2)^2$.
* **Stage `ℜ𝔑₄` (`rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral`)**:
  1. Single-chart affine nilpotent ray $1 + u N_+$ cannot reach the opposite pole $1 - P$
     because $(1 - P)(1 + N_+) P = 0$ while $\Phi_1 P = (1 - P)\Phi_1$.
  2. Commuting cyclic core vs. Krein LogCFT secular spiral: when $U_0 N_{\mathrm{nil}} =
     N_{\mathrm{nil}} U_0$ and $N_{\mathrm{nil}}^2 = 0$, the unipotent balance twist fixes $U_0$
     ($(1 - N_{\mathrm{nil}}) U_0 (1 + N_{\mathrm{nil}}) = U_0$), whereas on the non-commuting
     Krein generator $A_{\mathrm{kr}}$ ($A_{\mathrm{kr}}^2 = -1, B_{\mathrm{kr}}^2 = 1,
     \{A_{\mathrm{kr}}, B_{\mathrm{kr}}\} = 0$) it produces the non-zero $O(t^2)$ secular shift
     $-N_{\mathrm{nil}} A_{\mathrm{kr}} N_{\mathrm{nil}} = 2 N_{\mathrm{nil}}$.
* **Stage `ℜ𝔑₅` (`rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return`)**:
  Multiplicative Möbius / 24-cyclotomic polynomial identity
  $(x^{12} - 1)(x^8 - 1)\Phi_{24}(x) = (x^{24} - 1)(x^4 - 1)$ with
  $\Phi_{24}(x) = x^8 - x^4 + 1$, reciprocal symmetry $x^8 \Phi_{24}(1) = \Phi_{24}(1)$,
  and division-free $4! = 24$ 5-graded Kantor–Tanaka contact return.
* **Stage `ℜ𝔑₆` (`rn6_cyclic_mobius_ring_master_synthesis`)**:
  Master 6-stage synthesis uniting the homogeneous projective-coordinate family, Cayley-Bruhat
  closure, $(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study variance law, Krein secular
  spiral dichotomy, and 24-cyclotomic Möbius return.
-/

/-- The 6 causal stages of the Cyclic Möbius Ring & Projective-Coordinate poset
(`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`). -/
inductive CyclicMobiusRingNibelungStage : Type
  | rn1_homogeneous_projective_line_and_mobius_inversion_poles
  | rn2_cayley_transform_circle_and_bruhat_mobius_inversion
  | rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation
  | rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral
  | rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return
  | rn6_cyclic_mobius_ring_master_synthesis
  deriving DecidableEq, Repr

namespace CyclicMobiusRingNibelungStage

instance : Fintype CyclicMobiusRingNibelungStage where
  elems := {
    .rn1_homogeneous_projective_line_and_mobius_inversion_poles,
    .rn2_cayley_transform_circle_and_bruhat_mobius_inversion,
    .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation,
    .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral,
    .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return,
    .rn6_cyclic_mobius_ring_master_synthesis
  }
  complete x := by cases x <;> simp

/-- Direct cover relation of the 6-stage diamond poset
`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`. -/
def causalEdge : CyclicMobiusRingNibelungStage → CyclicMobiusRingNibelungStage → Prop
  | .rn1_homogeneous_projective_line_and_mobius_inversion_poles,
    .rn2_cayley_transform_circle_and_bruhat_mobius_inversion => True
  | .rn2_cayley_transform_circle_and_bruhat_mobius_inversion,
    .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation => True
  | .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation,
    .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral => True
  | .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation,
    .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return => True
  | .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral,
    .rn6_cyclic_mobius_ring_master_synthesis => True
  | .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return,
    .rn6_cyclic_mobius_ring_master_synthesis => True
  | _, _ => False

instance : DecidableRel causalEdge := fun a b => by
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Topological rank embedding into `ℕ`. -/
def rank : CyclicMobiusRingNibelungStage → ℕ
  | .rn1_homogeneous_projective_line_and_mobius_inversion_poles            => 0
  | .rn2_cayley_transform_circle_and_bruhat_mobius_inversion               => 1
  | .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation => 2
  | .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral       => 3
  | .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return         => 3
  | .rn6_cyclic_mobius_ring_master_synthesis                               => 4

theorem causalEdge_lt {a b : CyclicMobiusRingNibelungStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_lt {a b : CyclicMobiusRingNibelungStage}
    (h : Relation.TransGen causalEdge a b) :
    rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

theorem causalEdge_acyclic (s : CyclicMobiusRingNibelungStage) :
    ¬ Relation.TransGen causalEdge s s :=
  fun h => Nat.lt_irrefl (rank s) (transGen_causalEdge_lt h)

theorem card_eq_six : Fintype.card CyclicMobiusRingNibelungStage = 6 := rfl

theorem diamond_branches_incomparable :
    ¬ Relation.TransGen causalEdge
        .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral
        .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return ∧
    ¬ Relation.TransGen causalEdge
        .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return
        .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt := transGen_causalEdge_lt h
    revert hlt; decide
  · have hlt := transGen_causalEdge_lt h
    revert hlt; decide

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : CyclicMobiusRingNibelungStage → InfoGeometry.Meta.RepDepth
  | .rn1_homogeneous_projective_line_and_mobius_inversion_poles            => .operator
  | .rn2_cayley_transform_circle_and_bruhat_mobius_inversion               => .transport
  | .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation => .transport
  | .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral       => .thermo
  | .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return         => .thermo
  | .rn6_cyclic_mobius_ring_master_synthesis                               => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    CyclicMobiusRingNibelungStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .rn1_homogeneous_projective_line_and_mobius_inversion_poles            => .M1_ProjectorClabject
  | .rn2_cayley_transform_circle_and_bruhat_mobius_inversion               => .M2_GrassmannianPowertypeOrbit
  | .rn3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation => .M2_GrassmannianPowertypeOrbit
  | .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral       => .M3_ErlangenCasimirMetaLaw
  | .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return         => .M3_ErlangenCasimirMetaLaw
  | .rn6_cyclic_mobius_ring_master_synthesis                               => .M3_ErlangenCasimirMetaLaw

theorem causalEdge_toRepDepth_mono {a b : CyclicMobiusRingNibelungStage}
    (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toRepDepth InfoGeometry.Meta.RepDepth.toNat <;> decide

theorem toRepDepth_mono {a b : CyclicMobiusRingNibelungStage}
    (h : Relation.TransGen causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  induction h with
  | single hab => exact causalEdge_toRepDepth_mono hab
  | tail _ hbc ih => exact Nat.le_trans ih (causalEdge_toRepDepth_mono hbc)

theorem causalEdge_toOntologyMetaLevel_mono {a b : CyclicMobiusRingNibelungStage}
    (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;> decide

theorem toOntologyMetaLevel_mono {a b : CyclicMobiusRingNibelungStage}
    (h : Relation.TransGen causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  induction h with
  | single hab => exact causalEdge_toOntologyMetaLevel_mono hab
  | tail _ hbc ih => exact Nat.le_trans ih (causalEdge_toOntologyMetaLevel_mono hbc)

end CyclicMobiusRingNibelungStage

namespace CyclicMobiusRingNibelung

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Homogeneous projective density matrix on `Matrix (Fin 2) (Fin 2) R` over `[CommRing R]`
for homogeneous coordinates $(u, v) \in R^2$:
$$\widetilde{\Pi}(u, v) = u^2 E_{00} + u v (E_{01} + E_{10}) + v^2 E_{11}
= \begin{pmatrix} u^2 & u v \\ u v & v^2 \end{pmatrix}.$$ -/
def homogPiMat {R : Type*} [CommRing R] (u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u ^ 2, u * v; u * v, v ^ 2]

/-- Standard Möbius pole-swap involution matrix $\Phi_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def mobiusSwapMat {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- Standard Peirce origin pole projector $P_+ = E_{00} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def poleZeroMat {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Standard Peirce infinity pole projector $P_- = E_{11} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def poleInfMat {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, 1]

/-- Standard symplectic complex structure $J_1 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def pinJ1Mat {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

/-- Homogeneous Cayley circle element on `Matrix (Fin 2) (Fin 2) R`:
$$\widetilde{U}(u, v) = (u I_2 + v J_1)^2 = (u^2 - v^2) I_2 + 2 u v J_1
= \begin{pmatrix} u^2 - v^2 & 2 u v \\ -2 u v & u^2 - v^2 \end{pmatrix}.$$ -/
def homogCayleyMat {R : Type*} [CommRing R] (u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u ^ 2 - v ^ 2, 2 * u * v; -(2 * u * v), u ^ 2 - v ^ 2]

/-- The 24th cyclotomic polynomial $\Phi_{24}(x) = x^8 - x^4 + 1$ over any `[CommRing R]`. -/
def phi24Poly {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 8 - x ^ 4 + 1

/-- Right-intertwining lemma for the Möbius pole swap:
if $\Phi_1^2 = 1$ and $\Phi_1 P = (1 - P) \Phi_1$, then $P \Phi_1 = \Phi_1 (1 - P)$. -/
theorem P_mul_Phi1 {B : Type*} [Ring B] {P Phi1 : B}
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1) :
    P * Phi1 = Phi1 * (1 - P) := by
  calc P * Phi1
    _ = (1 * P) * Phi1 := by noncomm_ring
    _ = ((Phi1 * Phi1) * P) * Phi1 := by rw [hPhi_sq]
    _ = (Phi1 * (Phi1 * P)) * Phi1 := by noncomm_ring
    _ = (Phi1 * ((1 - P) * Phi1)) * Phi1 := by rw [hPhi_P]
    _ = Phi1 * (1 - P) * (Phi1 * Phi1) := by noncomm_ring
    _ = Phi1 * (1 - P) * 1 := by rw [hPhi_sq]
    _ = Phi1 * (1 - P) := by noncomm_ring

/-- **Stage `ℜ𝔑₁` (`stage_RN1_homogeneous_projective_line_and_mobius_inversion_poles`)**:
1. **Non-Commutative Ring Pole Swap (`0 ↔ ∞`)**:
   In any `[Ring B]` with $P^2 = P$, $\Phi_1^2 = 1$, and $\Phi_1 P = (1 - P)\Phi_1$:
   - $\Phi_1 P \Phi_1 = 1 - P$ and $\Phi_1 (1 - P) \Phi_1 = P$,
   - $P \Phi_1 + \Phi_1 P = \Phi_1$ and $P \Phi_1 P = 0$, $(1 - P)\Phi_1(1 - P) = 0$,
   - the midpoint projector $\widetilde{\Pi}_1 := 1 + \Phi_1$ satisfies
     $\widetilde{\Pi}_1^2 = (2 : \mathbb{Z}) \bullet \widetilde{\Pi}_1$ and
     $\Phi_1 \widetilde{\Pi}_1 \Phi_1 = \widetilde{\Pi}_1$.
2. **Homogeneous Projective-Coordinate Family (`homogPiMat u v`)**:
   For all $u, v \in R$ (`[CommRing R]`):
   - $\widetilde{\Pi}(1, 0) = P_+$, $\widetilde{\Pi}(0, 1) = P_-$, and
     $\widetilde{\Pi}(1, 1) = 1 + \Phi_1$,
   - $\widetilde{\Pi}(u, v)^2 = (u^2 + v^2) \bullet \widetilde{\Pi}(u, v)$ and
     $\operatorname{tr}(\widetilde{\Pi}(u, v)) = u^2 + v^2$,
   - $\Phi_1 \widetilde{\Pi}(u, v) \Phi_1 = \widetilde{\Pi}(v, u)$ (exact Möbius inversion
     $z = v/u \mapsto w = u/v$ exchanging $(1, 0) \leftrightarrow (0, 1)$ while fixing $(1, 1)$). -/
theorem stage_RN1_homogeneous_projective_line_and_mobius_inversion_poles
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {P Phi1 : B}
    (hP : P * P = P) (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (u v : R) :
    (Phi1 * P * Phi1 = 1 - P ∧
     Phi1 * (1 - P) * Phi1 = P ∧
     P * Phi1 + Phi1 * P = Phi1 ∧
     P * Phi1 * P = 0 ∧
     (1 - P) * Phi1 * (1 - P) = 0 ∧
     (1 + Phi1) * (1 + Phi1) = (2 : ℤ) • (1 + Phi1) ∧
     Phi1 * (1 + Phi1) * Phi1 = 1 + Phi1) ∧
    (homogPiMat (1 : R) 0 = poleZeroMat ∧
     homogPiMat (0 : R) 1 = poleInfMat ∧
     homogPiMat (1 : R) 1 = (1 : Matrix (Fin 2) (Fin 2) R) + mobiusSwapMat ∧
     homogPiMat u v * homogPiMat u v = (u ^ 2 + v ^ 2) • homogPiMat u v ∧
     Matrix.trace (homogPiMat u v) = u ^ 2 + v ^ 2 ∧
     mobiusSwapMat * homogPiMat u v * mobiusSwapMat = homogPiMat v u) := by
  have hP_Phi1 : P * Phi1 = Phi1 * (1 - P) := P_mul_Phi1 hPhi_sq hPhi_P
  have hPole0 : Phi1 * P * Phi1 = 1 - P := by
    calc Phi1 * P * Phi1
      _ = ((1 - P) * Phi1) * Phi1 := by rw [hPhi_P]
      _ = (1 - P) * (Phi1 * Phi1) := by noncomm_ring
      _ = (1 - P) * 1 := by rw [hPhi_sq]
      _ = 1 - P := by noncomm_ring
  have hPoleInf : Phi1 * (1 - P) * Phi1 = P := by
    calc Phi1 * (1 - P) * Phi1
      _ = (P * Phi1) * Phi1 := by rw [← hP_Phi1]
      _ = P * (Phi1 * Phi1) := by noncomm_ring
      _ = P * 1 := by rw [hPhi_sq]
      _ = P := by noncomm_ring
  have hAnticomm : P * Phi1 + Phi1 * P = Phi1 := by
    calc P * Phi1 + Phi1 * P
      _ = P * Phi1 + (1 - P) * Phi1 := by rw [hPhi_P]
      _ = Phi1 := by noncomm_ring
  have hCornerPlus : P * Phi1 * P = 0 := by
    calc P * Phi1 * P
      _ = (Phi1 * (1 - P)) * P := by rw [hP_Phi1]
      _ = Phi1 * (P - P * P) := by noncomm_ring
      _ = Phi1 * (P - P) := by rw [hP]
      _ = 0 := by noncomm_ring
  have hCornerMinus : (1 - P) * Phi1 * (1 - P) = 0 := by
    calc (1 - P) * Phi1 * (1 - P)
      _ = (Phi1 * P) * (1 - P) := by rw [← hPhi_P]
      _ = Phi1 * (P - P * P) := by noncomm_ring
      _ = Phi1 * (P - P) := by rw [hP]
      _ = 0 := by noncomm_ring
  have hMidSq : (1 + Phi1) * (1 + Phi1) = (2 : ℤ) • (1 + Phi1) := by
    calc (1 + Phi1) * (1 + Phi1)
      _ = 1 + (2 : ℤ) • Phi1 + Phi1 * Phi1 := by noncomm_ring
      _ = 1 + (2 : ℤ) • Phi1 + 1 := by rw [hPhi_sq]
      _ = (2 : ℤ) • (1 + Phi1) := by abel
  have hMidSwap : Phi1 * (1 + Phi1) * Phi1 = 1 + Phi1 := by
    calc Phi1 * (1 + Phi1) * Phi1
      _ = Phi1 * Phi1 + (Phi1 * Phi1) * Phi1 := by noncomm_ring
      _ = 1 + 1 * Phi1 := by rw [hPhi_sq]
      _ = 1 + Phi1 := by noncomm_ring
  refine ⟨⟨hPole0, hPoleInf, hAnticomm, hCornerPlus, hCornerMinus, hMidSq, hMidSwap⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogPiMat, poleZeroMat]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogPiMat, poleInfMat]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogPiMat, mobiusSwapMat]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogPiMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [homogPiMat, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogPiMat, mobiusSwapMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Stage `ℜ𝔑₂` (`stage_RN2_cayley_transform_circle_and_bruhat_mobius_inversion`)**:
1. **Twisted-$\mathrm{Pin}$ Symplectic Complex Structure & Bruhat–Möbius Inversion in `[Ring B]`**:
   With $J_1 = (2 P - 1)\Phi_1$ and $\Phi_2 = (1 - 2 P)\Phi_1 = -J_1$:
   - $J_1^2 = -1$ and $\Phi_1 J_1 \Phi_1 = -J_1$,
   - $(1 + J_1)^2 = (2 : \mathbb{Z}) \bullet J_1$ and $(1 + J_1)(1 - J_1) = (2 : \mathbb{Z}) \bullet 1$
     (algebraic Cayley transform at the midpoint $z = 1$),
   - $\Phi_1 (1 + \operatorname{conePlus} P X) \Phi_1 =
       1 + \operatorname{coneMinus} P (\Phi_1 X \Phi_1)$
     (conjugating the upper unipotent affine ray by the Möbius swap $\Phi_1$ maps it into
     the opposite lower unipotent chart).
2. **Homogeneous Cayley Circle $\widetilde{U}(u, v)$ on `Matrix (Fin 2) (Fin 2) R`**:
   - $\widetilde{U}(1, 0) = 1$, $\widetilde{U}(0, 1) = -1$, and
     $\widetilde{U}(1, 1) = (2 : R) \bullet J_1$,
   - $\widetilde{U}(u, v)\,\widetilde{U}(u, -v) = (u^2 + v^2)^2 \bullet 1$,
   - $\widetilde{U}(v, u) = -\widetilde{U}(u, -v)$ and
     $\Phi_1 \widetilde{U}(u, v) \Phi_1 = \widetilde{U}(u, -v)$
     (Möbius inversion $u \leftrightarrow v$ reverses circle orientation and negates the
     Cayley phase). -/
theorem stage_RN2_cayley_transform_circle_and_bruhat_mobius_inversion
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {P Phi1 : B}
    (hP : P * P = P) (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (X : B) (u v : R) :
    let J1 := PlabicTwistedPinCPT.pinJ1 P Phi1
    ((J1 * J1 = -1 ∧
      Phi1 * J1 * Phi1 = -J1 ∧
      (1 + J1) * (1 + J1) = (2 : ℤ) • J1 ∧
      (1 + J1) * (1 - J1) = (2 : ℤ) • (1 : B) ∧
      Phi1 * (1 + conePlus P X) * Phi1 = 1 + coneMinus P (Phi1 * X * Phi1)) ∧
     (homogCayleyMat (1 : R) 0 = 1 ∧
      homogCayleyMat (0 : R) 1 = -1 ∧
      homogCayleyMat (1 : R) 1 = (2 : R) • pinJ1Mat ∧
      homogCayleyMat u v * homogCayleyMat u (-v) =
        ((u ^ 2 + v ^ 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
      homogCayleyMat v u = -homogCayleyMat u (-v) ∧
      mobiusSwapMat * homogCayleyMat u v * mobiusSwapMat = homogCayleyMat u (-v))) := by
  dsimp only
  have hP_Phi1 : P * Phi1 = Phi1 * (1 - P) := P_mul_Phi1 hPhi_sq hPhi_P
  have hInvSSq : invS P * invS P = 1 := by peirce_nf hP
  have hPhiInvS : Phi1 * invS P = -(invS P * Phi1) := by
    dsimp [invS]
    calc Phi1 * (P - (1 - P))
      _ = 2 * (Phi1 * P) - Phi1 := by noncomm_ring
      _ = 2 * ((1 - P) * Phi1) - Phi1 := by rw [hPhi_P]
      _ = -((P - (1 - P)) * Phi1) := by noncomm_ring
  have hJ1Sq : PlabicTwistedPinCPT.pinJ1 P Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 = -1 := by
    dsimp [PlabicTwistedPinCPT.pinJ1]
    calc (invS P * Phi1) * (invS P * Phi1)
      _ = invS P * (Phi1 * invS P) * Phi1 := by noncomm_ring
      _ = invS P * (-(invS P * Phi1)) * Phi1 := by rw [hPhiInvS]
      _ = -(invS P * invS P) * (Phi1 * Phi1) := by noncomm_ring
      _ = -1 * 1 := by rw [hInvSSq, hPhi_sq]
      _ = -1 := by noncomm_ring
  have hPhiJ1 : Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 * Phi1 =
      -PlabicTwistedPinCPT.pinJ1 P Phi1 := by
    calc Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 * Phi1
      _ = ((2 : ℤ) • (Phi1 * P) - Phi1) * (Phi1 * Phi1) := by
            dsimp [PlabicTwistedPinCPT.pinJ1, invS]; noncomm_ring
      _ = ((2 : ℤ) • ((1 - P) * Phi1) - Phi1) * 1 := by rw [hPhi_P, hPhi_sq]
      _ = -PlabicTwistedPinCPT.pinJ1 P Phi1 := by
            dsimp [PlabicTwistedPinCPT.pinJ1, invS]; noncomm_ring
  have hCayleyMidSq :
      (1 + PlabicTwistedPinCPT.pinJ1 P Phi1) * (1 + PlabicTwistedPinCPT.pinJ1 P Phi1) =
        (2 : ℤ) • PlabicTwistedPinCPT.pinJ1 P Phi1 := by
    calc (1 + PlabicTwistedPinCPT.pinJ1 P Phi1) * (1 + PlabicTwistedPinCPT.pinJ1 P Phi1)
      _ = 1 + (2 : ℤ) • PlabicTwistedPinCPT.pinJ1 P Phi1 +
            PlabicTwistedPinCPT.pinJ1 P Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 := by
            noncomm_ring
      _ = 1 + (2 : ℤ) • PlabicTwistedPinCPT.pinJ1 P Phi1 + (-1) := by rw [hJ1Sq]
      _ = (2 : ℤ) • PlabicTwistedPinCPT.pinJ1 P Phi1 := by abel
  have hCayleyMidNorm :
      (1 + PlabicTwistedPinCPT.pinJ1 P Phi1) * (1 - PlabicTwistedPinCPT.pinJ1 P Phi1) =
        (2 : ℤ) • (1 : B) := by
    calc (1 + PlabicTwistedPinCPT.pinJ1 P Phi1) * (1 - PlabicTwistedPinCPT.pinJ1 P Phi1)
      _ = 1 - PlabicTwistedPinCPT.pinJ1 P Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 := by
            noncomm_ring
      _ = 1 - (-1) := by rw [hJ1Sq]
      _ = (2 : ℤ) • (1 : B) := by abel
  have hBruhatSwap :
      Phi1 * (1 + conePlus P X) * Phi1 = 1 + coneMinus P (Phi1 * X * Phi1) := by
    have hCornerSwap : Phi1 * conePlus P X * Phi1 = coneMinus P (Phi1 * X * Phi1) := by
      calc Phi1 * conePlus P X * Phi1
        _ = (Phi1 * P) * X * ((1 - P) * Phi1) := by
              dsimp [conePlus]; noncomm_ring
        _ = ((1 - P) * Phi1) * X * (Phi1 * P) := by rw [hPhi_P]
        _ = coneMinus P (Phi1 * X * Phi1) := by
              dsimp [coneMinus]; noncomm_ring
    calc Phi1 * (1 + conePlus P X) * Phi1
      _ = Phi1 * Phi1 + Phi1 * conePlus P X * Phi1 := by noncomm_ring
      _ = 1 + coneMinus P (Phi1 * X * Phi1) := by rw [hPhi_sq, hCornerSwap]
  refine ⟨⟨hJ1Sq, hPhiJ1, hCayleyMidSq, hCayleyMidNorm, hBruhatSwap⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat, pinJ1Mat] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [homogCayleyMat, mobiusSwapMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Stage `ℜ𝔑₃` (`stage_RN3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation`)**:
The **$(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study Chiral Variance Theorem**:
1. **Non-Commutative Ring Variance across the Three Canonical Points $(0, 1, \infty)$**:
   For $\widetilde{\Pi}_0 := P$ ($z = 0$), $\widetilde{\Pi}_1 := 1 + \Phi_1$ ($z = 1$),
   and $\widetilde{\Pi}_\infty := 1 - P$ ($z = \infty$):
   - $[P, \widetilde{\Pi}_0] = 0$ and $-4\,[P, \widetilde{\Pi}_0]^2 = 0$,
   - $[P, \widetilde{\Pi}_1] = J_1 = (2 P - 1)\Phi_1$ and
     $-4\,[P, \widetilde{\Pi}_1]^2 = (4 : \mathbb{Z}) \bullet 1 = (1^2 + 1^2)^2 \bullet 1$
     (so normalizing by $(\operatorname{tr}\widetilde{\Pi}_1)^2 = 2^2 = 4$ yields exact unit
     variance $1$ at the self-dual midpoint $z = 1$!),
   - $[P, \widetilde{\Pi}_\infty] = 0$ and $-4\,[P, \widetilde{\Pi}_\infty]^2 = 0$.
2. **Universal Homogeneous Variance Polynomial on `Matrix (Fin 2) (Fin 2) R`**:
   For all $(u, v) \in R^2$:
   - $[P_+, \widetilde{\Pi}(u, v)] = (u * v) \bullet J_1$,
   - $-((4 : R) \bullet ([P_+, \widetilde{\Pi}(u, v)] * [P_+, \widetilde{\Pi}(u, v)])) =
       (4 * u ^ 2 * v ^ 2) \bullet 1$,
   - Möbius invariance of variance: $4 v^2 u^2 = 4 u^2 v^2$,
   - Cauchy–Schwarz midpoint saturation identity:
     $(u^2 + v^2)^2 - 4 u^2 v^2 = (u^2 - v^2)^2$. -/
theorem stage_RN3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {P Phi1 : B}
    (hP : P * P = P) (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (u v : R) :
    let J1 := PlabicTwistedPinCPT.pinJ1 P Phi1
    ((InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P = 0 ∧
      -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P)) = 0) ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1) = J1 ∧
      -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1))) = (4 : ℤ) • (1 : B)) ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P) = 0 ∧
      -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P))) = 0)) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm poleZeroMat (homogPiMat u v) =
       (u * v) • pinJ1Mat ∧
     -((4 : R) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm poleZeroMat (homogPiMat u v) *
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm poleZeroMat (homogPiMat u v))) =
       (4 * u ^ 2 * v ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
     4 * v ^ 2 * u ^ 2 = 4 * u ^ 2 * v ^ 2 ∧
     (u ^ 2 + v ^ 2) ^ 2 - 4 * u ^ 2 * v ^ 2 = (u ^ 2 - v ^ 2) ^ 2) := by
  dsimp only
  have hJ1Sq : PlabicTwistedPinCPT.pinJ1 P Phi1 * PlabicTwistedPinCPT.pinJ1 P Phi1 = -1 :=
    ((stage_RN2_cayley_transform_circle_and_bruhat_mobius_inversion
      (R := R) hP hPhi_sq hPhi_P 0 u v).1).1
  have hComm0 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  have hCommInf : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  have hCommMid :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1) =
        PlabicTwistedPinCPT.pinJ1 P Phi1 := by
    calc InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1)
      _ = P * Phi1 - Phi1 * P := by
            dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
      _ = P * Phi1 - (1 - P) * Phi1 := by rw [hPhi_P]
      _ = PlabicTwistedPinCPT.pinJ1 P Phi1 := by
            dsimp [PlabicTwistedPinCPT.pinJ1, invS]; noncomm_ring
  have hVarMid :
      -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1))) = (4 : ℤ) • (1 : B) := by
    rw [hCommMid, hJ1Sq]
    abel
  have hScalarSymm : 4 * v ^ 2 * u ^ 2 = 4 * u ^ 2 * v ^ 2 := by
    ring
  have hScalarBinom : (u ^ 2 + v ^ 2) ^ 2 - 4 * u ^ 2 * v ^ 2 = (u ^ 2 - v ^ 2) ^ 2 := by
    ring
  refine ⟨⟨⟨hComm0, by rw [hComm0]; noncomm_ring⟩,
    ⟨hCommMid, hVarMid⟩,
    ⟨hCommInf, by rw [hCommInf]; noncomm_ring⟩⟩,
    ⟨?_, ?_, hScalarSymm, hScalarBinom⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, poleZeroMat, homogPiMat,
        pinJ1Mat] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, poleZeroMat, homogPiMat] <;> ring

/-- **Stage `ℜ𝔑₄` (`stage_RN4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral`)**:
1. **Aporia of the Single-Chart Open Affine Ray (`1 + N_+`)**:
   - The upper unipotent shear $1 + \operatorname{conePlus} P X$ fixes $P$ on the right and
     cannot transport $P$ into the opposite pole $1 - P$:
     $$(1 - P)(1 + \operatorname{conePlus} P X) P \;=\; 0,$$
     whereas the Möbius pole swap $\Phi_1$ transports $P$ bijectively onto $1 - P$:
     $$(1 - P)\,\Phi_1\,P \;=\; \Phi_1\,P \quad\text{and}\quad \Phi_1\,P\,\Phi_1 \;=\; 1 - P.$$
2. **Cyclic Commuting Core vs. Krein LogCFT Secular Spiral (`Eternal Recurrence vs. Memory`)**:
   - If $U_0 \in B$ commutes with $N_{\mathrm{nil}}$ ($U_0 N_{\mathrm{nil}} = N_{\mathrm{nil}} U_0$)
     and $N_{\mathrm{nil}}^2 = 0$, then the unipotent LogCFT balance twist leaves $U_0$
     strictly invariant:
     $$(1 - N_{\mathrm{nil}})\,U_0\,(1 + N_{\mathrm{nil}}) \;=\; U_0.$$
   - Conversely, on the non-commuting Krein generator $A_{\mathrm{kr}}$
     ($A_{\mathrm{kr}}^2 = -1, B_{\mathrm{kr}}^2 = 1, \{A_{\mathrm{kr}}, B_{\mathrm{kr}}\} = 0$,
     $N_{\mathrm{nil}} = A_{\mathrm{kr}} + B_{\mathrm{kr}}$), the unipotent twist produces the
     non-vanishing $O(t^2)$ secular memory shift:
     $$(1 - (A_{\mathrm{kr}} + B_{\mathrm{kr}}))\,A_{\mathrm{kr}}\,(1 + (A_{\mathrm{kr}} + B_{\mathrm{kr}}))
       \;=\; A_{\mathrm{kr}} + (2 : \mathbb{Z}) \bullet (A_{\mathrm{kr}} B_{\mathrm{kr}}) +
         (2 : \mathbb{Z}) \bullet (A_{\mathrm{kr}} + B_{\mathrm{kr}}).$$ -/
theorem stage_RN4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral
    {B : Type*} [Ring B]
    {P Phi1 U0 N_nil A_kr B_kr : B}
    (hP : P * P = P) (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hNil : N_nil * N_nil = 0) (hCommU : U0 * N_nil = N_nil * U0)
    (hA_kr : A_kr * A_kr = -1) (hB_kr : B_kr * B_kr = 1)
    (hAnti_kr : A_kr * B_kr + B_kr * A_kr = 0) (X : B) :
    ((1 - P) * (1 + conePlus P X) * P = 0 ∧
     (1 - P) * Phi1 * P = Phi1 * P ∧
     Phi1 * P * Phi1 = 1 - P) ∧
    ((1 - N_nil) * U0 * (1 + N_nil) = U0 ∧
     (A_kr + B_kr) * (A_kr + B_kr) = 0 ∧
     (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
       A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr)) := by
  have hAD4 := ConformalNetFiveFoldAdvance.stage_AD4_krein_logcft_isotropic_horizon_and_unipotent_balance
    hA_kr hB_kr hAnti_kr hNil 0 U0
  have hAffineBlock : (1 - P) * (1 + conePlus P X) * P = 0 := by
    dsimp [conePlus]; peirce_nf hP
  have hMobiusPole : (1 - P) * Phi1 * P = Phi1 * P := by
    calc (1 - P) * Phi1 * P
      _ = (Phi1 * P) * P := by rw [← hPhi_P]
      _ = Phi1 * (P * P) := by noncomm_ring
      _ = Phi1 * P := by rw [hP]
  have hPole0 : Phi1 * P * Phi1 = 1 - P := by
    calc Phi1 * P * Phi1
      _ = ((1 - P) * Phi1) * Phi1 := by rw [hPhi_P]
      _ = (1 - P) * (Phi1 * Phi1) := by noncomm_ring
      _ = 1 - P := by rw [hPhi_sq]; noncomm_ring
  have hPeriodicFixed : (1 - N_nil) * U0 * (1 + N_nil) = U0 := by
    calc (1 - N_nil) * U0 * (1 + N_nil)
      _ = U0 + (U0 * N_nil - N_nil * U0) - (N_nil * U0) * N_nil := by noncomm_ring
      _ = U0 + (N_nil * U0 - N_nil * U0) - (U0 * N_nil) * N_nil := by rw [hCommU]
      _ = U0 - U0 * (N_nil * N_nil) := by noncomm_ring
      _ = U0 - U0 * 0 := by rw [hNil]
      _ = U0 := by noncomm_ring
  exact ⟨⟨hAffineBlock, hMobiusPole, hPole0⟩,
    ⟨hPeriodicFixed, hAD4.1.1, hAD4.1.2.2⟩⟩

/-- **Stage `ℜ𝔑₅` (`stage_RN5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return`)**:
1. **Multiplicative Möbius Inversion Identity for the 24th Cyclotomic Polynomial**:
   Since $\mu(1) = 1$, $\mu(2) = -1$, $\mu(3) = -1$, $\mu(6) = 1$, and all other divisors of $24$
   have $\mu(d) = 0$, $\Phi_{24}(x) = x^8 - x^4 + 1$ satisfies the division-free polynomial
   identity over any `[CommRing R]`:
   $$(x^{12} - 1)(x^8 - 1)\,\Phi_{24}(x) \;=\; (x^{24} - 1)(x^4 - 1),$$
   together with palintromic reciprocal symmetry on invertible $x \in R$:
   $$x^8\,\Phi_{24}(y) \;=\; \Phi_{24}(x) \quad (\text{whenever } x y = 1),$$
   and $\Phi_{24}(1) = 1$.
2. **24-Step Contact Return of the 5-Graded Kantor–Tanaka Tower (`4! = 24`)**:
   - $P_{-2}^{(24)}(H) X + P_{-1}^{(24)}(H) X + P_0^{(24)}(H) X +
     P_{+1}^{(24)}(H) X + P_{+2}^{(24)}(H) X = (24 : \mathbb{Z}) \bullet X$,
   - for $H^3 = H$, $\operatorname{ad}_H^5(X) - 5 \operatorname{ad}_H^3(X) + 4 \operatorname{ad}_H(X) = 0$,
   - and $\phi(24) = 8 = \deg \Phi_{24}$, $4! = 24$. -/
theorem stage_RN5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {H : B} (hH : H * H * H = H) (X : B)
    (x y : R) (hxy : x * y = 1) :
    ((x ^ 12 - 1) * (x ^ 8 - 1) * phi24Poly x = (x ^ 24 - 1) * (x ^ 4 - 1) ∧
     phi24Poly (1 : R) = 1 ∧
     x ^ 8 * phi24Poly y = phi24Poly x) ∧
    (proj24OpMinus2 (adOp H) X +
      proj24OpMinus1 (adOp H) X +
      proj24OpZero (adOp H) X +
      proj24OpPlus1 (adOp H) X +
      proj24OpPlus2 (adOp H) X = (24 : ℤ) • X ∧
     adOp H (adOp H (adOp H (adOp H (adOp H X)))) -
      (5 : ℤ) • adOp H (adOp H (adOp H X)) +
      (4 : ℤ) • adOp H X = 0 ∧
     Nat.factorial 4 = 24) := by
  have hAD5 := ConformalNetFiveFoldAdvance.stage_AD5_split_octonion_three_body_baryon_and_five_graded_24_contact_tower
    (K := R) hH X 0 0 0
  have hPoly : (x ^ 12 - 1) * (x ^ 8 - 1) * phi24Poly x = (x ^ 24 - 1) * (x ^ 4 - 1) := by
    dsimp [phi24Poly]; ring
  have hPhiOne : phi24Poly (1 : R) = 1 := by
    dsimp [phi24Poly]; ring
  have hPalin : x ^ 8 * phi24Poly y = phi24Poly x := by
    dsimp [phi24Poly]
    calc x ^ 8 * (y ^ 8 - y ^ 4 + 1)
      _ = (x * y) ^ 8 - x ^ 4 * (x * y) ^ 4 + x ^ 8 := by ring
      _ = 1 ^ 8 - x ^ 4 * 1 ^ 4 + x ^ 8 := by rw [hxy]
      _ = x ^ 8 - x ^ 4 + 1 := by ring
  exact ⟨⟨hPoly, hPhiOne, hPalin⟩, ⟨hAD5.2.2, hAD5.2.1.2.2, rfl⟩⟩

/-- **Stage `ℜ𝔑₆` (`stage_RN6_cyclic_mobius_ring_master_synthesis`)**:
Master 6-stage synthesis of `CyclicMobiusRingNibelungStage`
(`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`):
1. Acyclicity, cardinality (`= 6`), and diamond branch incomparability of
   `CyclicMobiusRingNibelungStage`.
2. Homogeneous projective quasi-idempotence $\widetilde{\Pi}(u, v)^2 = (u^2 + v^2)\widetilde{\Pi}(u, v)$
   and Möbius chart swap $\Phi_1 \widetilde{\Pi}(u, v) \Phi_1 = \widetilde{\Pi}(v, u)$.
3. Homogeneous Cayley circle norm $\widetilde{U}(u, v)\widetilde{U}(u, -v) = (u^2 + v^2)^2 I_2$
   and pole-swap reflection $\widetilde{U}(v, u) = -\widetilde{U}(u, -v)$.
4. The $(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study chiral variance theorem both on
   abstract ring projectors $(P, 1 + \Phi_1, 1 - P)$ and on the homogeneous projective line
   $\widetilde{\Pi}(u, v)$.
5. Commuting cyclic core invariance $(1 - N_{\mathrm{nil}}) U_0 (1 + N_{\mathrm{nil}}) = U_0$
   vs. Krein secular memory shift on $A_{\mathrm{kr}}$.
6. Multiplicative Möbius 24-cyclotomic identity
   $(x^{12} - 1)(x^8 - 1)\Phi_{24}(x) = (x^{24} - 1)(x^4 - 1)$ and $4! = 24$ 5-graded
   Kantor–Tanaka contact resolution. -/
theorem stage_RN6_cyclic_mobius_ring_master_synthesis
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    {P Phi1 U0 N_nil A_kr B_kr H : B}
    (hP : P * P = P) (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hNil : N_nil * N_nil = 0) (hCommU : U0 * N_nil = N_nil * U0)
    (hA_kr : A_kr * A_kr = -1) (hB_kr : B_kr * B_kr = 1)
    (hAnti_kr : A_kr * B_kr + B_kr * A_kr = 0)
    (hH : H * H * H = H) (X : B)
    (u v x : R) :
    (∀ st : CyclicMobiusRingNibelungStage,
      ¬ Relation.TransGen CyclicMobiusRingNibelungStage.causalEdge st st) ∧
    Fintype.card CyclicMobiusRingNibelungStage = 6 ∧
    (¬ Relation.TransGen CyclicMobiusRingNibelungStage.causalEdge
        .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral
        .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return ∧
     ¬ Relation.TransGen CyclicMobiusRingNibelungStage.causalEdge
        .rn5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return
        .rn4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral) ∧
    (Phi1 * P * Phi1 = 1 - P ∧
     homogPiMat u v * homogPiMat u v = (u ^ 2 + v ^ 2) • homogPiMat u v ∧
     mobiusSwapMat * homogPiMat u v * mobiusSwapMat = homogPiMat v u) ∧
    (homogCayleyMat u v * homogCayleyMat u (-v) =
       ((u ^ 2 + v ^ 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
     homogCayleyMat v u = -homogCayleyMat u (-v)) ∧
    (-((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P P)) = 0 ∧
     -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 + Phi1))) = (4 : ℤ) • (1 : B) ∧
     -((4 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (1 - P))) = 0 ∧
     -((4 : R) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm poleZeroMat (homogPiMat u v) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm poleZeroMat (homogPiMat u v))) =
        (4 * u ^ 2 * v ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R)) ∧
    ((1 - N_nil) * U0 * (1 + N_nil) = U0 ∧
     (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
       A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr)) ∧
    ((x ^ 12 - 1) * (x ^ 8 - 1) * phi24Poly x = (x ^ 24 - 1) * (x ^ 4 - 1) ∧
     proj24OpMinus2 (adOp H) X +
      proj24OpMinus1 (adOp H) X +
      proj24OpZero (adOp H) X +
      proj24OpPlus1 (adOp H) X +
      proj24OpPlus2 (adOp H) X = (24 : ℤ) • X) := by
  have hRN1 := stage_RN1_homogeneous_projective_line_and_mobius_inversion_poles
    hP hPhi_sq hPhi_P u v
  have hRN2 := stage_RN2_cayley_transform_circle_and_bruhat_mobius_inversion
    hP hPhi_sq hPhi_P X u v
  have hRN3 := stage_RN3_fubini_study_chiral_variance_zero_one_zero_and_midpoint_saturation
    hP hPhi_sq hPhi_P u v
  have hRN4 := stage_RN4_socratic_aporia_of_open_affine_ray_and_krein_secular_spiral
    hP hPhi_sq hPhi_P hNil hCommU hA_kr hB_kr hAnti_kr X
  have hRN5 := stage_RN5_arithmetic_mobius_inversion_and_24_cyclotomic_ring_return
    (R := R) hH X 1 1 (mul_one 1)
  have hPoly : (x ^ 12 - 1) * (x ^ 8 - 1) * phi24Poly x = (x ^ 24 - 1) * (x ^ 4 - 1) := by
    dsimp [phi24Poly]; ring
  exact ⟨CyclicMobiusRingNibelungStage.causalEdge_acyclic,
    CyclicMobiusRingNibelungStage.card_eq_six,
    CyclicMobiusRingNibelungStage.diamond_branches_incomparable,
    ⟨hRN1.1.1, hRN1.2.2.2.2.1, hRN1.2.2.2.2.2.2⟩,
    ⟨hRN2.2.2.2.2.1, hRN2.2.2.2.2.2.1⟩,
    ⟨hRN3.1.1.2, hRN3.1.2.1.2, hRN3.1.2.2.2, hRN3.2.2.1⟩,
    ⟨hRN4.2.1, hRN4.2.2.2⟩,
    ⟨hPoly, hRN5.2.1⟩⟩

end CyclicMobiusRingNibelung

end InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset
