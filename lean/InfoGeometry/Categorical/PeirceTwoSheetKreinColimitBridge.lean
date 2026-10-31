/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.TwoSheetKreinStageSystem
import InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset

/-!
# Peirce Two-Sheet Krein Filtered-Colimit Bridge

This module closes the architectural gap between:
1. The associative-ring Peirce spine (`InfoGeometry.OperatorAlgebra.PeirceSpine` and
   `InfoGeometry.OperatorAlgebra.PeirceDefectBridge`), which defines the corner split
   `(P, 1 - P)`, the off-diagonal cones `(conePlus P A, coneMinus P C)`, the symmetric
   generator `genPhi P A C`, the horizon metric `genV P A C`, and the two Peirce cycles
   `(qgtPlus P A C, qgtMinus P A C)`; and
2. The categorical two-sheet Krein filtered colimit (`TwoSheetKreinFilteredColimit` and
   `TwoSheetKreinStageSystem`), together with the concrete `2 × 2` Pauli sheet matrix
   carrier `HestenesKreinFinite` (`SheetMatrix`).

## Main Results

1. **General Associative-Ring Peirce Exchange Law (`genPhi_conj_P_eq_compl`)**:
   In any associative ring `B` with idempotent `P` (`P * P = P`) and off-diagonal pair
   `(A, C)` whose horizon metric is unital (`genV P A C = 1`), the symmetric generator
   `η = genPhi P A C` is an involution (`η * η = 1`) whose conjugation exchanges the
   two Peirce corners (`η * P * η = 1 - P` and `η * (1 - P) * η = P`), while the two
   Peirce cycles evaluate directly to the corners (`qgtPlus P A C = P` and
   `qgtMinus P A C = 1 - P`).
2. **Categorical Filtered-Colimit Instantiation for Any `ℝ`-Algebra Peirce Spine**:
   For any `ℝ`-algebra `B` (`[Ring B] [Algebra ℝ B]`) equipped with `P, A, C : B`
   satisfying `P * P = P` and `genV P A C = 1`, the constant stage functor
   `peirceStageFunctor B : ℕ ⥤ ModuleCat ℝ` carries natural transformations
   `peirceKreinStage P A C` (`x ↦ η * x * η`), `peircePlusStage P` (`x ↦ P * x`), and
   `peirceMinusStage P` (`x ↦ (1 - P) * x`) whose induced colimit endomorphisms satisfy:
   - `colimitEnd (peirceKreinStage P A C) * colimitEnd (peirceKreinStage P A C) = LinearMap.id`,
   - `colimitEnd (peirceKreinStage P A C) * colimitEnd (peircePlusStage P) * colimitEnd (peirceKreinStage P A C) = colimitEnd (peirceMinusStage P)`.
3. **Exact Specialization to the Native Hestenes–Krein Two-Sheet Carrier (`SheetMatrix`)**:
   On `SheetMatrix`, setting `P = fPlus` and `A = C = fundamentalSymmetry` satisfies
   `fPlus * fPlus = fPlus`, `genPhi fPlus fundamentalSymmetry fundamentalSymmetry = fundamentalSymmetry`,
   `qgtPlus fPlus fundamentalSymmetry fundamentalSymmetry = fPlus`,
   `qgtMinus fPlus fundamentalSymmetry fundamentalSymmetry = fMinus`,
   `genV fPlus fundamentalSymmetry fundamentalSymmetry = 1`, and instantiates both
   `PeirceDefectBridge.evenGrade_idempotencyDefect_sub_idempotencyDefect_evenGrade`
   and `TwoSheetKreinStageSystem`.
-/

noncomputable section

namespace InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Krein.HestenesKreinFinite
open InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
open InfoGeometry.Categorical.TwoSheetKreinStageSystem

/-! ### 1. General Associative-Ring Peirce Exchange under Unital Horizon Metric (`genV P A C = 1`) -/

section AssociativeRing

variable {B : Type*} [Ring B] {P A C : B}

/-- The square of `genPhi P A C` is `genV P A C` for any idempotent `P` (`P * P = P`). -/
theorem genPhi_mul_self_eq_genV (hP : P * P = P) :
    genPhi P A C * genPhi P A C = genV P A C :=
  (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1

/-- When `genV P A C = 1` for an idempotent `P` (`P * P = P`), the symmetric off-diagonal
generator `genPhi P A C` is an involution (`genPhi P A C * genPhi P A C = 1`). -/
theorem genPhi_sq_eq_one_of_genV_eq_one (hP : P * P = P) (hV : genV P A C = 1) :
    genPhi P A C * genPhi P A C = 1 :=
  ((krein_involution_peirce_exchange_equivalence (A := A) (C := C) (η := P) hP).1 hV).1

/-- When `genV P A C = 1` for an idempotent `P` (`P * P = P`), the upper and lower
Peirce cycles coincide with `P` and `1 - P`:
`qgtPlus P A C = P` and `qgtMinus P A C = 1 - P`. -/
theorem qgt_cycles_eq_peirce_corners_of_genV_eq_one
    (hP : P * P = P) (hV : genV P A C = 1) :
    qgtPlus P A C = P ∧ qgtMinus P A C = 1 - P := by
  rcases (krein_involution_peirce_exchange_equivalence (A := A) (C := C) (η := P) hP).1 hV with
    ⟨_, hPlus, hMinus, _, _⟩
  exact ⟨hPlus, hMinus⟩

/-- Conjugating `P` by `genPhi P A C` yields `qgtMinus P A C`, and conjugating `1 - P`
by `genPhi P A C` yields `qgtPlus P A C`. -/
theorem genPhi_conj_P_eq_qgt (hP : P * P = P) (A C : B) :
    genPhi P A C * P * genPhi P A C = qgtMinus P A C ∧
    genPhi P A C * (1 - P) * genPhi P A C = qgtPlus P A C := by
  constructor <;> peirce_nf hP

/-- When `genV P A C = 1`, conjugating `P` by `genPhi P A C` exchanges the two
complementary Peirce corners `P` and `1 - P`. -/
theorem genPhi_conj_P_eq_compl (hP : P * P = P) (hV : genV P A C = 1) :
    genPhi P A C * P * genPhi P A C = 1 - P ∧
    genPhi P A C * (1 - P) * genPhi P A C = P := by
  rcases (krein_involution_peirce_exchange_equivalence (A := A) (C := C) (η := P) hP).1 hV with
    ⟨_, _, _, hConjP, hConjCompl⟩
  exact ⟨hConjP, hConjCompl⟩

/-- Conversely, in any associative ring `B`, if `P` is idempotent (`P * P = P`) and `η : B`
is an involution (`η * η = 1`) whose conjugation exchanges `P` with `1 - P`
(`η * P * η = 1 - P`), then `η` is purely odd with respect to `P`:
1. `conePlus P η = P * η` and `coneMinus P η = (1 - P) * η`,
2. `genPhi P η η = η`,
3. `genV P η η = 1`,
4. `qgtPlus P η η = P` and `qgtMinus P η η = 1 - P`. -/
theorem genPhi_eq_self_of_involution_exchanging_peirce
    {η : B} (hP : P * P = P) (hη : η * η = 1) (hEx : η * P * η = 1 - P) :
    conePlus P η = P * η ∧
    coneMinus P η = (1 - P) * η ∧
    genPhi P η η = η ∧
    genV P η η = 1 ∧
    qgtPlus P η η = P ∧
    qgtMinus P η η = 1 - P :=
  (krein_involution_peirce_exchange_equivalence (A := η) (C := η) hP).2 hη hEx

end AssociativeRing

/-! ### 2. Categorical Filtered-Colimit Transport for Any `ℝ`-Algebra Peirce Spine -/

section RealAlgebraColimit

variable (B : Type) [Ring B] [Algebra ℝ B]

/-- The constant stage functor `ℕ ⥤ ModuleCat ℝ` associated to an `ℝ`-algebra `B`. -/
abbrev peirceStageFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ B)

variable {B}

/-- Lifts an `ℝ`-linear endomorphism of `B` to a natural transformation on `peirceStageFunctor B`. -/
def peirceConstantNatTrans (T : B →ₗ[ℝ] B) :
    peirceStageFunctor B ⟶ peirceStageFunctor B :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom T)
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      rfl)

/-- Two-sided conjugation `x ↦ genPhi P A C * x * genPhi P A C` as an `ℝ`-linear endomorphism of `B`. -/
def peirceKreinAction (P A C : B) : B →ₗ[ℝ] B :=
  (LinearMap.mulLeft ℝ (genPhi P A C)).comp (LinearMap.mulRight ℝ (genPhi P A C))

/-- Left multiplication `x ↦ P * x` by the upper Peirce idempotent `P`. -/
def peircePlusAction (P : B) : B →ₗ[ℝ] B :=
  LinearMap.mulLeft ℝ P

/-- Left multiplication `x ↦ (1 - P) * x` by the complementary lower Peirce idempotent `1 - P`. -/
def peirceMinusAction (P : B) : B →ₗ[ℝ] B :=
  LinearMap.mulLeft ℝ (1 - P)

/-- Stage natural transformation for `peirceKreinAction P A C`. -/
def peirceKreinStage (P A C : B) : peirceStageFunctor B ⟶ peirceStageFunctor B :=
  peirceConstantNatTrans (peirceKreinAction P A C)

/-- Stage natural transformation for `peircePlusAction P`. -/
def peircePlusStage (P : B) : peirceStageFunctor B ⟶ peirceStageFunctor B :=
  peirceConstantNatTrans (peircePlusAction P)

/-- Stage natural transformation for `peirceMinusAction P`. -/
def peirceMinusStage (P : B) : peirceStageFunctor B ⟶ peirceStageFunctor B :=
  peirceConstantNatTrans (peirceMinusAction P)

theorem peirceKreinAction_square {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) :
    (peirceKreinAction P A C).comp (peirceKreinAction P A C) = LinearMap.id := by
  have hPhiSq := genPhi_sq_eq_one_of_genV_eq_one hP hV
  ext x
  change genPhi P A C * (genPhi P A C * (x * genPhi P A C) * genPhi P A C) = x
  calc
    genPhi P A C * (genPhi P A C * (x * genPhi P A C) * genPhi P A C) =
      (genPhi P A C * genPhi P A C) * x * (genPhi P A C * genPhi P A C) := by
        noncomm_ring
    _ = x := by rw [hPhiSq, one_mul, mul_one]

theorem peirceKreinStage_square {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) :
    peirceKreinStage P A C ≫ peirceKreinStage P A C = 𝟙 (peirceStageFunctor B) := by
  ext n x
  simpa [peirceKreinStage, peirceConstantNatTrans, ModuleCat.comp_apply] using
    congrArg (fun f => f x) (peirceKreinAction_square hP hV)

theorem peirceKreinStage_exchanges_plus {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) :
    peirceKreinStage P A C ≫ peircePlusStage P ≫ peirceKreinStage P A C =
      peirceMinusStage P := by
  have hPhiSq := genPhi_sq_eq_one_of_genV_eq_one hP hV
  have hConj := (genPhi_conj_P_eq_compl hP hV).1
  ext n x
  dsimp [peirceStageFunctor] at x ⊢
  change genPhi P A C *
      (P * (genPhi P A C * ((x : B) * genPhi P A C)) * genPhi P A C) =
      (1 - P) * (x : B)
  calc
    genPhi P A C * (P * (genPhi P A C * ((x : B) * genPhi P A C)) * genPhi P A C) =
      (genPhi P A C * P * genPhi P A C) * (x : B) * (genPhi P A C * genPhi P A C) := by
        noncomm_ring
    _ = (1 - P) * (x : B) := by rw [hConj, hPhiSq, mul_one]

/-- Filtered-colimit Krein involution and two-sheet corner exchange induced by any
Peirce spine `(P, A, C)` with `P * P = P` and `genV P A C = 1`. -/
theorem peirceColimit_krein_involutive_and_sheet_exchange
    {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) :
    colimitEnd (peirceKreinStage P A C) * colimitEnd (peirceKreinStage P A C) =
      LinearMap.id ∧
    colimitEnd (peirceKreinStage P A C) * colimitEnd (peircePlusStage P) *
      colimitEnd (peirceKreinStage P A C) = colimitEnd (peirceMinusStage P) :=
  ⟨colimitEnd_involutive (peirceKreinStage P A C) (peirceKreinStage_square hP hV),
   colimitEnd_exchange (peirceKreinStage P A C) (peircePlusStage P) (peirceMinusStage P)
     (peirceKreinStage_exchanges_plus hP hV)⟩

end RealAlgebraColimit

/-! ### 3. Exact Unification with `HestenesKreinFinite` (`SheetMatrix`) and `PeirceDefectBridge` -/

/-- On `SheetMatrix`, the Hestenes–Krein projectors `fPlus` and `fMinus` satisfy
`1 - fPlus = fMinus`. -/
theorem one_sub_fPlus_eq_fMinus : (1 : SheetMatrix) - fPlus = fMinus := by
  rw [← fPlus_add_fMinus, add_sub_cancel_left]

/-- On `SheetMatrix`, the Peirce off-diagonal cones of `fundamentalSymmetry` with respect
to `fPlus` sum to `fundamentalSymmetry`:
`genPhi fPlus fundamentalSymmetry fundamentalSymmetry = fundamentalSymmetry`. -/
theorem sheetMatrix_genPhi_eq_fundamentalSymmetry :
    genPhi fPlus fundamentalSymmetry fundamentalSymmetry = fundamentalSymmetry := by
  unfold genPhi conePlus coneMinus
  rw [one_sub_fPlus_eq_fMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fPlus, fMinus, fundamentalSymmetry, uPlus, uMinus, sheetFlip,
      sheetIdentity, sheetParity] <;>
    norm_num [div_eq_mul_inv]

/-- On `SheetMatrix`, the upper and lower Peirce cycles of `fundamentalSymmetry`
evaluate to `fPlus` and `fMinus`, and the horizon metric `genV` evaluates to `1`. -/
theorem sheetMatrix_qgt_and_genV_identities :
    qgtPlus fPlus fundamentalSymmetry fundamentalSymmetry = fPlus ∧
    qgtMinus fPlus fundamentalSymmetry fundamentalSymmetry = fMinus ∧
    genV fPlus fundamentalSymmetry fundamentalSymmetry = (1 : SheetMatrix) := by
  have hPhi := sheetMatrix_genPhi_eq_fundamentalSymmetry
  have hV : genV fPlus fundamentalSymmetry fundamentalSymmetry = (1 : SheetMatrix) := by
    rw [← genPhi_mul_self_eq_genV fPlus_idempotent,
      hPhi, fundamentalSymmetry_sq]
  rcases qgt_cycles_eq_peirce_corners_of_genV_eq_one fPlus_idempotent hV with ⟨hPlus, hMinus⟩
  rw [one_sub_fPlus_eq_fMinus] at hMinus
  exact ⟨hPlus, hMinus, hV⟩

/-- **Master Bridge Theorem Connecting `PeirceDefectBridge`, `HestenesKreinFinite`, and
`TwoSheetKreinFilteredColimit` on `SheetMatrix`**:
1. `genPhi fPlus fundamentalSymmetry fundamentalSymmetry = fundamentalSymmetry` and
   `genV fPlus fundamentalSymmetry fundamentalSymmetry = 1`;
2. `qgtPlus fPlus fundamentalSymmetry fundamentalSymmetry = fPlus` and
   `qgtMinus fPlus fundamentalSymmetry fundamentalSymmetry = fMinus`;
3. For every `X : SheetMatrix`, the pinching idempotency defect law holds:
   `evenGrade fPlus (idempotencyDefect X) - idempotencyDefect (evenGrade fPlus X) = genV fPlus X X`;
4. The induced filtered-colimit endomorphisms on `Carrier (peirceStageFunctor SheetMatrix)`
   satisfy `colimitEnd (peirceKreinStage ...)² = id` and exchange `peircePlusStage fPlus`
   with `peirceMinusStage fPlus`. -/
theorem hestenes_krein_peirce_colimit_master_bridge (X : SheetMatrix) :
    genPhi fPlus fundamentalSymmetry fundamentalSymmetry = fundamentalSymmetry ∧
    genV fPlus fundamentalSymmetry fundamentalSymmetry = (1 : SheetMatrix) ∧
    qgtPlus fPlus fundamentalSymmetry fundamentalSymmetry = fPlus ∧
    qgtMinus fPlus fundamentalSymmetry fundamentalSymmetry = fMinus ∧
    evenGrade fPlus (idempotencyDefect X) - idempotencyDefect (evenGrade fPlus X) =
      genV fPlus X X ∧
    colimitEnd (peirceKreinStage fPlus fundamentalSymmetry fundamentalSymmetry) *
      colimitEnd (peirceKreinStage fPlus fundamentalSymmetry fundamentalSymmetry) =
      LinearMap.id ∧
    colimitEnd (peirceKreinStage fPlus fundamentalSymmetry fundamentalSymmetry) *
      colimitEnd (peircePlusStage fPlus) *
      colimitEnd (peirceKreinStage fPlus fundamentalSymmetry fundamentalSymmetry) =
      colimitEnd (peirceMinusStage fPlus) := by
  rcases sheetMatrix_qgt_and_genV_identities with ⟨hPlus, hMinus, hV⟩
  rcases peirceColimit_krein_involutive_and_sheet_exchange fPlus_idempotent hV with
    ⟨hColInv, hColEx⟩
  exact ⟨sheetMatrix_genPhi_eq_fundamentalSymmetry,
         hV, hPlus, hMinus,
         even_idempotencyDefect_sub fPlus X fPlus_idempotent,
         hColInv, hColEx⟩

/-! ### 4. Exact Unification with the Non-Constant Dyadic `Cl(1,1)` Tensor Tower
(`Cl11HestenesKreinTwoSheetBridge` and `Cl11TwoSheetPeirceCorners`) -/

section Cl11DyadicTowerBridge

open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open InfoGeometry.Canonical.Cl11TwoSheetPeirceCorners

/-- At every stage `n : ℕ` of the non-constant dyadic `Cl(1,1)` tensor tower `Stage n`,
the complementary projector `1 - fPlusElem n` equals `fMinusElem n`. -/
@[simp] theorem one_sub_fPlusElem_eq_fMinusElem (n : ℕ) :
    (1 : Stage n) - fPlusElem n = fMinusElem n := by
  rw [← fPlusElem_add_fMinusElem n, add_sub_cancel_left]

/-- At every stage `n : ℕ` of the dyadic `Cl(1,1)` tensor tower `Stage n`, the four
corners defined in `Cl11TwoSheetPeirceCorners` (`plusPlus`, `plusMinus`, `minusPlus`,
`minusMinus`) coincide identically with the `PeirceSpine` corners
(`peirce11`, `conePlus`, `coneMinus`, `peirce00`) of `fPlusElem n`. -/
theorem cl11_two_sheet_corners_eq_peirce_spine (n : ℕ) (a : Stage n) :
    plusPlus n a = peirce11 (fPlusElem n) a ∧
    plusMinus n a = conePlus (fPlusElem n) a ∧
    minusPlus n a = coneMinus (fPlusElem n) a ∧
    minusMinus n a = peirce00 (fPlusElem n) a := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold plusMinus conePlus
    rw [one_sub_fPlusElem_eq_fMinusElem]
  · unfold minusPlus coneMinus
    rw [one_sub_fPlusElem_eq_fMinusElem]
  · unfold minusMinus peirce00
    rw [one_sub_fPlusElem_eq_fMinusElem]

/-- **Dyadic `Cl(1,1)` Tensor Tower Peirce–Krein Master Bridge**:
At every stage `n : ℕ` of the non-constant dyadic tensor tower `Stage n` and for every
stage operator `a : Stage n`:
1. The stage Krein involution `etaElem n` decomposes into the off-diagonal Peirce cones
   `conePlus (fPlusElem n) (etaElem n) = fPlusElem n * etaElem n` and
   `coneMinus (fPlusElem n) (etaElem n) = fMinusElem n * etaElem n`, with
   `genPhi (fPlusElem n) (etaElem n) (etaElem n) = etaElem n`;
2. The stage horizon metric is unital:
   `genV (fPlusElem n) (etaElem n) (etaElem n) = 1`;
3. The upper and lower Peirce cycles evaluate to the stage sheet projectors:
   `qgtPlus (fPlusElem n) (etaElem n) (etaElem n) = fPlusElem n` and
   `qgtMinus (fPlusElem n) (etaElem n) (etaElem n) = fMinusElem n`;
4. The pinching idempotency defect law holds at stage `n`:
   `evenGrade (fPlusElem n) (idempotencyDefect a) - idempotencyDefect (evenGrade (fPlusElem n) a) = genV (fPlusElem n) a a`. -/
theorem cl11_dyadic_tower_peirce_krein_bridge (n : ℕ) (a : Stage n) :
    conePlus (fPlusElem n) (etaElem n) = fPlusElem n * etaElem n ∧
    coneMinus (fPlusElem n) (etaElem n) = fMinusElem n * etaElem n ∧
    genPhi (fPlusElem n) (etaElem n) (etaElem n) = etaElem n ∧
    genV (fPlusElem n) (etaElem n) (etaElem n) = (1 : Stage n) ∧
    qgtPlus (fPlusElem n) (etaElem n) (etaElem n) = fPlusElem n ∧
    qgtMinus (fPlusElem n) (etaElem n) (etaElem n) = fMinusElem n ∧
    evenGrade (fPlusElem n) (idempotencyDefect a) -
        idempotencyDefect (evenGrade (fPlusElem n) a) =
      genV (fPlusElem n) a a := by
  have hEx : etaElem n * fPlusElem n * etaElem n = (1 : Stage n) - fPlusElem n := by
    rw [etaElem_fPlusElem_etaElem n, one_sub_fPlusElem_eq_fMinusElem n]
  rcases genPhi_eq_self_of_involution_exchanging_peirce
      (fPlusElem_idempotent n) (etaElem_sq n) hEx with
    ⟨hConeP, hConeM, hPhi, hV, hQPlus, hQMinus⟩
  rw [one_sub_fPlusElem_eq_fMinusElem n] at hConeM hQMinus
  exact ⟨hConeP, hConeM, hPhi, hV, hQPlus, hQMinus,
         even_idempotencyDefect_sub (fPlusElem n) a (fPlusElem_idempotent n)⟩

end Cl11DyadicTowerBridge

end InfoGeometry.Categorical.PeirceTwoSheetKreinColimitBridge
