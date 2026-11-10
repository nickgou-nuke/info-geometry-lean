/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Canonical Mathematical Theory (Cross-Poset Grand Unification Poset U₀ ≺ ... ≺ U₆)
-- ARCHITECTURAL ROLE: Exact Ring-Homomorphic Intertwiners Linking Cartan-Hestenes, Ternary Cantor, Bhoja-Krasnov, Xambó Wessel-Riesz, Bimetric Peirce Sheet Geometry, Aharonov Two-State Holonomy & Quantum Cheshire Cat, and Navier-Madelung Chiral Vortex Anomaly Posets
-- EPISTEMIC STATUS: 100% Constructive Proof (Zero Sorrys, Zero Axioms, Zero Wrapper Forgery)
-- DEPENDENCIES: CartanHestenesPinSkolemNoetherGaloisPoset, TernaryCantorCliffordCyclotomicBraidedPinPoset, BhojaKrasnovSpinorPolyformMixedParabolicPoset, XamboWesselRieszSkewDerivationOlindeRodriguesPoset, AharonovTwoStateWeakValueModularShiftHolonomyPoset, BimetricSheetGeometry, TwoStateModularShiftGeometry, NavierMadelungChiralVortexAnomalyPoset
-- [END HEADER]

import InfoGeometry.Canonical.CartanHestenesPinSkolemNoetherGaloisPoset
import InfoGeometry.Canonical.TernaryCantorCliffordCyclotomicBraidedPinPoset
import InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset
import InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset
import InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateModularShiftGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.NavierMadelungChiralVortexAnomalyPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset

/-!
# Grand Unification Poset: Cartan–Hestenes, Ternary Cantor, Bhoja–Krasnov, Xambó Wessel–Riesz, Bimetric Peirce Sheet Geometry & Aharonov Two-State Holonomy ($\mathcal{U}_0 \prec \dots \prec \mathcal{U}_5$)

Constructs the explicit ring-homomorphic intertwiners and cross-poset unification theorems uniting
the canonical Geometric Algebra, Non-Commutative Bimetric Peirce Sheet, and Quantum Two-State
Operator posets over an arbitrary non-commutative associative ring `[Ring B]`.

## Causal Unification Poset Architecture:
- **Archetype $\mathcal{U}_0$ (`archetype_U0_cartan_bhoja_krasnov_witt_polyform_intertwiner`)**:
  Constructs the mutual inverse ring bijections `mat2ToFin2` and `fin2ToMat2` between
  `BhojaKrasnov.Mat2 B` and `Matrix (Fin 2) (Fin 2) B` over any `[Ring B]`, proving multiplicative homomorphism and
  exact dictionary alignment between Bhoja–Krasnov’s matrix units (`E01`, `E10`, `E00`, `E11`,
  `Ex`, `Ez`), Cartan–Hestenes’ split-space operators (`wittNullU`, `wittNullV`,
  `cartanVacIdempotent`, `splitGenE`, `kreinGradeEta`), and Cantor’s multiparticle branch
  projectors (`cantorCreateU`, `cantorAnnihilateV`, `cantorBranchVac`, `cantorBranchOcc`).
- **Archetype $\mathcal{U}_1$ (`archetype_U1_xambo_wessel_riesz_to_witt_polyform_and_ternary_closure`)**:
  Over `[Ring B]`, intertwines `BhojaKrasnov.Mat2 B` and `Xambo.Mat2 B`, proving that Xambó’s Riesz
  contraction and wedge (`rieszDot`, `rieszWedge`) acting on the Cartan/Bhoja–Krasnov vacuum
  projector `E00` and 1-form `E10` realize the polyform interior/exterior operations on the spinor
  ideal, and proving that Xambó’s `parityHat`-odd 1-vectors are closed under the non-commutative
  ternary product $U V W$ ($\widehat{U V W} = -(U V W)$).
- **Archetype $\mathcal{U}_2$ (`archetype_U2_xambo_versor_reflection_to_hestenes_boost_and_pin_reflection`)**:
  Over `[Ring B]`, proves that Hestenes hyperbolic boost rotors $R(\alpha, \beta) = \mathrm{diag}(\alpha, \beta)$
  are fixed by Xambó’s `revTilde`, swapped by `parityHat` and `cliffConj`
  ($\widehat{R(\alpha, \beta)} = \overline{R(\alpha, \beta)} = R(\beta, \alpha)$), and scale the
  vacuum projector via $R(\alpha, \beta) E_{00} \overline{R(\alpha, \beta)} = \langle \alpha \beta, 0, 0, 0 \rangle$.
- **Archetype $\mathcal{U}_3$ (`archetype_U3_bhoja_krasnov_mixed_structures_and_xambo_spacetime_split`)**:
  Over `[Ring B]`, links Xambó’s 4D Dirac spacetime split bivectors $\Sigma_1, \Sigma_2, \Sigma_3 \in \mathrm{Op}_4(B)$
  with Bhoja–Krasnov’s mixed structure $(I_{\mathrm{para}}, J_{\mathrm{comp}}, P_{\mathrm{prod}})$,
  proving $\Sigma_1 \Sigma_3 = -(\Gamma_1 \Gamma_3)$ and $(\Sigma_1 \Sigma_3)^2 = -1$ alongside
  $I_{\mathrm{para}}^2 - J_{\mathrm{comp}}^2 = 1$ and $I_{\mathrm{para}}^2 + J_{\mathrm{comp}}^2 = P_{\mathrm{prod}}$.
- **Archetype $\mathcal{U}_4$ (`archetype_U4_aharonov_two_state_weak_value_and_xambo_riesz_holonomy`)**:
  Over `[Ring B]`, proves that sandwiching Aharonov’s Wilson-dressed modular shift $T_{\mathrm{AB}}(W_{12}, W_{21})$
  between the Cartan vacuum/occupied idempotents via `twoStateSandwich` isolates the directional
  Wilson link $W_{12} E_{01}$ and the closed slit holonomy $W_{12} W_{21} P_{\mathrm{vac}}$, while Xambó’s
  `parityHat` separates even local observables from odd symmetric modular shifts.
- **Archetype $\mathcal{U}_5$ (`archetype_U5_bimetric_bohm_curvature_and_cheshire_cat_unification`)**:
  Over `[Ring B]`, unites the Bimetric Peirce sheet geometry ($\mathcal{S}_0 \prec \dots \prec \mathcal{S}_4$)
  with Aharonov’s modular shift and Quantum Cheshire Cat ($\mathcal{A}_0 \prec \dots \prec \mathcal{A}_5$),
  proving exact intertwiner alignment (`aharonovToBimetric`), sheet-exchange holonomy conjugation
  $E_x T_{\mathrm{AB}}^2 E_x = \mathrm{localObs}(W_{21} W_{12}, W_{12} W_{21})$, Bohm double-commutator
  curvature restoration $-[\Phi_{\mathrm{mat}}, [\Phi_{\mathrm{mat}}, J_{\mathrm{mat}}]] = -4 V_{\mathrm{mat}} J_{\mathrm{mat}}$,
  and two-state spatial decoupling of particle presence vs. spin in the Quantum Cheshire Cat.

## Three-Bucket Audit Map:
- **BUCKET 1 (Keep)**: `mat2ToFin2`, `fin2ToMat2`, `bkToXambo`, `xamboToAharonov`, `aharonovToXambo`,
  `aharonovToBimetric`, `hestenesRotorXambo`, `aharonovVacProj`, `aharonovOccProj`,
  `archetype_U0_cartan_bhoja_krasnov_witt_polyform_intertwiner`,
  `archetype_U1_xambo_wessel_riesz_to_witt_polyform_and_ternary_closure`,
  `archetype_U2_xambo_versor_reflection_to_hestenes_boost_and_pin_reflection`,
  `archetype_U3_bhoja_krasnov_mixed_structures_and_xambo_spacetime_split`,
  `archetype_U4_aharonov_two_state_weak_value_and_xambo_riesz_holonomy`,
  `archetype_U5_bimetric_bohm_curvature_and_cheshire_cat_unification`,
  `fin2_integer_matrix_has_noncommuting_pair`.
- **BUCKET 2 (Rewrite)**: Renamed `bridge_U0_* .. bridge_U4_*` to `archetype_U0_* .. archetype_U4_*`
  and added `archetype_U5_bimetric_bohm_curvature_and_cheshire_cat_unification`.
- **BUCKET 3 (Delete)**: None (zero wrappers, zero sockets, zero certificates).
-/

namespace InfoGeometry.Canonical.CartanBhojaKrasnovXamboAharonovUnificationBridge

open InfoGeometry.Canonical.CartanHestenesPinSkolemNoetherGaloisPoset
open InfoGeometry.Canonical.TernaryCantorCliffordCyclotomicBraidedPinPoset
open InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset
open InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset
open InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 1. ARCHETYPE U₀: MAT2 B ↔ MATRIX (FIN 2) (FIN 2) B & CARTAN–BHOJA-KRASNOV DICTIONARY
-- ============================================================================

/-- Canonical matrix carrier conversion from `BhojaKrasnov.Mat2 B` to `Matrix (Fin 2) (Fin 2) B`. -/
def mat2ToFin2 (M : InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) :
    Matrix (Fin 2) (Fin 2) B :=
  !![M.a11, M.a12;
     M.a21, M.a22]

/-- Canonical inverse carrier conversion from `Matrix (Fin 2) (Fin 2) B` to `BhojaKrasnov.Mat2 B`. -/
def fin2ToMat2 (A : Matrix (Fin 2) (Fin 2) B) :
    InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B :=
  ⟨A 0 0, A 0 1, A 1 0, A 1 1⟩

/-- **Archetype $\mathcal{U}_0$ (`archetype_U0_cartan_bhoja_krasnov_witt_polyform_intertwiner`):**
Proves over any non-commutative associative ring `[Ring B]` that `mat2ToFin2` and `fin2ToMat2`
form an exact ring isomorphism between `BhojaKrasnov.Mat2 B` and `Matrix (Fin 2) (Fin 2) B`
that intertwines Bhoja–Krasnov’s matrix units with Cartan–Hestenes’ split-space basis and
Cantor’s branch projectors:
1. `fin2ToMat2 (mat2ToFin2 M) = M` and `mat2ToFin2 (fin2ToMat2 A) = A`;
2. `mat2ToFin2 (M * N) = mat2ToFin2 M * mat2ToFin2 N`;
3. `mat2ToFin2 E01 = wittNullU = cantorCreateU` and `mat2ToFin2 E10 = wittNullV = cantorAnnihilateV`;
4. `mat2ToFin2 E00 = cartanVacIdempotent = cantorBranchVac` and `mat2ToFin2 E11 = cantorBranchOcc`;
5. `mat2ToFin2 Ex = splitGenE` and `mat2ToFin2 Ez = kreinGradeEta`. -/
theorem archetype_U0_cartan_bhoja_krasnov_witt_polyform_intertwiner
    (M N : InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B)
    (A : Matrix (Fin 2) (Fin 2) B) :
    fin2ToMat2 (mat2ToFin2 M) = M ∧
    mat2ToFin2 (fin2ToMat2 A) = A ∧
    mat2ToFin2 (M * N) = mat2ToFin2 M * mat2ToFin2 N ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = wittNullU ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = wittNullV ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = cartanVacIdempotent ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = cantorCreateU ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = cantorAnnihilateV ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = cantorBranchVac ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E11 :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = cantorBranchOcc ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Ex :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = splitGenE ∧
    mat2ToFin2 (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Ez :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) = kreinGradeEta := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> exact Eq.refl _
  · ext i j; fin_cases i <;> fin_cases j <;> exact Eq.refl _
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, wittNullU,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, wittNullV,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, cartanVacIdempotent,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, cantorCreateU,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, cantorAnnihilateV,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, cantorBranchVac,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, cantorBranchOcc,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E11]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, splitGenE,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Ex]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2ToFin2, kreinGradeEta,
            InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Ez]

-- ============================================================================
-- 2. ARCHETYPE U₁: XAMBÓ WESSEL–RIESZ ↔ BHOJA–KRASNOV WITT & CANTOR TERNARY CLOSURE
-- ============================================================================

/-- Canonical non-commutative ring isomorphism from `BhojaKrasnov.Mat2 B` to `Xambo.Mat2 B`. -/
@[simp] def bkToXambo
    (M : InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B) :
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/-- **Archetype $\mathcal{U}_1$ (`archetype_U1_xambo_wessel_riesz_to_witt_polyform_and_ternary_closure`):**
Over ANY non-commutative associative ring `[Ring B]`:
1. `bkToXambo` is an exact multiplicative ring homomorphism:
   `bkToXambo (M * N) = bkToXambo M * bkToXambo N`.
2. **Xambó Riesz Contraction & Wedge Realize Polyform $(e_1 \lrcorner \cdot, e_1 \wedge \cdot)$ on the Spinor Ideal $\mathrm{Span}(E_{00}, E_{10})$:**
   - On the 0-form vacuum `E00`: `rieszDot Ex (bkToXambo E00) = 0` ($e_1 \lrcorner 1 = 0$) and
     `rieszWedge Ex (bkToXambo E00) = bkToXambo E10 + bkToXambo E10` ($2(e_1 \wedge 1) = 2 e_1$).
   - On the 1-form state `E10`: `rieszDot Ex (bkToXambo E10) = bkToXambo E00 + bkToXambo E00` ($2(e_1 \lrcorner e_1) = 2 \cdot 1$)
     and `rieszWedge Ex (bkToXambo E10) = 0` ($e_1 \wedge e_1 = 0$).
3. **Non-Commutative Ternary Reflection Closure on Xambó Grade-1 Odd Vectors:**
   For any three odd 1-vectors $U = \mathrm{vec}_1(u_1, u_2)$, $V = \mathrm{vec}_1(v_1, v_2)$, and
   $W = \mathrm{vec}_1(w_1, w_2)$ in `Xambo.Mat2 B`, their ternary product $U V W$ is strictly
   odd under `parityHat`:
   `parityHat (U * V * W) = -(U * V * W)`. -/
theorem archetype_U1_xambo_wessel_riesz_to_witt_polyform_and_ternary_closure
    (M N : InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2 B)
    (u1 u2 v1 v2 w1 w2 : B) :
    bkToXambo (M * N) = bkToXambo M * bkToXambo N ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszDot
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex (B := B))
      (bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 (B := B))) = 0 ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszWedge
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex (B := B))
      (bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 (B := B))) =
      bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 (B := B)) +
        bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 (B := B)) ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszDot
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex (B := B))
      (bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 (B := B))) =
      bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 (B := B)) +
        bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 (B := B)) ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszWedge
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex (B := B))
      (bkToXambo (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10 (B := B))) = 0 ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 u1 u2 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 v1 v2 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 w1 w2) =
      -(InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 u1 u2 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 v1 v2 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1 w1 w2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> exact Eq.refl _
  · ext <;>
      simp [bkToXambo,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszDot,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00]
  · ext <;>
      simp [bkToXambo,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszWedge,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10]
  · ext <;>
      simp [bkToXambo,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszDot,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10]
  · ext <;>
      simp [bkToXambo,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.rieszWedge,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E10]
  · ext <;>
      simp [
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.vec1,
        mul_add, mul_assoc] <;>
      abel

-- ============================================================================
-- 3. ARCHETYPE U₂: XAMBÓ INVOLUTIONS ↔ HESTENES HYPERBOLIC BOOST ROTOR
-- ============================================================================

/-- Hestenes hyperbolic split-space rotor $R(\alpha, \beta) = \begin{pmatrix} \alpha & 0 \\ 0 & \beta \end{pmatrix}$ in `Xambo.Mat2 B`. -/
@[simp] def hestenesRotorXambo (α β : B) :
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2 B :=
  ⟨α, 0, 0, β⟩

/-- **Archetype $\mathcal{U}_2$ (`archetype_U2_xambo_versor_reflection_to_hestenes_boost_and_pin_reflection`):**
Over ANY non-commutative associative ring `[Ring B]`:
1. **Even Grade of Hestenes Rotor under Xambó's `revTilde` & Swap under `parityHat` / `cliffConj`:**
   For $R(\alpha, \beta) = \mathrm{hestenesRotorXambo}(\alpha, \beta)$, $\widetilde{R(\alpha, \beta)} = R(\alpha, \beta)$
   while $\widehat{R(\alpha, \beta)} = \overline{R(\alpha, \beta)} = R(\beta, \alpha)$ (realizing the
   split-complex Galois involution swap $(\alpha, \beta) \mapsto (\beta, \alpha)$).
2. **Hestenes Rotor Sandwich on Null Polyform Projectors:**
   $R(\alpha, \beta) \cdot \mathrm{bkToXambo}(E_{00}) \cdot \overline{R(\alpha, \beta)} = \langle \alpha \beta, 0, 0, 0 \rangle$
   and $R(\alpha, \beta) \cdot \mathrm{bkToXambo}(E_{01}) = \langle 0, \alpha, 0, 0 \rangle$. -/
theorem archetype_U2_xambo_versor_reflection_to_hestenes_boost_and_pin_reflection
    (α β : B) :
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.revTilde
      (hestenesRotorXambo α β) = hestenesRotorXambo α β ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat
      (hestenesRotorXambo α β) = hestenesRotorXambo β α ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.cliffConj
      (hestenesRotorXambo α β) = hestenesRotorXambo β α ∧
    hestenesRotorXambo α β *
      bkToXambo InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00 *
      InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.cliffConj
        (hestenesRotorXambo α β) = ⟨α * β, 0, 0, 0⟩ ∧
    hestenesRotorXambo α β *
      bkToXambo InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01 =
      ⟨0, α, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · simp only [hestenesRotorXambo, bkToXambo,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.revTilde,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.cliffConj,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E00,
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.E01,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.mul_a11,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.mul_a12,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.mul_a21,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.mul_a22,
        mul_zero, zero_mul, mul_one, add_zero, neg_zero]

-- ============================================================================
-- 4. ARCHETYPE U₃: BHOJA–KRASNOV MIXED STRUCTURES ↔ XAMBÓ DIRAC SPACETIME SPLIT
-- ============================================================================

/-- **Archetype $\mathcal{U}_3$ (`archetype_U3_bhoja_krasnov_mixed_structures_and_xambo_spacetime_split`):**
Over ANY non-commutative associative ring `[Ring B]`, Xambó's relative spacetime bivectors
$\Sigma_1 = \Gamma_1 \Gamma_0$ and $\Sigma_3 = \Gamma_3 \Gamma_0$ in `Xambo.Op4 B` form an
anticommuting pair of paracomplex involutions ($\Sigma_1^2 = 1$, $\Sigma_3^2 = 1$,
$\{\Sigma_1, \Sigma_3\} = 0$) whose product $J_{\Sigma} = \Sigma_1 \Sigma_3 = -(\Gamma_1 \Gamma_3)$ is a
complex structure ($J_{\Sigma}^2 = -1$), while Bhoja–Krasnov's mixed subspace operators
$(I_{\mathrm{para}}, J_{\mathrm{comp}}, P_{\mathrm{prod}})$ satisfy
$I_{\mathrm{para}}^2 - J_{\mathrm{comp}}^2 = 1$ and $I_{\mathrm{para}}^2 + J_{\mathrm{comp}}^2 = P_{\mathrm{prod}}$. -/
theorem archetype_U3_bhoja_krasnov_mixed_structures_and_xambo_spacetime_split :
    (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 :
      InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Op4 B) *
      InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3 =
      -(InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam1 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam3) ∧
    ((InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 :
      InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Op4 B) *
      InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3) *
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3) = -1 ∧
    (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.I_para :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Op4 B) *
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.I_para -
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.J_comp *
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.J_comp = 1 ∧
    (InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.I_para :
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.Op4 B) *
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.I_para +
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.J_comp *
        InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.J_comp =
      InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.P_prod := by
  obtain ⟨_, _, _, _, hK_one, hK_prod, _, _, _⟩ :=
    InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset.Mat2.archetype_K1_mixed_structure_and_orthogonal_product_splitting (B := B)
  have h_s13 :
      (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 :
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Op4 B) *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3 =
        -(InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam1 *
          InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam3) := by
    ext <;>
      simp [
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam0,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam1,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam3,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ez]
  have h_s13_sq :
      ((InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 :
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Op4 B) *
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3) *
        (InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1 *
          InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3) = -1 := by
    ext <;>
      simp [
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig1,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Sig3,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam0,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam1,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Gam3,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ex,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.Ez]
  exact ⟨h_s13, h_s13_sq, hK_one, hK_prod⟩

-- ============================================================================
-- 5. ARCHETYPE U₄: AHARONOV TWO-STATE HOLONOMY ↔ XAMBÓ PARITY & CARTAN VACUUM
-- ============================================================================

/-- Canonical ring isomorphism from `Xambo.Mat2 B` to `Aharonov.Mat2 B`. -/
@[simp] def xamboToAharonov
    (M : InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2 B) :
    InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/-- Canonical inverse ring isomorphism from `Aharonov.Mat2 B` to `Xambo.Mat2 B`. -/
@[simp] def aharonovToXambo
    (M : InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2 B) :
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/-- Cartan upper-slit vacuum idempotent $P_{\mathrm{vac}} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ in `Aharonov.Mat2 B`. -/
@[simp] def aharonovVacProj :
    InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2 B :=
  ⟨1, 0, 0, 0⟩

/-- Cartan lower-slit occupied idempotent $P_{\mathrm{occ}} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ in `Aharonov.Mat2 B`. -/
@[simp] def aharonovOccProj :
    InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2 B :=
  ⟨0, 0, 0, 1⟩

/-- **Archetype $\mathcal{U}_4$ (`archetype_U4_aharonov_two_state_weak_value_and_xambo_riesz_holonomy`):**
Over ANY non-commutative associative ring `[Ring B]`:
1. **Two-State Transition Sandwich of the Wilson-Dressed Modular Shift:**
   Sandwiching $T_{\mathrm{AB}}(W_{12}, W_{21}) = \mathrm{modularShift}(W_{12}, W_{21})$ between
   `aharonovVacProj` (post-selected slit 1) and `aharonovOccProj` (pre-selected slit 2) via
   `twoStateSandwich` isolates the exact directed Wilson link $W_{12} E_{01}$:
   `twoStateSandwich aharonovVacProj aharonovOccProj (modularShift W12 W21) = diagScalar W12 * E01`.
2. **Two-State Diagonal Sandwich of the Closed Holonomy Loop:**
   `twoStateSandwich aharonovVacProj aharonovVacProj (modularShift W12 W21 * modularShift W12 W21) = diagScalar (W12 * W21) * aharonovVacProj`.
3. **Xambó `parityHat` Grading of Local vs. Modular Observables:**
   Under `aharonovToXambo`, any diagonal scalar observable `localObs f f` is strictly EVEN under
   Xambó's `parityHat` (`parityHat (aharonovToXambo (localObs f f)) = aharonovToXambo (localObs f f)`),
   whereas any symmetric modular shift `modularShift τ τ` is strictly ODD
   (`parityHat (aharonovToXambo (modularShift τ τ)) = -aharonovToXambo (modularShift τ τ)`). -/
theorem archetype_U4_aharonov_two_state_weak_value_and_xambo_riesz_holonomy
    (W12 W21 f τ : B) :
    twoStateSandwich (aharonovVacProj (B := B)) aharonovOccProj
      (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift W12 W21) =
      InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.diagScalar W12 *
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.E01 ∧
    twoStateSandwich (aharonovVacProj (B := B)) aharonovVacProj
      (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift W12 W21 *
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift W12 W21) =
      InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.diagScalar (W12 * W21) *
        aharonovVacProj ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat
      (aharonovToXambo
        (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs f f)) =
      aharonovToXambo
        (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs f f) ∧
    InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat
      (aharonovToXambo
        (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift τ τ)) =
      -aharonovToXambo
        (InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift τ τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · simp only [twoStateSandwich, aharonovVacProj, aharonovOccProj, aharonovToXambo,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.diagScalar,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.E01,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a11,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a12,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a21,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a22,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.parityHat,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.neg_a11,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.neg_a12,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.neg_a21,
        InfoGeometry.Canonical.XamboWesselRieszSkewDerivationOlindeRodriguesPoset.Mat2.neg_a22,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero]

-- ============================================================================
-- 6. ARCHETYPE U₅: BIMETRIC PEIRCE SHEET CURVATURE ↔ QUANTUM CHESHIRE CAT
--    (DIAGONAL & FULL ENTANGLED QUASI-PROJECTORS + WIDOM–HANKEL–TOEPLITZ)
-- ============================================================================

/-- Canonical non-commutative ring isomorphism from `Aharonov.Mat2 B` to
`NonCommutativeBimetricSheetGeometry.Mat2 B`. -/
@[simp] def aharonovToBimetric
    (M : InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a11, M.a12, M.a21, M.a22⟩

/-- Isotropic Witt creation nilpotent `wittB = E₁₀ = [[0, 0], [1, 0]]` in `Bimetric.Mat2 B`. -/
@[simp] def wittB : NonCommutativeBimetricSheetGeometry.Mat2 B := ⟨0, 0, 1, 0⟩

/-- Isotropic Witt annihilation nilpotent `wittB_dag = E₀₁ = [[0, 1], [0, 0]]` in `Bimetric.Mat2 B`. -/
@[simp] def wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B := ⟨0, 1, 0, 0⟩

/-- Polyform `ℤ₂` grade involution `polyParity(M) = Ez * M * Ez = [[m₁₁, -m₁₂], [-m₂₁, m₂₂]]`. -/
@[simp] def polyParity (M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a11, -M.a12, -M.a21, M.a22⟩

/-- Riesz interior contraction graded by `polyParity`: `rieszDotPoly(X, M) = X * M - polyParity(M) * X`. -/
@[simp] def rieszDotPoly (X M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  X * M - polyParity M * X

/-- Riesz exterior wedge graded by `polyParity`: `rieszWedgePoly(X, M) = X * M + polyParity(M) * X`. -/
@[simp] def rieszWedgePoly (X M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  X * M + polyParity M * X

/-- Twisted Pin reflection `pinReflect(V, M) = polyParity(V) * M * V`. -/
@[simp] def pinReflect (V M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  polyParity V * M * V

/-- **Polyform Riesz Skew-Derivation & Twisted Pin Jordan Pair Triple Product
(`archetype_U1_U2_polyform_riesz_and_pin_jordan_triple_product`):**
Over ANY non-commutative associative ring `[Ring B]`:
1. **Witt Nilpotent CAR & Corner Flip ($\mathcal{U}_0$):**
   `wittB² = 0`, `wittB_dag² = 0`, `wittB * wittB_dag + wittB_dag * wittB = 1`,
   `wittB_dag * wittB - wittB * wittB_dag = Ez`,
   `wittB_dag * matPhi A C * wittB_dag = ⟨0, C, 0, 0⟩`, and
   `wittB * matPhi A C * wittB = ⟨0, 0, A, 0⟩`.
2. **Polyform Riesz Skew-Derivation & CAR/Cartan Recovery ($\mathcal{U}_1$):**
   `polyParity (M * N) = polyParity M * polyParity N`,
   `rieszDotPoly X (M * N) = rieszDotPoly X M * N + polyParity M * rieszDotPoly X N`,
   `rieszWedgePoly X (M * N) = rieszDotPoly X M * N + polyParity M * rieszWedgePoly X N`,
   `rieszDotPoly wittB_dag wittB = 1`, and `rieszWedgePoly wittB_dag wittB = Ez`.
3. **Twisted Pin Reflection, Jordan Pair Triple Product & Householder Anomaly ($\mathcal{U}_2$):**
   `pinReflect U (pinReflect V M) = polyParity (U * V) * M * (V * U)`,
   `pinReflect (matPhi A C) Ez = matSig A C`,
   `pinReflect (matPhi A C) (matPhi X Y) = -matPhi (A * Y * A) (C * X * C)`, and
   `(U * U * matPhi X Y - rieszDotPoly U (matPhi X Y) * U) - (-(U * matPhi X Y * U)) = (U * U) * matPhi X Y - matPhi X Y * (U * U)`.
4. **Riesz Extraction of Wilson Holonomy & Bimetric Dipole ($\mathcal{U}_4$):**
   `rieszDotPoly (matPhi W12 W21) (matPhi W12 W21) = matV W12 W21 + matV W12 W21`,
   `rieszWedgePoly (matPhi W12 W21) (matPhi W12 W21) = 0`,
   `rieszDotPoly (matJ W12 W21) (matPhi W12 W21) = 0`, and
   `rieszWedgePoly (matPhi W12 W21) (matJ W12 W21) = -(matSig W12 W21 + matSig W12 W21)`. -/
theorem archetype_U1_U2_polyform_riesz_and_pin_jordan_triple_product
    (U V M N : NonCommutativeBimetricSheetGeometry.Mat2 B)
    (A C X Y W12 W21 : B) :
    let Ez_B  := NonCommutativeBimetricSheetGeometry.Mat2.Ez (B := B)
    let PhiAC := NonCommutativeBimetricSheetGeometry.Mat2.matPhi A C
    let PhiXY := NonCommutativeBimetricSheetGeometry.Mat2.matPhi X Y
    let PhiW  := NonCommutativeBimetricSheetGeometry.Mat2.matPhi W12 W21
    let JW    := NonCommutativeBimetricSheetGeometry.Mat2.matJ W12 W21
    let VW    := NonCommutativeBimetricSheetGeometry.Mat2.matV W12 W21
    let SigW  := NonCommutativeBimetricSheetGeometry.Mat2.matSig W12 W21
    -- 1. Witt nilpotent CAR & corner flip:
    (wittB : NonCommutativeBimetricSheetGeometry.Mat2 B) * wittB = 0 ∧
    (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) * wittB_dag = 0 ∧
    (wittB : NonCommutativeBimetricSheetGeometry.Mat2 B) * wittB_dag + wittB_dag * wittB = 1 ∧
    (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) * wittB - wittB * wittB_dag = Ez_B ∧
    (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) * PhiAC * wittB_dag = ⟨0, C, 0, 0⟩ ∧
    (wittB : NonCommutativeBimetricSheetGeometry.Mat2 B) * PhiAC * wittB = ⟨0, 0, A, 0⟩ ∧
    -- 2. Polyform Riesz skew-derivation & CAR/Cartan recovery:
    polyParity (M * N) = polyParity M * polyParity N ∧
    rieszDotPoly U (M * N) = rieszDotPoly U M * N + polyParity M * rieszDotPoly U N ∧
    rieszWedgePoly U (M * N) = rieszDotPoly U M * N + polyParity M * rieszWedgePoly U N ∧
    rieszDotPoly (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) wittB = 1 ∧
    rieszWedgePoly (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) wittB = Ez_B ∧
    -- 3. Twisted Pin reflection, Jordan pair triple product & Householder anomaly:
    pinReflect U (pinReflect V M) = polyParity (U * V) * M * (V * U) ∧
    pinReflect PhiAC Ez_B = NonCommutativeBimetricSheetGeometry.Mat2.matSig A C ∧
    pinReflect PhiAC PhiXY = -NonCommutativeBimetricSheetGeometry.Mat2.matPhi (A * Y * A) (C * X * C) ∧
    (U * U * PhiXY - rieszDotPoly U PhiXY * U) - (-(U * PhiXY * U)) =
      (U * U) * PhiXY - PhiXY * (U * U) ∧
    -- 4. Riesz extraction of Wilson holonomy V and bimetric dipole Σ:
    rieszDotPoly PhiW PhiW = VW + VW ∧
    rieszWedgePoly PhiW PhiW = 0 ∧
    rieszDotPoly JW PhiW = 0 ∧
    rieszWedgePoly PhiW JW = -(SigW + SigW) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    (simp only [wittB, wittB_dag, polyParity, rieszDotPoly, rieszWedgePoly, pinReflect,
                NonCommutativeBimetricSheetGeometry.Mat2.Ez,
                NonCommutativeBimetricSheetGeometry.Mat2.matPhi,
                NonCommutativeBimetricSheetGeometry.Mat2.matJ,
                NonCommutativeBimetricSheetGeometry.Mat2.matV,
                NonCommutativeBimetricSheetGeometry.Mat2.matSig,
                NonCommutativeBimetricSheetGeometry.Mat2.zero_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.zero_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.zero_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.zero_a22,
                NonCommutativeBimetricSheetGeometry.Mat2.one_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.one_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.one_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.one_a22,
                NonCommutativeBimetricSheetGeometry.Mat2.add_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.add_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.add_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.add_a22,
                NonCommutativeBimetricSheetGeometry.Mat2.neg_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.neg_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.neg_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.neg_a22,
                NonCommutativeBimetricSheetGeometry.Mat2.sub_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.sub_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.sub_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.sub_a22,
                NonCommutativeBimetricSheetGeometry.Mat2.mul_a11,
                NonCommutativeBimetricSheetGeometry.Mat2.mul_a12,
                NonCommutativeBimetricSheetGeometry.Mat2.mul_a21,
                NonCommutativeBimetricSheetGeometry.Mat2.mul_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_mul, mul_neg, neg_add_rev, sub_neg_eq_add, neg_neg, neg_zero,
                mul_assoc];
     try abel)

/-- **Archetype $\mathcal{U}_5$ (`archetype_U5_bimetric_bohm_curvature_and_cheshire_cat_unification`):**
Over ANY non-commutative associative ring `[Ring B]` equipped with anticommuting involutions
$\sigma_x^2 = 1, \sigma_z^2 = 1, \{\sigma_x, \sigma_z\} = 0$:
1. **Bimetric Boundary Bridge & Corner Metric Intertwiner:**
   Under `aharonovToBimetric`, Aharonov's Wilson-dressed modular shift `modularShift W12 W21` maps
   to the bimetric off-diagonal bridge `matPhi W12 W21`, and its closed holonomy square maps to
   the total bimetric corner metric `matV W12 W21 = [[W12 * W21, 0], [0, W21 * W12]]`.
2. **Sheet-Exchange Holonomy Duality:**
   Conjugating the closed slit holonomy `modularShift W12 W21 * modularShift W12 W21` by the
   sheet-exchange involution `Ex` exchanges the upper-slit loop `W12 * W21` and lower-slit loop
   `W21 * W12`:
   `Ex * (modularShift W12 W21 * modularShift W12 W21) * Ex = localObs (W21 * W12) (W12 * W21)`.
3. **Double-Commutator Bohm Curvature Restoration on the Modular Shift:**
   In `NonCommutativeBimetricSheetGeometry.Mat2 B`, the double-commutator derivation with respect
   to `Φ_mat = matPhi W12 W21` acts on the skew phase current `J_mat = matJ W12 W21` as a
   restoring operator with eigenvalue `-4 V_mat`:
   `-(rcomm Φ_mat (rcomm Φ_mat J_mat)) = -((V_mat + V_mat + V_mat + V_mat) * J_mat)`.
4. **Quantum Cheshire Cat Two-State Spatial Decoupling (Diagonal & Full Entangled 2x2 + Widom Cancellation):**
   - Diagonal specialization (`Ψ_cat`, `Φ_cat`):
     `Φ_cat * P_left * Ψ_cat = localObs ((1 + σx) + (1 + σx)) 0`, `Φ_cat * P_right * Ψ_cat = 0`,
     `Φ_cat * (P_left * S_z) * Ψ_cat = 0`, `Φ_cat * (P_right * S_z) * Ψ_cat = localObs 0 ((1 + σx) + (1 + σx))`.
   - Full non-diagonal entangled 2x2 quasi-projector decoupling (`Ψ_ent`, `Φ_ent`):
     `Φ_ent * P_left * Ψ_ent = Φ_ent * Ψ_ent`, `Φ_ent * P_right * Ψ_ent = 0`,
     `Φ_ent * (P_left * S_z) * Ψ_ent = 0`, `Φ_ent * (P_right * S_z) * Ψ_ent = Φ_ent * Ψ_ent`.
   - Widom–Hankel–Toeplitz cancellation of the joint product `P_left * (P_right * S_z) = 0`:
     `(Φ_ent * P_left * Φ_ent) * (Φ_ent * (P_right * S_z) * Ψ_ent) + (Φ_ent * P_left * Φ_comp) * (Φ_comp * (P_right * S_z) * Ψ_ent) = 0`. -/
theorem archetype_U5_bimetric_bohm_curvature_and_cheshire_cat_unification
    (W12 W21 : B) {σx σz : B}
    (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : NonCommutativeTwoStateAndModularShift.racomm σx σz = 0) :
    let T_AB := InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift W12 W21
    let Ex_A := InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.Ex (B := B)
    let Φ_mat := NonCommutativeBimetricSheetGeometry.Mat2.matPhi W12 W21
    let J_mat := NonCommutativeBimetricSheetGeometry.Mat2.matJ W12 W21
    let V_mat := NonCommutativeBimetricSheetGeometry.Mat2.matV W12 W21
    let Qplus  := 1 + σx
    let Qminus := 1 - σx
    let Ψ_cat  := NonCommutativeTwoStateAndModularShift.Mat2.localObs Qplus (Qminus * σz)
    let Φ_cat  := NonCommutativeTwoStateAndModularShift.Mat2.localObs Qplus Qplus
    let Ψ_ent  := NonCommutativeTwoStateAndModularShift.Mat2.PsiEnt σx σz
    let Φ_ent  := NonCommutativeTwoStateAndModularShift.Mat2.PhiEnt σx
    let Φ_comp := (1 + 1 + 1 + 1 : NonCommutativeTwoStateAndModularShift.Mat2 B) - Φ_ent
    let P_left := NonCommutativeTwoStateAndModularShift.Mat2.localObs (1 : B) 0
    let P_right := NonCommutativeTwoStateAndModularShift.Mat2.localObs (0 : B) 1
    let S_z    := NonCommutativeTwoStateAndModularShift.Mat2.diagScalar σz
    -- 1. Intertwiner alignment between Aharonov modularShift and Bimetric matPhi / matV:
    aharonovToBimetric T_AB = Φ_mat ∧
    aharonovToBimetric (T_AB * T_AB) = V_mat ∧
    -- 2. Sheet-exchange conjugation swaps the upper and lower Wilson holonomy loops:
    Ex_A * (T_AB * T_AB) * Ex_A =
      InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs (W21 * W12) (W12 * W21) ∧
    -- 3. Double-commutator Bohm curvature restoration on J_mat:
    -(Φ_mat * (Φ_mat * J_mat - J_mat * Φ_mat) - (Φ_mat * J_mat - J_mat * Φ_mat) * Φ_mat) =
      -((V_mat + V_mat + V_mat + V_mat) * J_mat) ∧
    -- 4. Diagonal Quantum Cheshire Cat two-state decoupling of particle vs. spin:
    Φ_cat * P_left * Ψ_cat =
      NonCommutativeTwoStateAndModularShift.Mat2.localObs (Qplus + Qplus) 0 ∧
    Φ_cat * P_right * Ψ_cat = 0 ∧
    Φ_cat * (P_left * S_z) * Ψ_cat = 0 ∧
    Φ_cat * (P_right * S_z) * Ψ_cat =
      NonCommutativeTwoStateAndModularShift.Mat2.localObs 0 (Qplus + Qplus) ∧
    -- 5. Full entangled 2x2 quasi-projector decoupling & Widom-Hankel-Toeplitz cancellation:
    Φ_ent * P_left * Ψ_ent = Φ_ent * Ψ_ent ∧
    Φ_ent * P_right * Ψ_ent = 0 ∧
    Φ_ent * (P_left * S_z) * Ψ_ent = 0 ∧
    Φ_ent * (P_right * S_z) * Ψ_ent = Φ_ent * Ψ_ent ∧
    (Φ_ent * P_left * Φ_ent) * (Φ_ent * (P_right * S_z) * Ψ_ent) +
      (Φ_ent * P_left * Φ_comp) * (Φ_comp * (P_right * S_z) * Ψ_ent) = 0 := by
  intro T_AB Ex_A Φ_mat J_mat V_mat Qplus Qminus Ψ_cat Φ_cat Ψ_ent Φ_ent Φ_comp P_left P_right S_z
  have h1 : aharonovToBimetric T_AB = Φ_mat := by
    ext <;> exact Eq.refl _
  have h2 : aharonovToBimetric (T_AB * T_AB) = V_mat := by
    ext <;>
      simp only [aharonovToBimetric, T_AB, V_mat,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a11,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a12,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a21,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a22,
        NonCommutativeBimetricSheetGeometry.Mat2.matV,
        mul_zero, zero_mul, add_zero, zero_add]
  have h3 : Ex_A * (T_AB * T_AB) * Ex_A =
      InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs (W21 * W12) (W12 * W21) := by
    ext <;>
      simp only [Ex_A, T_AB,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.Ex,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.modularShift,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.localObs,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a11,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a12,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a21,
        InfoGeometry.Canonical.AharonovTwoStateWeakValueModularShiftHolonomyPoset.Mat2.mul_a22,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  have hBohm :
      -(Φ_mat * (Φ_mat * J_mat - J_mat * Φ_mat) - (Φ_mat * J_mat - J_mat * Φ_mat) * Φ_mat) =
        -((V_mat + V_mat + V_mat + V_mat) * J_mat) := by
    ext <;>
    · simp only [Φ_mat, J_mat, V_mat,
        NonCommutativeBimetricSheetGeometry.Mat2.matPhi,
        NonCommutativeBimetricSheetGeometry.Mat2.matJ,
        NonCommutativeBimetricSheetGeometry.Mat2.matV,
        NonCommutativeBimetricSheetGeometry.Mat2.add_a11,
        NonCommutativeBimetricSheetGeometry.Mat2.add_a12,
        NonCommutativeBimetricSheetGeometry.Mat2.add_a21,
        NonCommutativeBimetricSheetGeometry.Mat2.add_a22,
        NonCommutativeBimetricSheetGeometry.Mat2.neg_a11,
        NonCommutativeBimetricSheetGeometry.Mat2.neg_a12,
        NonCommutativeBimetricSheetGeometry.Mat2.neg_a21,
        NonCommutativeBimetricSheetGeometry.Mat2.neg_a22,
        NonCommutativeBimetricSheetGeometry.Mat2.sub_a11,
        NonCommutativeBimetricSheetGeometry.Mat2.sub_a12,
        NonCommutativeBimetricSheetGeometry.Mat2.sub_a21,
        NonCommutativeBimetricSheetGeometry.Mat2.sub_a22,
        NonCommutativeBimetricSheetGeometry.Mat2.mul_a11,
        NonCommutativeBimetricSheetGeometry.Mat2.mul_a12,
        NonCommutativeBimetricSheetGeometry.Mat2.mul_a21,
        NonCommutativeBimetricSheetGeometry.Mat2.mul_a22,
        mul_add, add_mul, sub_mul, mul_sub,
        mul_zero, zero_mul, add_zero, zero_add, sub_zero,
        neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
        mul_assoc]
      try abel
  have hCat :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_A5_quantum_cheshire_cat_two_state_decoupling
      hx hz hxz
  have hG1 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_G1_entangled_corner_channel_decoupling
      hx hz hxz
  have hG2 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_G2_widom_hankel_toeplitz_cancellation_of_joint_product
      hx hz hxz
  exact ⟨h1, h2, h3, hBohm, hCat.1, hCat.2.1, hCat.2.2.1, hCat.2.2.2,
         hG1.1, hG1.2.1, hG1.2.2.1, hG1.2.2.2.1, hG2.2.2.2⟩

-- ============================================================================
-- 7. ARCHETYPE U₆: NAVIER–MADELUNG CHIRAL VORTEX ANOMALY & HELICITY UNIFICATION
-- ============================================================================

/-- **Archetype $\mathcal{U}_6$ (`archetype_U6_navier_madelung_chiral_vortex_anomaly_unification`):**
Over ANY non-commutative associative ring `[Ring B]`, unites the Peirce Navier–Madelung Chiral
Vortex Anomaly Poset ($\mathcal{V}_0 \prec \dots \prec \mathcal{V}_4$) with Xambó's 3D vector
algebra and the $2 \times 2$ bimetric matrix geometry:
1. **Chiral Vortex Anomaly vs. Fluid Density Duality ($\mathcal{V}_0$):**
   For any idempotent $P^2 = P \in B$, the chiral grading involution $S_P = \mathrm{invS}(P)$
   converts the chiral vortex anomaly $\Omega_{\mathrm{vortex}} = \mathrm{genSig}(P, X, Y)$ into
   the total fluid density $V = \mathrm{genV}(P, X, Y)$ ($S_P \Omega_{\mathrm{vortex}} = V$) with
   equal enstrophy and density squares ($\Omega_{\mathrm{vortex}}^2 = V^2$).
2. **Navier–Stokes Strain Depletion & Pure Chiral Lamb Torque ($\mathcal{V}_1$):**
   The symmetric Bernoulli strain vanishes identically ($\mathcal{B}(J, \Omega_{\mathrm{vortex}}) = 0$),
   while the non-commutative Lamb commutator is pure chiral torque
   ($\mathcal{L}(J, \Omega_{\mathrm{vortex}}) = V \Phi + V \Phi$).
3. **Bohm Quantum Pressure & Viscous Double-Commutator Momentum Closure ($\mathcal{V}_2$):**
   $\mathcal{Q}_{\mathrm{Bohm}}(\Phi, J) + (V + V + V + V) J = 0$ and
   $\mathcal{D}_{\mathrm{visc}}(J, \Phi) = (V + V + V + V) \Phi$.
4. **3D Non-Commutative Helicity Triple-Product Identity ($\mathcal{V}_3$):**
   For any $u, \omega, B_{\mathrm{mag}} \in \mathrm{Vec}_3(B)$,
   $\mathrm{dot}_3(u, \mathrm{cross}_3(\omega, B_{\mathrm{mag}})) = \mathrm{dot}_3(\mathrm{cross}_3(u, \omega), B_{\mathrm{mag}})$.
5. **Matrix ABJ Chiral Trace Anomaly & Healing-Core Regularization ($\mathcal{V}_4$):**
   In `NonCommutativeBimetricSheetGeometry.Mat2 B`, $\operatorname{tr}_2(\Sigma(A, C)) = [A, C]$
   and $D_\xi(A, C, m_\xi)^2 = V(A, C) + \mathrm{diagScalar}(m_\xi^2) + \langle 0, [m_\xi, A], [C, m_\xi], 0 \rangle$. -/
theorem archetype_U6_navier_madelung_chiral_vortex_anomaly_unification
    {P : B} (hP : P * P = P) (X Y A C m_xi : B)
    (u ω B_mag : NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) :
    let SP   := NonCommutativeBimetricSheetGeometry.invS P
    let Phi  := NonCommutativeBimetricSheetGeometry.genPhi P X Y
    let J    := NonCommutativeBimetricSheetGeometry.genJ P X Y
    let V    := NonCommutativeBimetricSheetGeometry.genV P X Y
    let Om_v := NonCommutativeBimetricSheetGeometry.genSig P X Y
    let Sig_mat := NonCommutativeBimetricSheetGeometry.Mat2.matSig A C
    let V_mat   := NonCommutativeBimetricSheetGeometry.Mat2.matV A C
    let D_xi    := NonCommutativeNavierMadelungChiralVortexPoset.Mat2.matRegularizedVortex A C m_xi
    -- 1. Chiral vortex anomaly duality & enstrophy square:
    SP * Om_v = V ∧
    Om_v * Om_v = V * V ∧
    -- 2. Vanishing symmetric Bernoulli strain & pure chiral Lamb torque:
    NonCommutativeNavierMadelungChiralVortexPoset.bernoulliStrain J Om_v = 0 ∧
    NonCommutativeNavierMadelungChiralVortexPoset.lambOperator J Om_v = V * Phi + V * Phi ∧
    -- 3. Bohm quantum pressure & viscous double-commutator closure:
    NonCommutativeBimetricSheetGeometry.bohmCurv P X Y J + (V + V + V + V) * J = 0 ∧
    NonCommutativeNavierMadelungChiralVortexPoset.viscousCurv P X Y Phi = (V + V + V + V) * Phi ∧
    -- 4. 3D non-commutative helicity triple-product identity:
    NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3 u
      (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 ω B_mag) =
      NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3
        (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 u ω) B_mag ∧
    -- 5. ABJ chiral trace anomaly & healing-core regularization square:
    NonCommutativeBimetricSheetGeometry.Mat2.tr2 Sig_mat =
      NonCommutativeBimetricSheetGeometry.rcomm A C ∧
    D_xi * D_xi =
      V_mat + NonCommutativeBimetricSheetGeometry.Mat2.diagScalar (m_xi * m_xi) +
        ⟨0, NonCommutativeBimetricSheetGeometry.rcomm m_xi A,
            NonCommutativeBimetricSheetGeometry.rcomm C m_xi, 0⟩ := by
  intro SP Phi J V Om_v Sig_mat V_mat D_xi
  have hV0 :=
    NonCommutativeNavierMadelungChiralVortexPoset.archetype_V0_madelung_amplitude_phase_vorticity_and_chiral_anomaly hP X Y
  have hV1 :=
    NonCommutativeNavierMadelungChiralVortexPoset.archetype_V1_navier_stokes_lamb_commutator_and_beltrami_depletion
      hP X Y J Om_v 1 (by rw [one_mul, mul_one])
  have hV2 :=
    NonCommutativeNavierMadelungChiralVortexPoset.archetype_V2_navier_madelung_bohm_quantum_pressure_momentum_closure hP X Y
  have hV3 :=
    NonCommutativeNavierMadelungChiralVortexPoset.archetype_V3_3d_vortex_stretching_riesz_curl_and_jacobi_helicity u ω B_mag
  have hV4 :=
    NonCommutativeNavierMadelungChiralVortexPoset.Mat2.archetype_V4_matrix_chiral_vortex_core_regularization_and_star_positivity A C m_xi
  exact ⟨hV0.2.2.2.2.1, hV0.2.2.2.2.2.2.2.2.1, hV1.2.2.2.1, hV1.2.2.2.2.2,
         hV2.2.2.2.1, hV2.2.2.1, hV3.2.2, hV4.2.2.2.2.2.1, hV4.2.2.2.2.2.2.2.2⟩

-- ============================================================================
-- 8. ARCHETYPE U₇: REPRESENTATION CONSEQUENCES R₀ ≺ R₁ ≺ R₂ ≺ R₃ ≺ R₄
--    (SPINOR IDEAL RECONSTRUCTION, HADAMARD DUALITY, HALMOS & MORITA SPLIT)
-- ============================================================================

/-- **Archetype $\mathcal{U}_7$ (`archetype_U7_representation_consequences_spinor_ideal_hadamard_halmos_morita`):**
Over ANY non-commutative associative ring `[Ring B]`, unites the five representation-theoretic
consequences ($\mathcal{R}_0 \prec \mathcal{R}_1 \prec \mathcal{R}_2 \prec \mathcal{R}_3 \prec \mathcal{R}_4$):
1. **$\mathcal{R}_0$ (Minimal Ideal Spinor Reconstruction & Corner Homomorphism):**
   Every `M ∈ Mat2 B` is reconstructed from the single minimal left ideal `Mat2 B * P_left` via
   `M = M * P_left + (M * Ex * P_left) * Ex`, `P_right = Ex * P_left * Ex`, and
   `(P_left * Y) * M * (X * P_left) = ⟨(Y * M * X).a11, 0, 0, 0⟩`.
2. **$\mathcal{R}_1$ (Walsh–Hadamard Localization–Shift Duality):**
   The reflection `H_Walsh = Ez + Ex` (`H_Walsh² = 2•1`) conjugates `Ez` into `2•Ex`, `Ex` into
   `2•Ez`, `Ey` into `-2•Ey`, and maps `localObs d₁ d₂` into
   `diagScalar (d₁ + d₂) + modularShift (d₁ - d₂) (d₁ - d₂)`.
3. **$\mathcal{R}_2$ (Halmos's Universal Two-Idempotent Theorem):**
   For any idempotents `P₁² = P₁` and `P₂² = P₂` in `B`, the chordal distance operator
   `Δ₂₁ = (P₂ - P₁)²` commutes with both `P₁` and `P₂`, governs the Born sandwiches
   `P₁ P₂ P₁ = P₁(1 - Δ₂₁)` and `P₂ P₁ P₂ = P₂(1 - Δ₂₁)`, and satisfies `-[P₂, P₁]² = Δ₂₁(1 - Δ₂₁)`.
4. **$\mathcal{R}_3 \prec \mathcal{R}_4$ (Morita Signature Split & Entangled Corner Routing):**
   `Φ² = +V`, `J² = -V`, `{Φ, J} = 0`, `[Φ, J] = -2 Σ`, `-[Φ, [Φ, J]] = -4 V J`, and the entangled
   quasi-projectors `Φ_ent, Ψ_ent` route `1` into `P_left` and `S_z` into `P_right`. -/
theorem archetype_U7_representation_consequences_spinor_ideal_hadamard_halmos_morita
    (M X Y : NonCommutativeTwoStateAndModularShift.Mat2 B)
    (d1 d2 A C : B)
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2)
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : NonCommutativeTwoStateAndModularShift.racomm σx σz = 0) :
    let P_l   := NonCommutativeTwoStateAndModularShift.Mat2.P_left (B := B)
    let P_r   := NonCommutativeTwoStateAndModularShift.Mat2.P_right (B := B)
    let Ex_M  := NonCommutativeTwoStateAndModularShift.Mat2.Ex (B := B)
    let Ey_M  := NonCommutativeTwoStateAndModularShift.Mat2.Ey (B := B)
    let Ez_M  := NonCommutativeTwoStateAndModularShift.Mat2.Ez (B := B)
    let HW    := NonCommutativeTwoStateAndModularShift.Mat2.H_Walsh (B := B)
    let Δ21   := (P2 - P1) * (P2 - P1)
    let C21   := NonCommutativeTwoStateAndModularShift.rcomm P2 P1
    let Phi   := NonCommutativeTwoStateAndModularShift.Mat2.modularShift A C
    let J     := NonCommutativeTwoStateAndModularShift.Mat2.modularShift A (-C)
    let V     := NonCommutativeTwoStateAndModularShift.Mat2.localObs (A * C) (C * A)
    let Sig   := NonCommutativeTwoStateAndModularShift.Mat2.localObs (A * C) (-(C * A))
    let V4    := (V + V) + (V + V)
    let Sz    := NonCommutativeTwoStateAndModularShift.Mat2.diagScalar σz
    let Psi_e := NonCommutativeTwoStateAndModularShift.Mat2.PsiEnt σx σz
    let Phi_e := NonCommutativeTwoStateAndModularShift.Mat2.PhiEnt σx
    -- 1. R₀: Minimal left-ideal spinor reconstruction & corner homomorphism:
    M = M * P_l + (M * Ex_M * P_l) * Ex_M ∧
    P_r = Ex_M * P_l * Ex_M ∧
    (P_l * Y) * M * (X * P_l) = ⟨(Y * M * X).a11, 0, 0, 0⟩ ∧
    -- 2. R₁: Walsh–Hadamard localization–shift duality:
    HW * HW = 1 + 1 ∧
    HW * Ez_M * HW = Ex_M + Ex_M ∧
    HW * Ex_M * HW = Ez_M + Ez_M ∧
    HW * Ey_M * HW = -(Ey_M + Ey_M) ∧
    HW * NonCommutativeTwoStateAndModularShift.Mat2.localObs d1 d2 * HW =
      NonCommutativeTwoStateAndModularShift.Mat2.diagScalar (d1 + d2) +
        NonCommutativeTwoStateAndModularShift.Mat2.modularShift (d1 - d2) (d1 - d2) ∧
    -- 3. R₂: Halmos two-idempotent chordal distance & commutator law:
    NonCommutativeTwoStateAndModularShift.rcomm Δ21 P1 = 0 ∧
    NonCommutativeTwoStateAndModularShift.rcomm Δ21 P2 = 0 ∧
    P1 * P2 * P1 = P1 * (1 - Δ21) ∧
    P2 * P1 * P2 = P2 * (1 - Δ21) ∧
    -(C21 * C21) = Δ21 * (1 - Δ21) ∧
    -- 4. R₃ ≺ R₄: Morita signature split (+V vs. -V) & entangled corner routing:
    Phi * Phi = V ∧
    J * J = -V ∧
    NonCommutativeTwoStateAndModularShift.racomm Phi J = 0 ∧
    NonCommutativeTwoStateAndModularShift.rcomm Phi J = -(Sig + Sig) ∧
    -NonCommutativeTwoStateAndModularShift.rcomm Phi
      (NonCommutativeTwoStateAndModularShift.rcomm Phi J) = -(V4 * J) ∧
    Phi_e * P_l * Psi_e         = Phi_e * Psi_e ∧
    Phi_e * P_r * Psi_e         = 0 ∧
    Phi_e * (P_l * Sz) * Psi_e  = 0 ∧
    Phi_e * (P_r * Sz) * Psi_e  = Phi_e * Psi_e := by
  have hR0 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_R0_minimal_ideal_spinor_reconstruction_and_corner_homomorphism M X Y
  have hR1 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_R1_walsh_hadamard_localization_shift_duality d1 d2
  have hR2 :=
    NonCommutativeTwoStateAndModularShift.archetype_R2_halmos_two_idempotent_trigonometry_and_commutator hP1 hP2
  have hR34 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_R3_R4_morita_signature_split_and_entangled_routing hx hz hxz A C
  exact ⟨hR0.1, hR0.2.1, hR0.2.2,
         hR1.1, hR1.2.1, hR1.2.2.1, hR1.2.2.2.1, hR1.2.2.2.2,
         hR2.1, hR2.2.1, hR2.2.2.1, hR2.2.2.2.1, hR2.2.2.2.2,
         hR34.1, hR34.2.1, hR34.2.2.1, hR34.2.2.2.1, hR34.2.2.2.2.1,
         hR34.2.2.2.2.2.1, hR34.2.2.2.2.2.2.1, hR34.2.2.2.2.2.2.2.1, hR34.2.2.2.2.2.2.2.2⟩

-- ============================================================================
-- 9. MASTER LITERATURE COMPARISON POSET L₀ ≺ L₁ ≺ L₂ ≺ L₃ ≺ L₄
-- ============================================================================

/-- **Lineage $\mathcal{L}_1$ (`lineage_L1_cartan_chevalley_riesz_witt_and_jordan_triple`):**
Unifies Cartan (1913), Chevalley (1954), and Riesz (1958) over ANY non-commutative `[Ring B]`:
1. `rieszDotPoly` is a skew-derivation of `NonCommutativeBimetricSheetGeometry.Mat2 B`.
2. On the Chevalley–Witt nilpotents `(wittB_dag, wittB)`, `rieszDotPoly wittB_dag wittB = 1`
   (CAR anticommutator) and `rieszWedgePoly wittB_dag wittB = Ez` (Cartan grading).
3. Twisted Pin reflection across `matPhi A C` acts on `matPhi W Z` as the negative Jordan Pair
   Triple Product `-matPhi (A * Z * A) (C * W * C)`. -/
theorem lineage_L1_cartan_chevalley_riesz_witt_and_jordan_triple
    (X M N : NonCommutativeBimetricSheetGeometry.Mat2 B) (A C W Z : B) :
    rieszDotPoly X (M * N) = rieszDotPoly X M * N + polyParity M * rieszDotPoly X N ∧
    rieszDotPoly (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) wittB = 1 ∧
    rieszWedgePoly (wittB_dag : NonCommutativeBimetricSheetGeometry.Mat2 B) wittB =
      NonCommutativeBimetricSheetGeometry.Mat2.Ez (B := B) ∧
    pinReflect (NonCommutativeBimetricSheetGeometry.Mat2.matPhi A C)
      (NonCommutativeBimetricSheetGeometry.Mat2.matPhi W Z) =
      -NonCommutativeBimetricSheetGeometry.Mat2.matPhi (A * Z * A) (C * W * C) := by
  have hU12 :=
    archetype_U1_U2_polyform_riesz_and_pin_jordan_triple_product X X M N A C W Z A C
  exact ⟨hU12.2.2.2.2.2.2.2.1, hU12.2.2.2.2.2.2.2.2.2.1,
         hU12.2.2.2.2.2.2.2.2.2.2.1, hU12.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Entrywise `ℕ`-scalar multiplication on `NonCommutativeBimetricSheetGeometry.Mat2 R`. -/
@[simp] def nsmulBimetric {R : Type u} [Ring R] (n : ℕ)
    (M : NonCommutativeBimetricSheetGeometry.Mat2 R) :
    NonCommutativeBimetricSheetGeometry.Mat2 R :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

/-- Entrywise `ℤ`-scalar multiplication on `NonCommutativeBimetricSheetGeometry.Mat2 R`. -/
@[simp] def zsmulBimetric {R : Type u} [Ring R] (n : ℤ)
    (M : NonCommutativeBimetricSheetGeometry.Mat2 R) :
    NonCommutativeBimetricSheetGeometry.Mat2 R :=
  ⟨n • M.a11, n • M.a12, n • M.a21, n • M.a22⟩

set_option linter.unusedSimpArgs false

macro "bimetric_nc_mat" : tactic =>
  `(tactic| (
    (try ext) <;>
    · (try simp only [NonCommutativeBimetricSheetGeometry.Mat2.zero_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.zero_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.zero_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.zero_a22,
                      NonCommutativeBimetricSheetGeometry.Mat2.one_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.one_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.one_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.one_a22,
                      NonCommutativeBimetricSheetGeometry.Mat2.add_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.add_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.add_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.add_a22,
                      NonCommutativeBimetricSheetGeometry.Mat2.neg_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.neg_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.neg_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.neg_a22,
                      NonCommutativeBimetricSheetGeometry.Mat2.sub_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.sub_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.sub_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.sub_a22,
                      NonCommutativeBimetricSheetGeometry.Mat2.mul_a11,
                      NonCommutativeBimetricSheetGeometry.Mat2.mul_a12,
                      NonCommutativeBimetricSheetGeometry.Mat2.mul_a21,
                      NonCommutativeBimetricSheetGeometry.Mat2.mul_a22,
                      mul_zero, zero_mul, mul_one, one_mul,
                      add_zero, zero_add, sub_zero, zero_sub, neg_zero])
      (try simp only [mul_add, add_mul, sub_mul, mul_sub,
                      mul_zero, zero_mul, mul_one, one_mul,
                      add_zero, zero_add, sub_zero, zero_sub,
                      neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                      mul_assoc])
      (try abel)))

/-- Associative unital `Ring` instance on `NonCommutativeBimetricSheetGeometry.Mat2 R` for any `[Ring R]`,
enabling recursive matrix towers `Mat2 (Mat2 B)` and `Bott3 B = Mat2 (Mat2 (Mat2 B))`. -/
instance instRingBimetricMat2 {R : Type u} [Ring R] :
    Ring (NonCommutativeBimetricSheetGeometry.Mat2 R) where
  add := NonCommutativeBimetricSheetGeometry.Mat2.add
  add_assoc := by intros; ext <;> exact add_assoc _ _ _
  zero := NonCommutativeBimetricSheetGeometry.Mat2.zero
  zero_add := by intros; ext <;> exact zero_add _
  add_zero := by intros; ext <;> exact add_zero _
  nsmul := nsmulBimetric
  nsmul_zero := by intros; ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ := by intros; ext <;> exact AddMonoid.nsmul_succ _ _
  neg := NonCommutativeBimetricSheetGeometry.Mat2.neg
  sub := NonCommutativeBimetricSheetGeometry.Mat2.sub
  sub_eq_add_neg := by intros; ext <;> exact sub_eq_add_neg _ _
  zsmul := zsmulBimetric
  zsmul_zero' := by intros; ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg_add_cancel := by intros; ext <;> exact neg_add_cancel _
  add_comm := by intros; ext <;> exact add_comm _ _
  mul := NonCommutativeBimetricSheetGeometry.Mat2.mul
  left_distrib := by
    intros a b c; ext <;>
    · change _ * (_ + _) + _ * (_ + _) = (_ * _ + _ * _) + (_ * _ + _ * _)
      simp only [mul_add]
      abel
  right_distrib := by
    intros a b c; ext <;>
    · change (_ + _) * _ + (_ + _) * _ = (_ * _ + _ * _) + (_ * _ + _ * _)
      simp only [add_mul]
      abel
  zero_mul := by
    intros a; ext <;>
    · change 0 * _ + 0 * _ = 0
      simp only [zero_mul, add_zero]
  mul_zero := by
    intros a; ext <;>
    · change _ * 0 + _ * 0 = 0
      simp only [mul_zero, add_zero]
  mul_assoc := by
    intros a b c; ext <;>
    · change (_ * _ + _ * _) * _ + (_ * _ + _ * _) * _ =
        _ * (_ * _ + _ * _) + _ * (_ * _ + _ * _)
      simp only [mul_add, add_mul, mul_assoc]
      abel
  one := NonCommutativeBimetricSheetGeometry.Mat2.one
  one_mul := by
    intros a; ext
    · change 1 * _ + 0 * _ = _; simp only [one_mul, zero_mul, add_zero]
    · change 1 * _ + 0 * _ = _; simp only [one_mul, zero_mul, add_zero]
    · change 0 * _ + 1 * _ = _; simp only [one_mul, zero_mul, zero_add]
    · change 0 * _ + 1 * _ = _; simp only [one_mul, zero_mul, zero_add]
  mul_one := by
    intros a; ext
    · change _ * 1 + _ * 0 = _; simp only [mul_one, mul_zero, add_zero]
    · change _ * 0 + _ * 1 = _; simp only [mul_one, mul_zero, zero_add]
    · change _ * 1 + _ * 0 = _; simp only [mul_one, mul_zero, add_zero]
    · change _ * 0 + _ * 1 = _; simp only [mul_one, mul_zero, zero_add]

/-- Bosonic permanent adjugate `adjBose(M) = [[m₂₂, m₁₂], [m₂₁, m₁₁]]`. -/
@[simp] def adjBose (M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨M.a22, M.a12, M.a21, M.a11⟩

/-- Left fermionic determinant `detFermiL(M) = m₁₁ m₂₂ - m₁₂ m₂₁`. -/
@[simp] def detFermiL (M : NonCommutativeBimetricSheetGeometry.Mat2 B) : B :=
  M.a11 * M.a22 - M.a12 * M.a21

/-- Right fermionic determinant `detFermiR(M) = m₂₂ m₁₁ - m₂₁ m₁₂`. -/
@[simp] def detFermiR (M : NonCommutativeBimetricSheetGeometry.Mat2 B) : B :=
  M.a22 * M.a11 - M.a21 * M.a12

/-- Left bosonic permanent `permBoseL(M) = m₁₁ m₂₂ + m₁₂ m₂₁`. -/
@[simp] def permBoseL (M : NonCommutativeBimetricSheetGeometry.Mat2 B) : B :=
  M.a11 * M.a22 + M.a12 * M.a21

/-- Right bosonic permanent `permBoseR(M) = m₂₂ m₁₁ + m₂₁ m₁₂`. -/
@[simp] def permBoseR (M : NonCommutativeBimetricSheetGeometry.Mat2 B) : B :=
  M.a22 * M.a11 + M.a21 * M.a12

/-- Upper-left matrix unit `wittE00 = [[1, 0], [0, 0]]`. -/
@[simp] def wittE00 : NonCommutativeBimetricSheetGeometry.Mat2 B := ⟨1, 0, 0, 0⟩

/-- Lower-right matrix unit `wittE11 = [[0, 0], [0, 1]]`. -/
@[simp] def wittE11 : NonCommutativeBimetricSheetGeometry.Mat2 B := ⟨0, 0, 0, 1⟩

/-- 4D tensor-factor swap `P_swap` in `Mat2 (Mat2 B)`. -/
@[simp] def P_swap :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  ⟨wittE00, wittB, wittB_dag, wittE11⟩

/-- 4D antisymmetrizer `SigmaMinus = 1 - P_swap` in `Mat2 (Mat2 B)`. -/
@[simp] def SigmaMinus :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  1 - P_swap

/-- Outer tensor lift `headLift(A)` into `Mat2 (Mat2 B)`. -/
@[simp] def headLift (A : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  ⟨NonCommutativeBimetricSheetGeometry.Mat2.diagScalar A.a11,
   NonCommutativeBimetricSheetGeometry.Mat2.diagScalar A.a12,
   NonCommutativeBimetricSheetGeometry.Mat2.diagScalar A.a21,
   NonCommutativeBimetricSheetGeometry.Mat2.diagScalar A.a22⟩

/-- Inner tensor lift `innerLift(M) = [[M, 0], [0, M]]` into `Mat2 (Mat2 B)`. -/
@[simp] def innerLift (M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  ⟨M, 0, 0, M⟩

/-- Non-commutative Kronecker product `ncKron(A, M) = headLift A * innerLift M`. -/
@[simp] def ncKron (A M : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  headLift A * innerLift M

/-- 4D trace `tr4(X) = tr2 X.a11 + tr2 X.a22`. -/
@[simp] def tr4
    (X : NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B)) : B :=
  NonCommutativeBimetricSheetGeometry.Mat2.tr2 X.a11 +
    NonCommutativeBimetricSheetGeometry.Mat2.tr2 X.a22

/-- **Lineage $\mathcal{L}_2$ (`lineage_L2_dieudonne_manin_verejones_alpha_adjugate_and_newton_trace`):**
Unifies Dieudonné (1943), Manin (1988), Vere-Jones (1988), and Gelfand–Retakh (1991) over `[Ring B]`:
1. `M * adj M` isolates the Manin row-commutators `-[a, b]` and `[c, d]` around `(detFermiL, detFermiR)`.
2. `M * adjBose M` isolates the Jordan anticommutators `{a, b}` and `{c, d}` around `(permBoseL, permBoseR)`.
3. The 4D antisymmetric Schur–Weyl trace `tr4 (ncKron A A * SigmaMinus)` equals
   `(tr2 A)² - tr2 (A²) = detFermiL A + detFermiR A`. -/
theorem lineage_L2_dieudonne_manin_verejones_alpha_adjugate_and_newton_trace
    (M A : NonCommutativeBimetricSheetGeometry.Mat2 B) :
    M * NonCommutativeBimetricSheetGeometry.Mat2.adj M =
      ⟨detFermiL M, -NonCommutativeBimetricSheetGeometry.rcomm M.a11 M.a12,
       NonCommutativeBimetricSheetGeometry.rcomm M.a21 M.a22, detFermiR M⟩ ∧
    M * adjBose M =
      ⟨permBoseL M, NonCommutativeBimetricSheetGeometry.racomm M.a11 M.a12,
       NonCommutativeBimetricSheetGeometry.racomm M.a21 M.a22, permBoseR M⟩ ∧
    tr4 (ncKron A A * SigmaMinus) = detFermiL A + detFermiR A ∧
    NonCommutativeBimetricSheetGeometry.Mat2.tr2 A *
        NonCommutativeBimetricSheetGeometry.Mat2.tr2 A -
      NonCommutativeBimetricSheetGeometry.Mat2.tr2 (A * A) =
      detFermiL A + detFermiR A := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [NonCommutativeBimetricSheetGeometry.Mat2.adj, adjBose,
               detFermiL, detFermiR, permBoseL, permBoseR,
               tr4, NonCommutativeBimetricSheetGeometry.Mat2.tr2,
               ncKron, headLift, innerLift, SigmaMinus, P_swap,
               NonCommutativeBimetricSheetGeometry.Mat2.diagScalar,
               wittE00, wittE11, wittB, wittB_dag,
               NonCommutativeBimetricSheetGeometry.rcomm,
               NonCommutativeBimetricSheetGeometry.racomm]
    bimetric_nc_mat

/-- 8D recursive matrix carrier `Bott3 B = Mat2 (Mat2 (Mat2 B))`. -/
abbrev Bott3 (B : Type u) :=
  NonCommutativeBimetricSheetGeometry.Mat2
    (NonCommutativeBimetricSheetGeometry.Mat2
      (NonCommutativeBimetricSheetGeometry.Mat2 B))

/-- 4D scalar diagonal matrix `diag4(c)`. -/
@[simp] def diag4 (c : B) :
    NonCommutativeBimetricSheetGeometry.Mat2 (NonCommutativeBimetricSheetGeometry.Mat2 B) :=
  ⟨NonCommutativeBimetricSheetGeometry.Mat2.diagScalar c, 0, 0,
   NonCommutativeBimetricSheetGeometry.Mat2.diagScalar c⟩

/-- 8D scalar diagonal matrix `diag8(c)`. -/
@[simp] def diag8 (c : B) : Bott3 B := ⟨diag4 c, 0, 0, diag4 c⟩

/-- Adjacent transposition `P₁₂ = (12)` in `Bott3 B`. -/
@[simp] def P12 : Bott3 B := ⟨wittE00, wittB, wittB_dag, wittE11⟩

/-- Adjacent transposition `P₂₃ = (23)` in `Bott3 B`. -/
@[simp] def P23 : Bott3 B := ⟨P_swap, 0, 0, P_swap⟩

/-- Non-adjacent transposition `P₁₃ = P₁₂ * P₂₃ * P₁₂ = (13)` in `Bott3 B`. -/
@[simp] def P13 : Bott3 B := P12 * P23 * P12

/-- 3-cycle `C₁₂₃ = P₁₂ * P₂₃` in `Bott3 B`. -/
@[simp] def C123 : Bott3 B := P12 * P23

/-- Inverse 3-cycle `C₁₃₂ = P₂₃ * P₁₂` in `Bott3 B`. -/
@[simp] def C132 : Bott3 B := P23 * P12

/-- Second Jucys–Murphy element `JM₂ = P₁₂` in `Bott3 B`. -/
@[simp] def JM2 : Bott3 B := P12

/-- Third Jucys–Murphy element `JM₃ = P₁₃ + P₂₃` in `Bott3 B`. -/
@[simp] def JM3 : Bott3 B := P13 + P23

/-- Alternating Young antisymmetrizer `SigmaAlt3 = 1 + C₁₂₃ + C₁₃₂ - P₁₂ - P₂₃ - P₁₃`. -/
@[simp] def SigmaAlt3 : Bott3 B := 1 + C123 + C132 - P12 - P23 - P13

/-- 2D standard representation hook projector `SigmaStd3 = 4•1 - 2 C₁₂₃ - 2 C₁₃₂`. -/
@[simp] def SigmaStd3 : Bott3 B := (1 + 1 + 1 + 1) - (C123 + C123) - (C132 + C132)

/-- Coxeter commutator `J_S3 = [P₁₂, P₂₃]` in `Bott3 B`. -/
@[simp] def J_S3 : Bott3 B := NonCommutativeBimetricSheetGeometry.rcomm P12 P23

/-- Yang R-matrix `R₁₂(u) = diag₈(u) + P₁₂`. -/
@[simp] def R12 (u : B) : Bott3 B := diag8 u + P12

/-- Yang R-matrix `R₂₃(v) = diag₈(v) + P₂₃`. -/
@[simp] def R23 (v : B) : Bott3 B := diag8 v + P23

/-- Yang R-matrix `R₁₃(w) = diag₈(w) + P₁₃`. -/
@[simp] def R13 (w : B) : Bott3 B := diag8 w + P13

/-- Explicit block evaluation of `C₁₂₃ = P₁₂ * P₂₃` in `Bott3 B`. -/
lemma C123_eq :
    (C123 : Bott3 B) =
      ⟨⟨wittE00, wittB, 0, 0⟩, ⟨0, 0, wittE00, wittB⟩,
       ⟨wittB_dag, wittE11, 0, 0⟩, ⟨0, 0, wittB_dag, wittE11⟩⟩ := by
  dsimp only [C123, P12, P23, P_swap, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Explicit block evaluation of `C₁₃₂ = P₂₃ * P₁₂` in `Bott3 B`. -/
lemma C132_eq :
    (C132 : Bott3 B) =
      ⟨⟨wittE00, 0, wittB_dag, 0⟩, ⟨wittB, 0, wittE11, 0⟩,
       ⟨0, wittE00, 0, wittB_dag⟩, ⟨0, wittB, 0, wittE11⟩⟩ := by
  dsimp only [C132, P12, P23, P_swap, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Explicit block evaluation of `P₁₃ = P₁₂ * P₂₃ * P₁₂` in `Bott3 B`. -/
lemma P13_eq :
    (P13 : Bott3 B) =
      ⟨innerLift wittE00, innerLift wittB, innerLift wittB_dag, innerLift wittE11⟩ := by
  change C123 * P12 = _
  rw [C123_eq]
  dsimp only [P12, innerLift, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Jucys–Murphy commutativity `[JM₂, JM₃] = 0` in `Bott3 B`. -/
lemma l3_jm_comm :
    NonCommutativeBimetricSheetGeometry.rcomm (JM2 : Bott3 B) JM3 = 0 := by
  dsimp only [JM2, JM3, NonCommutativeBimetricSheetGeometry.rcomm]
  rw [P13_eq]
  dsimp only [P12, P23, P_swap, innerLift, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Jucys–Murphy factorization `(1 - JM₂)(1 - JM₃) = SigmaAlt3` in `Bott3 B`. -/
lemma l3_jm_factor :
    (1 - (JM2 : Bott3 B)) * (1 - JM3) = SigmaAlt3 := by
  dsimp only [JM2, JM3, SigmaAlt3]
  rw [P13_eq, C123_eq, C132_eq]
  dsimp only [P12, P23, P_swap, innerLift, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Procesi–Razmyslov rank-2 vanishing `SigmaAlt3 = 0` in `Bott3 B`. -/
lemma l3_sigmaAlt3_eq_zero :
    (SigmaAlt3 : Bott3 B) = 0 := by
  dsimp only [SigmaAlt3]
  rw [P13_eq, C123_eq, C132_eq]
  dsimp only [P12, P23, P_swap, innerLift, wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Coxeter commutator generation of the 2D Standard Immanant `2 J_S3² = -SigmaStd3` in `Bott3 B`. -/
lemma l3_coxeter_sq :
    (J_S3 : Bott3 B) * J_S3 + J_S3 * J_S3 = -SigmaStd3 := by
  have hJ : (J_S3 : Bott3 B) = C123 - C132 := Eq.refl _
  rw [hJ]
  dsimp only [SigmaStd3]
  rw [C123_eq, C132_eq]
  dsimp only [wittE00, wittE11, wittB, wittB_dag]
  bimetric_nc_mat

/-- Universal Non-Commutative Yang–Baxter Anomaly in `Bott3 B` for non-commuting `u, v ∈ B`. -/
lemma l3_ybe_anomaly (u v : B) :
    R12 u * R13 (u + v) * R23 v - R23 v * R13 (u + v) * R12 u =
      diag8 (NonCommutativeBimetricSheetGeometry.racomm (u + v)
        (NonCommutativeBimetricSheetGeometry.rcomm u v)) +
      diag8 (NonCommutativeBimetricSheetGeometry.rcomm u v) * (JM2 + JM3) := by
  dsimp only [R12, R23, R13, JM2, JM3]
  rw [P13_eq]
  dsimp only [P12, P23, P_swap, innerLift, diag8, diag4,
              NonCommutativeBimetricSheetGeometry.Mat2.diagScalar,
              wittE00, wittE11, wittB, wittB_dag,
              NonCommutativeBimetricSheetGeometry.rcomm,
              NonCommutativeBimetricSheetGeometry.racomm]
  bimetric_nc_mat

/-- **Lineage $\mathcal{L}_3$ (`lineage_L3_procesi_razmyslov_jucys_murphy_cherednik_and_ybe_anomaly`):**
Unifies Jucys (1974), Razmyslov (1974), Procesi (1976), Murphy (1981), and Cherednik (1986)
in `Bott3 B` over `[Ring B]`:
1. Jucys–Murphy commutativity `[JM₂, JM₃] = 0` and factorization `(1 - JM₂)(1 - JM₃) = SigmaAlt3 = 0`.
2. Coxeter commutator generation of the 2D Standard Immanant: `2 [P₁₂, P₂₃]² = -SigmaStd3`.
3. Universal Non-Commutative Yang–Baxter Anomaly for non-commuting `u, v ∈ B`:
   `R₁₂(u) R₁₃(u+v) R₂₃(v) - R₂₃(v) R₁₃(u+v) R₁₂(u) = diag₈({u+v, [u,v]}) + diag₈([u,v])(JM₂ + JM₃)`. -/
theorem lineage_L3_procesi_razmyslov_jucys_murphy_cherednik_and_ybe_anomaly
    (u v : B) :
    NonCommutativeBimetricSheetGeometry.rcomm (JM2 : Bott3 B) JM3 = 0 ∧
    (1 - (JM2 : Bott3 B)) * (1 - JM3) = SigmaAlt3 ∧
    (1 - (JM2 : Bott3 B)) * (1 - JM3) = 0 ∧
    (J_S3 : Bott3 B) * J_S3 + J_S3 * J_S3 = -SigmaStd3 ∧
    R12 u * R13 (u + v) * R23 v - R23 v * R13 (u + v) * R12 u =
      diag8 (NonCommutativeBimetricSheetGeometry.racomm (u + v)
        (NonCommutativeBimetricSheetGeometry.rcomm u v)) +
      diag8 (NonCommutativeBimetricSheetGeometry.rcomm u v) * (JM2 + JM3) := by
  refine ⟨l3_jm_comm, l3_jm_factor, ?_, l3_coxeter_sq, l3_ybe_anomaly u v⟩
  rw [l3_jm_factor, l3_sigmaAlt3_eq_zero]

/-- **Archetype $\mathcal{U}_8$ (`archetype_U8_master_literature_comparison_poset_L0_to_L4`):**
Unites the entire Master Literature Comparison Poset ($\mathcal{L}_0 \prec \mathcal{L}_1 \prec \mathcal{L}_2 \prec \mathcal{L}_3 \prec \mathcal{L}_4$)
over ANY non-commutative associative ring `[Ring B]`:
1. **$\mathcal{L}_0$ (Jordan–Dixmier–Davis–Halmos Dihedral Pair):**
   For any idempotents `P₁² = P₁` and `P₂² = P₂`, `D = P₂ - P₁` and `Σ = P₁ + P₂ - 1` satisfy
   `{D, Σ} = 0`, `D² + Σ² = 1`, `D * Σ = [P₂, P₁]`, and `P₁ * P₂ * P₁ = P₁ * Σ² = P₁ * (1 - D²)`.
2. **$\mathcal{L}_1$ (Cartan–Chevalley–Riesz Skew-Derivation & Jordan Triple):**
   `rieszDotPoly X (M * N) = rieszDotPoly X M * N + polyParity M * rieszDotPoly X N` and
   `pinReflect (matPhi A C) (matPhi W Z) = -matPhi (A * Z * A) (C * W * C)`.
3. **$\mathcal{L}_2$ (Dieudonné–Manin–Vere-Jones $\alpha$-Adjugate & 4D Newton Trace):**
   `tr4 (ncKron A_mat A_mat * SigmaMinus) = detFermiL A_mat + detFermiR A_mat = (tr2 A_mat)² - tr2 (A_mat²)`.
4. **$\mathcal{L}_3$ (Procesi–Razmyslov–Jucys–Murphy Factorization & Non-Commutative YBE Anomaly):**
   `(1 - JM₂)(1 - JM₃) = 0`, `2 J_S3² = -SigmaStd3`, and
   `R₁₂(u) R₁₃(u+v) R₂₃(v) - R₂₃(v) R₁₃(u+v) R₁₂(u) = diag₈({u+v, [u,v]}) + diag₈([u,v])(JM₂ + JM₃)`.
5. **$\mathcal{L}_4$ (Kirkwood–Dirac–Widom–Aharonov Trace Marginalization & Toeplitz–Hankel Cancellation):**
   `tr2 (Q₂ * K * Q₁) + tr2 ((1 - Q₂) * K * Q₁) = tr2 (K * Q₁)` and
   `(Φ_e * P_left * Φ_e) * (Φ_e * (P_right * Sz) * Ψ_e) + (Φ_e * P_left * Φ_comp) * (Φ_comp * (P_right * Sz) * Ψ_e) = 0`. -/
theorem archetype_U8_master_literature_comparison_poset_L0_to_L4
    {P1 P2 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2)
    (X M N A_mat : NonCommutativeBimetricSheetGeometry.Mat2 B)
    (A C W Z u v : B)
    {σx σz : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : NonCommutativeTwoStateAndModularShift.racomm σx σz = 0)
    (Q2 Q1 K : NonCommutativeTwoStateAndModularShift.Mat2 B) :
    let D      := P2 - P1
    let Sig_d  := P1 + P2 - 1
    let P_l    := NonCommutativeTwoStateAndModularShift.Mat2.P_left (B := B)
    let P_r    := NonCommutativeTwoStateAndModularShift.Mat2.P_right (B := B)
    let Sz     := NonCommutativeTwoStateAndModularShift.Mat2.diagScalar σz
    let Ψ_e    := NonCommutativeTwoStateAndModularShift.Mat2.PsiEnt σx σz
    let Φ_e    := NonCommutativeTwoStateAndModularShift.Mat2.PhiEnt σx
    let Φ_comp := (1 + 1 + 1 + 1 : NonCommutativeTwoStateAndModularShift.Mat2 B) - Φ_e
    -- 1. L₀: Dihedral pair anticommutation & Pythagorean identity:
    NonCommutativeTwoStateAndModularShift.racomm D Sig_d = 0 ∧
    D * D + Sig_d * Sig_d = 1 ∧
    D * Sig_d = NonCommutativeTwoStateAndModularShift.rcomm P2 P1 ∧
    -- 2. L₁: Riesz skew-derivation & Jordan pair triple product:
    rieszDotPoly X (M * N) = rieszDotPoly X M * N + polyParity M * rieszDotPoly X N ∧
    pinReflect (NonCommutativeBimetricSheetGeometry.Mat2.matPhi A C)
      (NonCommutativeBimetricSheetGeometry.Mat2.matPhi W Z) =
      -NonCommutativeBimetricSheetGeometry.Mat2.matPhi (A * Z * A) (C * W * C) ∧
    -- 3. L₂: 4D Schur–Weyl antisymmetric trace & Newton identity:
    tr4 (ncKron A_mat A_mat * SigmaMinus) = detFermiL A_mat + detFermiR A_mat ∧
    -- 4. L₃: Jucys–Murphy factorization, Standard Immanant & Non-Commutative YBE Anomaly:
    (1 - (JM2 : Bott3 B)) * (1 - JM3) = 0 ∧
    (J_S3 : Bott3 B) * J_S3 + J_S3 * J_S3 = -SigmaStd3 ∧
    R12 u * R13 (u + v) * R23 v - R23 v * R13 (u + v) * R12 u =
      diag8 (NonCommutativeBimetricSheetGeometry.racomm (u + v)
        (NonCommutativeBimetricSheetGeometry.rcomm u v)) +
      diag8 (NonCommutativeBimetricSheetGeometry.rcomm u v) * (JM2 + JM3) ∧
    -- 5. L₄: Kirkwood–Dirac trace marginalization & Widom Toeplitz–Hankel cancellation:
    NonCommutativeTwoStateAndModularShift.Mat2.tr2 (Q2 * K * Q1) +
      NonCommutativeTwoStateAndModularShift.Mat2.tr2 ((1 - Q2) * K * Q1) =
      NonCommutativeTwoStateAndModularShift.Mat2.tr2 (K * Q1) ∧
    (Φ_e * P_l * Φ_e) * (Φ_e * (P_r * Sz) * Ψ_e) +
      (Φ_e * P_l * Φ_comp) * (Φ_comp * (P_r * Sz) * Ψ_e) = 0 := by
  have hL0 :=
    NonCommutativeTwoStateAndModularShift.lineage_L0_jordan_dixmier_davis_halmos_dihedral_two_idempotent_theorem hP1 hP2
  have hL1 :=
    lineage_L1_cartan_chevalley_riesz_witt_and_jordan_triple X M N A C W Z
  have hL2 :=
    lineage_L2_dieudonne_manin_verejones_alpha_adjugate_and_newton_trace M A_mat
  have hL3 :=
    lineage_L3_procesi_razmyslov_jucys_murphy_cherednik_and_ybe_anomaly u v
  have hL4 :=
    NonCommutativeTwoStateAndModularShift.Mat2.lineage_L4_widom_kirkwood_dirac_aharonov_toeplitz_hankel_decoupling hx hz hxz Q2 Q1 K
  exact ⟨hL0.2.2.1, hL0.2.2.2.2.1, hL0.1,
         hL1.1, hL1.2.2.2,
         hL2.2.2.1,
         hL3.2.2.1, hL3.2.2.2.1, hL3.2.2.2.2,
         hL4.1, hL4.2.2.2.2.2⟩

-- ============================================================================
-- 10. THREE-IDEMPOTENT BARGMANN–WIDOM–NAMBU UNIFICATION POSET N₀ ≺ ... ≺ N₄
-- ============================================================================

/-- **Archetype $\mathcal{U}_9$ (`archetype_U9_bargmann_widom_nambu_three_idempotent_poset_N0_to_N4`):**
Unites the Three-Idempotent Bargmann–Widom–Nambu Poset ($\mathcal{N}_0 \prec \mathcal{N}_1 \prec \mathcal{N}_2 \prec \mathcal{N}_3 \prec \mathcal{N}_4$)
with the Bimetric Sheet Geometry over ANY non-commutative associative ring `[Ring B]`:
1. **$\mathcal{N}_0$ (Operator Double-Angle Euler Formula):**
   `S₁ * S₂ = (1 - 2 D₁₂²) + 2 [P₁, P₂]`, `{S₁, S₂} = 2(1 - 2 D₁₂²)`, and `[S₁, S₂] = 4 [P₁, P₂]`.
2. **$\mathcal{N}_1$ (Orthogonal Channel Splitting & Widom Hankel Excursion):**
   `Σ₁₂ * Σ₂₃ = P₁ P₂ P₃ + (1 - P₁)(1 - P₂)(1 - P₃)` and `P₁ (Σ₁₃ - Σ₁₂ * Σ₂₃) P₃ = P₁ (1 - P₂) P₃`.
3. **$\mathcal{N}_2$ (3-Step Bargmann Holonomy & Linear Jordan Reduction):**
   `B₁₂₃ = P₁ P₂ P₃ P₁ - (1 - P₁)(1 - P₂)(1 - P₃)(1 - P₁)`, `[B₁₂₃, P₁] = 0`, and
   `B₁₂₃ - B₁₃₂ = {P₁, [P₂, P₃]} - [P₂, P₃]`.
4. **$\mathcal{N}_3$ (The Bargmann–Nambu Theorem):**
   `(B₁₂₃ - B₁₃₂) + (B₂₃₁ - B₂₁₃) + (B₃₁₂ - B₃₂₁) + [D₁₂, D₂₃] = 2 [P₁, P₂, P₃]_Nambu`.
5. **$\mathcal{N}_4$ (Division-Free Idempotent Triangle Realizing Bimetric `matSig` and `matV`):**
   In `Mat2 B`, `P₁ = idem1, P₂ = idem2 a, P₃ = idem3 c` satisfy
   `toBimetricMat2 (B₁₂₃ + B₁₃₂) = matSig a c` and `toBimetricMat2 (B₁₂₃ - B₁₃₂) = matV a c`. -/
theorem archetype_U9_bargmann_widom_nambu_three_idempotent_poset_N0_to_N4
    {P1 P2 P3 : B} (hP1 : P1 * P1 = P1) (hP2 : P2 * P2 = P2) (hP3 : P3 * P3 = P3)
    (a c : B) :
    let Sig12 := NonCommutativeTwoStateAndModularShift.Mat2.davisSigma P1 P2
    let Sig23 := NonCommutativeTwoStateAndModularShift.Mat2.davisSigma P2 P3
    let Sig13 := NonCommutativeTwoStateAndModularShift.Mat2.davisSigma P1 P3
    let D12   := NonCommutativeTwoStateAndModularShift.Mat2.davisDiff P1 P2
    let D23   := NonCommutativeTwoStateAndModularShift.Mat2.davisDiff P2 P3
    let S1    := NonCommutativeTwoStateAndModularShift.Mat2.cartanS P1
    let S2    := NonCommutativeTwoStateAndModularShift.Mat2.cartanS P2
    let C12   := NonCommutativeTwoStateAndModularShift.rcomm P1 P2
    let B123  := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1 P2 P3
    let B132  := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1 P3 P2
    let Om1   := B123 - B132
    let Om2   := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P2 P3 P1 -
                 NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P2 P1 P3
    let Om3   := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P3 P1 P2 -
                 NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P3 P2 P1
    let N123  := NonCommutativeTwoStateAndModularShift.Mat2.nambu3 P1 P2 P3
    let P1_m  := (NonCommutativeTwoStateAndModularShift.Mat2.idem1 :
                   NonCommutativeTwoStateAndModularShift.Mat2 B)
    let P2_m  := NonCommutativeTwoStateAndModularShift.Mat2.idem2 a
    let P3_m  := NonCommutativeTwoStateAndModularShift.Mat2.idem3 c
    let Bm123 := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1_m P2_m P3_m
    let Bm132 := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1_m P3_m P2_m
    -- 1. N₀: Operator Euler Double-Angle Formula:
    S1 * S2 = (1 - (D12 * D12 + D12 * D12)) + (C12 + C12) ∧
    NonCommutativeTwoStateAndModularShift.rcomm S1 S2 = C12 + C12 + C12 + C12 ∧
    -- 2. N₁: Two-step Davis reflection splitting & Widom Hankel excursion:
    Sig12 * Sig23 = P1 * P2 * P3 + (1 - P1) * (1 - P2) * (1 - P3) ∧
    P1 * (Sig13 - Sig12 * Sig23) * P3 = P1 * (1 - P2) * P3 ∧
    -- 3. N₂: 3-step Bargmann holonomy decomposition, centrality & linear Jordan reduction:
    B123 = P1 * P2 * P3 * P1 - (1 - P1) * (1 - P2) * (1 - P3) * (1 - P1) ∧
    NonCommutativeTwoStateAndModularShift.rcomm B123 P1 = 0 ∧
    B123 - B132 = NonCommutativeTwoStateAndModularShift.racomm P1
      (NonCommutativeTwoStateAndModularShift.rcomm P2 P3) -
      NonCommutativeTwoStateAndModularShift.rcomm P2 P3 ∧
    -- 4. N₃: The Bargmann–Nambu Theorem:
    (Om1 + Om2 + Om3) + NonCommutativeTwoStateAndModularShift.rcomm D12 D23 = N123 + N123 ∧
    -- 5. N₄: Division-free idempotent triangle realizing bimetric `matSig` and `matV`:
    NonCommutativeTwoStateAndModularShift.Mat2.toBimetricMat2 (Bm123 + Bm132) =
      NonCommutativeBimetricSheetGeometry.Mat2.matSig a c ∧
    NonCommutativeTwoStateAndModularShift.Mat2.toBimetricMat2 (Bm123 - Bm132) =
      NonCommutativeBimetricSheetGeometry.Mat2.matV a c := by
  have hN0 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_N0_operator_double_angle_euler_identities hP1 hP2
  have hN1 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_N1_two_step_davis_reflection_and_widom_hankel_split hP1 hP2 hP3
  have hN2 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_N2_three_step_bargmann_holonomy_and_linear_reduction hP1 hP2 hP3
  have hN3 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_N3_bargmann_nambu_ternary_curvature_theorem hP1 hP2 hP3
  have hN4 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_N4_idempotent_triangle_generates_bimetric_dipole a c
  have hSig :
      NonCommutativeTwoStateAndModularShift.Mat2.toBimetricMat2
        (NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy
          NonCommutativeTwoStateAndModularShift.Mat2.idem1
          (NonCommutativeTwoStateAndModularShift.Mat2.idem2 a)
          (NonCommutativeTwoStateAndModularShift.Mat2.idem3 c) +
         NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy
          NonCommutativeTwoStateAndModularShift.Mat2.idem1
          (NonCommutativeTwoStateAndModularShift.Mat2.idem3 c)
          (NonCommutativeTwoStateAndModularShift.Mat2.idem2 a)) =
        NonCommutativeBimetricSheetGeometry.Mat2.matSig a c := by
    rw [hN4.2.2.2.2.2.1]
    rfl
  have hV :
      NonCommutativeTwoStateAndModularShift.Mat2.toBimetricMat2
        (NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy
          NonCommutativeTwoStateAndModularShift.Mat2.idem1
          (NonCommutativeTwoStateAndModularShift.Mat2.idem2 a)
          (NonCommutativeTwoStateAndModularShift.Mat2.idem3 c) -
         NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy
          NonCommutativeTwoStateAndModularShift.Mat2.idem1
          (NonCommutativeTwoStateAndModularShift.Mat2.idem3 c)
          (NonCommutativeTwoStateAndModularShift.Mat2.idem2 a)) =
        NonCommutativeBimetricSheetGeometry.Mat2.matV a c := by
    rw [hN4.2.2.2.2.2.2.1]
    rfl
  exact ⟨hN0.2.2.2.2.2.1, hN0.2.2.2.2.2.2.2,
         hN1.1, hN1.2.2,
         hN2.1, hN2.2.1, hN2.2.2.2.2,
         hN3.2,
         hSig, hV⟩

-- ============================================================================
-- 11. CHIRAL MODULAR GENESIS, BOHM MASS–SPIN TRANSDUCTION & CHIRAL GAUGE VALVE
--     UNIFICATION POSET C₀ ≺ C₁ ≺ C₂ ≺ C₃ ≺ C₄
-- ============================================================================

/-- **Archetype $\mathcal{U}_{10}$ (`archetype_U10_chiral_cheshire_cat_genesis_bohm_transduction_and_gauge_valve`):**
Unites the Chiral Cheshire Cat Genesis, Bohm Mass–Spin Transduction, and Non-Reciprocal Chiral
Gauge Valve Poset ($\mathcal{C}_0 \prec \mathcal{C}_1 \prec \mathcal{C}_2 \prec \mathcal{C}_3 \prec \mathcal{C}_4$)
over ANY non-commutative associative ring `[Ring B]`:
1. **$\mathcal{C}_0$ (Chiral Modular Shift Bimetric Spin Identity):**
   For `Φ_c = modularShift σz 1`, `Φ_c² = Sz` and `Φ_c⁴ = 1`, with bimetric dipole `spinDipole σz`.
2. **$\mathcal{C}_1$ (Dynamic Intertwiner Genesis & Entangled Similarity Conjugation):**
   `Φ_c * Ψ_diag * Ex = Φ_diag`, `Sz * Φ_c * Φ_diag * Ex = Ψ_diag`, and
   `Φ_c * Ψ_ent * (Ex * Φ_c * Ex) = Φ_ent`.
3. **$\mathcal{C}_2$ (Bohm Double-Commutator Transduction Between Mass and Spin Dipoles):**
   `-[Φ_c, [Φ_c, D_mass]] = -4 • D_spin(σz)`, `-[Φ_c, [Φ_c, D_spin(σz)]] = -4 • D_mass`, and
   `-[Φ_c, [Φ_c, -[Φ_c, [Φ_c, D_mass]]]] = 16 • D_mass`.
4. **$\mathcal{C}_3$ (Non-Reciprocal Chiral Cheshire Cat Gauge Valve):**
   `Φ_diag * modularShift w w * Ψ_diag = modularShift 0 (2 w (1 + σx))` and
   `Φ_diag * modularShift (w * σz) (w * σz) * Ψ_diag = modularShift (2 w (1 + σx)) 0`.
5. **$\mathcal{C}_4$ (Sheet-Exchange Swaps Cat and Grin):**
   For `Ψ_swap = Ex * Ψ_diag * Ex`, `Φ_diag * P_left * Ψ_swap = 0`,
   `Φ_diag * P_right * Ψ_swap = localObs 0 (2(1 + σx))`, and
   `Φ_diag * (P_left * Sz) * Ψ_swap = localObs (2(1 + σx)) 0`.
6. **$\mathcal{C}_5$ (3-Idempotent Bargmann–Berry Phase Generates Spin Dipole & Disembodied Grin):**
   For `P₁ = idem1, P₂ = idem2 σz, P₃ = idem3 1`, `B₁₂₃ + B₁₃₂ = D_spin(σz)`, `B₁₂₃ - B₁₃₂ = Sz`,
   `Φ_diag * B₁₂₃ * Ψ_diag = 0`, and `Φ_diag * (-B₁₃₂) * Ψ_diag = localObs 0 (2(1 + σx))`. -/
theorem archetype_U10_chiral_cheshire_cat_genesis_bohm_transduction_and_gauge_valve
    {σx σz w : B} (hx : σx * σx = 1) (hz : σz * σz = 1)
    (hxz : NonCommutativeTwoStateAndModularShift.racomm σx σz = 0)
    (hw : NonCommutativeTwoStateAndModularShift.rcomm w σx = 0) :
    let Φc     := NonCommutativeTwoStateAndModularShift.Mat2.chiralPhi σz
    let Φc_inv := NonCommutativeTwoStateAndModularShift.Mat2.Ex * Φc *
                  NonCommutativeTwoStateAndModularShift.Mat2.Ex
    let Sz     := NonCommutativeTwoStateAndModularShift.Mat2.diagScalar σz
    let Dm     := (NonCommutativeTwoStateAndModularShift.Mat2.Ez :
                   NonCommutativeTwoStateAndModularShift.Mat2 B)
    let Ds     := NonCommutativeTwoStateAndModularShift.Mat2.spinDipole σz
    let Ds4    := (Ds + Ds) + (Ds + Ds)
    let Dm4    := (Dm + Dm) + (Dm + Dm)
    let Dm16   := (Dm4 + Dm4) + (Dm4 + Dm4)
    let Ψ_d    := NonCommutativeTwoStateAndModularShift.Mat2.PsiDiag σx σz
    let Φ_d    := NonCommutativeTwoStateAndModularShift.Mat2.PhiDiag σx
    let Ψ_e    := NonCommutativeTwoStateAndModularShift.Mat2.PsiEnt σx σz
    let Φ_e    := NonCommutativeTwoStateAndModularShift.Mat2.PhiEnt σx
    let Ψ_swap := NonCommutativeTwoStateAndModularShift.Mat2.Ex * Ψ_d *
                  NonCommutativeTwoStateAndModularShift.Mat2.Ex
    let Teven  := NonCommutativeTwoStateAndModularShift.Mat2.modularShift w w
    let Todd   := NonCommutativeTwoStateAndModularShift.Mat2.modularShift (w * σz) (w * σz)
    let wP     := w * (1 + σx)
    let twoWP  := wP + wP
    let twoPiP := (1 + σx) + (1 + σx)
    let P_l    := NonCommutativeTwoStateAndModularShift.Mat2.P_left (B := B)
    let P_r    := NonCommutativeTwoStateAndModularShift.Mat2.P_right (B := B)
    let P1_c   := (NonCommutativeTwoStateAndModularShift.Mat2.idem1 :
                   NonCommutativeTwoStateAndModularShift.Mat2 B)
    let P2_c   := NonCommutativeTwoStateAndModularShift.Mat2.idem2 σz
    let P3_c   := NonCommutativeTwoStateAndModularShift.Mat2.idem3 (1 : B)
    let Bc123  := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1_c P2_c P3_c
    let Bc132  := NonCommutativeTwoStateAndModularShift.Mat2.bargmannHolonomy P1_c P3_c P2_c
    -- 1. C₀: Chiral modular shift square is Sz and its fourth power is one:
    Φc * Φc = Sz ∧
    (Φc * Φc) * (Φc * Φc) = 1 ∧
    -- 2. C₁: Dynamic intertwiner genesis (diagonal and full entangled):
    Φc * Ψ_d * NonCommutativeTwoStateAndModularShift.Mat2.Ex = Φ_d ∧
    Sz * Φc * Φ_d * NonCommutativeTwoStateAndModularShift.Mat2.Ex = Ψ_d ∧
    Φc * Ψ_e * Φc_inv = Φ_e ∧
    -- 3. C₂: Bohm curvature transduction between mass and spin dipoles:
    -NonCommutativeTwoStateAndModularShift.rcomm Φc
      (NonCommutativeTwoStateAndModularShift.rcomm Φc Dm) = -Ds4 ∧
    -NonCommutativeTwoStateAndModularShift.rcomm Φc
      (NonCommutativeTwoStateAndModularShift.rcomm Φc Ds) = -Dm4 ∧
    -NonCommutativeTwoStateAndModularShift.rcomm Φc
      (NonCommutativeTwoStateAndModularShift.rcomm Φc
        (-NonCommutativeTwoStateAndModularShift.rcomm Φc
          (NonCommutativeTwoStateAndModularShift.rcomm Φc Dm))) = Dm16 ∧
    -- 4. C₃: Non-reciprocal chiral gauge valve:
    Φ_d * Teven * Ψ_d = NonCommutativeTwoStateAndModularShift.Mat2.modularShift 0 twoWP ∧
    Φ_d * Todd * Ψ_d  = NonCommutativeTwoStateAndModularShift.Mat2.modularShift twoWP 0 ∧
    -- 5. C₄: Sheet-exchange swaps Cat and Grin:
    Φ_d * P_l * Ψ_swap = 0 ∧
    Φ_d * P_r * Ψ_swap = NonCommutativeTwoStateAndModularShift.Mat2.localObs 0 twoPiP ∧
    Φ_d * (P_l * Sz) * Ψ_swap = NonCommutativeTwoStateAndModularShift.Mat2.localObs twoPiP 0 ∧
    Φ_d * (P_r * Sz) * Ψ_swap = 0 ∧
    -- 6. C₅: 3-idempotent Bargmann–Berry holonomy generates spin dipole & disembodied grin:
    Bc123 + Bc132 = Ds ∧
    Bc123 - Bc132 = Sz ∧
    Φ_d * Bc123 * Ψ_d = 0 ∧
    Φ_d * (-Bc132) * Ψ_d = NonCommutativeTwoStateAndModularShift.Mat2.localObs 0 twoPiP := by
  have hC0 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C0_chiral_modular_shift_bimetric_spin_identity hz
  have hC1 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C1_cheshire_cat_chiral_intertwiner_genesis hz hxz
  have hC2 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C2_bohm_curvature_transduces_mass_and_spin_dipoles hz
  have hC3 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C3_cheshire_cat_chiral_modular_valve hx hz hxz hw
  have hC4 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C4_cheshire_cat_sheet_exchange_swaps_cat_and_grin hx hz hxz
  have hC5 :=
    NonCommutativeTwoStateAndModularShift.Mat2.archetype_C5_cheshire_cat_bargmann_berry_holonomy_generates_spin_dipole_and_grin hx hz hxz
  exact ⟨hC0.2.2.2.1, hC0.2.2.2.2,
         hC1.2.1, hC1.2.2.1, hC1.2.2.2.1,
         hC2.1, hC2.2.1, hC2.2.2,
         hC3.1, hC3.2,
         hC4.1, hC4.2.1, hC4.2.2.1, hC4.2.2.2,
         hC5.2.2.2.1, hC5.2.2.2.2.1, hC5.2.2.2.2.2.1, hC5.2.2.2.2.2.2⟩

-- ============================================================================
-- 12. UNIVERSAL 4-STEP ZORN–YANG–MILLS LADDER & SPIN-1 g_S = 2 CHROMOELECTRIC
--     WAVE EQUATION OVER [Ring B] (Z₀ ≺ Z₁ ≺ Z₂ ≺ Z₃ ≺ Z₄ ≺ U₁₁)
-- ============================================================================

/-- 3-vector carrier `γ × γ × γ` over a non-commutative ring `γ`. -/
def Vec3NC (γ : Type u) : Type u := γ × γ × γ

/-- First component `v1` of `a : Vec3NC γ`. -/
@[simp] def Vec3NC.v1 {γ : Type u} (a : Vec3NC γ) : γ := a.1
/-- Second component `v2` of `a : Vec3NC γ`. -/
@[simp] def Vec3NC.v2 {γ : Type u} (a : Vec3NC γ) : γ := a.2.1
/-- Third component `v3` of `a : Vec3NC γ`. -/
@[simp] def Vec3NC.v3 {γ : Type u} (a : Vec3NC γ) : γ := a.2.2

/-- Componentwise extensionality for `Vec3NC γ`. -/
@[ext] lemma Vec3NC.ext {γ : Type u} {a b : Vec3NC γ}
    (h1 : a.v1 = b.v1) (h2 : a.v2 = b.v2) (h3 : a.v3 = b.v3) : a = b := by
  rcases a with ⟨a1, a2, a3⟩
  rcases b with ⟨b1, b2, b3⟩
  dsimp [Vec3NC.v1, Vec3NC.v2, Vec3NC.v3] at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- Zorn octonion vector-matrix carrier `γ × Vec3NC γ × Vec3NC γ × γ` over a non-commutative ring `γ`. -/
def ZornMatNC (γ : Type u) : Type u := γ × Vec3NC γ × Vec3NC γ × γ

/-- Upper-left scalar entry `α` of `M : ZornMatNC γ`. -/
@[simp] def ZornMatNC.α {γ : Type u} (M : ZornMatNC γ) : γ := M.1
/-- Upper-right 3-vector entry `x` of `M : ZornMatNC γ`. -/
@[simp] def ZornMatNC.x {γ : Type u} (M : ZornMatNC γ) : Vec3NC γ := M.2.1
/-- Lower-left 3-vector entry `y` of `M : ZornMatNC γ`. -/
@[simp] def ZornMatNC.y {γ : Type u} (M : ZornMatNC γ) : Vec3NC γ := M.2.2.1
/-- Lower-right scalar entry `β` of `M : ZornMatNC γ`. -/
@[simp] def ZornMatNC.β {γ : Type u} (M : ZornMatNC γ) : γ := M.2.2.2

/-- Componentwise extensionality for `ZornMatNC γ`. -/
@[ext] lemma ZornMatNC.ext {γ : Type u} {M N : ZornMatNC γ}
    (hα : M.α = N.α) (hx : M.x = N.x) (hy : M.y = N.y) (hβ : M.β = N.β) : M = N := by
  rcases M with ⟨mα, mx, my, mβ⟩
  rcases N with ⟨nα, nx, ny, nβ⟩
  dsimp [ZornMatNC.α, ZornMatNC.x, ZornMatNC.y, ZornMatNC.β] at hα hx hy hβ
  subst hα hx hy hβ
  rfl

/-- Zero 3-vector over `B`. -/
@[simp] def vecZero : Vec3NC B := ⟨0, 0, 0⟩

/-- Entrywise addition on `Vec3NC B`. -/
@[simp] def vecAdd (a b : Vec3NC B) : Vec3NC B := ⟨a.v1 + b.v1, a.v2 + b.v2, a.v3 + b.v3⟩

/-- Entrywise subtraction on `Vec3NC B`. -/
@[simp] def vecSub (a b : Vec3NC B) : Vec3NC B := ⟨a.v1 - b.v1, a.v2 - b.v2, a.v3 - b.v3⟩

/-- Entrywise negation on `Vec3NC B`. -/
@[simp] def vecNeg (a : Vec3NC B) : Vec3NC B := ⟨-a.v1, -a.v2, -a.v3⟩

/-- Left scalar-operator multiplication on `Vec3NC B`. -/
@[simp] def vecLmul (c : B) (a : Vec3NC B) : Vec3NC B := ⟨c * a.v1, c * a.v2, c * a.v3⟩

/-- Right scalar-operator multiplication on `Vec3NC B`. -/
@[simp] def vecRmul (a : Vec3NC B) (c : B) : Vec3NC B := ⟨a.v1 * c, a.v2 * c, a.v3 * c⟩

/-- Non-commutative dot product `a · b = a₁ b₁ + a₂ b₂ + a₃ b₃`. -/
@[simp] def vecDot (a b : Vec3NC B) : B := a.v1 * b.v1 + a.v2 * b.v2 + a.v3 * b.v3

/-- Non-commutative cross product `a × b`. -/
@[simp] def vecCross (a b : Vec3NC B) : Vec3NC B :=
  ⟨a.v2 * b.v3 - a.v3 * b.v2,
   a.v3 * b.v1 - a.v1 * b.v3,
   a.v1 * b.v2 - a.v2 * b.v1⟩

/-- Adjoint commutator of a scalar operator `d0` with a 3-vector `v`. -/
@[simp] def vecComm (d0 : B) (v : Vec3NC B) : Vec3NC B :=
  ⟨NonCommutativeBimetricSheetGeometry.rcomm d0 v.v1,
   NonCommutativeBimetricSheetGeometry.rcomm d0 v.v2,
   NonCommutativeBimetricSheetGeometry.rcomm d0 v.v3⟩

/-- Covariant adjoint gradient `Grad_ad(p, φ)_i = [p_i, φ]`. -/
@[simp] def adjointGrad (p : Vec3NC B) (φ : B) : Vec3NC B :=
  ⟨NonCommutativeBimetricSheetGeometry.rcomm p.v1 φ,
   NonCommutativeBimetricSheetGeometry.rcomm p.v2 φ,
   NonCommutativeBimetricSheetGeometry.rcomm p.v3 φ⟩

/-- Covariant adjoint divergence `p ·_ad V = ∑_{i=1}^3 [p_i, V_i]`. -/
@[simp] def adjointDiv (p V : Vec3NC B) : B :=
  NonCommutativeBimetricSheetGeometry.rcomm p.v1 V.v1 +
  NonCommutativeBimetricSheetGeometry.rcomm p.v2 V.v2 +
  NonCommutativeBimetricSheetGeometry.rcomm p.v3 V.v3

/-- Covariant adjoint curl `(p ×_ad V)_k = ϵ_{ijk} [p_i, V_j]`. -/
@[simp] def adjointCurl (p V : Vec3NC B) : Vec3NC B :=
  ⟨NonCommutativeBimetricSheetGeometry.rcomm p.v2 V.v3 -
     NonCommutativeBimetricSheetGeometry.rcomm p.v3 V.v2,
   NonCommutativeBimetricSheetGeometry.rcomm p.v3 V.v1 -
     NonCommutativeBimetricSheetGeometry.rcomm p.v1 V.v3,
   NonCommutativeBimetricSheetGeometry.rcomm p.v1 V.v2 -
     NonCommutativeBimetricSheetGeometry.rcomm p.v2 V.v1⟩

/-- Covariant Bochner scalar Laplacian `lapScalar(p, φ) = ∑_{j=1}^3 [p_j, [p_j, φ]]`. -/
@[simp] def bochnerLapScalar (p : Vec3NC B) (φ : B) : B :=
  NonCommutativeBimetricSheetGeometry.rcomm p.v1
    (NonCommutativeBimetricSheetGeometry.rcomm p.v1 φ) +
  NonCommutativeBimetricSheetGeometry.rcomm p.v2
    (NonCommutativeBimetricSheetGeometry.rcomm p.v2 φ) +
  NonCommutativeBimetricSheetGeometry.rcomm p.v3
    (NonCommutativeBimetricSheetGeometry.rcomm p.v3 φ)

/-- Covariant Bochner vector Laplacian `(Δ_ad V)_i = ∑_{j=1}^3 [p_j, [p_j, V_i]]`. -/
@[simp] def bochnerLaplacian (p V : Vec3NC B) : Vec3NC B :=
  ⟨bochnerLapScalar p V.v1, bochnerLapScalar p V.v2, bochnerLapScalar p V.v3⟩

/-- Yoichiro Nambu's ternary bracket `[p₁, p₂, p₃]_Nambu = p · (p × p)`. -/
@[simp] def vecNambu3 (p : Vec3NC B) : B := vecDot p (vecCross p p)

/-- Covariant chromoelectric curvature 3-vector `E_cov(d0, p) = [d0, p]`. -/
@[simp] def covE (d0 : B) (p : Vec3NC B) : Vec3NC B := vecComm d0 p

/-- Covariant chromomagnetic curvature 3-vector `B_cov(p) = p × p`. -/
@[simp] def covB (p : Vec3NC B) : Vec3NC B := vecCross p p

/-- Entrywise addition on `ZornMatNC B`. -/
@[simp] def zornAdd (M N : ZornMatNC B) : ZornMatNC B :=
  ⟨M.α + N.α, vecAdd M.x N.x, vecAdd M.y N.y, M.β + N.β⟩

/-- Entrywise subtraction on `ZornMatNC B`. -/
@[simp] def zornSub (M N : ZornMatNC B) : ZornMatNC B :=
  ⟨M.α - N.α, vecSub M.x N.x, vecSub M.y N.y, M.β - N.β⟩

/-- Non-associative Zorn vector-matrix multiplication over `B`. -/
@[simp] def zornMul (M N : ZornMatNC B) : ZornMatNC B :=
  ⟨M.α * N.α - vecDot M.x N.y,
   vecAdd (vecAdd (vecLmul M.α N.x) (vecRmul M.x N.β)) (vecCross M.y N.y),
   vecAdd (vecAdd (vecLmul M.β N.y) (vecRmul M.y N.α)) (vecCross M.x N.x),
   M.β * N.β - vecDot M.y N.x⟩

/-- Zorn commutator `[M, N]_Z = M * N - N * M`. -/
@[simp] def zornComm (M N : ZornMatNC B) : ZornMatNC B := zornSub (zornMul M N) (zornMul N M)

/-- Zorn anticommutator `{M, N}_Z = M * N + N * M`. -/
@[simp] def zornAnticomm (M N : ZornMatNC B) : ZornMatNC B := zornAdd (zornMul M N) (zornMul N M)

/-- Zorn cubic self-associator `(Ψ * Ψ) * Ψ - Ψ * (Ψ * Ψ)`. -/
@[simp] def zornSelfAssociator (Ψ : ZornMatNC B) : ZornMatNC B :=
  zornSub (zornMul (zornMul Ψ Ψ) Ψ) (zornMul Ψ (zornMul Ψ Ψ))

/-- Chiral Weyl–Zorn operator `D_+(d0, p) = [[d0, p], [-p, -d0]]`. -/
@[simp] def weylZornPlus (d0 : B) (p : Vec3NC B) : ZornMatNC B :=
  ⟨d0, p, vecNeg p, -d0⟩

/-- Anti-chiral Weyl–Zorn operator `D_-(d0, p) = [[d0, -p], [p, -d0]]`. -/
@[simp] def weylZornMinus (d0 : B) (p : Vec3NC B) : ZornMatNC B :=
  ⟨d0, vecNeg p, p, -d0⟩

/-- Klein–Gordon diagonal Zorn operator `L_KG(d0, p) = [[d0² + p·p, 0], [0, d0² + p·p]]`. -/
@[simp] def kgZorn (d0 : B) (p : Vec3NC B) : ZornMatNC B :=
  let lap := d0 * d0 + vecDot p p
  ⟨lap, vecZero, vecZero, lap⟩

/-- Self-dual curvature Zorn matrix `F_+(d0, p) = [[0, B + E], [B + E, 0]]`. -/
@[simp] def curvZornPlus (d0 : B) (p : Vec3NC B) : ZornMatNC B :=
  let fp := vecAdd (covB p) (covE d0 p)
  ⟨0, fp, fp, 0⟩

/-- Anti-self-dual curvature Zorn matrix `F_-(d0, p) = [[0, B - E], [B - E, 0]]`. -/
@[simp] def curvZornMinus (d0 : B) (p : Vec3NC B) : ZornMatNC B :=
  let fm := vecSub (covB p) (covE d0 p)
  ⟨0, fm, fm, 0⟩

macro "zorn_nc_calc" : tactic =>
  `(tactic| (
    (try ext) <;>
    · (try simp only [Vec3NC.v1, Vec3NC.v2, Vec3NC.v3,
                      ZornMatNC.α, ZornMatNC.x, ZornMatNC.y, ZornMatNC.β,
                      vecZero, vecAdd, vecSub, vecNeg, vecLmul, vecRmul,
                      vecDot, vecCross, vecComm,
                      adjointGrad, adjointDiv, adjointCurl,
                      bochnerLapScalar, bochnerLaplacian, vecNambu3,
                      covE, covB,
                      zornAdd, zornSub, zornMul, zornComm, zornAnticomm, zornSelfAssociator,
                      weylZornPlus, weylZornMinus, kgZorn, curvZornPlus, curvZornMinus,
                      NonCommutativeBimetricSheetGeometry.rcomm,
                      mul_add, add_mul, sub_mul, mul_sub,
                      mul_zero, zero_mul, mul_one, one_mul,
                      add_zero, zero_add, sub_zero, zero_sub,
                      neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                      mul_assoc])
      (try abel)))

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{Z}_0$ (`archetype_Z0_bianchi_vanishing_ricci_obstruction_and_symmetric_adjoint_curl`):**
Over ANY non-commutative associative ring `[Ring B]` and ANY `d0 : B`, `p U V : Vec3NC B`:
1. **Magnetic Bianchi Identity:** `p ·_ad B_cov(p) = 0`.
2. **Faraday–Bianchi Identity:** `[d0, B_cov(p)] - p ×_ad E_cov(d0, p) = 0`.
3. **Non-Abelian Ricci Curvature Obstruction:** `p ·_ad (p ×_ad V) = B_cov(p) ·_ad V`.
4. **Symmetry of the Adjoint Cross-Product & Symmetrized Cross-Product Bridge:**
   `U ×_ad V = + V ×_ad U` and `(U × V) + (V × U) = U ×_ad V`.
5. **Independent Electric Conservation Identity:** `p ·_ad [d0, E] - [d0, p ·_ad E] = 0`. -/
theorem archetype_Z0_bianchi_vanishing_ricci_obstruction_and_symmetric_adjoint_curl
    (d0 : B) (p U V : Vec3NC B) :
    adjointDiv p (covB p) = 0 ∧
    vecSub (vecComm d0 (covB p)) (adjointCurl p (covE d0 p)) = vecZero ∧
    adjointDiv p (adjointCurl p V) = adjointDiv (covB p) V ∧
    adjointCurl U V = adjointCurl V U ∧
    vecAdd (vecCross U V) (vecCross V U) = adjointCurl U V ∧
    adjointDiv p (vecComm d0 (covE d0 p)) -
      NonCommutativeBimetricSheetGeometry.rcomm d0 (adjointDiv p (covE d0 p)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_nc_calc

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{Z}_1$ (`archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator`):**
Over ANY non-commutative associative ring `[Ring B]` and ANY `d0 : B`, `p : Vec3NC B`:
1. **Zorn–Lichnerowicz–Weitzenböck Square:**
   `D_+² = L_KG + F_+` and `D_-² = L_KG + F_-`.
2. **Cubic Self-Associator Nambu Doubling:**
   `(D_+² * D_+ - D_+ * D_+²).α = 2 [p₁, p₂, p₃]_Nambu`,
   `(D_+² * D_+ - D_+ * D_+²).β = -2 [p₁, p₂, p₃]_Nambu`,
   `(D_-² * D_- - D_- * D_-²).α = -2 [p₁, p₂, p₃]_Nambu`, and
   `(D_-² * D_- - D_- * D_-²).β = 2 [p₁, p₂, p₃]_Nambu`. -/
theorem archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator
    (d0 : B) (p : Vec3NC B) :
    let Dp := weylZornPlus d0 p
    let Dm := weylZornMinus d0 p
    let N2 := vecNambu3 p + vecNambu3 p
    zornMul Dp Dp = zornAdd (kgZorn d0 p) (curvZornPlus d0 p) ∧
    zornMul Dm Dm = zornAdd (kgZorn d0 p) (curvZornMinus d0 p) ∧
    (zornSelfAssociator Dp).α = N2 ∧
    (zornSelfAssociator Dp).β = -N2 ∧
    (zornSelfAssociator Dm).α = -N2 ∧
    (zornSelfAssociator Dm).β = N2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zorn_nc_calc

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{Z}_2$ (`archetype_Z2_unified_gauss_ampere_anticommutator`):**
Over ANY non-commutative associative ring `[Ring B]` and ANY `d0 : B`, `p : Vec3NC B`,
the Zorn anticommutator `{D_±, F_±}_Z` packages the Gauss law operator
`G_gauss = p ·_ad E` on the diagonal and the Ampère–Maxwell operator
`J_ampere = [d0, E] - p ×_ad B` on the off-diagonal (since the homogeneous Bianchi terms
vanish identically in every associative ring `B`):
`{D_+, F_+}_Z = [[-G_gauss, J_ampere], [-J_ampere, G_gauss]]` and
`{D_-, F_-}_Z = [[-G_gauss, -J_ampere], [J_ampere, G_gauss]]`. -/
theorem archetype_Z2_unified_gauss_ampere_anticommutator
    (d0 : B) (p : Vec3NC B) :
    let E        := covE d0 p
    let B_vec    := covB p
    let G_gauss  := adjointDiv p E
    let J_ampere := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    zornAnticomm (weylZornPlus d0 p) (curvZornPlus d0 p) =
      ⟨-G_gauss, J_ampere, vecNeg J_ampere, G_gauss⟩ ∧
    zornAnticomm (weylZornMinus d0 p) (curvZornMinus d0 p) =
      ⟨-G_gauss, vecNeg J_ampere, J_ampere, G_gauss⟩ := by
  refine ⟨?_, ?_⟩ <;> zorn_nc_calc

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{Z}_3$ (`archetype_Z3_fourth_order_noether_commutator_and_wave_anticommutator`):**
Over ANY non-commutative associative ring `[Ring B]` and ANY `d0 : B`, `p : Vec3NC B`:
1. **4th-Order Covariant Noether Current Conservation:**
   `p ·_ad J_ampere - [d0, G_gauss] = 0`, so the diagonal of `[D_±, {D_±, F_±}]_Z` vanishes identically!
2. **4th-Order Wave Anticommutator `{D_±, {D_±, F_±}}_Z`:**
   Assembles `±([d0, J_ampere] + Grad_ad G_gauss) + p ×_ad J_ampere` on the off-diagonal `.x`
   and `.y` blocks, so the entire chiral difference matrix is
   `W_+ - W_- = [[0, 2([d0, J_ampere] + Grad_ad G_gauss)], [2([d0, J_ampere] + Grad_ad G_gauss), 0]]`! -/
theorem archetype_Z3_fourth_order_noether_commutator_and_wave_anticommutator
    (d0 : B) (p : Vec3NC B) :
    let E          := covE d0 p
    let B_vec      := covB p
    let G_gauss    := adjointDiv p E
    let J_ampere   := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    let waveSource := vecAdd (vecComm d0 J_ampere) (adjointGrad p G_gauss)
    let curlJ      := adjointCurl p J_ampere
    let J_plus     := zornAnticomm (weylZornPlus d0 p) (curvZornPlus d0 p)
    let J_minus    := zornAnticomm (weylZornMinus d0 p) (curvZornMinus d0 p)
    let W_plus     := zornAnticomm (weylZornPlus d0 p) J_plus
    let W_minus    := zornAnticomm (weylZornMinus d0 p) J_minus
    adjointDiv p J_ampere - NonCommutativeBimetricSheetGeometry.rcomm d0 G_gauss = 0 ∧
    (zornComm (weylZornPlus d0 p) J_plus).α = 0 ∧
    (zornComm (weylZornPlus d0 p) J_plus).β = 0 ∧
    (zornComm (weylZornMinus d0 p) J_minus).α = 0 ∧
    (zornComm (weylZornMinus d0 p) J_minus).β = 0 ∧
    W_plus.x = vecAdd waveSource curlJ ∧
    W_minus.x = vecSub curlJ waveSource ∧
    zornSub W_plus W_minus =
      ⟨0, vecAdd waveSource waveSource, vecAdd waveSource waveSource, 0⟩ := by
  have hZ2 := archetype_Z2_unified_gauss_ampere_anticommutator d0 p
  have hNoether :
      adjointDiv p (vecSub (vecComm d0 (covE d0 p)) (adjointCurl p (covB p))) -
        NonCommutativeBimetricSheetGeometry.rcomm d0 (adjointDiv p (covE d0 p)) = 0 := by
    zorn_nc_calc
  have hCommP_a (G : B) (J : Vec3NC B) :
      (zornComm (weylZornPlus d0 p) ⟨-G, J, vecNeg J, G⟩).α =
        adjointDiv p J - NonCommutativeBimetricSheetGeometry.rcomm d0 G := by
    zorn_nc_calc
  have hCommP_b (G : B) (J : Vec3NC B) :
      (zornComm (weylZornPlus d0 p) ⟨-G, J, vecNeg J, G⟩).β =
        adjointDiv p J - NonCommutativeBimetricSheetGeometry.rcomm d0 G := by
    zorn_nc_calc
  have hCommM_a (G : B) (J : Vec3NC B) :
      (zornComm (weylZornMinus d0 p) ⟨-G, vecNeg J, J, G⟩).α =
        adjointDiv p J - NonCommutativeBimetricSheetGeometry.rcomm d0 G := by
    zorn_nc_calc
  have hCommM_b (G : B) (J : Vec3NC B) :
      (zornComm (weylZornMinus d0 p) ⟨-G, vecNeg J, J, G⟩).β =
        adjointDiv p J - NonCommutativeBimetricSheetGeometry.rcomm d0 G := by
    zorn_nc_calc
  have hAntiP_x (G : B) (J : Vec3NC B) :
      (zornAnticomm (weylZornPlus d0 p) ⟨-G, J, vecNeg J, G⟩).x =
        vecAdd (vecAdd (vecComm d0 J) (adjointGrad p G)) (adjointCurl p J) := by
    zorn_nc_calc
  have hAntiM_x (G : B) (J : Vec3NC B) :
      (zornAnticomm (weylZornMinus d0 p) ⟨-G, vecNeg J, J, G⟩).x =
        vecSub (adjointCurl p J) (vecAdd (vecComm d0 J) (adjointGrad p G)) := by
    zorn_nc_calc
  have hSub_mat (G : B) (J : Vec3NC B) :
      zornSub (zornAnticomm (weylZornPlus d0 p) ⟨-G, J, vecNeg J, G⟩)
              (zornAnticomm (weylZornMinus d0 p) ⟨-G, vecNeg J, J, G⟩) =
        let ws := vecAdd (vecComm d0 J) (adjointGrad p G)
        ⟨0, vecAdd ws ws, vecAdd ws ws, 0⟩ := by
    zorn_nc_calc
  dsimp only []
  refine ⟨hNoether, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hZ2.1, hCommP_a, hNoether]
  · rw [hZ2.1, hCommP_b, hNoether]
  · rw [hZ2.2, hCommM_a, hNoether]
  · rw [hZ2.2, hCommM_b, hNoether]
  · rw [hZ2.1, hAntiP_x]
  · rw [hZ2.2, hAntiM_x]
  · rw [hZ2.1, hZ2.2, hSub_mat]

/-- The diagonal entries of either chiral fourth-order wave anticommutator are
the same residual. The conservation law from `archetype_Z3` controls a
commutator (`p ·_ad J = [d0, G]`); it does not by itself set this sum of
products to zero. -/
theorem fourth_order_wave_anticommutator_diagonal_residual
    (d0 : B) (p : Vec3NC B) :
    let E        := covE d0 p
    let B_vec    := covB p
    let G        := adjointDiv p E
    let J        := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    let Dp       := weylZornPlus d0 p
    let Dm       := weylZornMinus d0 p
    let Fp       := curvZornPlus d0 p
    let Fm       := curvZornMinus d0 p
    let Wp       := zornAnticomm Dp (zornAnticomm Dp Fp)
    let Wm       := zornAnticomm Dm (zornAnticomm Dm Fm)
    let residual := -(d0 * G) - G * d0 + vecDot p J + vecDot J p
    Wp.α = residual ∧ Wp.β = residual ∧
    Wm.α = residual ∧ Wm.β = residual := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> zorn_nc_calc

/-- Component expansion of the fourth-order chiral wave terms.

Both chiralities have the same diagonal residual. Their upper off-diagonal
components are the wave source plus the adjoint curl of the Ampère operator
for the plus chirality, and that curl minus the wave source for the minus
chirality. In particular, cancellation of the diagonal holds for the chiral
difference, not for either wave term separately. -/
theorem fourth_order_wave_anticommutator_components
    (d0 : B) (p : Vec3NC B) :
    let E          := covE d0 p
    let B_vec      := covB p
    let G_gauss    := adjointDiv p E
    let J_ampere   := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    let waveSource := vecAdd (vecComm d0 J_ampere) (adjointGrad p G_gauss)
    let curlJ      := adjointCurl p J_ampere
    let Dp         := weylZornPlus d0 p
    let Dm         := weylZornMinus d0 p
    let Fp         := curvZornPlus d0 p
    let Fm         := curvZornMinus d0 p
    let Jp         := zornAnticomm Dp Fp
    let Jm         := zornAnticomm Dm Fm
    let Wp         := zornAnticomm Dp Jp
    let Wm         := zornAnticomm Dm Jm
    let residual   := -(d0 * G_gauss) - G_gauss * d0 +
      vecDot p J_ampere + vecDot J_ampere p
    Wp.α = residual ∧ Wp.β = residual ∧
    Wp.x = vecAdd waveSource curlJ ∧
    Wm.α = residual ∧ Wm.β = residual ∧
    Wm.x = vecSub curlJ waveSource := by
  have hDiag := fourth_order_wave_anticommutator_diagonal_residual d0 p
  have hZ3 := archetype_Z3_fourth_order_noether_commutator_and_wave_anticommutator d0 p
  rcases hZ3 with ⟨_, _, _, _, _, hPlus, hMinus, _⟩
  refine ⟨hDiag.1, hDiag.2.1, ?_, hDiag.2.2.1, hDiag.2.2.2, ?_⟩
  · exact hPlus
  · exact hMinus

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{Z}_4$ (`archetype_Z4_non_abelian_g2_chromoelectric_wave_equation`):**
**The Universal Non-Abelian `g_S = 2` Chromoelectric Wave Equation & Curvature Square Bridge over `[Ring B]`:**
For ANY `d0 : B` and `p : Vec3NC B` in ANY non-commutative associative ring `[Ring B]`:
1. **Non-Abelian Weitzenböck Curl-of-Curl Identity:**
   `p ×_ad (p ×_ad E) = Grad_ad(G_gauss) - Δ_ad E + (B ×_ad E)`.
2. **Temporal–Spatial Curl Commutation Identity:**
   `[d0, p ×_ad B] = p ×_ad (p ×_ad E) + (B ×_ad E)`.
3. **Constructive Doubling of the Spin-1 Chromomagnetic Moment (`g_S = 2`):**
   `[d0, [d0, E]] + Δ_ad E - 2 (B ×_ad E) = [d0, J_ampere] + Grad_ad(G_gauss)`.
4. **Zorn Curvature Square Bogomolny Energy, Pontryagin Density & `g_S = 2` Spin-1 Bridge:**
   `(F_+² + F_-²).α = -2 (E · E + B · B)`,
   `(F_-² - F_+²).α = 2 (E · B + B · E)`, and
   `(F_+² - F_-²).x = 2 (B ×_ad E)`! -/
theorem archetype_Z4_non_abelian_g2_chromoelectric_wave_equation
    (d0 : B) (p : Vec3NC B) :
    let E        := covE d0 p
    let B_vec    := covB p
    let G_gauss  := adjointDiv p E
    let J_ampere := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    let dt2_E    := vecComm d0 (vecComm d0 E)
    let lap_E    := bochnerLaplacian p E
    let BxE      := adjointCurl B_vec E
    let spin1_g2 := vecAdd BxE BxE
    let F_plus2  := zornMul (curvZornPlus d0 p) (curvZornPlus d0 p)
    let F_minus2 := zornMul (curvZornMinus d0 p) (curvZornMinus d0 p)
    let bogomolnyEnergy   := vecDot E E + vecDot B_vec B_vec
    let pontryaginDensity := vecDot E B_vec + vecDot B_vec E
    -- 1. Non-Abelian Weitzenböck curl-of-curl identity:
    adjointCurl p (adjointCurl p E) =
      vecAdd (vecSub (adjointGrad p G_gauss) lap_E) BxE ∧
    -- 2. Temporal-spatial curl commutation identity:
    vecComm d0 (adjointCurl p B_vec) =
      vecAdd (adjointCurl p (adjointCurl p E)) BxE ∧
    -- 3. Universal Non-Abelian g_S = 2 Chromoelectric Wave Equation:
    vecSub (vecAdd dt2_E lap_E) spin1_g2 =
      vecAdd (vecComm d0 J_ampere) (adjointGrad p G_gauss) ∧
    -- 4. Zorn Curvature Square Bogomolny Energy, Pontryagin Density & g_S = 2 Spin-1 Bridge:
    (zornAdd F_plus2 F_minus2).α = -(bogomolnyEnergy + bogomolnyEnergy) ∧
    (zornSub F_minus2 F_plus2).α = pontryaginDensity + pontryaginDensity ∧
    (zornSub F_plus2 F_minus2).x = spin1_g2 := by
  have hCurvSum (E_v B_v : Vec3NC B) :
      (zornAdd (zornMul ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩
                        ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩)
               (zornMul ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩
                        ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩)).α =
        -((vecDot E_v E_v + vecDot B_v B_v) + (vecDot E_v E_v + vecDot B_v B_v)) := by
    zorn_nc_calc
  have hCurvDiff_a (E_v B_v : Vec3NC B) :
      (zornSub (zornMul ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩
                        ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩)
               (zornMul ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩
                        ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩)).α =
        (vecDot E_v B_v + vecDot B_v E_v) + (vecDot E_v B_v + vecDot B_v E_v) := by
    zorn_nc_calc
  have hCurvDiff_x (E_v B_v : Vec3NC B) :
      (zornSub (zornMul ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩
                        ⟨0, vecAdd B_v E_v, vecAdd B_v E_v, 0⟩)
               (zornMul ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩
                        ⟨0, vecSub B_v E_v, vecSub B_v E_v, 0⟩)).x =
        vecAdd (adjointCurl B_v E_v) (adjointCurl B_v E_v) := by
    zorn_nc_calc
  refine ⟨?_, ?_, ?_, hCurvSum (covE d0 p) (covB p), hCurvDiff_a (covE d0 p) (covB p), hCurvDiff_x (covE d0 p) (covB p)⟩
  · zorn_nc_calc
  · zorn_nc_calc
  · zorn_nc_calc

/-- **Archetype $\mathcal{U}_{11}$ (`archetype_U11_zorn_yang_mills_four_step_ladder_and_g2_wave_poset_Z0_to_Z4`):**
**Master Unification of the 4-Step Dirac–Zorn–Yang–Mills Ladder & Non-Abelian `g_S = 2` Wave Poset ($\mathcal{Z}_0 \prec \mathcal{Z}_1 \prec \mathcal{Z}_2 \prec \mathcal{Z}_3 \prec \mathcal{Z}_4 \prec \mathcal{U}_{11}$):**
Unifies over ANY non-commutative associative ring `[Ring B]`:
1. **$\mathcal{Z}_0$ (Bianchi Vanishing, Ricci Obstruction & Symmetric Adjoint Curl):**
   `p ·_ad B_cov(p) = 0`, `[d0, B_cov(p)] - p ×_ad E_cov(d0, p) = 0`, `p ·_ad (p ×_ad V) = B_cov(p) ·_ad V`,
   `U ×_ad V = + V ×_ad U`, and `(U × V) + (V × U) = U ×_ad V`.
2. **$\mathcal{Z}_1$ (Step 1 — Zorn–Lichnerowicz–Weitzenböck Square & Cubic Nambu Associator):**
   `D_±² = L_KG + F_±` and `(D_±² * D_± - D_± * D_±²).α = ±2 [p₁, p₂, p₃]_Nambu`.
3. **$\mathcal{Z}_2$ (Step 2 — Unified Gauss–Ampère Anticommutator):**
   `{D_±, F_±}_Z = [[-G_gauss, ±J_ampere], [∓J_ampere, G_gauss]]`.
4. **$\mathcal{Z}_3$ (Steps 3 & 4 — 4th-Order Noether Commutator & Wave Anticommutator):**
   `p ·_ad J_ampere - [d0, G_gauss] = 0`, `[D_±, {D_±, F_±}]_Z` has vanishing diagonal, and
   `W_+ - W_- = [[0, 2([d0, J_ampere] + Grad_ad G_gauss)], [2([d0, J_ampere] + Grad_ad G_gauss), 0]]`.
5. **$\mathcal{Z}_4$ (Non-Abelian `g_S = 2` Chromoelectric Wave Equation & Curvature Square Bridge):**
   `[d0, [d0, E]] + Δ_ad E - 2 (B ×_ad E) = [d0, J_ampere] + Grad_ad(G_gauss)` where
   `2 (B ×_ad E) = (F_+² - F_-²).x`! -/
theorem archetype_U11_zorn_yang_mills_four_step_ladder_and_g2_wave_poset_Z0_to_Z4
    (d0 : B) (p U V : Vec3NC B) :
    let E          := covE d0 p
    let B_vec      := covB p
    let G_gauss    := adjointDiv p E
    let J_ampere   := vecSub (vecComm d0 E) (adjointCurl p B_vec)
    let waveSource := vecAdd (vecComm d0 J_ampere) (adjointGrad p G_gauss)
    let dt2_E      := vecComm d0 (vecComm d0 E)
    let lap_E      := bochnerLaplacian p E
    let BxE        := adjointCurl B_vec E
    let spin1_g2   := vecAdd BxE BxE
    let Dp         := weylZornPlus d0 p
    let Dm         := weylZornMinus d0 p
    let Fp         := curvZornPlus d0 p
    let Fm         := curvZornMinus d0 p
    let J_plus     := zornAnticomm Dp Fp
    let J_minus    := zornAnticomm Dm Fm
    let W_plus     := zornAnticomm Dp J_plus
    let W_minus    := zornAnticomm Dm J_minus
    let N2         := vecNambu3 p + vecNambu3 p
    -- Z₀: Bianchi vanishing, Ricci obstruction, and symmetric adjoint curl
    (adjointDiv p B_vec = 0 ∧
     vecSub (vecComm d0 B_vec) (adjointCurl p E) = vecZero ∧
     adjointDiv p (adjointCurl p V) = adjointDiv B_vec V ∧
     adjointCurl U V = adjointCurl V U ∧
     vecAdd (vecCross U V) (vecCross V U) = adjointCurl U V) ∧
    -- Z₁: Step 1 — Zorn–Lichnerowicz–Weitzenböck square & cubic Nambu associator
    (zornMul Dp Dp = zornAdd (kgZorn d0 p) Fp ∧
     zornMul Dm Dm = zornAdd (kgZorn d0 p) Fm ∧
     (zornSelfAssociator Dp).α = N2 ∧
     (zornSelfAssociator Dm).α = -N2) ∧
    -- Z₂: Step 2 — Unified Gauss–Ampère anticommutator
    (J_plus = ⟨-G_gauss, J_ampere, vecNeg J_ampere, G_gauss⟩ ∧
     J_minus = ⟨-G_gauss, vecNeg J_ampere, J_ampere, G_gauss⟩) ∧
    -- Z₃: Steps 3 & 4 — 4th-order Noether commutator and wave anticommutator
    (adjointDiv p J_ampere - NonCommutativeBimetricSheetGeometry.rcomm d0 G_gauss = 0 ∧
     (zornComm Dp J_plus).α = 0 ∧
     (zornComm Dm J_minus).α = 0 ∧
     zornSub W_plus W_minus =
       ⟨0, vecAdd waveSource waveSource, vecAdd waveSource waveSource, 0⟩) ∧
    -- Z₄: Non-Abelian g_S = 2 chromoelectric wave equation & curvature square bridge
    (vecSub (vecAdd dt2_E lap_E) spin1_g2 = waveSource ∧
     (zornSub (zornMul Fp Fp) (zornMul Fm Fm)).x = spin1_g2) := by
  have hZ0 := archetype_Z0_bianchi_vanishing_ricci_obstruction_and_symmetric_adjoint_curl d0 p U V
  have hZ1 := archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator d0 p
  have hZ2 := archetype_Z2_unified_gauss_ampere_anticommutator d0 p
  have hZ3 := archetype_Z3_fourth_order_noether_commutator_and_wave_anticommutator d0 p
  have hZ4 := archetype_Z4_non_abelian_g2_chromoelectric_wave_equation d0 p
  refine ⟨⟨hZ0.1, hZ0.2.1, hZ0.2.2.1, hZ0.2.2.2.1, hZ0.2.2.2.2.1⟩,
          ⟨hZ1.1, hZ1.2.1, hZ1.2.2.1, hZ1.2.2.2.2.1⟩,
          ⟨hZ2.1, hZ2.2⟩,
          ⟨hZ3.1, hZ3.2.1, hZ3.2.2.2.1, hZ3.2.2.2.2.2.2.2⟩,
          ⟨hZ4.2.2.1, hZ4.2.2.2.2.2⟩⟩

/-- **Archetype $\mathcal{U}_{12}$ (`archetype_U12_navier_madelung_dirac_schrodinger_grand_unification`):**
**Grand Unification of the Non-Commutative Dirac $\to$ Pauli–Schrödinger $\to$ Madelung $\to$ Navier–Stokes Hierarchy over `[Ring B]`:**
Unifies across the Peirce algebra `B`, `Mat2 B`, and 3D Zorn vector-matrices `ZornMatNC B`:
1. **Peirce Chiral Dirac-to-Schrödinger Factorization ($\mathcal{V}_5$):**
   For $\Psi_+ = \Phi + J$ and $\Psi_- = \Phi - J$,
   $\Psi_+^2 = 0$, $\Psi_-^2 = 0$, $\{\Psi_+, \Psi_-\} = 4 V$, and $[\Psi_+, \Psi_-] = 4 \Omega_{\mathrm{vortex}}$.
2. **Schrödinger-to-Madelung Real/Imaginary Double-Commutator Split ($\mathcal{V}_5$):**
   $\mathcal{S}_{+-}(Z) + \mathcal{S}_{-+}(Z) = 2(\mathcal{D}_{\mathrm{visc}}(J, Z) - \mathcal{Q}_{\mathrm{Bohm}}(\Phi, Z))$ (Hamilton–Jacobi–Bohm balance)
   and $\mathcal{S}_{+-}(Z) - \mathcal{S}_{-+}(Z) = 4\,\mathcal{L}(Z, \Omega_{\mathrm{vortex}})$ (Navier–Stokes Lamb vorticity transport).
3. **$\mathrm{Mat}_2(B)$ Massive Dirac-to-Gross–Pitaevskii Vortex Core Square ($\mathcal{V}_4$):**
   $D_\xi(A, C, m_\xi)^2 = V(A, C) + \mathrm{diagScalar}(m_\xi^2) + \begin{pmatrix} 0 & [m_\xi, A] \\ [C, m_\xi] & 0 \end{pmatrix}$ and $\operatorname{tr}_2(\Sigma(A, C)) = [A, C]$.
4. **3D Zorn–Dirac–Madelung–Navier–Stokes Helicity & $g_S = 2$ Vortex-Stretching Wave Equation ($\mathcal{Z}_0..\mathcal{Z}_4$):**
   For 3D velocity $\mathbf{u} \in \mathrm{Vec3NC}(B)$, convective enthalpy operator $h_0 \in B$, vorticity $\boldsymbol{\omega} = \mathbf{u} \times \mathbf{u}$, and convective acceleration $\mathbf{a} = [h_0, \mathbf{u}]$:
   - $\widehat{\mathcal{D}}_+(h_0, \mathbf{u})^2 = \widehat{\mathcal{L}}_{\mathrm{KG}}(h_0, \mathbf{u}) + \widehat{\mathcal{F}}_+(h_0, \mathbf{u})$ and $(\widehat{\mathcal{D}}_+^2 \cdot_Z \widehat{\mathcal{D}}_+ - \widehat{\mathcal{D}}_+ \cdot_Z \widehat{\mathcal{D}}_+^2)_\alpha = 2(\mathbf{u} \cdot \boldsymbol{\omega})$ (3D fluid helicity);
   - $[h_0, [h_0, \mathbf{a}]] + \Delta_{\mathrm{ad}}\mathbf{a} - 2(\boldsymbol{\omega} \times_{\mathrm{ad}} \mathbf{a}) = [h_0, \mathbf{J}_{\mathrm{NS}}] + \mathrm{Grad}_{\mathrm{ad}}(\mathbf{u}, G_{\mathrm{div}})$! -/
theorem archetype_U12_navier_madelung_dirac_schrodinger_grand_unification
    {P : B} (hP : P * P = P) (X Y Z A C m_xi h0 : B) (u : Vec3NC B) :
    let Phi    := NonCommutativeBimetricSheetGeometry.genPhi P X Y
    let J      := NonCommutativeBimetricSheetGeometry.genJ P X Y
    let V      := NonCommutativeBimetricSheetGeometry.genV P X Y
    let Om_v   := NonCommutativeBimetricSheetGeometry.genSig P X Y
    let Psi_p  := Phi + J
    let Psi_m  := Phi - J
    let V4     := V + V + V + V
    let Om4    := Om_v + Om_v + Om_v + Om_v
    let S_pm   := NonCommutativeNavierMadelungChiralVortexPoset.chiralSchrodingerPlusMinus P X Y
    let S_mp   := NonCommutativeNavierMadelungChiralVortexPoset.chiralSchrodingerMinusPlus P X Y
    let D_visc := NonCommutativeNavierMadelungChiralVortexPoset.viscousCurv P X Y Z
    let Q_bohm := NonCommutativeBimetricSheetGeometry.bohmCurv P X Y Z
    let L_vort := NonCommutativeNavierMadelungChiralVortexPoset.lambOperator Z Om_v
    let D_xi   := NonCommutativeNavierMadelungChiralVortexPoset.Mat2.matRegularizedVortex A C m_xi
    let a_acc  := covE h0 u
    let ω_vort := covB u
    let G_div  := adjointDiv u a_acc
    let J_NS   := vecSub (vecComm h0 a_acc) (adjointCurl u ω_vort)
    let dt2_a  := vecComm h0 (vecComm h0 a_acc)
    let lap_a  := bochnerLaplacian u a_acc
    let ωxa    := adjointCurl ω_vort a_acc
    let Dp     := weylZornPlus h0 u
    let Fp     := curvZornPlus h0 u
    let hel2   := vecNambu3 u + vecNambu3 u
    -- 1. Peirce Chiral Dirac-to-Schrödinger factorization:
    (Psi_p * Psi_p = 0 ∧
     Psi_m * Psi_m = 0 ∧
     NonCommutativeBimetricSheetGeometry.racomm Psi_p Psi_m = V4 ∧
     NonCommutativeBimetricSheetGeometry.rcomm Psi_p Psi_m = Om4) ∧
    -- 2. Schrödinger-to-Madelung Hamilton-Jacobi-Bohm & Navier-Stokes Lamb splitting:
    (S_pm Z + S_mp Z = (D_visc - Q_bohm) + (D_visc - Q_bohm) ∧
     S_pm Z - S_mp Z = L_vort + L_vort + L_vort + L_vort) ∧
    -- 3. Mat2 Massive Dirac-to-Gross-Pitaevskii vortex core regularization & ABJ trace anomaly:
    (D_xi * D_xi =
       NonCommutativeBimetricSheetGeometry.Mat2.matV A C +
       NonCommutativeBimetricSheetGeometry.Mat2.diagScalar (m_xi * m_xi) +
       ⟨0, NonCommutativeBimetricSheetGeometry.rcomm m_xi A,
           NonCommutativeBimetricSheetGeometry.rcomm C m_xi, 0⟩ ∧
     NonCommutativeBimetricSheetGeometry.Mat2.tr2
       (NonCommutativeBimetricSheetGeometry.Mat2.matSig A C) =
       NonCommutativeBimetricSheetGeometry.rcomm A C) ∧
    -- 4. 3D Zorn–Dirac–Madelung–Navier–Stokes helicity & g_S = 2 vortex-stretching wave equation:
    (zornMul Dp Dp = zornAdd (kgZorn h0 u) Fp ∧
     (zornSelfAssociator Dp).α = hel2 ∧
     vecSub (vecAdd dt2_a lap_a) (vecAdd ωxa ωxa) =
       vecAdd (vecComm h0 J_NS) (adjointGrad u G_div)) := by
  have hV5 := NonCommutativeNavierMadelungChiralVortexPoset.archetype_V5_dirac_schrodinger_madelung_navier_stokes_chiral_splitting hP X Y Z
  have hV4 := NonCommutativeNavierMadelungChiralVortexPoset.Mat2.archetype_V4_matrix_chiral_vortex_core_regularization_and_star_positivity A C m_xi
  have hZ1 := archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator h0 u
  have hZ4 := archetype_Z4_non_abelian_g2_chromoelectric_wave_equation h0 u
  refine ⟨⟨hV5.1, hV5.2.1, hV5.2.2.1, hV5.2.2.2.1⟩,
          ⟨hV5.2.2.2.2.1, hV5.2.2.2.2.2.1⟩,
          ⟨hV4.2.2.2.2.2.2.2.2, hV4.2.2.2.2.2.1⟩,
          ⟨hZ1.1, hZ1.2.2.1, hZ4.2.2.1⟩⟩

-- ============================================================================
-- 13. ARCHETYPE U₁₃: ZORN–YANG–MILLS LADDER ↔ NAVIER–MADELUNG CHIRAL VORTEX
--     HELICITY & ERTEL–BIANCHI ANOMALY BRIDGE (Z₀–Z₄ × V₀–V₅ ≺ U₁₃)
-- ============================================================================

/-- Coordinate isomorphism from `Vec3NC B` to Xambó's `Vec3 B`. -/
@[simp] def vec3NCToXambo (v : Vec3NC B) :
    NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B :=
  ⟨v.v1, v.v2, v.v3⟩

/-- Inverse coordinate isomorphism from Xambó's `Vec3 B` to `Vec3NC B`. -/
@[simp] def xamboToVec3NC (u : NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) :
    Vec3NC B :=
  ⟨u.x, u.y, u.z⟩

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{U}_{13}$ (`archetype_U13_zorn_navier_madelung_vortex_helicity_and_ertel_bianchi_bridge`):**
**Unification of the Zorn–Yang–Mills 4-Step Ladder ($\mathcal{Z}_0\text{–}\mathcal{Z}_4$) with the Navier–Madelung Chiral Vortex Anomaly Poset ($\mathcal{V}_0\text{–}\mathcal{V}_5$):**
Over ANY non-commutative associative ring `[Ring B]` and ANY `d0 : B`, `p U V : Vec3NC B`:
1. **Chromomagnetic Field = Navier–Madelung Self-Cross Chiral Vortex Curvature ($\mathcal{Z}_0 \leftrightarrow \mathcal{V}_3$):**
   `vec3NCToXambo (covB p) = Rotor3.cross3 (vec3NCToXambo p) (vec3NCToXambo p)`.
2. **Adjoint Curl = Navier–Madelung Lamb Cross-Product Anomaly ($\mathcal{Z}_0 \leftrightarrow \mathcal{V}_3$):**
   `vec3NCToXambo (adjointCurl U V) = addVec3 (Rotor3.cross3 (vec3NCToXambo U) (vec3NCToXambo V)) (Rotor3.cross3 (vec3NCToXambo V) (vec3NCToXambo U))`.
3. **Triple Identity of the Nambu Helicity ($\mathcal{Z}_1 \leftrightarrow \mathcal{V}_3 \leftrightarrow \mathcal{N}_3$):**
   The Nambu ternary bracket `vecNambu3 p = p · (p × p)`, the Navier–Madelung chiral vortex helicity
   `Rotor3.dot3 (vec3NCToXambo p) (Rotor3.cross3 (vec3NCToXambo p) (vec3NCToXambo p))`, and half the
   Zorn cubic self-associator `(zornSelfAssociator (weylZornPlus d0 p)).α` are identical:
   `vecNambu3 p = Rotor3.dot3 (vec3NCToXambo p) (Rotor3.cross3 (vec3NCToXambo p) (vec3NCToXambo p))` and
   `(zornSelfAssociator (weylZornPlus d0 p)).α = 2 • Rotor3.dot3 (vec3NCToXambo p) (Rotor3.cross3 (vec3NCToXambo p) (vec3NCToXambo p))`.
4. **Universal Non-Commutative Helicity Anomaly & Ertel–Bianchi Evolution Law over `[Ring B]`:**
   `[d0, vecNambu3 p] = vecDot (covE d0 p) (covB p) + vecDot p (adjointCurl p (covE d0 p))` and
   `[d0, vecNambu3 p] = (vecDot (covE d0 p) (covB p) + vecDot (covB p) (covE d0 p)) + vecDot (vecCross p (covE d0 p)) p`! -/
theorem archetype_U13_zorn_navier_madelung_vortex_helicity_and_ertel_bianchi_bridge
    (d0 : B) (p U V : Vec3NC B) :
    let E       := covE d0 p
    let B_vec   := covB p
    let p_xambo := vec3NCToXambo p
    let U_xambo := vec3NCToXambo U
    let V_xambo := vec3NCToXambo V
    let H_vort  := NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3 p_xambo
                     (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 p_xambo p_xambo)
    let Dp      := weylZornPlus d0 p
    -- 1. Chromomagnetic field = Navier–Madelung self-cross chiral vortex curvature:
    vec3NCToXambo B_vec =
      NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 p_xambo p_xambo ∧
    -- 2. Adjoint curl = Navier–Madelung Lamb cross-product anomaly:
    vec3NCToXambo (adjointCurl U V) =
      NonCommutativeNavierMadelungChiralVortexPoset.addVec3
        (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 U_xambo V_xambo)
        (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 V_xambo U_xambo) ∧
    -- 3. Triple identity of Nambu bracket, Navier–Madelung vortex helicity, and Zorn self-associator:
    vecNambu3 p = H_vort ∧
    (zornSelfAssociator Dp).α = H_vort + H_vort ∧
    -- 4. Universal Non-Commutative Helicity Anomaly & Ertel–Bianchi Evolution Law:
    NonCommutativeBimetricSheetGeometry.rcomm d0 (vecNambu3 p) =
      vecDot E B_vec + vecDot p (adjointCurl p E) ∧
    NonCommutativeBimetricSheetGeometry.rcomm d0 (vecNambu3 p) =
      (vecDot E B_vec + vecDot B_vec E) + vecDot (vecCross p E) p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> exact Eq.refl _
  · ext <;>
    · (simp only [vec3NCToXambo, adjointCurl,
                  NonCommutativeNavierMadelungChiralVortexPoset.addVec3,
                  NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3,
                  NonCommutativeBimetricSheetGeometry.rcomm])
      abel
  · exact Eq.refl _
  · exact (archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator d0 p).2.2.1
  · zorn_nc_calc
  · zorn_nc_calc

-- ============================================================================
-- 14. ARCHETYPE U₁₄: OPERATOR DE RHAM–DIRAC–KÄHLER, OPERATOR PELL &
--     MALIK–THOME DRAZIN–TETRAKTYS UNIFICATION (Z₀–Z₄ × ZND₁–ZND₃ × S₀–S₄ ≺ U₁₄)
-- ============================================================================

/-- Coordinate isomorphism from `Vec3NC B` to `ZornNambuDeRhamDiracKahlerPoset.Vec3 B`. -/
@[simp] def vec3NCToZND (v : Vec3NC B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 B :=
  ⟨v.v1, v.v2, v.v3⟩

/-- Inverse coordinate isomorphism from `ZornNambuDeRhamDiracKahlerPoset.Vec3 B` to `Vec3NC B`. -/
@[simp] def zndToVec3NC
    (u : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 B) :
    Vec3NC B :=
  ⟨u.x, u.y, u.z⟩

/-- Non-associative Zorn matrix isomorphism from `ZornMatNC B` to `ZornNambuDeRhamDiracKahlerPoset.ZornNC B`. -/
@[simp] def zornMatNCToZND (M : ZornMatNC B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornNC B :=
  ⟨M.α, vec3NCToZND M.x, vec3NCToZND M.y, M.β⟩

/-- Inverse Zorn matrix isomorphism from `ZornNambuDeRhamDiracKahlerPoset.ZornNC B` to `ZornMatNC B`. -/
@[simp] def zndToZornMatNC
    (X : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornNC B) :
    ZornMatNC B :=
  ⟨X.α, zndToVec3NC X.x, zndToVec3NC X.y, X.β⟩

/-- The two vector carriers have the same adjoint-curl coordinates. -/
theorem vec3NCToZND_adjointCurl (p V : Vec3NC B) :
    vec3NCToZND (adjointCurl p V) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointCurl
        (vec3NCToZND p) (vec3NCToZND V) := by
  ext <;>
    simp [vec3NCToZND, adjointCurl, vecCross,
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointCurl,
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.cross,
      NonCommutativeBimetricSheetGeometry.rcomm] <;> abel

/-- The two vector carriers have the same adjoint-divergence scalar. -/
theorem adjointDiv_eq_znd (p V : Vec3NC B) :
    adjointDiv p V =
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv
        (vec3NCToZND p) (vec3NCToZND V) := by
  (simp [adjointDiv, vecDot,
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv,
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.dot,
    NonCommutativeBimetricSheetGeometry.rcomm])
  abel

set_option linter.unusedSimpArgs false in
/-- **Archetype $\mathcal{U}_{14}$ (`archetype_U14_zorn_de_rham_dirac_kaehler_pell_drazin_unification`):**
**Unification of the 4-Step Zorn–Yang–Mills Ladder ($\mathcal{Z}_0\text{–}\mathcal{Z}_4$), the 3D Operator De Rham–Dirac–Kähler Complex ($\mathrm{ZND}_1\text{–}\mathrm{ZND}_2$), and the Operator Pell / Malik–Thome Drazin–Tetraktys Spine ($\mathrm{ZND}_3 \leftrightarrow \mathcal{S}_0\text{–}\mathcal{S}_4$):**
Over ANY non-commutative associative ring `[Ring B]`:
1. **Zorn–De Rham Carrier & Operator Intertwiners ($\mathcal{Z}_0\text{–}\mathcal{Z}_4 \leftrightarrow \mathrm{ZND}_1\text{–}\mathrm{ZND}_2$):**
   - `zornMatNCToZND (zornMul M N) = zornMatNCToZND M * zornMatNCToZND N` and
     `zornMatNCToZND (weylZornPlus d0 p) = ZornNC.diracPlus d0 (vec3NCToZND p)`.
   - `vec3NCToZND (adjointGrad p φ) = (ZornForms.extCurl (vec3NCToZND p) (ZornForms.form0 φ)).ω1`,
     `vec3NCToZND (adjointCurl p V) = (ZornForms.extCurl (vec3NCToZND p) (ZornForms.form1 (vec3NCToZND V))).ω2`,
     `adjointDiv p V = (ZornForms.extDiv (vec3NCToZND p) (ZornForms.form1 (vec3NCToZND V))).ω0`, and
     `vecNambu3 p = Vec3.nambu3 (vec3NCToZND p)`.
2. **Dirac–Kähler Square vs. Zorn–Weitzenböck Wave Operator & Commutator/Anticommutator Pontryagin Split ($\mathrm{DK}_5, \mathrm{DK}_7, \mathrm{DK}_8 \leftrightarrow \mathcal{Z}_4$):**
   - On `form1 (vec3NCToZND E)` where `E = covE d0 p` and `B_vec = covB p`, the 1-form block of the
     Dirac–Kähler square `(ZornForms.diracKaehler p_znd (ZornForms.diracKaehler p_znd (ZornForms.form1 E_znd))).ω1`
     equals `vec3NCToZND (vecSub (bochnerLaplacian p E) (adjointCurl B_vec E))`.
   - The 3-step De Rham–Pontryagin chain `(ZornForms.extCurl p_znd (ZornForms.extCurl p_znd (ZornForms.extCurl p_znd (ZornForms.form0 d0)))).ω3`
     equals the **commutator Pontryagin density** `vecDot E B_vec - vecDot B_vec E`, whose sum with
     half the Zorn curvature-square difference `vecDot E B_vec + vecDot B_vec E` isolates `2 • vecDot E B_vec`.
3. **Operator Pell Equation & Malik–Thome Drazin–Tetraktys Unification ($\mathrm{MT}_1, \mathrm{MT}_4 \leftrightarrow \mathcal{S}_0\text{–}\mathcal{S}_4$):**
   - For any `Q : B` (without assuming `Q * Q = Q`), `ZornNambuDeRhamDiracKahlerPoset.invS Q = NonCommutativeBimetricSheetGeometry.invS Q`,
     `invS Q * invS Q - fourOp (idempDefect Q) = 1`, and
     `idempDefect (newtonStep Q) = (idempDefect Q * idempDefect Q) * (fourOp (idempDefect Q) - threeOp 1)`.
   - For any Drazin resolution `DrazinResolution M_op P C_core N_nil B_d` and any `Mdag : B` satisfying
     `P * Mdag * P = B_d` and `N_nil * Mdag * N_nil = N_nil`, the Malik–Thome DMP/MPD generalized
     inverses decompose into the Bimetric Peirce sheet bridge `NonCommutativeBimetricSheetGeometry.genPhi P Mdag Mdag`:
     `dmpOp B_d M_op Mdag = B_d + NonCommutativeBimetricSheetGeometry.conePlus P Mdag`,
     `mpdOp B_d M_op Mdag = B_d + NonCommutativeBimetricSheetGeometry.coneMinus P Mdag`,
     `Mdag = B_d + row4ShadowOp B_d M_op Mdag + NonCommutativeBimetricSheetGeometry.genPhi P Mdag Mdag`, and
     `dmpOp B_d M_op Mdag * C_core * mpdOp B_d M_op Mdag = B_d`. -/
theorem archetype_U14_zorn_de_rham_dirac_kaehler_pell_drazin_unification
    (d0 φ Q : B) (p V : Vec3NC B) (M N : ZornMatNC B)
    {M_op P C_core N_nil B_d Mdag : B}
    (hD : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.DrazinResolution
            M_op P C_core N_nil B_d)
    (hMonad : P * Mdag * P = B_d)
    (hNilMP : N_nil * Mdag * N_nil = N_nil) :
    let E       := covE d0 p
    let B_vec   := covB p
    let p_znd   := vec3NCToZND p
    let V_znd   := vec3NCToZND V
    let E_znd   := vec3NCToZND E
    let ω1_E    := InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form1 E_znd
    let ω0_d0   := InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form0 d0
    let dk2_E   := InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.diracKaehler
                     p_znd
                     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.diracKaehler
                       p_znd ω1_E)
    let d3_d0   := InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl
                     p_znd
                     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl
                       p_znd
                       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl
                         p_znd ω0_d0))
    let pont_c  := vecDot E B_vec - vecDot B_vec E
    let pont_a  := vecDot E B_vec + vecDot B_vec E
    -- 1. Zorn–De Rham carrier & operator intertwiners:
    (zornMatNCToZND (zornMul M N) = zornMatNCToZND M * zornMatNCToZND N ∧
     zornMatNCToZND (weylZornPlus d0 p) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornNC.diracPlus d0 p_znd ∧
     vec3NCToZND (adjointGrad p φ) =
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl p_znd
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form0 φ)).ω1 ∧
     vec3NCToZND (adjointCurl p V) =
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl p_znd
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form1 V_znd)).ω2 ∧
     adjointDiv p V =
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extDiv p_znd
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form1 V_znd)).ω0 ∧
     vecNambu3 p =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.nambu3 p_znd) ∧
    -- 2. Dirac–Kähler square vs. Zorn–Weitzenböck wave operator & Pontryagin commutator/anticommutator split:
    (dk2_E.ω1 = vec3NCToZND (vecSub (bochnerLaplacian p E) (adjointCurl B_vec E)) ∧
     d3_d0.ω3 = pont_c ∧
     pont_c + pont_a = vecDot E B_vec + vecDot E B_vec) ∧
    -- 3. Operator Pell equation, Malik–Thome Drazin–Tetraktys & 5-Graded NCG Cartan Curvature Unification:
    (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.invS Q =
       NonCommutativeBimetricSheetGeometry.invS Q ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.invS Q *
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.invS Q -
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.fourOp
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.idempDefect Q) = 1 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.idempDefect
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.newtonStep Q) =
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.idempDefect Q *
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.idempDefect Q) *
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.fourOp
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.idempDefect Q) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.threeOp 1) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.dmpOp B_d M_op Mdag =
       B_d + NonCommutativeBimetricSheetGeometry.conePlus P Mdag ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.mpdOp B_d M_op Mdag =
       B_d + NonCommutativeBimetricSheetGeometry.coneMinus P Mdag ∧
     Mdag =
       B_d +
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.row4ShadowOp B_d M_op Mdag +
       NonCommutativeBimetricSheetGeometry.genPhi P Mdag Mdag ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.dmpOp B_d M_op Mdag *
       C_core *
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.mpdOp B_d M_op Mdag = B_d ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartanCurvature5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartan3Grade d0 φ p_znd p_znd)
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartan3Grade φ d0 V_znd V_znd)).gp2 =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartanCurvature5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartan3Grade d0 φ p_znd p_znd)
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.cartan3Grade φ d0 V_znd V_znd)).gm2 =
       -InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.kantorBracket
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP1 p_znd)
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP1 V_znd) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP2
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.elieCartanTorsion5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP2
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd))
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injM1 V_znd) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP1
         (-InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adCross
           (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd)
           V_znd) ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.riemannConformalCurv5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injM2
         (-InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd))
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP2
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd))).g0L +
     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.riemannConformalCurv5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injM2
         (-InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd))
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP2
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd))).g0R =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv
         (-InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd)
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross p_znd V_znd) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.kantorAnomalyDefect
         p_znd V_znd E_znd =
       -InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv
         V_znd
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.cross p_znd E_znd) ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.riemannConformalCurv5D
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injM2 p_znd)
       (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.kantorBracket
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP1 V_znd)
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.injP1 E_znd))).g0L =
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.dot
         (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointCurl p_znd V_znd)
         E_znd +
       InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.kantorAnomalyDefect
         p_znd V_znd E_znd) := by
  have hPell :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.archetype_A81_operator_pell_equation_and_wavelet_scaling Q
  have hMT :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.monad_sandwich_master_mp_and_row4_nilpotent_inversion
      hD hMonad hNilMP
  have hCartan :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.noncommutative_3grade_cartan_curvature_commutator_decomposition
      d0 φ φ d0 (vec3NCToZND p) (vec3NCToZND p) (vec3NCToZND V) (vec3NCToZND V)
  have hAnom :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.higher_grade_anomaly_generators_source_torsion_and_curvature
      (vec3NCToZND p) (vec3NCToZND V) (vec3NCToZND p) (vec3NCToZND V)
      (vec3NCToZND p) (vec3NCToZND V)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross (vec3NCToZND p) (vec3NCToZND V))
      (-InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commCross (vec3NCToZND p) (vec3NCToZND V))
      (⟨M.α, vec3NCToZND M.x, vec3NCToZND M.y, M.β⟩ :
        InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix B)
  have hBianchi :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded.bianchi_torsion_exterior_derivative_determines_conformal_curvature
      (vec3NCToZND p) (vec3NCToZND V) (vec3NCToZND (covE d0 p))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
          ⟨?_, hPell.2.1, hPell.2.2.2.2.2.2.2.1, hMT.1, hMT.2.1, hMT.2.2.2.1, hMT.2.2.2.2.2.2.1,
           hCartan.2.2.2.1, hCartan.2.2.2.2.1, hAnom.1, hAnom.2.2.2.2.1, hAnom.2.2.2.2.2.2.2.2.2.1,
           InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.kantorAnomalyDefect_eq_neg_adjointDiv_cross _ _ _,
           hBianchi.2.2.2.2.1⟩⟩
  · ext <;> exact Eq.refl _
  · ext <;> exact Eq.refl _
  · ext <;> exact Eq.refl _
  · exact vec3NCToZND_adjointCurl p V
  · exact adjointDiv_eq_znd p V
  · exact Eq.refl _
  · ext <;>
    · (simp only [vec3NCToZND, covE, covB, vecComm, vecSub, bochnerLaplacian, bochnerLapScalar,
                  adjointCurl, vecCross, NonCommutativeBimetricSheetGeometry.rcomm,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.diracKaehler,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extDiv,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form1,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.zero_ω0,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.zero_ω1,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.zero_ω2,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.zero_ω3,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.add_ω0,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.add_ω1,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.add_ω2,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.add_ω3,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.dot,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.cross,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_x,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_y,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_z,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_x,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_y,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_z,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_x,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_y,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_z,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_x,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_y,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_z,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointGrad,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointCurl,
                  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commOp,
                  neg_mul, mul_neg, mul_add, add_mul, sub_mul, mul_sub,
                  mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
                  neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero, mul_assoc])
      abel
  · (simp only [vec3NCToZND, covE, covB, vecComm, vecDot, vecCross,
                NonCommutativeBimetricSheetGeometry.rcomm,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.extCurl,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms.form0,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.dot,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.cross,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_x,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_y,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.add_z,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_x,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_y,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.sub_z,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_x,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_y,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.neg_z,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_x,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_y,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.zero_z,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointGrad,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointDiv,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.adjointCurl,
                InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3.commOp,
                neg_mul, mul_neg, mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
                neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero, mul_assoc])
    abel
  · abel
  · simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.invS,
               NonCommutativeBimetricSheetGeometry.invS]

/-- Explicit noncommutativity witness for the carrier `Matrix (Fin 2) (Fin 2) ℤ`.
This theorem records noncommutativity of the integer matrix carrier; it does not assert
or certify the U₀–U₆ dependency poset. -/
theorem fin2_integer_matrix_has_noncommuting_pair :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℤ, X * Y ≠ Y * X := by
  refine ⟨wittNullU, wittNullV, ?_⟩
  intro h
  have h00 : (wittNullU * wittNullV : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
      (wittNullV * wittNullU : Matrix (Fin 2) (Fin 2) ℤ) 0 0 :=
    congrFun (congrFun h 0) 0
  revert h00
  decide

/-- **Inductive Colimit Cone Transport (`cartan_bhoja_krasnov_colimit_cone_transport`):**
    Under any compatible inductive ring cone `toLimit : ∀ k : ℕ, Stage k →+* Limit`
    (`toLimit (k + 1) (embed k Z) = toLimit k Z`), the Nambu ternary bracket `vecNambu3`,
    magnetic/Faraday–Bianchi identities (`archetype_Z0`), and Zorn–Lichnerowicz–Weitzenböck
    cubic self-associator Nambu doubling (`archetype_Z1`) transport functorially into `Limit`. -/
theorem cartan_bhoja_krasnov_colimit_cone_transport
    {Stage : ℕ → Type u} [∀ k, Ring (Stage k)]
    {Limit : Type u} [Ring Limit]
    (embed : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (toLimit : ∀ k : ℕ, Stage k →+* Limit)
    (hCone : ∀ (k : ℕ) (Z : Stage k), toLimit (k + 1) (embed k Z) = toLimit k Z)
    (k : ℕ) (d0 : Stage k) (p : Vec3NC (Stage k)) :
    let d0_inf := toLimit k d0
    let p_inf : Vec3NC Limit := ⟨toLimit k p.v1, toLimit k p.v2, toLimit k p.v3⟩
    let p_emb : Vec3NC (Stage (k + 1)) := ⟨embed k p.v1, embed k p.v2, embed k p.v3⟩
    toLimit k (vecNambu3 p) = vecNambu3 p_inf ∧
    toLimit (k + 1) (vecNambu3 p_emb) = vecNambu3 p_inf ∧
    adjointDiv p_inf (covB p_inf) = 0 ∧
    vecSub (vecComm d0_inf (covB p_inf)) (adjointCurl p_inf (covE d0_inf p_inf)) = vecZero ∧
    (zornSelfAssociator (weylZornPlus d0_inf p_inf)).α = vecNambu3 p_inf + vecNambu3 p_inf ∧
    (zornSelfAssociator (weylZornPlus d0_inf p_inf)).β = -(vecNambu3 p_inf + vecNambu3 p_inf) := by
  have hNam : toLimit k (vecNambu3 p) =
      vecNambu3 (⟨toLimit k p.v1, toLimit k p.v2, toLimit k p.v3⟩ : Vec3NC Limit) := by
    dsimp [vecNambu3, vecDot, vecCross, Vec3NC.v1, Vec3NC.v2, Vec3NC.v3]
    simp only [map_add, map_sub, map_mul]
  have hNamEmb : toLimit (k + 1) (vecNambu3 (⟨embed k p.v1, embed k p.v2, embed k p.v3⟩ : Vec3NC (Stage (k + 1)))) =
      vecNambu3 (⟨toLimit k p.v1, toLimit k p.v2, toLimit k p.v3⟩ : Vec3NC Limit) := by
    have hE : embed k (vecNambu3 p) =
        vecNambu3 (⟨embed k p.v1, embed k p.v2, embed k p.v3⟩ : Vec3NC (Stage (k + 1))) := by
      dsimp [vecNambu3, vecDot, vecCross, Vec3NC.v1, Vec3NC.v2, Vec3NC.v3]
      simp only [map_add, map_sub, map_mul]
    rw [← hE, hCone k, hNam]
  set d0_inf := toLimit k d0
  set p_inf : Vec3NC Limit := ⟨toLimit k p.v1, toLimit k p.v2, toLimit k p.v3⟩
  have hZ0 := archetype_Z0_bianchi_vanishing_ricci_obstruction_and_symmetric_adjoint_curl
    d0_inf p_inf p_inf p_inf
  have hZ1 := archetype_Z1_zorn_lichnerowicz_weitzenboeck_and_cubic_nambu_associator
    d0_inf p_inf
  exact ⟨hNam, hNamEmb, hZ0.1, hZ0.2.1, hZ1.2.2.1, hZ1.2.2.2.1⟩

end InfoGeometry.Canonical.CartanBhojaKrasnovXamboAharonovUnificationBridge
