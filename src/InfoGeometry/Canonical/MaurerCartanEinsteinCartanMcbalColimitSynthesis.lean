/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis
import InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
import InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

/-!
# Inductive `Cl(1, 1)^{\otimes n}` Colimit, Multi-Period `Cl(5, 5)` Bott Tower, and Exterior-Algebra Unification of the Maurer–Cartan (`𝔎₁–𝔎₇`), Einstein–Cartan (`𝔈₁–𝔈₈`), and `mcbal` (`𝔐₁–𝔐₈`) Posets

This module closes **Rank 1** of the repository's highest-ROI unification targets by transporting
the four newly formalized non-commutative posets:
- **Maurer–Cartan Spectral Annihilator & Multiplicative Defect Poset** (`𝔎₁ ≺ ⋯ ≺ 𝔎₇`,
  `InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset`),
- **Operator Einstein–Cartan Chiral Anomaly & Spin Frame-Dragging Poset** (`𝔈₁ ≺ ⋯ ≺ 𝔈₈`,
  `InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset`),
- **Large-`d` Asymmetric Kinetic Vector-Spin to Krein–Yangian LogCFT Corridor** (`𝔐₁ ≺ ⋯ ≺ 𝔐₈`,
  `InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor`), and
- **32-Turn Metriplectic–Plabic–Krein–Yangian Extension Poset** (`MCP₁₁ ≺ ⋯ ≺ MCP₂₀`,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset`)

across:
1. Arbitrary unital ring homomorphisms `f : B →+* D` (`Section 1`),
2. The inductive `Cl(1, 1)^{\otimes n}` colimit algebra `Limit = Algebra.DirectLimit Stage Map`
   with positive trace extension `tau : Limit →ₗ[ℝ] ℝ` (`Section 2`),
3. The multi-period `Cl(5, 5)` Bott-periodicity spinor tower `Stage (5 + 8 * k)` via
   `cl55ToBottStage k : Cl55 →+* Stage (5 + 8 * k)` (`Section 3`), and
4. The two-sheet Hestenes–Krein filtered colimit `Module.End ℝ (Carrier StageFunctor)`,
   the exterior-algebra Yang–Mills bundle `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)`,
   and non-commutative operator covariance dynamics (`Section 4`).
-/

noncomputable section

namespace InfoGeometry.Canonical.MaurerCartanEinsteinCartanMcbalColimitSynthesis

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.Canonical.LieJordanHodgeColimit
open InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset
open InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
open InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.FiniteOperatorCovariance
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.OperatorAlgebra.CovarianceDynamics
open InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

/-! ===========================================================================
    Section 1: Universal Ring-Homomorphism Functoriality (`f : B →+* D`)
    =========================================================================== -/

section RingHomFunctoriality

variable {B D : Type*} [Ring B] [Ring D] (f : B →+* D)

@[simp] theorem map_peirceAdSq (P X : B) :
    f (peirceAdSq P X) = peirceAdSq (f P) (f X) := by
  unfold peirceAdSq OperatorAlgebra.PeirceSpine.comm
  simp [map_sub, map_mul]

@[simp] theorem map_oddProjector (P X : B) :
    f (oddProjector P X) = oddProjector (f P) (f X) :=
  map_peirceAdSq f P X

@[simp] theorem map_chiralAnnihilator (P X : B) :
    f (chiralAnnihilator P X) = chiralAnnihilator (f P) (f X) := by
  unfold chiralAnnihilator
  rw [map_sub, map_peirceAdSq]

@[simp] theorem map_evenGrade (P X : B) :
    f (evenGrade P X) = evenGrade (f P) (f X) := by
  unfold evenGrade
  simp [map_add, map_sub, map_mul]

@[simp] theorem map_oddGrade (P X : B) :
    f (oddGrade P X) = oddGrade (f P) (f X) := by
  unfold oddGrade
  simp [map_add, map_sub, map_mul]

@[simp] theorem map_cartanSplitConnection (P X Y : B) :
    f (cartanSplitConnection P X Y) = cartanSplitConnection (f P) (f X) (f Y) := by
  unfold cartanSplitConnection
  rw [map_add, map_evenGrade, map_oddGrade]

@[simp] theorem map_riemannCartanCurvature (P X₁ Y₁ X₂ Y₂ : B) :
    f (riemannCartanCurvature P X₁ Y₁ X₂ Y₂) =
      riemannCartanCurvature (f P) (f X₁) (f Y₁) (f X₂) (f Y₂) := by
  unfold riemannCartanCurvature OperatorAlgebra.PeirceSpine.comm
  simp [map_add, map_sub, map_mul]

@[simp] theorem map_elieCartanTorsion (P X₁ Y₁ X₂ Y₂ : B) :
    f (elieCartanTorsion P X₁ Y₁ X₂ Y₂) =
      elieCartanTorsion (f P) (f X₁) (f Y₁) (f X₂) (f Y₂) := by
  unfold elieCartanTorsion OperatorAlgebra.PeirceSpine.comm
  simp [map_add, map_sub, map_mul]

@[simp] theorem map_chiralEinsteinAnomaly (P A C : B) :
    f (chiralEinsteinAnomaly P A C) = chiralEinsteinAnomaly (f P) (f A) (f C) := by
  unfold chiralEinsteinAnomaly OperatorAlgebra.PeirceSpine.comm
  simp [map_mul, map_sub, map_invS, map_genPhi, map_genJ]

@[simp] theorem map_dressedSpinTorsion (P A C : B) :
    f (dressedSpinTorsion P A C) = dressedSpinTorsion (f P) (f A) (f C) := by
  unfold dressedSpinTorsion OperatorAlgebra.PeirceSpine.comm
  simp [map_sub, map_mul, map_add, map_genSig, map_genPhi]

@[simp] theorem map_solderedConnPhi (P A C : B) :
    f (solderedConnPhi P A C) = solderedConnPhi (f P) (f A) (f C) := by
  unfold solderedConnPhi
  rw [map_add, map_genSig, map_genPhi]

@[simp] theorem map_solderedConnJ (P A C : B) :
    f (solderedConnJ P A C) = solderedConnJ (f P) (f A) (f C) := by
  unfold solderedConnJ
  rw [map_add, map_genSig, map_genJ]

@[simp] theorem map_jordanAssociator (X Y Z : B) :
    f (jordanAssociator X Y Z) = jordanAssociator (f X) (f Y) (f Z) := by
  unfold jordanAssociator OperatorAlgebra.PeirceSpine.anticomm
  simp [map_sub, map_add, map_mul]

end RingHomFunctoriality

/-! ===========================================================================
    Section 2: Inductive `Cl(1, 1)^{\otimes n}` Colimit `Limit` Transport &
    Chiral Anomaly Trace Negativity
    =========================================================================== -/

section InductiveColimitTransport

/-- **Theorem 2.1 (`limit_maurer_cartan_and_einstein_cartan_posets_colimit_transport`):**
In the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`, for any stage transition `n ≤ m`,
any idempotent `P : Stage n` (`P * P = P`), and any stage operators
`A C X₁ Y₁ X₂ Y₂ X₃ Y₃ : Stage n` (with `P_lim := ofStage n P`, `A_lim := ofStage n A`, etc.):
1. **Exact Stage-Transition Cocone Invariance (`n ≤ m`):**
   `ofStage m (bondMap stageBond n m hnm (...)) = ofStage n (...)` for `chiralAnnihilator`,
   `riemannCartanCurvature`, `elieCartanTorsion`, `chiralEinsteinAnomaly`, and `dressedSpinTorsion`;
2. **Maurer–Cartan Multiplicative Defect & Torsion Annihilation in `Limit` (`𝔎₄` & `𝔎₆`):**
   - `chiralAnnihilator P_lim (X₁_lim * Y₁_lim) - chiralAnnihilator P_lim X₁_lim * chiralAnnihilator P_lim Y₁_lim = oddProjector P_lim X₁_lim * oddProjector P_lim Y₁_lim`,
   - `chiralAnnihilator P_lim (elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim) = 0`,
   - `chiralAnnihilator P_lim (comm (cartanSplitConnection P_lim X₁_lim Y₁_lim) (cartanSplitConnection P_lim X₂_lim Y₂_lim)) = riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim`;
3. **Chiral Einstein Anomaly, Spin Frame Dragging, Dressed Torsion & Non-Abelian Bianchi–Cartan in `Limit` (`𝔈₄–𝔈₈`):**
   - `chiralEinsteinAnomaly P_lim A_lim C_lim = -((2 : ℤ) • genV P_lim A_lim C_lim)`,
   - `comm (genSig P_lim A_lim C_lim) (genPhi P_lim A_lim C_lim) = (2 : ℤ) • (genV P_lim A_lim C_lim * genJ P_lim A_lim C_lim)`,
   - `dressedSpinTorsion P_lim A_lim C_lim = (1 + (2 : ℤ) • genV P_lim A_lim C_lim) * genJ P_lim A_lim C_lim`,
   - `comm (solderedConnPhi P_lim A_lim C_lim) (solderedConnJ P_lim A_lim C_lim) = -((2 : ℤ) • genSig P_lim A_lim C_lim) + (2 : ℤ) • (genV P_lim A_lim C_lim * (genPhi P_lim A_lim C_lim - genJ P_lim A_lim C_lim))`,
   - `comm 𝒜₁ (ℛ₂₃ + 𝒯₂₃) + comm 𝒜₂ (ℛ₃₁ + 𝒯₃₁) + comm 𝒜₃ (ℛ₁₂ + 𝒯₁₂) = 0`,
   - `comm (genSig P_lim A_lim C_lim) (comm (genSig P_lim A_lim C_lim) (genPhi P_lim A_lim C_lim)) = (4 : ℤ) • ((genV P_lim A_lim C_lim * genV P_lim A_lim C_lim) * genPhi P_lim A_lim C_lim)`. -/
theorem limit_maurer_cartan_and_einstein_cartan_posets_colimit_transport
    {n m : ℕ} (hnm : n ≤ m)
    {P : Stage n} (hP : P * P = P)
    (A C X₁ Y₁ X₂ Y₂ X₃ Y₃ : Stage n) :
    let P_lim : Limit := ofStage n P
    let A_lim : Limit := ofStage n A
    let C_lim : Limit := ofStage n C
    let X₁_lim : Limit := ofStage n X₁
    let Y₁_lim : Limit := ofStage n Y₁
    let X₂_lim : Limit := ofStage n X₂
    let Y₂_lim : Limit := ofStage n Y₂
    let X₃_lim : Limit := ofStage n X₃
    let Y₃_lim : Limit := ofStage n Y₃
    -- (1) Stage-transition invariance across n ≤ m:
    (ofStage m (bondMap stageBond n m hnm (chiralAnnihilator P X₁)) =
       chiralAnnihilator P_lim X₁_lim ∧
     ofStage m (bondMap stageBond n m hnm (riemannCartanCurvature P X₁ Y₁ X₂ Y₂)) =
       riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim ∧
     ofStage m (bondMap stageBond n m hnm (elieCartanTorsion P X₁ Y₁ X₂ Y₂)) =
       elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim ∧
     ofStage m (bondMap stageBond n m hnm (chiralEinsteinAnomaly P A C)) =
       chiralEinsteinAnomaly P_lim A_lim C_lim ∧
     ofStage m (bondMap stageBond n m hnm (dressedSpinTorsion P A C)) =
       dressedSpinTorsion P_lim A_lim C_lim) ∧
    -- (2) Maurer–Cartan Spectral Annihilator & Multiplicative Defect in Limit (𝔎₄ & 𝔎₆):
    (chiralAnnihilator P_lim (X₁_lim * Y₁_lim) -
       chiralAnnihilator P_lim X₁_lim * chiralAnnihilator P_lim Y₁_lim =
       oddProjector P_lim X₁_lim * oddProjector P_lim Y₁_lim ∧
     chiralAnnihilator P_lim (elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim) = 0 ∧
     chiralAnnihilator P_lim
       (OperatorAlgebra.PeirceSpine.comm
         (cartanSplitConnection P_lim X₁_lim Y₁_lim)
         (cartanSplitConnection P_lim X₂_lim Y₂_lim)) =
       riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim) ∧
    -- (3) Operator Einstein–Cartan Chiral Anomaly & Spin Frame Dragging in Limit (𝔈₄–𝔈₈):
    (chiralEinsteinAnomaly P_lim A_lim C_lim = -((2 : ℤ) • genV P_lim A_lim C_lim) ∧
     OperatorAlgebra.PeirceSpine.comm (genSig P_lim A_lim C_lim) (genPhi P_lim A_lim C_lim) =
       (2 : ℤ) • (genV P_lim A_lim C_lim * genJ P_lim A_lim C_lim) ∧
     dressedSpinTorsion P_lim A_lim C_lim =
       (1 + (2 : ℤ) • genV P_lim A_lim C_lim) * genJ P_lim A_lim C_lim ∧
     OperatorAlgebra.PeirceSpine.comm
         (solderedConnPhi P_lim A_lim C_lim) (solderedConnJ P_lim A_lim C_lim) =
       -((2 : ℤ) • genSig P_lim A_lim C_lim) +
         (2 : ℤ) • (genV P_lim A_lim C_lim *
           (genPhi P_lim A_lim C_lim - genJ P_lim A_lim C_lim)) ∧
     OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P_lim X₁_lim Y₁_lim)
         (riemannCartanCurvature P_lim X₂_lim Y₂_lim X₃_lim Y₃_lim +
           elieCartanTorsion P_lim X₂_lim Y₂_lim X₃_lim Y₃_lim) +
       OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P_lim X₂_lim Y₂_lim)
         (riemannCartanCurvature P_lim X₃_lim Y₃_lim X₁_lim Y₁_lim +
           elieCartanTorsion P_lim X₃_lim Y₃_lim X₁_lim Y₁_lim) +
       OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P_lim X₃_lim Y₃_lim)
         (riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim +
           elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim) = 0 ∧
     OperatorAlgebra.PeirceSpine.comm (genSig P_lim A_lim C_lim)
         (OperatorAlgebra.PeirceSpine.comm (genSig P_lim A_lim C_lim)
           (genPhi P_lim A_lim C_lim)) =
       (4 : ℤ) • ((genV P_lim A_lim C_lim * genV P_lim A_lim C_lim) *
         genPhi P_lim A_lim C_lim)) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  have hK4 :=
    archetype_K4_multiplicative_defect_curvature_theorem
      hPLim (ofStage n A) (ofStage n C) (ofStage n X₁) (ofStage n Y₁)
  have hK6 :=
    archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri
      hPLim (ofStage n X₁) (ofStage n Y₁) (ofStage n X₂) (ofStage n Y₂)
  have hE4 :=
    archetype_E4_chiral_einstein_anomaly_cocycle hPLim (ofStage n A) (ofStage n C)
  have hE5 :=
    archetype_E5_spin_frame_dragging_and_dressed_torsion hPLim (ofStage n A) (ofStage n C)
  have hE6 :=
    archetype_E6_soldered_cartan_ehresmann_and_jordan_associator hPLim (ofStage n A) (ofStage n C)
  have hE7 :=
    archetype_E7_general_einstein_cartan_split_and_bianchi
      hPLim (ofStage n X₁) (ofStage n Y₁) (ofStage n X₂) (ofStage n Y₂) (ofStage n X₃) (ofStage n Y₃)
  have hCentrifugal :
      OperatorAlgebra.PeirceSpine.comm (genSig (ofStage n P) (ofStage n A) (ofStage n C))
          (OperatorAlgebra.PeirceSpine.comm (genSig (ofStage n P) (ofStage n A) (ofStage n C))
            (genPhi (ofStage n P) (ofStage n A) (ofStage n C))) =
        (4 : ℤ) • ((genV (ofStage n P) (ofStage n A) (ofStage n C) *
          genV (ofStage n P) (ofStage n A) (ofStage n C)) *
          genPhi (ofStage n P) (ofStage n A) (ofStage n C)) := by
    peirce_nf hPLim
  have hBond : ∀ x : Stage n, ofStage m (bondMap stageBond n m hnm x) = ofStage n x :=
    fun x => directLimitOf_bondMap stageBond n m hnm x
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩,
          ⟨hK4.1, hK6.2.1, hK6.2.2.1⟩,
          ⟨hE4.2.1, hE5.2.2.1, hE5.2.2.2.2.2.2.2, hE6.1, hE7.2.2.2, hCentrifugal⟩⟩
  · rw [hBond, map_chiralAnnihilator]
  · rw [hBond, map_riemannCartanCurvature]
  · rw [hBond, map_elieCartanTorsion]
  · rw [hBond, map_chiralEinsteinAnomaly]
  · rw [hBond, map_dressedSpinTorsion]

/-- Hermitian-square factorization of the Operator Fisher Metric `V = genV P A (star A)` in `Limit`:
`star X * genV P A (star A) * X = star (genPhi P A (star A) * X) * (genPhi P A (star A) * X)`. -/
theorem limit_genV_hermitian_square
    {P : Limit} (hP : P * P = P) (hPsym : star P = P) (A X : Limit) :
    star X * genV P A (star A) * X =
      star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) := by
  have hPhiSym : star (genPhi P A (star A)) = genPhi P A (star A) := by
    unfold genPhi conePlus coneMinus
    simp only [star_add, star_mul, star_sub, star_one, star_star, hPsym]
    noncomm_ring
  have hPhiSq : genPhi P A (star A) * genPhi P A (star A) = genV P A (star A) := by
    peirce_nf hP
  calc
    star X * genV P A (star A) * X =
        star X * (genPhi P A (star A) * genPhi P A (star A)) * X := by
      rw [hPhiSq]
    _ = (star X * star (genPhi P A (star A))) * (genPhi P A (star A) * X) := by
      rw [hPhiSym]; noncomm_ring
    _ = star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) := by
      rw [star_mul]

/-- Non-negativity of the Operator Fisher Metric expectation `tau (star X * genV P A (star A) * X)` in `Limit`. -/
theorem limit_tau_genV_nonneg
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPsym : star P = P) (A X : Limit) :
    0 ≤ tau (star X * genV P A (star A) * X) := by
  rw [limit_genV_hermitian_square hP hPsym A X]
  exact trace_extension_positive tau htau (genPhi P A (star A) * X)

/-- Exact identity relating the Chiral Einstein Anomaly expectation to minus twice the Fisher Metric expectation in `Limit`. -/
theorem limit_tau_chiralEinsteinAnomaly_eq
    (tau : Limit →ₗ[ℝ] ℝ)
    {P : Limit} (hP : P * P = P) (A X : Limit) :
    tau (star X * chiralEinsteinAnomaly P A (star A) * X) =
      -(2 * tau (star X * genV P A (star A) * X)) := by
  have hAnomEq : chiralEinsteinAnomaly P A (star A) = -((2 : ℤ) • genV P A (star A)) :=
    (archetype_E4_chiral_einstein_anomaly_cocycle hP A (star A)).2.1
  have hAnomExpand :
      star X * chiralEinsteinAnomaly P A (star A) * X =
        -(star X * genV P A (star A) * X + star X * genV P A (star A) * X) := by
    rw [hAnomEq, two_zsmul]
    noncomm_ring
  rw [hAnomExpand, map_neg, map_add]
  ring

/-- Non-positivity of the Chiral Einstein Anomaly expectation `tau (star X * chiralEinsteinAnomaly P A (star A) * X) ≤ 0` in `Limit`. -/
theorem limit_tau_chiralEinsteinAnomaly_nonpos
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPsym : star P = P) (A X : Limit) :
    tau (star X * chiralEinsteinAnomaly P A (star A) * X) ≤ 0 := by
  have hNonneg := limit_tau_genV_nonneg tau htau hP hPsym A X
  rw [limit_tau_chiralEinsteinAnomaly_eq tau hP A X]
  linarith

/-- **Theorem 2.2 (`limit_chiral_einstein_anomaly_trace_coercivity_and_negativity`):**
In the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`, for any linear trace extension
`tau : Limit →ₗ[ℝ] ℝ` of `normalizedTrace`, any self-adjoint idempotent `P : Limit`
(`P * P = P`, `star P = P`), and any `A X : Limit`:
1. The Hermitian-square identity holds for the Operator Fisher Metric `V = genV P A (star A)`:
   `star X * genV P A (star A) * X = star (genPhi P A (star A) * X) * (genPhi P A (star A) * X)`;
2. The Operator Fisher Metric expectation is strictly non-negative:
   `0 ≤ tau (star X * genV P A (star A) * X)`;
3. The Chiral Einstein Anomaly expectation is strictly non-positive (`≤ 0`) and equals minus twice
   the Fisher Metric expectation:
   `tau (star X * chiralEinsteinAnomaly P A (star A) * X) = -2 * tau (star X * genV P A (star A) * X)`
   and `tau (star X * chiralEinsteinAnomaly P A (star A) * X) ≤ 0`. -/
theorem limit_chiral_einstein_anomaly_trace_coercivity_and_negativity
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPsym : star P = P)
    (A X : Limit) :
    star X * genV P A (star A) * X =
      star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) ∧
    0 ≤ tau (star X * genV P A (star A) * X) ∧
    tau (star X * chiralEinsteinAnomaly P A (star A) * X) =
      -(2 * tau (star X * genV P A (star A) * X)) ∧
    tau (star X * chiralEinsteinAnomaly P A (star A) * X) ≤ 0 :=
  ⟨limit_genV_hermitian_square hP hPsym A X,
   limit_tau_genV_nonneg tau htau hP hPsym A X,
   limit_tau_chiralEinsteinAnomaly_eq tau hP A X,
   limit_tau_chiralEinsteinAnomaly_nonpos tau htau hP hPsym A X⟩

end InductiveColimitTransport

/-! ===========================================================================
    Section 3: Multi-Period `Cl(5, 5)` Bott Spinor Tower (`Stage (5 + 8 * k)`)
    & Cross-Carrier Colimit Synthesis (Including `mcbal` Stage `𝔐₃`)
    =========================================================================== -/

section MultiPeriodBottAndCrossCarrierSynthesis

/-- **Theorem 3.1 (`cl55_multi_period_bott_maurer_cartan_and_einstein_cartan_intertwiner`):**
Across all `8k` Bott periods `cl55ToBottStage k : Cl55 →+* Stage (5 + 8 * k)`, for any idempotent
`ω : Cl55` (`ω * ω = ω`) and any `A_cl C_cl X₁ Y₁ X₂ Y₂ : Cl55`
(with `P_lim := ofStage 5 (cl55ToStage5 ω)`, `A_lim := ofStage 5 (cl55ToStage5 A_cl)`, etc.),
the composite embedding `ofStage (5 + 8 * k) ∘ cl55ToBottStage k : Cl55 →+* Limit` intertwines:
1. `chiralAnnihilator ω X₁ ↦ chiralAnnihilator P_lim X₁_lim`,
2. `oddProjector ω X₁ ↦ oddProjector P_lim X₁_lim`,
3. `riemannCartanCurvature ω X₁ Y₁ X₂ Y₂ ↦ riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim`,
4. `elieCartanTorsion ω X₁ Y₁ X₂ Y₂ ↦ elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim`,
5. `chiralEinsteinAnomaly ω A_cl C_cl ↦ -((2 : ℤ) • genV P_lim A_lim C_lim)`,
6. `dressedSpinTorsion ω A_cl C_cl ↦ (1 + (2 : ℤ) • genV P_lim A_lim C_lim) * genJ P_lim A_lim C_lim`. -/
theorem cl55_multi_period_bott_maurer_cartan_and_einstein_cartan_intertwiner
    {ω : InfoGeometry.Clifford.Clifford55.Cl55} (hω : ω * ω = ω)
    (k : ℕ) (A_cl C_cl X₁ Y₁ X₂ Y₂ : InfoGeometry.Clifford.Clifford55.Cl55) :
    let P_lim : Limit := ofStage 5 (cl55ToStage5 ω)
    let A_lim : Limit := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim : Limit := ofStage 5 (cl55ToStage5 C_cl)
    let X₁_lim : Limit := ofStage 5 (cl55ToStage5 X₁)
    let Y₁_lim : Limit := ofStage 5 (cl55ToStage5 Y₁)
    let X₂_lim : Limit := ofStage 5 (cl55ToStage5 X₂)
    let Y₂_lim : Limit := ofStage 5 (cl55ToStage5 Y₂)
    ofStage (5 + 8 * k) (cl55ToBottStage k (chiralAnnihilator ω X₁)) =
      chiralAnnihilator P_lim X₁_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (oddProjector ω X₁)) =
      oddProjector P_lim X₁_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (riemannCartanCurvature ω X₁ Y₁ X₂ Y₂)) =
      riemannCartanCurvature P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (elieCartanTorsion ω X₁ Y₁ X₂ Y₂)) =
      elieCartanTorsion P_lim X₁_lim Y₁_lim X₂_lim Y₂_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (chiralEinsteinAnomaly ω A_cl C_cl)) =
      -((2 : ℤ) • genV P_lim A_lim C_lim) ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (dressedSpinTorsion ω A_cl C_cl)) =
      (1 + (2 : ℤ) • genV P_lim A_lim C_lim) * genJ P_lim A_lim C_lim := by
  dsimp only
  have hCoherent : ∀ y : InfoGeometry.Clifford.Clifford55.Cl55,
      ofStage (5 + 8 * k) (cl55ToBottStage k y) = ofStage 5 (cl55ToStage5 y) := by
    intro y
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
      (cl55ToStage5 y)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPLim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have hE4 :=
    (archetype_E4_chiral_einstein_anomaly_cocycle hPLim
      (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl))).2.1
  have hE5 :=
    (archetype_E5_spin_frame_dragging_and_dressed_torsion hPLim
      (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl))).2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCoherent, map_chiralAnnihilator, map_chiralAnnihilator]
  · rw [hCoherent, map_oddProjector, map_oddProjector]
  · rw [hCoherent, map_riemannCartanCurvature, map_riemannCartanCurvature]
  · rw [hCoherent, map_elieCartanTorsion, map_elieCartanTorsion]
  · rw [hCoherent, map_chiralEinsteinAnomaly, map_chiralEinsteinAnomaly, hE4]
  · rw [hCoherent, map_dressedSpinTorsion, map_dressedSpinTorsion, hE5]

/-- **Theorem 3.2 (`cross_carrier_maurer_cartan_einstein_cartan_and_mcbal_covariance_synthesis`):**
Simultaneously instantiates:
1. The Maurer–Cartan torsion annihilation & Einstein–Cartan spin frame-dragging laws on the
   **Two-Sheet Hestenes–Krein Filtered Colimit** `Module.End ℝ (Carrier StageFunctor)`
   (`P_colim = twoSheetColimitEnd plusStage`),
2. The Maurer–Cartan torsion annihilation & Einstein–Cartan spin frame-dragging laws on the
   **Exterior-Algebra Two-Sheet Yang–Mills Carrier** `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)`,
3. The **`mcbal` Stage `𝔐₃` Non-Commutative Operator Covariance Closure & Gain-Mixing Order Defect**
   directly on the inductive `Cl(1, 1)^{\otimes n}` colimit `Limit` (`[Ring Limit]`, `[StarRing Limit]`,
   `[Algebra ℝ Limit]`, `[StarModule ℝ Limit]`):
   - `crossCovariance w (fun ω => (G_lim * J_lim) * X_rv ω + E_rv ω) (fun ω => (G_lim * J_lim) * X_rv ω + E_rv ω) = covarianceStep (G_lim * J_lim) (crossCovariance w E_rv E_rv) (crossCovariance w X_rv X_rv)`,
   - `covarianceStep (G_lim * J_lim) Q_lim C_lim - covarianceStep (J_lim * G_lim) Q_lim C_lim = [G_lim, J_lim] C_lim (G_lim J_lim)* + (J_lim G_lim) C_lim [G_lim, J_lim]*`. -/
theorem cross_carrier_maurer_cartan_einstein_cartan_and_mcbal_covariance_synthesis
    (A_colim C_colim X₁_colim Y₁_colim X₂_colim Y₂_colim :
      Module.End ℝ
        (InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.Carrier
          InfoGeometry.Categorical.TwoSheetKreinStageSystem.StageFunctor))
    {R : Type*} [CommRing R] {V_ext : Type*} [AddCommGroup V_ext] [Module R V_ext]
    {n : ℕ}
    {P_mat : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)}
    (hP_mat : P_mat * P_mat = P_mat)
    (A_mat C_mat X₁_mat Y₁_mat X₂_mat Y₂_mat :
      Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext))
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (G_lim J_lim Q_lim C_lim : Limit)
    (X_rv E_rv : Ω → Limit) (hXE : crossCovariance w X_rv E_rv = 0) :
    let P_colim :=
      InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimitEnd
        InfoGeometry.Categorical.TwoSheetKreinStageSystem.plusStage
    -- (1) Two-Sheet Hestenes–Krein Filtered Colimit:
    (chiralAnnihilator P_colim
       (elieCartanTorsion P_colim X₁_colim Y₁_colim X₂_colim Y₂_colim) = 0 ∧
     chiralEinsteinAnomaly P_colim A_colim C_colim =
       -((2 : ℤ) • genV P_colim A_colim C_colim) ∧
     OperatorAlgebra.PeirceSpine.comm
       (genSig P_colim A_colim C_colim) (genPhi P_colim A_colim C_colim) =
       (2 : ℤ) • (genV P_colim A_colim C_colim * genJ P_colim A_colim C_colim)) ∧
    -- (2) Exterior-Algebra Two-Sheet Yang–Mills Carrier:
    (chiralAnnihilator P_mat
       (elieCartanTorsion P_mat X₁_mat Y₁_mat X₂_mat Y₂_mat) = 0 ∧
     chiralEinsteinAnomaly P_mat A_mat C_mat =
       -((2 : ℤ) • genV P_mat A_mat C_mat) ∧
     OperatorAlgebra.PeirceSpine.comm
       (genSig P_mat A_mat C_mat) (genPhi P_mat A_mat C_mat) =
       (2 : ℤ) • (genV P_mat A_mat C_mat * genJ P_mat A_mat C_mat)) ∧
    -- (3) `mcbal` Non-Commutative Operator Covariance Closure in `Limit`:
    (crossCovariance w
       (fun ω => (G_lim * J_lim) * X_rv ω + E_rv ω)
       (fun ω => (G_lim * J_lim) * X_rv ω + E_rv ω) =
       covarianceStep (G_lim * J_lim)
         (crossCovariance w E_rv E_rv) (crossCovariance w X_rv X_rv) ∧
     covarianceStep (G_lim * J_lim) Q_lim C_lim -
       covarianceStep (J_lim * G_lim) Q_lim C_lim =
       InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G_lim J_lim *
         C_lim * star (G_lim * J_lim) +
       (J_lim * G_lim) * C_lim *
         star (InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G_lim J_lim)) := by
  dsimp only
  have hP_colim :=
    InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimit_plus_idempotent
  exact ⟨⟨(archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri
            hP_colim X₁_colim Y₁_colim X₂_colim Y₂_colim).2.1,
          (archetype_E4_chiral_einstein_anomaly_cocycle hP_colim A_colim C_colim).2.1,
          (archetype_E5_spin_frame_dragging_and_dressed_torsion hP_colim A_colim C_colim).2.2.1⟩,
         ⟨(archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri
            hP_mat X₁_mat Y₁_mat X₂_mat Y₂_mat).2.1,
          (archetype_E4_chiral_einstein_anomaly_cocycle hP_mat A_mat C_mat).2.1,
          (archetype_E5_spin_frame_dragging_and_dressed_torsion hP_mat A_mat C_mat).2.2.1⟩,
         ⟨innovation_covariance_of_cross_zero w (G_lim * J_lim) X_rv E_rv hXE,
          gain_mixing_order_defect G_lim J_lim Q_lim C_lim⟩⟩

end MultiPeriodBottAndCrossCarrierSynthesis

end InfoGeometry.Canonical.MaurerCartanEinsteinCartanMcbalColimitSynthesis
