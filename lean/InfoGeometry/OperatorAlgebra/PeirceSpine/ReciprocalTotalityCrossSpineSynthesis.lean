/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset
import InfoGeometry.Canonical.SmoothPrincipalCartanBundleClosure
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
import InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
import InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
import InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge

/-!
# Reciprocal Totality & Six-Pillar Spine II ↔ R1–R2–R3 Cross-Spine Synthesis

This canonical leaf synthesis module couples the **Six-Pillar Plücker–Grassmann–Klein–Clifford–
Möbius–Evanston Spine** (Spine II) with the **R1–R2–R3 Noncommutative Cartan–Clifford–Krein
Spine** solely through their public canonical endpoint modules, avoiding internal cross-spine
coupling:

1. **Bridge 1 (`principalTransition_gaugeTransformL_cocycle`)**:
   Maps smooth principal Cartan bundle transition cocycles `principalTransition B e₁ e₃ x =
   principalTransition B e₁ e₂ x * principalTransition B e₂ e₃ x` via any Lie-action unit
   representation `ρ : H →* Aˣ` to left/right noncommutative Maurer–Cartan gauge compositions and
   covariant Chevalley–Eilenberg curvature conjugation (`ceCurvature K (Γ · g) = g⁻¹ F(Γ) g`).
2. **Bridge 2 (`biquatBivector_peirce_grace_krein_polarization`)**:
   Identifies Clifford's chiral biquaternion idempotents `(biquatIdempPlus, biquatIdempMinus)` with
   the Peirce complementary pair `(p, 1 - p)` whose Grace reflection `2 p - 1` is `ω₄ ℝ`,
   splitting `(D + ω₄ M)²` into chiral directional sectors `-(d ± m)²` separated by
   `4 * (directionMomentEquiv.symm (d, m)).kleinQ`.
3. **Bridge 3 (`casimir_skew_violates_cone_salience`, `symmetric_onsager_cone_salient`,
   `gibbsBKM_onsager_birkhoffHilbert_chord_metric`)**:
   Separates skew-symmetric Casimir operators (`Aᵀ = -A`, identically null quadratic form, nonzero
   salience countermodel on `Fin 2`) from symmetric positive Onsager–BKM kernels (`Sᵀ = S`,
   salient via polarization), and attaches the unconditional Birkhoff–Hilbert projective
   cross-ratio chord metric on arbitrary distinct interior rays of a salient proper cone.
4. **Bridge 4 (`su2ToSpinGroupCl03`, `binaryIcosahedralToSpinGroupCl03`,
   `binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20`)**:
   Constructs an explicit trig-free 2-vector Clifford factorization proving every unit quaternion
   in `SU(2)` lifts to `spinGroup (cliffordNegSqForm ℝ 3)` as a group homomorphism, restricts it
   to Klein's binary icosahedral group `2I ⊂ SU(2)`, and couples `2I`-invariance of aligned
   icosahedral forms/ratios with `spinGroup_cliffordOneForms_naturality` and `quatRotMatrix`.
5. **Bridge 5 (`sixPillar_r1r2r3_mannheim_reciprocal_master_synthesis`)**:
   Packages Bridges 1–4 together with the abstract Star-ring Mannheim–Krein `V`-metric theorem and
   the concrete `M₂(ℤ)` aporia/positive-definite `V₀` realization from
   `ReciprocalTotalityAporiaPoset`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityCrossSpineSynthesis

/-! ## Bridge 1: Smooth Principal Cartan Cocycle ↔ Maurer–Cartan Gauge & Curvature -/

section Bridge1_PrincipalTransitionMaurerCartan

open InfoGeometry.Canonical.SmoothPrincipalCartanBundleClosure
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra

/-- Coupling the triple-overlap transition cocycle of a `SmoothPrincipalCartanGeometry` with
left/right Maurer–Cartan gauge composition and CE curvature covariance along `ρ : H →* Aˣ`. -/
theorem principalTransition_gaugeTransformL_cocycle
    {EP EM EH : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    {HP HM HH : Type*} [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {IH : ModelWithCorners ℝ EH HH}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ e₃ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {x : M} (hx₁ : x ∈ e₁.toTrivialization.baseSet) (hx₂ : x ∈ e₂.toTrivialization.baseSet)
    (hx₃ : x ∈ e₃.toTrivialization.baseSet)
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A)
    (ρ : H →* Aˣ) (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K (ρ (principalTransition B e₁ e₃ x)) Γ =
      gaugeTransformOneForm K (ρ (principalTransition B e₁ e₂ x))
        (gaugeTransformOneForm K (ρ (principalTransition B e₂ e₃ x)) Γ) ∧
    rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₃ x)) =
      rightGaugeTransformOneForm K
        (rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₂ x)))
        (ρ (principalTransition B e₂ e₃ x)) ∧
    ceCurvature K (rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₃ x))) =
      conjugateForm K (ρ (principalTransition B e₁ e₃ x))⁻¹ (ceCurvature K Γ) := by
  have hcoc := principalTransition_cocycle B e₁ e₂ e₃ hx₁ hx₂ hx₃
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoc, map_mul, ← gaugeTransformOneForm_mul]
  · rw [hcoc, map_mul, ← rightGaugeTransformOneForm_mul]
  · exact ceCurvature_rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₃ x))

end Bridge1_PrincipalTransitionMaurerCartan

/-! ## Bridge 2: Chiral Biquaternions ↔ Peirce/Grace Reflection & Plücker–Klein Polarization -/

section Bridge2_BiquatPeirceGraceKrein

open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.IdempotentCartan

/-- Chiral biquaternion Peirce idempotents `biquatIdempPlus`, `biquatIdempMinus` realize the
abstract complementary idempotent pair whose Grace reflection `2 p - 1` is `ω₄ ℝ`, and polarize
`(D + ω₄ M)²` into chiral directional sectors `-‖d ± m‖²` with difference `4 * kleinQ`. -/
theorem biquatBivector_peirce_grace_krein_polarization (d m : Fin 3 → ℝ) :
    complementIdempotent biquatIdempPlus = biquatIdempMinus ∧
    reflection biquatIdempPlus = ω₄ ℝ ∧
    biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
      (-(d ⬝ᵥ d + m ⬝ᵥ m) - 2 * (d ⬝ᵥ m)) • biquatIdempPlus ∧
    biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
      (-((d + m) ⬝ᵥ (d + m))) • biquatIdempPlus ∧
    biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
      (-(d ⬝ᵥ d + m ⬝ᵥ m) + 2 * (d ⬝ᵥ m)) • biquatIdempMinus ∧
    biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
      (-((d - m) ⬝ᵥ (d - m))) • biquatIdempMinus ∧
    ((d + m) ⬝ᵥ (d + m)) - ((d - m) ⬝ᵥ (d - m)) =
      4 * (directionMomentEquiv.symm (d, m)).kleinQ := by
  have hdec := biquat_chiral_peirce_decomposition
  rcases hdec with ⟨_, _, _, _, _, _, hsum, hωP, hωM, _, _⟩
  have hcomp : complementIdempotent biquatIdempPlus = biquatIdempMinus := by
    rw [complementIdempotent, ← hsum]
    abel
  have hrefl : reflection biquatIdempPlus = ω₄ ℝ := by
    rw [← ωEven_two_eq_ω₄ ℝ, reflection, two_nsmul, biquatIdempPlus]
    module
  have hsq : biquatBivector ℝ d m * biquatBivector ℝ d m =
      (-(d ⬝ᵥ d + m ⬝ᵥ m)) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ 4)) -
        (2 * (d ⬝ᵥ m)) • ωEven ℝ 2 := by
    have h0 := biquatBivector_sq_plucker_kleinQ d m
    rw [kleinQ_directionMoment d m, ← ωEven_two_eq_ω₄ ℝ, Algebra.algebraMap_eq_smul_one] at h0
    exact h0
  have hP1 : biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
      (-(d ⬝ᵥ d + m ⬝ᵥ m) - 2 * (d ⬝ᵥ m)) • biquatIdempPlus := by
    rw [hsq, sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hωP, sub_smul]
  have hdotPlus : -(d ⬝ᵥ d + m ⬝ᵥ m) - 2 * (d ⬝ᵥ m) = -((d + m) ⬝ᵥ (d + m)) := by
    simp only [dotProduct, Pi.add_apply, Fin.sum_univ_three]
    ring
  have hP2 : biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
      (-((d + m) ⬝ᵥ (d + m))) • biquatIdempPlus := by
    rw [hP1, hdotPlus]
  have hM1 : biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
      (-(d ⬝ᵥ d + m ⬝ᵥ m) + 2 * (d ⬝ᵥ m)) • biquatIdempMinus := by
    rw [hsq, sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hωM, smul_neg, sub_neg_eq_add,
      add_smul]
  have hdotMinus : -(d ⬝ᵥ d + m ⬝ᵥ m) + 2 * (d ⬝ᵥ m) = -((d - m) ⬝ᵥ (d - m)) := by
    simp only [dotProduct, Pi.sub_apply, Fin.sum_univ_three]
    ring
  have hM2 : biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
      (-((d - m) ⬝ᵥ (d - m))) • biquatIdempMinus := by
    rw [hM1, hdotMinus]
  have hdiff : ((d + m) ⬝ᵥ (d + m)) - ((d - m) ⬝ᵥ (d - m)) =
      4 * (directionMomentEquiv.symm (d, m)).kleinQ := by
    rw [kleinQ_directionMoment d m]
    simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_three]
    ring
  exact ⟨hcomp, hrefl, hP1, hP2, hM1, hM2, hdiff⟩

end Bridge2_BiquatPeirceGraceKrein

/-! ## Bridge 3: Skew Casimir Non-Salience vs. Onsager Salience & Birkhoff–Hilbert Chord -/

section Bridge3_OnsagerCasimirBirkhoffHilbert

open InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
open InfoGeometry.Erlangen.BirkhoffHilbertConeMetric
open InfoGeometry.Projective.GeneralHilbertConeMetric
open Matrix

/-- Every skew-symmetric matrix `A.transpose = -A` has identically vanishing quadratic form
`v ⬝ᵥ (A *ᵥ v) = 0`, and therefore fails cone salience on `Fin 2` (`!![0, 1; -1, 0] ≠ 0`). -/
theorem casimir_skew_violates_cone_salience {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose = -A) :
    (∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) = 0) ∧
      ∃ A₀ : Matrix (Fin 2) (Fin 2) ℝ,
        A₀.transpose = -A₀ ∧ A₀ ≠ 0 ∧
          (∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (A₀ *ᵥ v)) ∧
          (∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ ((-A₀) *ᵥ v)) := by
  have hnull : ∀ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ),
      B.transpose = -B → ∀ v : Fin m → ℝ, v ⬝ᵥ (B *ᵥ v) = 0 := by
    intro m B hB v
    have hsum : v ⬝ᵥ (B *ᵥ v) = -(v ⬝ᵥ (B *ᵥ v)) := by
      have hT : ∀ i j : Fin m, B j i = -B i j := by
        intro i j
        simpa [Matrix.transpose_apply, Matrix.neg_apply] using
          congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M i j) hB
      calc
        v ⬝ᵥ (B *ᵥ v)
            = ∑ i : Fin m, ∑ j : Fin m, B i j * (v i * v j) := by
                simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                ring
        _ = ∑ j : Fin m, ∑ i : Fin m, B i j * (v i * v j) := Finset.sum_comm
        _ = ∑ j : Fin m, ∑ i : Fin m, (-B j i) * (v j * v i) := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
              rw [hT j i]
              ring
        _ = -(∑ j : Fin m, ∑ i : Fin m, B j i * (v j * v i)) := by
              simp only [neg_mul, Finset.sum_neg_distrib]
        _ = -(v ⬝ᵥ (B *ᵥ v)) := by
              congr 1
              simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
              ring
    linarith
  refine ⟨hnull A hA, !![0, 1; -1, 0], ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h0
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h0
    simp at h01
  · intro v
    rw [hnull !![0, 1; -1, 0] (by ext i j; fin_cases i <;> fin_cases j <;> simp) v]
  · intro v
    have hnegT : (-!![(0 : ℝ), 1; -1, 0]).transpose = -(-!![(0 : ℝ), 1; -1, 0]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hnull (-!![(0 : ℝ), 1; -1, 0]) hnegT v]

/-- Any symmetric matrix `S.transpose = S` whose quadratic form satisfies both `0 ≤ v ⬝ᵥ (S *ᵥ v)`
and `0 ≤ v ⬝ᵥ ((-S) *ᵥ v)` vanishes identically (`S = 0`), establishing cone salience. -/
theorem symmetric_onsager_cone_salient {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.transpose = S)
    (hpos : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (S *ᵥ v))
    (hneg : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ ((-S) *ᵥ v)) :
    S = 0 := by
  have hzero : ∀ v : Fin n → ℝ, v ⬝ᵥ (S *ᵥ v) = 0 := by
    intro v
    have h1 := hpos v
    have h2 : v ⬝ᵥ ((-S) *ᵥ v) = -(v ⬝ᵥ (S *ᵥ v)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
        mul_neg]
    have h2' := hneg v
    rw [h2] at h2'
    linarith
  have hsymm : ∀ i j : Fin n, S j i = S i j := by
    intro i j
    simpa [Matrix.transpose_apply] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hS
  have hsingle : ∀ a b : Fin n,
      (Pi.single a (1 : ℝ)) ⬝ᵥ (S *ᵥ Pi.single b (1 : ℝ)) = S a b := by
    intro a b
    simp only [dotProduct, Matrix.mulVec]
    rw [Finset.sum_eq_single a]
    · simp only [Pi.single_eq_same, one_mul]
      rw [Finset.sum_eq_single b]
      · simp
      · intro k _ hkb
        simp [Pi.single_eq_of_ne hkb]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    · intro k _ hka
      simp [Pi.single_eq_of_ne hka]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  ext i j
  let u : Fin n → ℝ := Pi.single i 1
  let w : Fin n → ℝ := Pi.single j 1
  have huw := hzero (u + w)
  have hu : u ⬝ᵥ (S *ᵥ u) = 0 := hzero u
  have hw : w ⬝ᵥ (S *ᵥ w) = 0 := hzero w
  have hexp :
      (u + w) ⬝ᵥ (S *ᵥ (u + w)) =
        u ⬝ᵥ (S *ᵥ u) + u ⬝ᵥ (S *ᵥ w) + w ⬝ᵥ (S *ᵥ u) + w ⬝ᵥ (S *ᵥ w) := by
    simp only [dotProduct, Matrix.mulVec_add, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring
  rw [hexp, hu, hw, hsingle i j, hsingle j i, hsymm i j] at huw
  rw [Matrix.zero_apply]
  linarith

/-- Unified Onsager–Casimir salience contrast together with the unconditional Birkhoff–Hilbert
projective cross-ratio chord metric on any salient proper cone `C : ProperCone ℝ E`. -/
theorem gibbsBKM_onsager_birkhoffHilbert_chord_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (C : ProperCone ℝ E) (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    (∃ A₀ : Matrix (Fin 2) (Fin 2) ℝ,
      A₀.transpose = -A₀ ∧ A₀ ≠ 0 ∧
        (∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (A₀ *ᵥ v)) ∧
        (∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ ((-A₀) *ᵥ v))) ∧
    (∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ),
      S.transpose = S →
      (∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (S *ᵥ v)) →
      (∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ ((-S) *ᵥ v)) → S = 0) ∧
    (let u := extremalRayLeft C x y
     let v := extremalRayRight C x y
     let τ_x := 1 / (upperGauge C x y + 1)
     let τ_y := upperGauge C y x / (upperGauge C y x + 1)
     let p : ℝ → E := fun τ => (1 - τ) • u + τ • v
     u ∈ frontier (C : Set E) ∧ v ∈ frontier (C : Set E) ∧
       0 < τ_x ∧ τ_x < τ_y ∧ τ_y < 1 ∧
       (∃ cx : ℝ, 0 < cx ∧ p τ_x = cx • x) ∧ (∃ cy : ℝ, 0 < cy ∧ p τ_y = cy • y) ∧
       birkhoffHilbertMetric C x y =
         (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0 τ_x τ_y 1)) := by
  have hcas :=
    (casimir_skew_violates_cone_salience (0 : Matrix (Fin 0) (Fin 0) ℝ)
      (by ext i; exact Fin.elim0 i)).2
  refine ⟨hcas, ?_, ?_⟩
  · intro n S hS hpos hneg
    exact symmetric_onsager_cone_salient S hS hpos hneg
  · exact birkhoffHilbertMetric_arbitrary_endpoints_projective_chord C hC hx hy hray

end Bridge3_OnsagerCasimirBirkhoffHilbert

/-! ## Bridge 4: Binary Icosahedral `2I ⊂ SU(2)` ↔ `Spin(0,3)` ↔ Clifford One-Forms (`Erlangen20`) -/

section Bridge4_IcosahedralSU2SpinCl03OneForms

open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
open InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open Matrix

private lemma su2_eq_quatToMat (g : SU2) :
    (g : Mat2C) =
      quatToMat (g.1 0 0).re (g.1 0 0).im (g.1 0 1).re (g.1 0 1).im := by
  have hg := Matrix.mem_specialUnitaryGroup_iff.mp g.prop
  have hadj : g.1.adjugate = star g.1 := by
    calc
      g.1.adjugate = g.1.adjugate * 1 := (Matrix.mul_one _).symm
      _ = g.1.adjugate * (g.1 * star g.1) := by rw [Matrix.mem_unitaryGroup_iff.mp hg.1]
      _ = (g.1.adjugate * g.1) * star g.1 := (Matrix.mul_assoc _ _ _).symm
      _ = (g.1.det • (1 : Mat2C)) * star g.1 := by rw [Matrix.adjugate_mul]
      _ = 1 * star g.1 := by rw [hg.2, one_smul]
      _ = star g.1 := Matrix.one_mul _
  have h11 : g.1 1 1 = star (g.1 0 0) := by
    have h00 := congrArg (fun M : Mat2C => M 0 0) hadj
    simpa [Matrix.adjugate_fin_two, Matrix.star_apply] using h00
  have h10 : g.1 1 0 = -star (g.1 0 1) := by
    have h01 := congrArg (fun M : Mat2C => M 0 1) hadj
    simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.star_apply] at h01
    have hs := congrArg star h01
    simp only [star_neg, star_star] at hs
    exact hs.symm
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatToMat, h11, h10, Complex.I_re, Complex.I_im]

private lemma su2_norm_sq (g : SU2) :
    (g.1 0 0).re ^ 2 + (g.1 0 0).im ^ 2 + (g.1 0 1).re ^ 2 + (g.1 0 1).im ^ 2 = 1 := by
  have hg := (Matrix.mem_specialUnitaryGroup_iff.mp g.prop).2
  have hdet := congrArg (fun M : Mat2C => M.det) (su2_eq_quatToMat g)
  rw [hg] at hdet
  have hre := congrArg Complex.re hdet
  simp only [Complex.one_re, quatToMat, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_im,
    mul_zero, sub_zero, add_zero, mul_one, zero_add] at hre
  nlinarith

private lemma cl03_quat_mul_table (R : Type*) [CommRing R] :
    q3I R * q3I R = -1 ∧ q3J R * q3J R = -1 ∧ q3K R * q3K R = -1 ∧
    q3I R * q3J R = q3K R ∧ q3J R * q3K R = q3I R ∧ q3K R * q3I R = q3J R ∧
    q3J R * q3I R = -q3K R ∧ q3K R * q3J R = -q3I R ∧ q3I R * q3K R = -q3J R := by
  have h00 : cGen R 3 0 * cGen R 3 0 = -1 := cGen_sq R 3 0
  have h11 : cGen R 3 1 * cGen R 3 1 = -1 := cGen_sq R 3 1
  have h22 : cGen R 3 2 * cGen R 3 2 = -1 := cGen_sq R 3 2
  have h01 : cGen R 3 0 * cGen R 3 1 = -(cGen R 3 1 * cGen R 3 0) := cGen_anticomm (by decide)
  have h12 : cGen R 3 1 * cGen R 3 2 = -(cGen R 3 2 * cGen R 3 1) := cGen_anticomm (by decide)
  have h20 : cGen R 3 2 * cGen R 3 0 = -(cGen R 3 0 * cGen R 3 2) := cGen_anticomm (by decide)
  have h10 : cGen R 3 1 * cGen R 3 0 = -(cGen R 3 0 * cGen R 3 1) := cGen_anticomm (by decide)
  have h21 : cGen R 3 2 * cGen R 3 1 = -(cGen R 3 1 * cGen R 3 2) := cGen_anticomm (by decide)
  have h02 : cGen R 3 0 * cGen R 3 2 = -(cGen R 3 2 * cGen R 3 0) := cGen_anticomm (by decide)
  have hii : q3I R * q3I R = -1 := by
    calc q3I R * q3I R
        = cGen R 3 1 * (cGen R 3 2 * cGen R 3 1) * cGen R 3 2 := by simp [q3I, mul_assoc]
    _ = cGen R 3 1 * -(cGen R 3 1 * cGen R 3 2) * cGen R 3 2 := by rw [h21]
    _ = -((cGen R 3 1 * cGen R 3 1) * (cGen R 3 2 * cGen R 3 2)) := by noncomm_ring
    _ = -1 := by rw [h11, h22]; noncomm_ring
  have hjj : q3J R * q3J R = -1 := by
    calc q3J R * q3J R
        = cGen R 3 2 * (cGen R 3 0 * cGen R 3 2) * cGen R 3 0 := by simp [q3J, mul_assoc]
    _ = cGen R 3 2 * -(cGen R 3 2 * cGen R 3 0) * cGen R 3 0 := by rw [h02]
    _ = -((cGen R 3 2 * cGen R 3 2) * (cGen R 3 0 * cGen R 3 0)) := by noncomm_ring
    _ = -1 := by rw [h22, h00]; noncomm_ring
  have hkk : q3K R * q3K R = -1 := by
    calc q3K R * q3K R
        = cGen R 3 0 * (cGen R 3 1 * cGen R 3 0) * cGen R 3 1 := by simp [q3K, mul_assoc]
    _ = cGen R 3 0 * -(cGen R 3 0 * cGen R 3 1) * cGen R 3 1 := by rw [h10]
    _ = -((cGen R 3 0 * cGen R 3 0) * (cGen R 3 1 * cGen R 3 1)) := by noncomm_ring
    _ = -1 := by rw [h00, h11]; noncomm_ring
  have hij : q3I R * q3J R = q3K R := by
    calc q3I R * q3J R
        = (cGen R 3 1 * cGen R 3 2) * (cGen R 3 2 * cGen R 3 0) := rfl
    _ = cGen R 3 1 * (cGen R 3 2 * cGen R 3 2) * cGen R 3 0 := by noncomm_ring
    _ = -(cGen R 3 1 * cGen R 3 0) := by rw [h22]; noncomm_ring
    _ = -(-(cGen R 3 0 * cGen R 3 1)) := by rw [h10]
    _ = q3K R := neg_neg _
  have hjk : q3J R * q3K R = q3I R := by
    calc q3J R * q3K R
        = (cGen R 3 2 * cGen R 3 0) * (cGen R 3 0 * cGen R 3 1) := rfl
    _ = cGen R 3 2 * (cGen R 3 0 * cGen R 3 0) * cGen R 3 1 := by noncomm_ring
    _ = -(cGen R 3 2 * cGen R 3 1) := by rw [h00]; noncomm_ring
    _ = -(-(cGen R 3 1 * cGen R 3 2)) := by rw [h21]
    _ = q3I R := neg_neg _
  have hki : q3K R * q3I R = q3J R := by
    calc q3K R * q3I R
        = (cGen R 3 0 * cGen R 3 1) * (cGen R 3 1 * cGen R 3 2) := rfl
    _ = cGen R 3 0 * (cGen R 3 1 * cGen R 3 1) * cGen R 3 2 := by noncomm_ring
    _ = -(cGen R 3 0 * cGen R 3 2) := by rw [h11]; noncomm_ring
    _ = -(-(cGen R 3 2 * cGen R 3 0)) := by rw [h02]
    _ = q3J R := neg_neg _
  have hji : q3J R * q3I R = -q3K R := by
    calc q3J R * q3I R
        = (cGen R 3 2 * cGen R 3 0) * (cGen R 3 1 * cGen R 3 2) := rfl
    _ = (-(cGen R 3 0 * cGen R 3 2)) * (-(cGen R 3 2 * cGen R 3 1)) := by rw [h20, h12]
    _ = cGen R 3 0 * (cGen R 3 2 * cGen R 3 2) * cGen R 3 1 := by noncomm_ring
    _ = -(cGen R 3 0 * cGen R 3 1) := by rw [h22]; noncomm_ring
    _ = -q3K R := rfl
  have hkj : q3K R * q3J R = -q3I R := by
    calc q3K R * q3J R
        = (cGen R 3 0 * cGen R 3 1) * (cGen R 3 2 * cGen R 3 0) := rfl
    _ = (-(cGen R 3 1 * cGen R 3 0)) * (-(cGen R 3 0 * cGen R 3 2)) := by rw [h01, h20]
    _ = cGen R 3 1 * (cGen R 3 0 * cGen R 3 0) * cGen R 3 2 := by noncomm_ring
    _ = -(cGen R 3 1 * cGen R 3 2) := by rw [h00]; noncomm_ring
    _ = -q3I R := rfl
  have hik : q3I R * q3K R = -q3J R := by
    calc q3I R * q3K R
        = (cGen R 3 1 * cGen R 3 2) * (cGen R 3 0 * cGen R 3 1) := rfl
    _ = (-(cGen R 3 2 * cGen R 3 1)) * (-(cGen R 3 1 * cGen R 3 0)) := by rw [h12, h01]
    _ = cGen R 3 2 * (cGen R 3 1 * cGen R 3 1) * cGen R 3 0 := by noncomm_ring
    _ = -(cGen R 3 2 * cGen R 3 0) := by rw [h11]; noncomm_ring
    _ = -q3J R := rfl
  exact ⟨hii, hjj, hkk, hij, hjk, hki, hji, hkj, hik⟩

private lemma spinQuat3_mul {R : Type*} [CommRing R] (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : R) :
    spinQuat3 a₁ b₁ c₁ d₁ * spinQuat3 a₂ b₂ c₂ d₂ =
      spinQuat3
        (a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂)
        (a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂)
        (a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂)
        (a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂) := by
  obtain ⟨hii, hjj, hkk, hij, hjk, hki, hji, hkj, hik⟩ := cl03_quat_mul_table R
  simp only [spinQuat3, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    hii, hjj, hkk, hij, hjk, hki, hji, hkj, hik, smul_neg]
  module

private lemma ι_cl03_eq (v : Fin 3 → ℝ) :
    CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) v =
      v 0 • cGen ℝ 3 0 + v 1 • cGen ℝ 3 1 + v 2 • cGen ℝ 3 2 := by
  have hv : v =
      v 0 • Pi.single 0 (1 : ℝ) + v 1 • Pi.single 1 (1 : ℝ) + v 2 • Pi.single 2 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, cGen]

private lemma ι_cl03_mul_ι (u w : Fin 3 → ℝ) :
    CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) u *
        CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) w =
      spinQuat3
        (-(u 0 * w 0 + u 1 * w 1 + u 2 * w 2))
        (u 1 * w 2 - u 2 * w 1)
        (u 2 * w 0 - u 0 * w 2)
        (u 0 * w 1 - u 1 * w 0) := by
  have h00 : cGen ℝ 3 0 * cGen ℝ 3 0 = -1 := cGen_sq ℝ 3 0
  have h11 : cGen ℝ 3 1 * cGen ℝ 3 1 = -1 := cGen_sq ℝ 3 1
  have h22 : cGen ℝ 3 2 * cGen ℝ 3 2 = -1 := cGen_sq ℝ 3 2
  have h10 : cGen ℝ 3 1 * cGen ℝ 3 0 = -(cGen ℝ 3 0 * cGen ℝ 3 1) := cGen_anticomm (by decide)
  have h21 : cGen ℝ 3 2 * cGen ℝ 3 1 = -(cGen ℝ 3 1 * cGen ℝ 3 2) := cGen_anticomm (by decide)
  have h02 : cGen ℝ 3 0 * cGen ℝ 3 2 = -(cGen ℝ 3 2 * cGen ℝ 3 0) := cGen_anticomm (by decide)
  have hi : cGen ℝ 3 1 * cGen ℝ 3 2 = q3I ℝ := rfl
  have hj : cGen ℝ 3 2 * cGen ℝ 3 0 = q3J ℝ := rfl
  have hk : cGen ℝ 3 0 * cGen ℝ 3 1 = q3K ℝ := rfl
  rw [ι_cl03_eq u, ι_cl03_eq w]
  simp only [spinQuat3, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    h00, h11, h22, h10, h21, h02, hi, hj, hk, smul_neg]
  module

private lemma ι_cl03_mem_pinGroup (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) v ∈ pinGroup (cliffordNegSqForm ℝ 3) := by
  have hq : cliffordNegSqForm ℝ 3 v = -1 := by
    rw [cliffordNegSqForm_apply, Fin.sum_univ_three]
    linarith
  let uv : (CliffordAlgebra (cliffordNegSqForm ℝ 3))ˣ :=
    { val := CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) v
      inv := -CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) v
      val_inv := by
        rw [mul_neg, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one, neg_neg]
      inv_val := by
        rw [neg_mul, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one, neg_neg] }
  refine ⟨⟨uv, Subgroup.subset_closure ⟨v, rfl⟩, rfl⟩, ?_⟩
  rw [SetLike.mem_coe, Unitary.mem_iff]
  constructor
  · rw [CliffordAlgebra.star_ι, neg_mul, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one,
      neg_neg]
  · rw [CliffordAlgebra.star_ι, mul_neg, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one,
      neg_neg]

private lemma spinQuat3_mem_spinGroup {a b c d : ℝ} (habcd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    spinQuat3 a b c d ∈ spinGroup (cliffordNegSqForm ℝ 3) := by
  have hexu : ∃ u : Fin 3 → ℝ,
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 ∧ b * u 0 + c * u 1 + d * u 2 = 0 := by
    by_cases hbc : b = 0 ∧ c = 0
    · refine ⟨![1, 0, 0], ?_, ?_⟩
      · simp
      · simp [hbc.1, hbc.2]
    · have hpos : 0 < b ^ 2 + c ^ 2 := by
        by_contra hle
        push Not at hle
        have hb0 : b = 0 := by nlinarith
        have hc0 : c = 0 := by nlinarith
        exact hbc ⟨hb0, hc0⟩
      let r : ℝ := Real.sqrt (b ^ 2 + c ^ 2)
      have hr_pos : 0 < r := Real.sqrt_pos.mpr hpos
      have hr_sq : r ^ 2 = b ^ 2 + c ^ 2 := Real.sq_sqrt hpos.le
      refine ⟨![-c / r, b / r, 0], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        have hr0 : r ≠ 0 := hr_pos.ne'
        field_simp [hr0]
        rw [hr_sq]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        ring
  rcases hexu with ⟨u, hu, huv⟩
  let u₀ : ℝ := u 0
  let u₁ : ℝ := u 1
  let u₂ : ℝ := u 2
  let w : Fin 3 → ℝ :=
    ![-a * u₀ + c * u₂ - d * u₁,
      -a * u₁ + d * u₀ - b * u₂,
      -a * u₂ + b * u₁ - c * u₀]
  have hw_norm : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    have hpoly :
        (-a * u₀ + c * u₂ - d * u₁) ^ 2 +
          (-a * u₁ + d * u₀ - b * u₂) ^ 2 +
          (-a * u₂ + b * u₁ - c * u₀) ^ 2 =
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (u₀ ^ 2 + u₁ ^ 2 + u₂ ^ 2) -
          (b * u₀ + c * u₁ + d * u₂) ^ 2 := by ring
    change (-a * u₀ + c * u₂ - d * u₁) ^ 2 +
      (-a * u₁ + d * u₀ - b * u₂) ^ 2 +
      (-a * u₂ + b * u₁ - c * u₀) ^ 2 = 1
    rw [hpoly, habcd, hu, huv]
    ring
  have hfac : CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) u *
      CliffordAlgebra.ι (cliffordNegSqForm ℝ 3) w = spinQuat3 a b c d := by
    rw [ι_cl03_mul_ι]
    congr 1
    · change -(u₀ * (-a * u₀ + c * u₂ - d * u₁) +
        u₁ * (-a * u₁ + d * u₀ - b * u₂) +
        u₂ * (-a * u₂ + b * u₁ - c * u₀)) = a
      linear_combination a * hu
    · change u₁ * (-a * u₂ + b * u₁ - c * u₀) - u₂ * (-a * u₁ + d * u₀ - b * u₂) = b
      linear_combination b * hu - u₀ * huv
    · change u₂ * (-a * u₀ + c * u₂ - d * u₁) - u₀ * (-a * u₂ + b * u₁ - c * u₀) = c
      linear_combination c * hu - u₁ * huv
    · change u₀ * (-a * u₁ + d * u₀ - b * u₂) - u₁ * (-a * u₀ + c * u₂ - d * u₁) = d
      linear_combination d * hu - u₂ * huv
  rw [← hfac]
  exact ⟨Submonoid.mul_mem _ (ι_cl03_mem_pinGroup u hu) (ι_cl03_mem_pinGroup w hw_norm),
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (cliffordNegSqForm ℝ 3) u w⟩

/-- Explicit group homomorphism lifting `SU(2)` into `spinGroup (cliffordNegSqForm ℝ 3)`. -/
def su2ToSpinGroupCl03 : SU2 →* spinGroup (cliffordNegSqForm ℝ 3) where
  toFun g := ⟨spinQuat3 (g.1 0 0).re (g.1 0 0).im (g.1 0 1).re (g.1 0 1).im,
    spinQuat3_mem_spinGroup (su2_norm_sq g)⟩
  map_one' := by
    apply Subtype.ext
    simp [spinQuat3]
  map_mul' g₁ g₂ := by
    apply Subtype.ext
    change spinQuat3 ((g₁ * g₂).1 0 0).re ((g₁ * g₂).1 0 0).im
        ((g₁ * g₂).1 0 1).re ((g₁ * g₂).1 0 1).im =
      spinQuat3 (g₁.1 0 0).re (g₁.1 0 0).im (g₁.1 0 1).re (g₁.1 0 1).im *
        spinQuat3 (g₂.1 0 0).re (g₂.1 0 0).im (g₂.1 0 1).re (g₂.1 0 1).im
    rw [spinQuat3_mul]
    have hmul : (g₁.1 * g₂.1) =
        quatToMat (g₁.1 0 0).re (g₁.1 0 0).im (g₁.1 0 1).re (g₁.1 0 1).im *
          quatToMat (g₂.1 0 0).re (g₂.1 0 0).im (g₂.1 0 1).re (g₂.1 0 1).im := by
      rw [← su2_eq_quatToMat g₁, ← su2_eq_quatToMat g₂]
    have h00 : ((g₁ * g₂).1 0 0) = (g₁.1 * g₂.1) 0 0 := rfl
    have h01 : ((g₁ * g₂).1 0 1) = (g₁.1 * g₂.1) 0 1 := rfl
    rw [h00, h01, hmul]
    congr 1 <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, quatToMat, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring

/-- Restriction of `su2ToSpinGroupCl03` to Klein's binary icosahedral subgroup `2I ⊂ SU(2)`. -/
def binaryIcosahedralToSpinGroupCl03 :
    binaryIcosahedralGroup →* spinGroup (cliffordNegSqForm ℝ 3) :=
  su2ToSpinGroupCl03.comp binaryIcosahedralGroup.subtype

/-- Binary icosahedral elements simultaneously leave Klein's aligned icosahedral forms and ratio
invariant and act by equivariant `Spin(0,3)` conjugation (`spinGroup_cliffordOneForms_naturality` +
`quatRotMatrix`) on noncommutative Clifford 1-forms `OneForms (CliffordAlgebra (cliffordNegSqForm ℝ 3))`. -/
theorem binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20
    [Invertible (2 : ℝ)]
    (γ : binaryIcosahedralGroup) (z₁ z₂ : ℂ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ 3)) (v : Fin 3 → ℝ) :
    let gSU2 : SU2 := γ.1
    let gSpin := binaryIcosahedralToSpinGroupCl03 γ
    let a := (gSU2.1 0 0).re
    let b := (gSU2.1 0 0).im
    let c := (gSU2.1 0 1).re
    let d := (gSU2.1 0 1).im
    let w := kleinBinaryAction gSU2 z₁ z₂
    (gSU2 : Mat2C) = quatToMat a b c d ∧
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧
    (gSpin : CliffordAlgebra (cliffordNegSqForm ℝ 3)) = spinQuat3 a b c d ∧
    kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
    kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
    kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂ ∧
    kleinAlignedRatio w.1 w.2 = kleinAlignedRatio z₁ z₂ ∧
    cliffordOneFormsEquiv (cliffordNegSqForm ℝ 3)
        (spinGroupToIsometryHom (cliffordNegSqForm ℝ 3) gSpin)
        (differential (CliffordAlgebra (cliffordNegSqForm ℝ 3)) x) =
      differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
        (spinQuat3 a b c d * x * CliffordAlgebra.reverse (spinQuat3 a b c d)) ∧
    cliffordOneFormsEquiv (cliffordNegSqForm ℝ 3)
        (spinGroupToIsometryHom (cliffordNegSqForm ℝ 3) gSpin)
        (differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
          (∑ r : Fin 3, v r • cGen ℝ 3 r)) =
      differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
        (∑ r : Fin 3, (quatRotMatrix a b c d *ᵥ v) r • cGen ℝ 3 r) := by
  have hforms := binaryIcosahedralGroup_invariant_alignedForms γ.2 z₁ z₂
  have hratio := binaryIcosahedralGroup_invariant_ratio γ.2 z₁ z₂
  have hnatx := spinGroup_cliffordOneForms_naturality (cliffordNegSqForm ℝ 3)
    (binaryIcosahedralToSpinGroupCl03 γ) x
  have hnatv := spinGroup_cliffordOneForms_naturality (cliffordNegSqForm ℝ 3)
    (binaryIcosahedralToSpinGroupCl03 γ) (∑ r : Fin 3, v r • cGen ℝ 3 r)
  have hrot := rotor_conjugation_eq_quatRotMatrix (R := ℝ)
    (γ.1.1 0 0).re (γ.1.1 0 0).im (γ.1.1 0 1).re (γ.1.1 0 1).im v
  refine ⟨su2_eq_quatToMat γ.1, su2_norm_sq γ.1, rfl,
    hforms.1, hforms.2.1, hforms.2.2, hratio.1, hnatx, ?_⟩
  rw [hnatv]
  change differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
      (spinQuat3 (γ.1.1 0 0).re (γ.1.1 0 0).im (γ.1.1 0 1).re (γ.1.1 0 1).im *
          (∑ r : Fin 3, v r • cGen ℝ 3 r) *
        CliffordAlgebra.reverse
          (spinQuat3 (γ.1.1 0 0).re (γ.1.1 0 0).im (γ.1.1 0 1).re (γ.1.1 0 1).im)) =
    differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
      (∑ r : Fin 3,
        (quatRotMatrix (γ.1.1 0 0).re (γ.1.1 0 0).im (γ.1.1 0 1).re (γ.1.1 0 1).im *ᵥ v) r •
          cGen ℝ 3 r)
  rw [hrot]

end Bridge4_IcosahedralSU2SpinCl03OneForms

/-! ## Bridge 5: Master Cross-Spine & Mannheim–Krein Reciprocal Totality Synthesis -/

section Bridge5_MasterSynthesis

open InfoGeometry.Canonical.SmoothPrincipalCartanBundleClosure
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
open InfoGeometry.Erlangen.BirkhoffHilbertConeMetric
open InfoGeometry.Projective.GeneralHilbertConeMetric
open Matrix
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
open InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset

/-- Master cross-spine synthesis uniting Spine II (Cartan bundles, Plücker–Clifford
biquaternions, Birkhoff–Hilbert salient cones, and Klein binary icosahedral `2I` invariants) with
the R1–R2–R3 Maurer–Cartan / `Spin(0,3)` / noncommutative differential lane and the Mannheim–Krein
reciprocal totality `V`-metric theorem and `M₂(ℤ)` witness. -/
theorem sixPillar_r1r2r3_mannheim_reciprocal_master_synthesis
    [Invertible (2 : ℝ)]
    -- Bridge 1 inputs
    {EP EM EH : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    {HP HM HH : Type*} [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HH]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {IH : ModelWithCorners ℝ EH HH}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (B : SmoothPrincipalCartanGeometry EP EM EH HP HM HH IP IM IH P M H 𝔤 𝔥)
    (e₁ e₂ e₃ : SmoothPrincipalTrivialization EP EM EH HP HM HH IP IM IH P M H
      B.toCartan.proj B.toCartan.rightAct)
    {xM : M} (hx₁ : xM ∈ e₁.toTrivialization.baseSet) (hx₂ : xM ∈ e₂.toTrivialization.baseSet)
    (hx₃ : xM ∈ e₃.toTrivialization.baseSet)
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A)
    (ρ : H →* Aˣ) (Γ : DerivationOperatorForm K 1)
    -- Bridge 2 inputs
    (d m : Fin 3 → ℝ)
    -- Bridge 3 inputs
    {Econe : Type*} [NormedAddCommGroup Econe] [NormedSpace ℝ Econe] [Nontrivial Econe]
    (C : ProperCone ℝ Econe) (hC : C.toPointedCone.toConvexCone.Salient)
    {xC yC : Econe} (hxC : xC ∈ interior (C : Set Econe)) (hyC : yC ∈ interior (C : Set Econe))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ xC = c • yC)
    -- Bridge 4 inputs
    (γ : binaryIcosahedralGroup) (z₁ z₂ : ℂ)
    (xCl : CliffordAlgebra (cliffordNegSqForm ℝ 3)) (v : Fin 3 → ℝ)
    -- Bridge 5 (Mannheim–Krein V-metric) inputs
    {Rop : Type*} [Ring Rop] [StarRing Rop] (Ω η : Rop)
    (hΩ : Ω * Ω = Ω) (hη : star η = η) (hηΩ : η * Ω = star Ω * η) :
    -- 1. Bridge 1: Principal bundle cocycle → Maurer–Cartan gauge & CE curvature
    (gaugeTransformOneForm K (ρ (principalTransition B e₁ e₃ xM)) Γ =
      gaugeTransformOneForm K (ρ (principalTransition B e₁ e₂ xM))
        (gaugeTransformOneForm K (ρ (principalTransition B e₂ e₃ xM)) Γ) ∧
     rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₃ xM)) =
      rightGaugeTransformOneForm K
        (rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₂ xM)))
        (ρ (principalTransition B e₂ e₃ xM)) ∧
     ceCurvature K (rightGaugeTransformOneForm K Γ (ρ (principalTransition B e₁ e₃ xM))) =
      conjugateForm K (ρ (principalTransition B e₁ e₃ xM))⁻¹ (ceCurvature K Γ)) ∧
    -- 2. Bridge 2: Chiral biquaternions ↔ Peirce/Grace reflection & Plücker–Klein polarization
    (complementIdempotent biquatIdempPlus = biquatIdempMinus ∧
     reflection biquatIdempPlus = ω₄ ℝ ∧
     biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
       (-(d ⬝ᵥ d + m ⬝ᵥ m) - 2 * (d ⬝ᵥ m)) • biquatIdempPlus ∧
     biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempPlus =
       (-((d + m) ⬝ᵥ (d + m))) • biquatIdempPlus ∧
     biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
       (-(d ⬝ᵥ d + m ⬝ᵥ m) + 2 * (d ⬝ᵥ m)) • biquatIdempMinus ∧
     biquatBivector ℝ d m * biquatBivector ℝ d m * biquatIdempMinus =
       (-((d - m) ⬝ᵥ (d - m))) • biquatIdempMinus ∧
     ((d + m) ⬝ᵥ (d + m)) - ((d - m) ⬝ᵥ (d - m)) =
       4 * (directionMomentEquiv.symm (d, m)).kleinQ) ∧
    -- 3. Bridge 3: Skew Casimir non-salience vs. Onsager salience & Birkhoff–Hilbert chord metric
    ((∃ A₀ : Matrix (Fin 2) (Fin 2) ℝ,
        A₀.transpose = -A₀ ∧ A₀ ≠ 0 ∧
          (∀ w : Fin 2 → ℝ, 0 ≤ w ⬝ᵥ (A₀ *ᵥ w)) ∧
          (∀ w : Fin 2 → ℝ, 0 ≤ w ⬝ᵥ ((-A₀) *ᵥ w))) ∧
     (∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ),
        S.transpose = S →
        (∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (S *ᵥ w)) →
        (∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ ((-S) *ᵥ w)) → S = 0) ∧
     (let u := extremalRayLeft C xC yC
      let vRay := extremalRayRight C xC yC
      let τ_x := 1 / (upperGauge C xC yC + 1)
      let τ_y := upperGauge C yC xC / (upperGauge C yC xC + 1)
      let p : ℝ → Econe := fun τ => (1 - τ) • u + τ • vRay
      u ∈ frontier (C : Set Econe) ∧ vRay ∈ frontier (C : Set Econe) ∧
        0 < τ_x ∧ τ_x < τ_y ∧ τ_y < 1 ∧
        (∃ cx : ℝ, 0 < cx ∧ p τ_x = cx • xC) ∧ (∃ cy : ℝ, 0 < cy ∧ p τ_y = cy • yC) ∧
        birkhoffHilbertMetric C xC yC =
          (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0 τ_x τ_y 1))) ∧
    -- 4. Bridge 4: Binary icosahedral `2I` ↔ `Spin(0,3)` ↔ Clifford 1-forms (`Erlangen20`)
    (let gSU2 : SU2 := γ.1
     let gSpin := binaryIcosahedralToSpinGroupCl03 γ
     let a := (gSU2.1 0 0).re
     let b := (gSU2.1 0 0).im
     let c := (gSU2.1 0 1).re
     let d₀ := (gSU2.1 0 1).im
     let w := kleinBinaryAction gSU2 z₁ z₂
     (gSU2 : Mat2C) = quatToMat a b c d₀ ∧
     a ^ 2 + b ^ 2 + c ^ 2 + d₀ ^ 2 = 1 ∧
     (gSpin : CliffordAlgebra (cliffordNegSqForm ℝ 3)) = spinQuat3 a b c d₀ ∧
     kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
     kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
     kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂ ∧
     kleinAlignedRatio w.1 w.2 = kleinAlignedRatio z₁ z₂ ∧
     cliffordOneFormsEquiv (cliffordNegSqForm ℝ 3)
         (spinGroupToIsometryHom (cliffordNegSqForm ℝ 3) gSpin)
         (differential (CliffordAlgebra (cliffordNegSqForm ℝ 3)) xCl) =
       differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
         (spinQuat3 a b c d₀ * xCl * CliffordAlgebra.reverse (spinQuat3 a b c d₀)) ∧
     cliffordOneFormsEquiv (cliffordNegSqForm ℝ 3)
         (spinGroupToIsometryHom (cliffordNegSqForm ℝ 3) gSpin)
         (differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
           (∑ r : Fin 3, v r • cGen ℝ 3 r)) =
       differential (CliffordAlgebra (cliffordNegSqForm ℝ 3))
         (∑ r : Fin 3, (quatRotMatrix a b c d₀ *ᵥ v) r • cGen ℝ 3 r)) ∧
    -- 5. Abstract Mannheim–Krein `V`-metric & concrete `M₂(ℤ)` aporia/positivity witness
    ((star (mannheimV η Ω) = mannheimV η Ω ∧
      mannheimV η Ω * JOmega Ω = η ∧
      mannheimV η Ω * JOmega Ω = star (JOmega Ω) * mannheimV η Ω ∧
      mannheimV η Ω * Ω = η * Ω ∧
      mannheimV η Ω * Ω = star Ω * mannheimV η Ω ∧
      star (JOmega Ω) * mannheimV η Ω * JOmega Ω = mannheimV η Ω) ∧
     (cutP0 * cutP0 = cutP0 ∧
      totalityOmega0 * totalityOmega0 = totalityOmega0 ∧
      _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0 kreinEta0 = 0 ∧
      kreinEta0.transpose = kreinEta0 ∧
      kreinEta0.det = -2 ∧
      kreinEta0 * totalityOmega0 = !![4, 2; 2, 1] ∧
      kreinEta0 * totalityOmega0 = totalityOmega0.transpose * kreinEta0 ∧
      (JOmega totalityOmega0).transpose * kreinEta0 * JOmega totalityOmega0 = kreinEta0 ∧
      aporia cutP0 totalityOmega0 = !![-2, 0; 0, 0] ∧
      1 - Sigma0 cutP0 totalityOmega0 * Sigma0 cutP0 totalityOmega0 = !![-8, 0; 0, -8] ∧
      JOmega totalityOmega0 = !![3, 2; -4, -3] ∧
      mannheimV0 = !![6, 4; 4, 3] ∧
      mannheimV0.transpose = mannheimV0 ∧
      mannheimV0.det = 2 ∧
      (∀ x y : ℤ, 6 * x ^ 2 + 8 * x * y + 3 * y ^ 2 = (2 * x + y) ^ 2 + 2 * (x + y) ^ 2) ∧
      (∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → 0 < (2 * x + y) ^ 2 + 2 * (x + y) ^ 2))) := by
  exact
    ⟨principalTransition_gaugeTransformL_cocycle B e₁ e₂ e₃ hx₁ hx₂ hx₃ K ρ Γ,
     biquatBivector_peirce_grace_krein_polarization d m,
     gibbsBKM_onsager_birkhoffHilbert_chord_metric C hC hxC hyC hray,
     binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20 γ z₁ z₂ xCl v,
     ⟨krein_reciprocalTotality_mannheim_V_metric Ω η hΩ hη hηΩ,
      concrete_mat2Z_krein_mannheim_V_metric_witness⟩⟩

end Bridge5_MasterSynthesis

end InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityCrossSpineSynthesis
