/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
import InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis
import InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis

/-!
# Intertwining Krein Positive-Sector Projections, Peirce Defect Spine, and Colimits

Connects the `ClTower` Krein/positive-sector/Mathlib-colimit lane
(`NoncommutativeYangMillsKreinCantorSynthesis`, `NoncommutativeKreinMathlibBridge`)
and the noncommutative Berry–Chern curvature lane
(`NoncommutativePeierlsBerryKitaevSynthesis`) with the repository's existing
Peirce defect & Yang–Mills Bianchi spine (`PeirceDefectBridge`):

1. **Peirce upper-corner compression = positive-sector Krein positivity**:
   For any self-adjoint `+1`-sector projection `P` (`P * P = P`, `star P = P`,
   `kroneckerGamma γ₀ n * P = P`), `peirce11 P X = P * X * P` satisfies both the
   Peirce corner defect identity (`peirce11_idempotencyDefect_sub`), the
   Maurer–Cartan self-dual Bianchi identity
   (`peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills`), and
   `StarOrderedRing` Krein positivity `0 ≤ towerTrace (kreinAdjoint γ₀ n (peirce11 P X) * peirce11 P X)`.
2. **Tower-morphism & colimit transport**:
   `PeirceSpine.RingHomTransport` supplies naturality for `evenGrade`, `oddGrade`,
   and `genV`. This module packages `RingHom` naturality for `peirce11`,
   `peirceCovariantDeriv`, `peirceMaurerCartanCurvature`, and
   `idempotencyDefect`; its `clTowerHom`/Mathlib-colimit theorem proves transport
   of curvature and `peirce11` across `m ≤ n`.
3. **Berry–Chern curvature on `positiveSectorProj`**:
   `positiveSectorProj π₀ n` satisfies the noncommutative Berry–Chern curvature
   identity (`noncomm_berry_chern_projection_curvature`) at every depth `n`.
-/

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
open InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
open InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis

namespace InfoGeometry.Algebra.KreinPeirceTowerIntertwine

universe u

section PeircePositiveSector

variable {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
  [StarRing B] [StarOrderedRing B]

/-- On any self-adjoint `+1`-sector projection `P` in `ClTower B n`, the Peirce
upper-corner compression `peirce11 P X` has `kreinAdjoint = star` and non-negative
`towerTrace` pairing, simultaneously with the Peirce corner defect and Bianchi
identities. -/
theorem peirce11_positive_sector_krein_positivity_and_bianchi
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ) (P X A C : ClTower B n)
    (hP_sq : P * P = P) (hP_star : star P = P)
    (hP_pos : kroneckerGamma γ₀ n * P = P) :
    kreinAdjoint γ₀ n (OperatorAlgebra.PeirceSpine.peirce11 P X) =
      star (OperatorAlgebra.PeirceSpine.peirce11 P X) ∧
      (0 : B) ≤ towerTrace (kreinAdjoint γ₀ n
        (OperatorAlgebra.PeirceSpine.peirce11 P X) *
          OperatorAlgebra.PeirceSpine.peirce11 P X) ∧
      OperatorAlgebra.PeirceSpine.peirce11 P (idempotencyDefect X) -
        idempotencyDefect (OperatorAlgebra.PeirceSpine.peirce11 P X) =
        qgtPlus P X X ∧
      peirceCovariantDeriv P A C (genV P A C) = 0 := by
  have h1 : OperatorAlgebra.PeirceSpine.peirce11 P X = P * X * P := by
    simp [OperatorAlgebra.PeirceSpine.peirce11, mul_assoc]
  have h_adj : kreinAdjoint γ₀ n (OperatorAlgebra.PeirceSpine.peirce11 P X) =
      star (OperatorAlgebra.PeirceSpine.peirce11 P X) := by
    rw [h1]
    exact (positive_sector_ghost_excision hγ₀_star n P X X hP_star hP_pos).2.1
  have h_nonneg :
      (0 : B) ≤ towerTrace (kreinAdjoint γ₀ n
        (OperatorAlgebra.PeirceSpine.peirce11 P X) *
          OperatorAlgebra.PeirceSpine.peirce11 P X) := by
    rw [h1]
    exact positive_sector_krein_pairing_nonneg hγ₀_star n P X hP_star hP_pos
  have h_defect := peirce11_idempotencyDefect_sub P X hP_sq
  have h_bianchi :=
    (peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP_sq A C X X).2.2.2.2.2.2.2.2.2.1
  exact ⟨h_adj, h_nonneg, h_defect, h_bianchi⟩

end PeircePositiveSector

section RingHomAndColimitTransport

variable {B : Type u} [Ring B]

/-- Any `RingHom` `f : R →+* S` preserves the Peirce upper-corner, Maurer–Cartan
curvature, covariant derivative, and idempotency defect. Grading naturality for
`evenGrade`, `oddGrade`, and `genV` is provided by
`PeirceSpine.RingHomTransport`. -/
theorem ringHom_preserves_peirce_yang_mills
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (P A C X : R) :
    f (OperatorAlgebra.PeirceSpine.peirce11 P X) =
      OperatorAlgebra.PeirceSpine.peirce11 (f P) (f X) ∧
      f (idempotencyDefect X) = idempotencyDefect (f X) ∧
      f (peirceMaurerCartanCurvature P A C) =
        peirceMaurerCartanCurvature (f P) (f A) (f C) ∧
      f (peirceCovariantDeriv P A C X) =
        peirceCovariantDeriv (f P) (f A) (f C) (f X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [OperatorAlgebra.PeirceSpine.peirce11]
  · simp [idempotencyDefect]
  · simp [peirceMaurerCartanCurvature, peirceGradingDeriv, genPhi,
      OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus,
      map_add, map_sub, map_mul]
  · simp [peirceCovariantDeriv, peirceGradingDeriv, genPhi,
      OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus,
      map_add, map_sub, map_mul]

/-- `clTowerHom B h` transports the Peirce Yang–Mills spine across all tower
scales `m ≤ n`, and `colimit.ι (clTowerFunctor B) n` transports it into the
native Mathlib `RingCat` colimit `ClTowerColimit B`. -/
theorem clTower_and_colimit_peirce_transport
    {m n : ℕ} (h : m ≤ n) (P A C X : ClTower B m) :
    clTowerHom B h (peirceMaurerCartanCurvature P A C) =
      peirceMaurerCartanCurvature (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C) ∧
      (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) n).hom
          (OperatorAlgebra.PeirceSpine.peirce11 (clTowerHom B h P)
            (clTowerHom B h X)) =
        OperatorAlgebra.PeirceSpine.peirce11
          ((CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom P)
          ((CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom X) := by
  refine ⟨(ringHom_preserves_peirce_yang_mills (clTowerHom B h) P A C X).2.2.1, ?_⟩
  have hmul : clTowerHom B h P * clTowerHom B h X * clTowerHom B h P =
      clTowerHom B h (P * X * P) := by simp
  simp only [OperatorAlgebra.PeirceSpine.peirce11]
  change (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) n).hom
      (clTowerHom B h P * clTowerHom B h X * clTowerHom B h P) =
    (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom P *
      (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom X *
      (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom P
  rw [hmul, clTowerColimit_ι_comp h (P * X * P)]
  erw [map_mul, map_mul]

end RingHomAndColimitTransport

section PositiveSectorBerryChern

variable {B : Type u} [Ring B] [StarRing B]

/-- `positiveSectorProj π₀ n` carries the noncommutative Berry–Chern projection
curvature identity at every tower depth `n`. -/
theorem positiveSectorProj_berry_chern_curvature
    {γ₀ π₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (hπ_sq : π₀ * π₀ = π₀) (hπ_star : star π₀ = π₀) (hπ_pos : γ₀ * π₀ = π₀)
    (n : ℕ) (d₁ d₂ : RingDeriv (ClTower B n)) :
    let P := positiveSectorProj π₀ n
    P * d₁.toFun P * P = 0 ∧
      P * d₁.toFun P = d₁.toFun P * (1 - P) ∧
      berryChernCurvature d₁ d₂ P =
        P * d₁.toFun P * (1 - P) * d₂.toFun P * P -
          P * d₂.toFun P * (1 - P) * d₁.toFun P * P ∧
      (P * berryChernCurvature d₁ d₂ P = berryChernCurvature d₁ d₂ P ∧
        berryChernCurvature d₁ d₂ P * P = berryChernCurvature d₁ d₂ P) := by
  have hP_sq := (positiveSectorProj_props hγ₀_star hπ_sq hπ_star hπ_pos n).2.1
  exact noncomm_berry_chern_projection_curvature d₁ d₂ hP_sq

end PositiveSectorBerryChern

section KitaevMajoranaKreinPeirceClosure

/-- `hexPlaquette` on the `M₂(B)` Zorn triad `(Γ₁, Σ, Ω, Γ₁, Σ, Ω)` equals
`kitaevPlaquette6` and hence `1`. -/
theorem hexPlaquette_eq_kitaevPlaquette6 {B : Type u} [Ring B] :
    hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp = kitaevPlaquette6 ∧
    hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp = 1 := by
  have h1 : hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp = kitaevPlaquette6 := by
    dsimp [hexPlaquette, kitaevPlaquette6]
  exact ⟨h1, h1.trans (kitaev_honeycomb_triad_and_plaquette_invariant (B := B)).2.2.2.2.2.2.1⟩

/-- `cantorProj n` in `NoncommutativeDiracSheetMixingAndEntropyTower` coincides
with `positiveSectorProj (1 : B) n`, and `majoranaPlusProj n` coincides with
`positiveSectorProj (1 : B) (n + 1)`. -/
theorem cantorProj_eq_positiveSectorProj {B : Type u} [Ring B] :
    ∀ (n : ℕ), cantorProj (A := B) n = positiveSectorProj (1 : B) n
  | 0 => rfl
  | n + 1 => by
      dsimp [cantorProj, positiveSectorProj, topSheetEmbed]
      rw [cantorProj_eq_positiveSectorProj n]

theorem majoranaPlusProj_eq_positiveSectorProj {B : Type u} [Ring B] (n : ℕ) :
    majoranaPlusProj (B := B) n = positiveSectorProj (1 : B) (n + 1) := by
  dsimp [majoranaPlusProj, positiveSectorProj, topSheetEmbed]
  rw [cantorProj_eq_positiveSectorProj n]

/-- The two recursively defined chiral mode projections are the orthogonal
`+1` and `-1` eigensector projections of the tower grading.  This connects the
trace-splitting projections to the positive-sector/Krein projection API while
retaining their full matrix-algebra carriers. -/
theorem majorana_chiral_projections_are_orthogonal_grading_sectors
    {B : Type u} [Ring B] [StarRing B] (n : ℕ) :
    let Pplus := majoranaPlusProj (B := B) n
    let Pminus := majoranaMinusProj (B := B) n
    let P := kroneckerGamma (1 : B) (n + 1)
    Pplus * Pplus = Pplus ∧ Pminus * Pminus = Pminus ∧
      Pplus * Pminus = 0 ∧ Pminus * Pplus = 0 ∧
      star Pplus = Pplus ∧ star Pminus = Pminus ∧
      P * Pplus = Pplus ∧ P * Pminus = -Pminus ∧
      Pplus + Pminus = fullDiracModeProj (B := B) n := by
  let Pplus : ClTower B (n + 1) := majoranaPlusProj (B := B) n
  let Pminus : ClTower B (n + 1) := majoranaMinusProj (B := B) n
  let P : ClTower B (n + 1) := kroneckerGamma (1 : B) (n + 1)
  have hsplit := all_scales_chiral_projection_trace_split (B := B) n
  have hproj := (positiveSectorProj_props
    (γ₀ := (1 : B)) (π₀ := (1 : B))
    (star_one B) (one_mul 1) (star_one B) (one_mul 1) n)
  have hcantor_star : star (cantorProj (A := B) n) = cantorProj n := by
    rw [cantorProj_eq_positiveSectorProj (B := B) n]
    exact hproj.2.2
  have hcantor_pos : kroneckerGamma (1 : B) n * cantorProj (A := B) n =
      cantorProj n := by
    rw [cantorProj_eq_positiveSectorProj (B := B) n]
    exact hproj.1
  have hPplus : P * Pplus = Pplus := by
    dsimp [P, Pplus]
    rw [majoranaPlusProj_eq_positiveSectorProj]
    exact (positiveSectorProj_props
      (γ₀ := (1 : B)) (π₀ := (1 : B))
      (star_one B) (one_mul 1) (star_one B) (one_mul 1) (n + 1)).1
  have hPminus : P * Pminus = -Pminus := by
    apply ext_fin2
    · simp [P, Pminus, kroneckerGamma, majoranaMinusProj]
    · simp [P, Pminus, kroneckerGamma, majoranaMinusProj]
    · simp [P, Pminus, kroneckerGamma, majoranaMinusProj]
    · simp [P, Pminus, kroneckerGamma, majoranaMinusProj, hcantor_pos]
  have hstarPlus : star Pplus = Pplus := by
    dsimp [Pplus]
    rw [majoranaPlusProj_eq_positiveSectorProj]
    exact (positiveSectorProj_props
      (γ₀ := (1 : B)) (π₀ := (1 : B))
      (star_one B) (one_mul 1) (star_one B) (one_mul 1) (n + 1)).2.2
  have hstarMinus : star Pminus = Pminus := by
    apply ext_fin2 <;> simp [Pminus, majoranaMinusProj, hcantor_star]
  rcases hsplit with ⟨hsum, hp2, hm2, hpm, hmp, _, _, _, _, _⟩
  exact ⟨hp2, hm2, hpm, hmp, hstarPlus, hstarMinus, hPplus, hPminus, hsum⟩

/-- The `-1` chiral mode projection gives a nonpositive Krein quadratic pairing
on its compressed states. The exact sign is the negative of the tower
Hilbert-star square, so this is a matrix-tower statement over `B`, independent
of the separate real Hilbert-space sheet results. -/
theorem majoranaMinusProj_krein_pairing_nonpos
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    (n : ℕ) (X : ClTower B (n + 1)) :
    let Mminus := majoranaMinusProj (B := B) n
    let GammaN := kroneckerGamma (1 : B) (n + 1)
    InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
        (star (Mminus * X) * GammaN * (Mminus * X)) =
        -(InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
          (star (Mminus * X) * (Mminus * X))) ∧
      InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
        (star (Mminus * X) * GammaN * (Mminus * X)) ≤ 0 := by
  intro Mminus GammaN
  rcases majorana_chiral_projections_are_orthogonal_grading_sectors
      (B := B) n with ⟨_, _, _, _, _, hMstar, _, hMeigen, _⟩
  have hGammaStar : star GammaN = GammaN := by
    dsimp [GammaN]
    exact kroneckerGamma_star (γ₀ := (1 : B)) (star_one B) (n + 1)
  have hRight : Mminus * GammaN = -Mminus := by
    have h := congrArg star hMeigen
    simpa [Mminus, GammaN, star_mul, hMstar, hGammaStar] using h
  have hPair : star (Mminus * X) * GammaN * (Mminus * X) =
      -(star (Mminus * X) * (Mminus * X)) := by
    calc
      star (Mminus * X) * GammaN * (Mminus * X) =
          star X * (Mminus * GammaN) * (Mminus * X) := by
            rw [star_mul, hMstar]
            noncomm_ring
      _ = star X * (-Mminus) * (Mminus * X) := by rw [hRight]
      _ = -(star X * Mminus * (Mminus * X)) := by noncomm_ring
      _ = -(star (Mminus * X) * (Mminus * X)) := by
            rw [star_mul, hMstar]
  have hTrace : InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
        (star (Mminus * X) * GammaN * (Mminus * X)) =
      -(InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
        (star (Mminus * X) * (Mminus * X))) := by
    rw [hPair, InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace_neg]
  refine ⟨hTrace, ?_⟩
  rw [hTrace]
  exact neg_nonpos.mpr
    (InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge.towerTrace_star_mul_self_nonneg
      (n := n + 1) (Mminus * X))

/-- Every chiral Majorana projection `majoranaPlusProj n` in `ClTower B (n + 1)`
inherits `StarOrderedRing` Krein positivity, Peirce corner defect, and self-dual
Yang–Mills Bianchi conservation. -/
theorem majoranaPlusProj_krein_positivity_and_bianchi
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    (n : ℕ) (X A C : ClTower B (n + 1)) :
    let M_plus := majoranaPlusProj (B := B) n
    kreinAdjoint (1 : B) (n + 1)
        (OperatorAlgebra.PeirceSpine.peirce11 M_plus X) =
      star (OperatorAlgebra.PeirceSpine.peirce11 M_plus X) ∧
      (0 : B) ≤ InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace (n := n + 1)
        (kreinAdjoint (1 : B) (n + 1)
          (OperatorAlgebra.PeirceSpine.peirce11 M_plus X) *
            OperatorAlgebra.PeirceSpine.peirce11 M_plus X) ∧
      OperatorAlgebra.PeirceSpine.peirce11 M_plus (idempotencyDefect X) -
        idempotencyDefect (OperatorAlgebra.PeirceSpine.peirce11 M_plus X) =
        qgtPlus M_plus X X ∧
      peirceCovariantDeriv M_plus A C (genV M_plus A C) = 0 := by
  intro M_plus
  have h_eq : M_plus = positiveSectorProj (1 : B) (n + 1) :=
    majoranaPlusProj_eq_positiveSectorProj n
  obtain ⟨h_pos, h_sq, h_star⟩ :=
    positiveSectorProj_props (γ₀ := (1 : B)) (π₀ := (1 : B))
      (star_one B) (one_mul 1) (star_one B) (one_mul 1) (n + 1)
  rw [← h_eq] at h_pos h_sq h_star
  exact peirce11_positive_sector_krein_positivity_and_bianchi
    (star_one B) (n + 1) M_plus X A C h_sq h_star h_pos

/-- The Kitaev honeycomb Dirac–Zorn Hamiltonian `kitaevHoneycombH Δ_H K₁ K₂ K₃`
satisfies `StarOrderedRing` spectral-action nonnegativity whenever the bond
couplings commute. -/
theorem kitaevHoneycombH_spectral_action_nonneg
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    (Δ_H K₁ K₂ K₃ : B) :
    let H_Δ := kitaevHoneycombH Δ_H K₁ K₂ K₃
    (0 : B) ≤ trace4 ((H_Δ ^ 2)ᴴ * H_Δ ^ 2) := by
  intro H_Δ
  change (0 : B) ≤ trace4 (((diracZornOp Δ_H (-Δ_H) K₁ K₂ K₃ K₁ K₂ K₃ : NestedMat B) ^ 2)ᴴ *
    (diracZornOp Δ_H (-Δ_H) K₁ K₂ K₃ K₁ K₂ K₃ : NestedMat B) ^ 2)
  exact unified_yang_mills_higgs_spectral_action_nonneg Δ_H 0 0 0 K₁ K₂ K₃
    (by rw [Ring.lie_def]; simp) (by rw [Ring.lie_def]; simp)
    (by rw [Ring.lie_def]; simp) |> fun h => by
      simpa [zero_add] using h

end KitaevMajoranaKreinPeirceClosure

end InfoGeometry.Algebra.KreinPeirceTowerIntertwine
