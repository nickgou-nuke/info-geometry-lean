/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Canonical.LieJordanHodgeColimit
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixColimitTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Stage-System Intertwining and Quadratic-Bound Transfer for the Peirce Tetraktys Colimit

This module connects the noncommutative Peirce Tetraktys and two-sheeted operator
identities (`TwoSheetedYangMillsInductiveColimit`, `MatrixColimitTransport`,
`StarGrading`, `CurvatureDoubleCommutator`) to the inductive colimit `Limit` and
conditional quadratic-bound transfer in `LieJordanHodgeColimit`.

## Main Theorems

1. `genV_eq_conePlus_hodge_coefficient`: For any self-adjoint idempotent `P` (`star P = P`)
   in a `StarRing B`, the Peirce Tetraktys quadratic coupling `genV P A (star A)`
   (`opQuadraticCoupling P A (star A)`) equals the symmetric Gram expression
   `conePlus P A * star (conePlus P A) + star (conePlus P A) * conePlus P A`.
2. `stageEmbed_intertwines_two_sheeted_tetraktys` and
   `ofStage_intertwines_two_sheeted_tetraktys`: The stage bonding homomorphisms
   `stageEmbed n : Stage n →ₐ[ℝ] Stage (n + 1)` and colimit canonical maps
   `ofStage n : Stage n →+* Limit` intertwine the entire two-sheeted Tetraktys
   (`opBitGrading`, `opZig`, `opZag`, `opElectron`, `opAxial`, `opQuadraticCoupling`,
   `opSpinDipole`, and `derivSqPhi`).
3. `peirce_tetraktys_hodge_identity_at_limit`: At the inductive colimit `Limit`, for any
   `P A : Limit` with `star P = P`, the anticommutator of `boundary (conePlus P A)` and
   `coboundary (coneMinus P (star A))` equals `liftOp (jordanLeft (genV P A (star A)))`.
4. `peirce_genV_normalized_energy_bond`: The normalized trace pairing of the Jordan action
   of `genV P A (star A)` is invariant under `stageEmbed n`.
5. `peirce_tetraktys_uniform_quadratic_bound_descends`: When a stage family `(P n, A n)`
   stabilizes in `Limit` above `start : ℕ` to `(Pinf, Ainf)`, an assumed uniform finite-stage
   quadratic inequality for `genV (P n) (A n) (star (A n))` transfers to
   `genV Pinf Ainf (star Ainf)` on all of `Limit`. The hypotheses do not require `gamma > 0`
   or make `P n` a projection, so this theorem alone asserts no positivity or coercivity.
-/

namespace InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

open InfoGeometry.OperatorAlgebra.PeirceSpine
open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.Canonical.LieJordanHodgeColimit
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-! ## 1. Universal Star-Ring Identification of `genV` with the Hodge Coefficient -/

section StarRingIdentity

variable {B : Type*} [Ring B] [StarRing B]

/-- For a self-adjoint element `P` (`star P = P`), the Peirce Tetraktys quadratic coupling
`genV P A (star A)` is the symmetric Gram sum `N₊ N₊* + N₊* N₊` of `N₊ = conePlus P A`. -/
theorem genV_eq_conePlus_hodge_coefficient {P : B} (hPs : star P = P) (A : B) :
    genV P A (star A) =
      conePlus P A * star (conePlus P A) + star (conePlus P A) * conePlus P A := by
  rw [star_conePlus hPs A]
  rfl

/-- Equivalent statement in the `CanonicalTwoSheetedInductiveColimit` vocabulary:
`opQuadraticCoupling P A (star A)` equals `opZig P A * star (opZig P A) + star (opZig P A) * opZig P A`. -/
theorem opQuadraticCoupling_eq_opZig_gram {P : B} (hPs : star P = P) (A : B) :
    opQuadraticCoupling P A (star A) =
      opZig P A * star (opZig P A) + star (opZig P A) * opZig P A :=
  genV_eq_conePlus_hodge_coefficient hPs A

end StarRingIdentity

/-! ## 2. Stage-Bonding and Colimit Intertwining of the Two-Sheeted Tetraktys -/

/-- The stage-bonding homomorphism `stageEmbed n : Stage n →ₐ[ℝ] Stage (n + 1)` intertwines
all seven two-sheeted Tetraktys operators and the curvature double commutator `derivSqPhi`. -/
theorem stageEmbed_intertwines_two_sheeted_tetraktys (n : ℕ) (P A C X : Stage n) :
    stageEmbed n (opBitGrading P) = opBitGrading (stageEmbed n P) ∧
    stageEmbed n (opZig P A) = opZig (stageEmbed n P) (stageEmbed n A) ∧
    stageEmbed n (opZag P C) = opZag (stageEmbed n P) (stageEmbed n C) ∧
    stageEmbed n (opElectron P A C) =
      opElectron (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) ∧
    stageEmbed n (opAxial P A C) =
      opAxial (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) ∧
    stageEmbed n (opQuadraticCoupling P A C) =
      opQuadraticCoupling (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) ∧
    stageEmbed n (opSpinDipole P A C) =
      opSpinDipole (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) ∧
    stageEmbed n (derivSqPhi P A C X) =
      derivSqPhi (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) (stageEmbed n X) := by
  let f : Stage n →+* Stage (n + 1) := (stageEmbed n).toRingHom
  exact ⟨map_invS f P, map_conePlus f P A, map_coneMinus f P C,
    map_genPhi f P A C, map_genJ f P A C, map_genV f P A C,
    map_genSig f P A C, map_derivSqPhi f P A C X⟩

/-- The canonical stage-to-colimit homomorphism `ofStage n : Stage n →+* Limit` intertwines
all seven two-sheeted Tetraktys operators and the curvature double commutator `derivSqPhi`. -/
theorem ofStage_intertwines_two_sheeted_tetraktys (n : ℕ) (P A C X : Stage n) :
    ofStage n (opBitGrading P) = opBitGrading (ofStage n P) ∧
    ofStage n (opZig P A) = opZig (ofStage n P) (ofStage n A) ∧
    ofStage n (opZag P C) = opZag (ofStage n P) (ofStage n C) ∧
    ofStage n (opElectron P A C) =
      opElectron (ofStage n P) (ofStage n A) (ofStage n C) ∧
    ofStage n (opAxial P A C) =
      opAxial (ofStage n P) (ofStage n A) (ofStage n C) ∧
    ofStage n (opQuadraticCoupling P A C) =
      opQuadraticCoupling (ofStage n P) (ofStage n A) (ofStage n C) ∧
    ofStage n (opSpinDipole P A C) =
      opSpinDipole (ofStage n P) (ofStage n A) (ofStage n C) ∧
    ofStage n (derivSqPhi P A C X) =
      derivSqPhi (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) :=
  ⟨map_invS (ofStage n) P, map_conePlus (ofStage n) P A, map_coneMinus (ofStage n) P C,
    map_genPhi (ofStage n) P A C, map_genJ (ofStage n) P A C, map_genV (ofStage n) P A C,
    map_genSig (ofStage n) P A C, map_derivSqPhi (ofStage n) P A C X⟩

/-- Stage-bonding coherence in `Limit` for the two-sheeted Peirce Tetraktys and its
double-commutator operator `derivSqPhi`. -/
theorem ofStage_bond_two_sheeted_tetraktys (n : ℕ) (P A C X : Stage n) :
    ofStage (n + 1) (genPhi (stageEmbed n P) (stageEmbed n A) (stageEmbed n C)) =
      ofStage n (genPhi P A C) ∧
    ofStage (n + 1) (genJ (stageEmbed n P) (stageEmbed n A) (stageEmbed n C)) =
      ofStage n (genJ P A C) ∧
    ofStage (n + 1) (genV (stageEmbed n P) (stageEmbed n A) (stageEmbed n C)) =
      ofStage n (genV P A C) ∧
    ofStage (n + 1) (genSig (stageEmbed n P) (stageEmbed n A) (stageEmbed n C)) =
      ofStage n (genSig P A C) ∧
    ofStage (n + 1)
        (derivSqPhi (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) (stageEmbed n X)) =
      ofStage n (derivSqPhi P A C X) := by
  let f : Stage n →+* Stage (n + 1) := (stageEmbed n).toRingHom
  have hPhi : genPhi (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) =
      stageEmbed n (genPhi P A C) := (map_genPhi f P A C).symm
  have hJ : genJ (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) =
      stageEmbed n (genJ P A C) := (map_genJ f P A C).symm
  have hV : genV (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) =
      stageEmbed n (genV P A C) := (map_genV f P A C).symm
  have hSig : genSig (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) =
      stageEmbed n (genSig P A C) := (map_genSig f P A C).symm
  have hD : derivSqPhi (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) (stageEmbed n X) =
      stageEmbed n (derivSqPhi P A C X) := (map_derivSqPhi f P A C X).symm
  rw [hPhi, hJ, hV, hSig, hD]
  simp only [ofStage_apply_bond, and_self]

/-- At the inductive colimit `Limit`, any stage idempotent `P : Stage n` (`P * P = P`) and
limit amplitudes `A C : Limit` satisfy the full two-sheeted Peirce Tetraktys table and
the quadratic curvature double-commutator identity `curvatureDoubleCommutator_quadratic_phi`. -/
theorem limit_two_sheeted_tetraktys_from_stage
    (n : ℕ) {P : Stage n} (hP : P * P = P) (A C : Limit) :
    let Pinf := ofStage n P
    opZig Pinf A * opZig Pinf A = 0 ∧
    opZag Pinf C * opZag Pinf C = 0 ∧
    opElectron Pinf A C * opElectron Pinf A C = opQuadraticCoupling Pinf A C ∧
    opAxial Pinf A C * opAxial Pinf A C = -opQuadraticCoupling Pinf A C ∧
    opAxial Pinf A C * opElectron Pinf A C = opSpinDipole Pinf A C ∧
    curvatureDoubleCommutator Pinf A C (curvatureDoubleCommutator Pinf A C (genPhi Pinf A C)) +
      (4 : ℤ) • (genV Pinf A C * curvatureDoubleCommutator Pinf A C (genPhi Pinf A C)) -
      (4 : ℤ) • ((genV Pinf A C * genV Pinf A C) * genPhi Pinf A C) = 0 := by
  dsimp only
  have hPinf : ofStage n P * ofStage n P = ofStage n P := map_idempotent (ofStage n) hP
  rcases directed_components_square_zero hPinf A C with ⟨hZig, hZag⟩
  rcases two_sheet_tetraktys hPinf A C with ⟨hEl, hAx, hDip⟩
  exact ⟨hZig, hZag, hEl, hAx, hDip, curvatureDoubleCommutator_quadratic_phi hPinf A C⟩

/-! ## 3. Hodge Boundary–Coboundary Identity and Coercivity Descent at `Limit` -/

/-- At the inductive colimit `Limit`, for any `P A : Limit` with `star P = P`, the
anticommutator of the Lie–Jordan boundary of `conePlus P A` and the coboundary of
`coneMinus P (star A)` is the lifted Jordan multiplication by the Peirce Tetraktys
scale operator `genV P A (star A)`. -/
theorem peirce_tetraktys_hodge_identity_at_limit
    {P : Limit} (hPs : star P = P) (A : Limit) :
    boundary (R := ℝ) (conePlus P A) * coboundary (R := ℝ) (coneMinus P (star A)) +
      coboundary (R := ℝ) (coneMinus P (star A)) * boundary (R := ℝ) (conePlus P A) =
        liftOp (jordanLeft (R := ℝ) (genV P A (star A))) := by
  rw [← star_conePlus hPs A, genV_eq_conePlus_hodge_coefficient hPs A]
  exact hodge_identity_at_limit (conePlus P A)

/-- Normalized trace energy of the Peirce Tetraktys quadratic coupling `genV P A (star A)`
is preserved under the stage embedding `stageEmbed n`. -/
theorem peirce_genV_normalized_energy_bond (n : ℕ) (P A x : Stage n) :
    normalizedTrace (n + 1)
      (star (stageEmbed n x) *
        (genV (stageEmbed n P) (stageEmbed n A) (star (stageEmbed n A)) * stageEmbed n x +
          stageEmbed n x * genV (stageEmbed n P) (stageEmbed n A) (star (stageEmbed n A)))) =
      normalizedTrace n
        (star x * (genV P A (star A) * x + x * genV P A (star A))) := by
  let f : Stage n →+* Stage (n + 1) := (stageEmbed n).toRingHom
  have hV : genV (stageEmbed n P) (stageEmbed n A) (star (stageEmbed n A)) =
      stageEmbed n (genV P A (star A)) := by
    rw [← stageEmbed_star n A]
    exact (map_genV f P A (star A)).symm
  rw [hV]
  exact normalized_energy_bond n (genV P A (star A)) x

/-- An assumed uniform real quadratic inequality on a cofinal stage tail `start ≤ n`
transfers to the inductive colimit `Limit`. No positivity assumption on `gamma` or
projection/self-adjointness assumption on `P` is part of this transfer theorem. -/
theorem peirce_tetraktys_uniform_quadratic_bound_descends
    (start : ℕ) (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (P A : ∀ n, Stage n) (Pinf Ainf : Limit)
    (hP : ∀ n, start ≤ n → ofStage n (P n) = Pinf)
    (hA : ∀ n, start ≤ n → ofStage n (A n) = Ainf)
    (gamma : ℝ)
    (hfinite : ∀ n, start ≤ n → ∀ x : Stage n,
      gamma * normalizedTrace n
        (star (x - P n * x * P n) * (x - P n * x * P n)) ≤
      normalizedTrace n
        (star x *
          (genV (P n) (A n) (star (A n)) * x + x * genV (P n) (A n) (star (A n)))))
    (x : Limit) :
    gamma * tau (star (x - Pinf * x * Pinf) * (x - Pinf * x * Pinf)) ≤
      tau (star x *
        (genV Pinf Ainf (star Ainf) * x + x * genV Pinf Ainf (star Ainf))) := by
  apply uniform_coercivity_descends start tau htau
    (fun n => genV (P n) (A n) (star (A n))) P (genV Pinf Ainf (star Ainf)) Pinf
  · intro n hn
    rw [map_genV (ofStage n), ofStage_star, hP n hn, hA n hn]
  · exact hP
  · exact hfinite

/-! ## 4. Bridge to `CellularSheafOperatorPoset` and `Topology.EckmannDiscreteHodge` -/

/-- For square real matrices `d₀, d₁ : Matrix (Fin m) (Fin m) ℝ`, the discrete Eckmann–Hodge
1-Laplacian `eckmannLaplacian1 d₀ d₁` coincides with `sheafHodgeLaplacian d₀ d₁`. -/
theorem eckmannLaplacian1_eq_sheafHodgeLaplacian
    {m : ℕ} (d₀ d₁ : Matrix (Fin m) (Fin m) ℝ) :
    InfoGeometry.Topology.EckmannDiscreteHodge.eckmannLaplacian1 d₀ d₁ =
      sheafHodgeLaplacian d₀ d₁ := by
  unfold InfoGeometry.Topology.EckmannDiscreteHodge.eckmannLaplacian1
    sheafHodgeLaplacian sheafHodgeDown sheafHodgeUp
  change d₁.transpose * d₁ + d₀ * d₀.transpose =
    d₀ * d₀.transpose + d₁.transpose * d₁
  exact add_comm _ _

/-- Any star-preserving ring homomorphism `f : B →+* C` intertwines `sheafCoboundary0`,
`sheafLaplacian0`, `sheafHodgeLaplacian`, and `sheafCurvature2`. -/
theorem map_cellular_sheaf_operators
    {B C : Type*} [Ring B] [StarRing B] [Ring C] [StarRing C]
    (f : B →+* C) (hf_star : ∀ x : B, f (star x) = star (f x))
    (P R_u R_v d₀ d₁ : B) :
    f (sheafCoboundary0 P R_u R_v) = sheafCoboundary0 (f P) (f R_u) (f R_v) ∧
    f (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 (f P) (f R_u) (f R_v) ∧
    f (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian (f d₀) (f d₁) ∧
    f (sheafCurvature2 d₀ d₁) = sheafCurvature2 (f d₀) (f d₁) := by
  have hCob : f (sheafCoboundary0 P R_u R_v) = sheafCoboundary0 (f P) (f R_u) (f R_v) := by
    unfold sheafCoboundary0
    simp only [map_sub, map_mul, map_one]
  refine ⟨hCob, ?_, ?_, ?_⟩
  · unfold sheafLaplacian0
    rw [map_mul, hf_star, hCob]
  · unfold sheafHodgeLaplacian sheafHodgeDown sheafHodgeUp
    simp only [map_add, map_mul, hf_star]
  · unfold sheafCurvature2
    exact map_mul f d₁ d₀

/-- The colimit canonical maps `ofStage n : Stage n →+* Limit` intertwine the cellular
sheaf operators `sheafCoboundary0`, `sheafLaplacian0`, `sheafHodgeLaplacian`, and
`sheafCurvature2`. -/
theorem ofStage_intertwines_cellular_sheaf_operators
    (n : ℕ) (P R_u R_v d₀ d₁ : Stage n) :
    ofStage n (sheafCoboundary0 P R_u R_v) =
      sheafCoboundary0 (ofStage n P) (ofStage n R_u) (ofStage n R_v) ∧
    ofStage n (sheafLaplacian0 P R_u R_v) =
      sheafLaplacian0 (ofStage n P) (ofStage n R_u) (ofStage n R_v) ∧
    ofStage n (sheafHodgeLaplacian d₀ d₁) =
      sheafHodgeLaplacian (ofStage n d₀) (ofStage n d₁) ∧
    ofStage n (sheafCurvature2 d₀ d₁) =
      sheafCurvature2 (ofStage n d₀) (ofStage n d₁) :=
  map_cellular_sheaf_operators (ofStage n) (ofStage_star n) P R_u R_v d₀ d₁

/-- **Inductive-Colimit Cellular Sheaf Dirichlet Positivity and Lie–Jordan Hodge Bridge**:
At the inductive colimit `Limit`, for any linear functional `tau : Limit →ₗ[ℝ] ℝ`
extending `normalizedTrace n`:
1. Both the single-edge and multi-edge cellular sheaf Dirichlet energies are non-negative:
   `0 ≤ tau (sheafDirichletForm P R_u R_v X)` and
   `0 ≤ tau (multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X)`;
2. Both the curved sheaf 2-cell curvature energy and squared Hodge Laplacian form are
   non-negative:
   `0 ≤ tau (sheafCurvatureEnergy d₀ d₁ X)` and `0 ≤ tau (sheafHodgeSqForm d₀ d₁ X)`;
3. For any self-adjoint idempotent `P : Limit` (`P * P = P`, `star P = P`) and `A : Limit`,
   the Lie–Jordan boundary/coboundary anticommutator equals the lifted Jordan multiplication
   by both `sheafHodgeLaplacian (conePlus P A) (conePlus P A)` and
   `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)`. -/
theorem limit_cellular_sheaf_hodge_and_dirichlet_positivity
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (a : Stage n), tau (ofStage n a) = normalizedTrace n a)
    {ι : Type*} (E : Finset ι) (P_edge R_u_edge R_v_edge : ι → Limit)
    {P : Limit} (hP : P * P = P) (hPs : star P = P)
    (R_u R_v A d₀ d₁ X : Limit) :
    0 ≤ tau (sheafDirichletForm P R_u R_v X) ∧
    0 ≤ tau (multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X) ∧
    0 ≤ tau (sheafCurvatureEnergy d₀ d₁ X) ∧
    0 ≤ tau (sheafHodgeSqForm d₀ d₁ X) ∧
    boundary (R := ℝ) (conePlus P A) * coboundary (R := ℝ) (coneMinus P (star A)) +
      coboundary (R := ℝ) (coneMinus P (star A)) * boundary (R := ℝ) (conePlus P A) =
        liftOp (jordanLeft (R := ℝ) (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) ∧
    boundary (R := ℝ) (conePlus P A) * coboundary (R := ℝ) (coneMinus P (star A)) +
      coboundary (R := ℝ) (coneMinus P (star A)) * boundary (R := ℝ) (conePlus P A) =
        liftOp (jordanLeft (R := ℝ)
          (sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A))) := by
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  have hSingle : 0 ≤ tau (sheafDirichletForm P R_u R_v X) := by
    rw [sheafDirichletForm_eq_star_coboundary_mul]
    exact hPos (sheafCoboundary0 P R_u R_v * X)
  have hMulti : 0 ≤ tau (multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X) := by
    have hDecomp :
        multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X =
          ∑ e ∈ E,
            star (sheafCoboundary0 (P_edge e) (R_u_edge e) (R_v_edge e) * X) *
              (sheafCoboundary0 (P_edge e) (R_u_edge e) (R_v_edge e) * X) := by
      unfold multiEdgeDirichletForm multiEdgeSheafLaplacian
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun e _ =>
        sheafDirichletForm_eq_star_coboundary_mul (P_edge e) (R_u_edge e) (R_v_edge e) X)
    rw [hDecomp, map_sum]
    exact Finset.sum_nonneg (fun e _ => hPos _)
  have hCurv : 0 ≤ tau (sheafCurvatureEnergy d₀ d₁ X) := by
    have hCurvSq : sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X)) := by
      simp only [sheafCurvatureEnergy, sheafCurvature2, star_mul, mul_assoc]
    rw [hCurvSq]
    exact hPos (d₁ * (d₀ * X))
  have hHodgeSq : 0 ≤ tau (sheafHodgeSqForm d₀ d₁ X) := by
    have hStarLap : star (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian d₀ d₁ := by
      unfold sheafHodgeLaplacian sheafHodgeDown sheafHodgeUp
      rw [star_add, star_mul, star_mul, star_star, star_star]
    have hSq :
        sheafHodgeSqForm d₀ d₁ X =
          star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X) := by
      unfold sheafHodgeSqForm
      rw [star_mul, hStarLap]
      noncomm_ring
    rw [hSq]
    exact hPos (sheafHodgeLaplacian d₀ d₁ * X)
  have hHodgeId := peirce_tetraktys_hodge_identity_at_limit hPs A
  have hHodgeV : sheafHodgeLaplacian (conePlus P A) (conePlus P A) = genV P A (star A) :=
    (sheafHodge_concrete_horizon_instantiation hP hPs A).2.2.2.1
  have hLap0V :
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) :=
    (sheaf_to_tetraktys_bridge hP hPs A (star A)).2.2
  exact ⟨hSingle, hMulti, hCurv, hHodgeSq,
         by rw [hHodgeV]; exact hHodgeId,
         by rw [hLap0V]; exact hHodgeId⟩

end InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
