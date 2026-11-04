/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Canonical.LieJordanHodgeColimit
import InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixColimitTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.PositroidClusterTwistPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly
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

open InfoGeometry.Core.IdempotentGraphGrassmannian
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

/-- Complementing the cut exchanges the upper and lower ordered homotope
brackets without changing the order of their inputs. -/
theorem upperHomotopeBracket_complement {B : Type*} [Ring B] (P A Y W : B) :
    upperHomotopeBracket (1 - P) A Y W = lowerCornerCrossProduct P A Y W := by
  simp [upperHomotopeBracket, lowerCornerCrossProduct, opKantorAnomaly, conePlus, coneMinus]

/-- Every tensor-tower bonding map transports the upper homotope bracket. -/
theorem bondMap_upperHomotopeBracket {n m : ℕ} (hnm : n ≤ m) (P C A Z : Stage n) :
    bondMap stageBond n m hnm (upperHomotopeBracket P C A Z) =
      upperHomotopeBracket (bondMap stageBond n m hnm P) (bondMap stageBond n m hnm C)
        (bondMap stageBond n m hnm A) (bondMap stageBond n m hnm Z) :=
  map_upperHomotopeBracket (bondMap stageBond n m hnm) P C A Z

/-- The canonical stage-to-limit homomorphism transports the upper bracket. -/
theorem ofStage_upperHomotopeBracket (n : ℕ) (P C A Z : Stage n) :
    ofStage n (upperHomotopeBracket P C A Z) =
      upperHomotopeBracket (ofStage n P) (ofStage n C) (ofStage n A) (ofStage n Z) :=
  map_upperHomotopeBracket (ofStage n) P C A Z

/-- The successor-stage bracket and its original representative agree in the
existing algebraic direct limit. -/
theorem ofStage_bond_upperHomotopeBracket (n : ℕ) (P C A Z : Stage n) :
    ofStage (n + 1) (upperHomotopeBracket (stageEmbed n P) (stageEmbed n C)
      (stageEmbed n A) (stageEmbed n Z)) = ofStage n (upperHomotopeBracket P C A Z) := by
  have h : upperHomotopeBracket (stageEmbed n P) (stageEmbed n C)
      (stageEmbed n A) (stageEmbed n Z) = stageEmbed n (upperHomotopeBracket P C A Z) :=
    (map_upperHomotopeBracket (stageEmbed n).toRingHom P C A Z).symm
  rw [h]
  exact ofStage_apply_bond n _

/-- The bracket transported to any later stage has the same direct-limit
representative as the original bracket. -/
theorem ofStage_bondMap_upperHomotopeBracket {n m : ℕ} (hnm : n ≤ m)
    (P C A Z : Stage n) :
    ofStage m (upperHomotopeBracket (bondMap stageBond n m hnm P)
      (bondMap stageBond n m hnm C) (bondMap stageBond n m hnm A)
      (bondMap stageBond n m hnm Z)) = ofStage n (upperHomotopeBracket P C A Z) := by
  rw [← bondMap_upperHomotopeBracket]
  exact directLimitOf_bondMap stageBond n m hnm _

/-- A stage idempotent induces a Jacobi-satisfying upper homotope bracket on
arbitrary elements of the existing algebraic direct limit. -/
theorem limit_upperHomotopeBracket_jacobi_from_stage
    (n : ℕ) {P : Stage n} (hP : P * P = P) (C A Z W : Limit) :
    upperHomotopeBracket (ofStage n P) C A
        (upperHomotopeBracket (ofStage n P) C Z W) +
      upperHomotopeBracket (ofStage n P) C Z
        (upperHomotopeBracket (ofStage n P) C W A) +
      upperHomotopeBracket (ofStage n P) C W
        (upperHomotopeBracket (ofStage n P) C A Z) = 0 := by
  exact upper_homotope_jacobi (map_idempotent (ofStage n) hP) C A Z W

/-- The lower-corner ordered triple is natural under every tensor-tower bond. -/
theorem bondMap_lowerCornerCrossProduct {n m : ℕ} (hnm : n ≤ m) (P A Y W : Stage n) :
    bondMap stageBond n m hnm (lowerCornerCrossProduct P A Y W) =
      lowerCornerCrossProduct (bondMap stageBond n m hnm P) (bondMap stageBond n m hnm A)
        (bondMap stageBond n m hnm Y) (bondMap stageBond n m hnm W) := by
  simp only [lowerCornerCrossProduct, map_sub, map_mul, map_coneMinus, map_conePlus]

/-- The transported lower-corner triple has the same direct-limit
representative at every later stage. -/
theorem ofStage_bondMap_lowerCornerCrossProduct {n m : ℕ} (hnm : n ≤ m)
    (P A Y W : Stage n) :
    ofStage m (lowerCornerCrossProduct (bondMap stageBond n m hnm P)
      (bondMap stageBond n m hnm A) (bondMap stageBond n m hnm Y)
      (bondMap stageBond n m hnm W)) = ofStage n (lowerCornerCrossProduct P A Y W) := by
  rw [← bondMap_lowerCornerCrossProduct]
  exact directLimitOf_bondMap stageBond n m hnm _

/-- A stage idempotent induces the lower-corner Jacobi identity on arbitrary
elements of the existing algebraic direct limit. -/
theorem limit_lowerCornerCrossProduct_jacobi_from_stage
    (n : ℕ) {P : Stage n} (hP : P * P = P) (A Y W U : Limit) :
    lowerCornerCrossProduct (ofStage n P) A Y
        (lowerCornerCrossProduct (ofStage n P) A W U) +
      lowerCornerCrossProduct (ofStage n P) A W
        (lowerCornerCrossProduct (ofStage n P) A U Y) +
      lowerCornerCrossProduct (ofStage n P) A U
        (lowerCornerCrossProduct (ofStage n P) A Y W) = 0 := by
  exact lower_corner_cross_product_jacobi (map_idempotent (ofStage n) hP) A Y W U

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

/-- The concrete block-doubling transition preserves nonvanishing of the
two-sheeted quadratic coupling.  This is stagewise algebraic persistence in
the matrix tower; it makes no claim about a numerical spectral gap. -/
theorem stageEmbed_preserves_nonzero_two_sheeted_quadratic_coupling
    (n : ℕ) (P A C : Stage n)
    (hV : opQuadraticCoupling P A C ≠ 0) :
    opQuadraticCoupling (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) ≠ 0 := by
  intro hzero
  apply hV
  apply (stageEmbed n).injective
  calc stageEmbed n (opQuadraticCoupling P A C)
      = opQuadraticCoupling (stageEmbed n P) (stageEmbed n A) (stageEmbed n C) :=
          (stageEmbed_intertwines_two_sheeted_tetraktys n P A C 0).2.2.2.2.2.1
    _ = 0 := hzero
    _ = stageEmbed n 0 := by simp

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

/-- The canonical map into the actual Cl(1,1) algebraic direct limit preserves
nonvanishing of the two-sheeted quadratic coupling. This uses injectivity of
the matrix block-doubling bonds and the established colimit intertwining law. -/
theorem ofStage_preserves_nonzero_two_sheeted_quadratic_coupling
    (n : ℕ) (P A C : Stage n)
    (hV : opQuadraticCoupling P A C ≠ 0) :
    opQuadraticCoupling (ofStage n P) (ofStage n A) (ofStage n C) ≠ 0 := by
  intro hzero
  apply hV
  apply directLimitOf_injective stageBond (fun k => matStageEmbed_injective k) n
  calc ofStage n (opQuadraticCoupling P A C)
      = opQuadraticCoupling (ofStage n P) (ofStage n A) (ofStage n C) :=
          (ofStage_intertwines_two_sheeted_tetraktys n P A C 0).2.2.2.2.2.1
    _ = 0 := hzero
    _ = ofStage n 0 := by simp

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
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hPinf A C
  have hZig := hA3.1
  have hZag := hA3.2.1
  have hPhi := hA3.2.2.1
  have hJ := hA3.2.2.2.1
  have hDip := hA3.2.2.2.2.2.1
  have hEl : opElectron (ofStage n P) A C * opElectron (ofStage n P) A C =
      opQuadraticCoupling (ofStage n P) A C := hPhi
  have hAx : opAxial (ofStage n P) A C * opAxial (ofStage n P) A C =
      -opQuadraticCoupling (ofStage n P) A C := hJ
  have hDip' : opAxial (ofStage n P) A C * opElectron (ofStage n P) A C =
      opSpinDipole (ofStage n P) A C := hDip
  exact ⟨hZig, hZag, hEl, hAx, hDip', curvatureDoubleCommutator_quadratic_phi hPinf A C⟩

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

/-! ## 3a. A uniform finite bound from an operator-valued unit horizon mass -/

/-- Compression by an orthogonal projection is contractive for the real
Hilbert–Schmidt energy. The proof uses cyclicity of matrix trace and positivity
of `star c * c`; it does not diagonalize either operator. -/
theorem normalizedTrace_offcorner_energy_le
    (n : ℕ) (P x : Stage n) (hP : P * P = P) (hPs : star P = P) :
    normalizedTrace n
        (star (x - P * x * P) * (x - P * x * P)) ≤
      normalizedTrace n (star x * x) := by
  let c : Stage n := P * x * P
  have hAbsorb (y : Stage n) : P * (P * y) = P * y := by
    rw [← mul_assoc, hP]
  have hcycle : Matrix.trace (star x * c) = Matrix.trace (star c * x) := by
    calc
      Matrix.trace (star x * c) = star (Matrix.trace (star x * c)) := by simp
      _ = Matrix.trace (star (star x * c)) :=
        (Matrix.trace_conjTranspose (star x * c)).symm
      _ = Matrix.trace (star c * x) := by simp
  have hcross : Matrix.trace (star c * x) = Matrix.trace (star c * c) := by
    have hcyc := Matrix.trace_mul_comm (P * star x * P * x) P
    have hcyc' : Matrix.trace ((P * star x * P * x) * P) =
        Matrix.trace (P * (P * star x * P * x)) := hcyc
    dsimp [c]
    have hleft : (P * star x * P * x) * P =
        star (P * x * P) * (P * x * P) := by
      rw [star_mul, star_mul, hPs]
      simp only [mul_assoc]
      exact congrArg (fun y => P * (star x * y)) (hAbsorb (x * P)).symm
    have hright : P * (P * star x * P * x) = star (P * x * P) * x := by
      rw [star_mul, star_mul, hPs]
      simp only [mul_assoc]
      exact hAbsorb (star x * (P * x))
    rw [hleft, hright] at hcyc'
    -- Cyclically moving the final projection identifies this with the
    -- compressed Gram trace.
    exact hcyc'.symm
  have henergy : Matrix.trace
      (star (x - c) * (x - c)) =
        Matrix.trace (star x * x) - Matrix.trace (star c * c) := by
    simp only [star_sub, sub_mul, mul_sub, Matrix.trace_sub]
    rw [hcycle, hcross]
    ring
  have hpos : 0 ≤ Matrix.trace (star c * c) := by
    have hgram := Matrix.posSemidef_conjTranspose_mul_self c
    exact hgram.trace_nonneg
  have htrace := sub_le_self (Matrix.trace (star x * x)) hpos
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  unfold normalizedTrace
  dsimp [c] at henergy
  rw [henergy]
  exact (div_le_div_of_nonneg_right htrace (le_of_lt hden))

/-- If the Peirce horizon mass is the identity operator at a finite stage,
the two-sided Jordan energy is exactly twice the normalized Hilbert–Schmidt
energy. Together with compression contractivity this gives the common
coercivity constant `2` on every Peirce off-corner. -/
theorem unit_horizon_mass_stage_coercivity
    (n : ℕ) (P A x : Stage n) (hP : P * P = P) (hPs : star P = P)
    (hV : genV P A (star A) = 1) :
    (2 : ℝ) * normalizedTrace n
        (star (x - P * x * P) * (x - P * x * P)) ≤
      normalizedTrace n
        (star x * (genV P A (star A) * x + x * genV P A (star A))) := by
  rw [hV]
  have hcontract := normalizedTrace_offcorner_energy_le n P x hP hPs
  have henergy : normalizedTrace n
      (star x * (1 * x + x * 1)) =
        (2 : ℝ) * normalizedTrace n (star x * x) := by
    simp only [one_mul, mul_one, mul_add]
    unfold normalizedTrace
    rw [Matrix.trace_add]
    ring
  rw [henergy]
  exact mul_le_mul_of_nonneg_left hcontract (by norm_num : (0 : ℝ) ≤ 2)

/-- An operator-valued unit horizon mass supplies the uniform finite-stage
inequality needed by the existing Peirce–Hodge colimit descent. The assumptions
state the actual stage projections and the unit-mass identity on a cofinal
tail; the result then invokes the repository's direct-limit induction theorem. -/
theorem peirce_tetraktys_unit_horizon_coercivity_descends
    (start : ℕ) (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (P A : ∀ n, Stage n) (Pinf Ainf : Limit)
    (hP : ∀ n, start ≤ n → ofStage n (P n) = Pinf)
    (hA : ∀ n, start ≤ n → ofStage n (A n) = Ainf)
    (hPid : ∀ n, start ≤ n → P n * P n = P n)
    (hPstar : ∀ n, start ≤ n → star (P n) = P n)
    (hV : ∀ n, start ≤ n → genV (P n) (A n) (star (A n)) = 1)
    (x : Limit) :
    (2 : ℝ) * tau (star (x - Pinf * x * Pinf) * (x - Pinf * x * Pinf)) ≤
      tau (star x *
        (genV Pinf Ainf (star Ainf) * x + x * genV Pinf Ainf (star Ainf))) := by
  apply peirce_tetraktys_uniform_quadratic_bound_descends start tau htau P A Pinf Ainf
    hP hA 2
  · intro n hn y
    exact unit_horizon_mass_stage_coercivity n (P n) (A n) y
      (hPid n hn) (hPstar n hn) (hV n hn)

/-! ## 3b. Seed-generated mass family and its colimit coercivity -/

/-- Transport a finite-stage operator to every later matrix stage. Before `start`,
the family is set to zero; all statements about it are restricted to the cofinal
tail where the bonding map is defined. -/
noncomputable def seedBondFamily (start : ℕ) (x : Stage start) : (n : ℕ) → Stage n :=
  fun n => if hn : start ≤ n then bondMap stageBond start n hn x else 0

/-- On its cofinal domain, `seedBondFamily` is exactly the iterated stage map. -/
theorem seedBondFamily_ofStage (start n : ℕ) (x : Stage start) (hn : start ≤ n) :
    seedBondFamily start x n = bondMap stageBond start n hn x := by
  simp [seedBondFamily, hn]

/-- A finite self-adjoint idempotent seed generates self-adjoint idempotents at
every later stage, and all of them represent the same colimit element. -/
theorem seedBondFamily_projection_coherence
    (start : ℕ) (P₀ : Stage start) (hP₀ : P₀ * P₀ = P₀)
    (hP₀star : star P₀ = P₀) :
    (∀ n, start ≤ n → seedBondFamily start P₀ n * seedBondFamily start P₀ n =
      seedBondFamily start P₀ n) ∧
    (∀ n, start ≤ n → star (seedBondFamily start P₀ n) = seedBondFamily start P₀ n) ∧
    (∀ n, start ≤ n → ofStage n (seedBondFamily start P₀ n) = ofStage start P₀) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [seedBondFamily_ofStage start n P₀ hn]
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.map_idempotent
      (bondMap stageBond start n hn) hP₀
  · intro n hn
    rw [seedBondFamily_ofStage start n P₀ hn]
    calc
      star (bondMap stageBond start n hn P₀) =
          bondMap stageBond start n hn (star P₀) :=
        (bondMap_star start n hn P₀).symm
      _ = bondMap stageBond start n hn P₀ := by rw [hP₀star]
  · intro n hn
    rw [seedBondFamily_ofStage start n P₀ hn]
    exact directLimitOf_bondMap stageBond start n hn P₀

/-- A unit-horizon seed determines, rather than assumes, the cofinal hypotheses
of the finite-to-colimit coercivity theorem. Thus the common constant `2` is
derived from one finite self-adjoint Peirce seed and the star-preserving bonding
maps. -/
theorem seed_unit_horizon_mass_coercivity_descends
    (start : ℕ) (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (P₀ A₀ : Stage start) (hP₀ : P₀ * P₀ = P₀)
    (hP₀star : star P₀ = P₀)
    (hV₀ : genV P₀ A₀ (star A₀) = 1) (x : Limit) :
    (2 : ℝ) * tau
        (star (x - ofStage start P₀ * x * ofStage start P₀) *
          (x - ofStage start P₀ * x * ofStage start P₀)) ≤
      tau (star x *
        (genV (ofStage start P₀) (ofStage start A₀)
          (star (ofStage start A₀)) * x +
          x * genV (ofStage start P₀) (ofStage start A₀)
            (star (ofStage start A₀)))) := by
  let Pseq := seedBondFamily start P₀
  let Aseq := seedBondFamily start A₀
  have hPcoh := seedBondFamily_projection_coherence start P₀ hP₀ hP₀star
  have hP : ∀ n, start ≤ n → ofStage n (Pseq n) = ofStage start P₀ := by
    intro n hn
    exact hPcoh.2.2 n hn
  have hA : ∀ n, start ≤ n → ofStage n (Aseq n) = ofStage start A₀ := by
    intro n hn
    dsimp [Aseq]
    rw [seedBondFamily_ofStage start n A₀ hn]
    exact directLimitOf_bondMap stageBond start n hn A₀
  have hPid : ∀ n, start ≤ n → Pseq n * Pseq n = Pseq n := by
    intro n hn
    exact hPcoh.1 n hn
  have hPstar : ∀ n, start ≤ n → star (Pseq n) = Pseq n := by
    intro n hn
    exact hPcoh.2.1 n hn
  have hV : ∀ n, start ≤ n → genV (Pseq n) (Aseq n) (star (Aseq n)) = 1 := by
    intro n hn
    dsimp [Pseq, Aseq]
    rw [seedBondFamily_ofStage start n P₀ hn,
      seedBondFamily_ofStage start n A₀ hn]
    let f := bondMap stageBond start n hn
    have hStar : f (star A₀) = star (f A₀) := bondMap_star start n hn A₀
    calc
      genV (f P₀) (f A₀) (star (f A₀)) =
          genV (f P₀) (f A₀) (f (star A₀)) := by rw [← hStar]
      _ = f (genV P₀ A₀ (star A₀)) := by
        symm
        exact InfoGeometry.OperatorAlgebra.PeirceSpine.map_genV f P₀ A₀ (star A₀)
      _ = 1 := by rw [hV₀, map_one]
  exact peirce_tetraktys_unit_horizon_coercivity_descends start tau htau
    Pseq Aseq (ofStage start P₀) (ofStage start A₀) hP hA hPid hPstar hV x

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

/-- The colimit canonical maps `ofStage n : Stage n →+* Limit` intertwine the Stage `D₂₂`
Hodge complement `sheafHodgeComplement`, degree-2 Green polynomial `sheafGreenPolynomial2`,
and directed simplicial edge operator `simplicialEdge`. -/
theorem ofStage_intertwines_D22_hodge_complement_and_simplicial_sheaf
    (n : ℕ) (P_i P_j A d₀ d₁ : Stage n) :
    ofStage n (sheafHodgeComplement d₀ d₁) =
      sheafHodgeComplement (ofStage n d₀) (ofStage n d₁) ∧
    ofStage n (sheafGreenPolynomial2 d₀ d₁) =
      sheafGreenPolynomial2 (ofStage n d₀) (ofStage n d₁) ∧
    ofStage n (simplicialEdge P_i P_j A) =
      simplicialEdge (ofStage n P_i) (ofStage n P_j) (ofStage n A) := by
  have hLap : ofStage n (sheafHodgeLaplacian d₀ d₁) =
      sheafHodgeLaplacian (ofStage n d₀) (ofStage n d₁) :=
    (ofStage_intertwines_cellular_sheaf_operators n P_i A A d₀ d₁).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · unfold sheafHodgeComplement
    rw [map_sub, map_one, hLap]
  · unfold sheafGreenPolynomial2
    rw [map_add, map_add, map_one, map_mul, hLap]
  · unfold simplicialEdge
    rw [map_mul, map_mul]

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

/-- Any ring homomorphism `f : B →+* C` intertwines `mandelbrotTower k` at every depth `k : ℕ`. -/
theorem map_mandelbrotTower {B C : Type*} [Ring B] [Ring C]
    (f : B →+* C) (k : ℕ) (X : B) :
    f (mandelbrotTower k X) = mandelbrotTower k (f X) := by
  induction k with
  | zero =>
    unfold mandelbrotTower InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
    simp only [map_sub, map_mul]
  | succ k ih =>
    change f (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (mandelbrotTower k X)) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (mandelbrotTower k (f X))
    unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
    rw [map_sub, map_mul, ih]

/-- Any star-preserving ring homomorphism `f : B →+* C` intertwines the Stage `D₂₂`
operators `sheafWeitzenboeckDefect`, `sheafHodgeComplement`, `sheafGreenPolynomial2`,
`fractalHodgeComplement`, `simplicialEdge`, and `simplicialCycleOp`. -/
theorem map_stage_D22_sheaf_and_simplicial_operators
    {B C : Type*} [Ring B] [StarRing B] [Ring C] [StarRing C]
    (f : B →+* C) (hf_star : ∀ x : B, f (star x) = star (f x))
    (k : ℕ) (P A D d₀ d₁ P₁ P₂ P₃ A₁₂ A₂₃ A₃₁ : B) :
    f (sheafWeitzenboeckDefect d₀ d₁) = sheafWeitzenboeckDefect (f d₀) (f d₁) ∧
    f (sheafHodgeComplement d₀ d₁) = sheafHodgeComplement (f d₀) (f d₁) ∧
    f (sheafGreenPolynomial2 d₀ d₁) = sheafGreenPolynomial2 (f d₀) (f d₁) ∧
    f (fractalHodgeComplement k P A D) = fractalHodgeComplement k (f P) (f A) (f D) ∧
    f (simplicialEdge P₁ P₂ A₁₂) = simplicialEdge (f P₁) (f P₂) (f A₁₂) ∧
    f (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) =
      simplicialCycleOp (f P₁) (f P₂) (f P₃) (f A₁₂) (f A₂₃) (f A₃₁) := by
  have hHodge := (map_cellular_sheaf_operators f hf_star P A D d₀ d₁).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sheafWeitzenboeckDefect sheafCurvature2
    simp only [map_add, map_mul, hf_star]
  · unfold sheafHodgeComplement
    rw [map_sub, map_one, hHodge]
  · unfold sheafGreenPolynomial2
    rw [map_add, map_add, map_one, map_mul, hHodge]
  · unfold fractalHodgeComplement
    rw [map_sub, map_one, map_add, map_mandelbrotTower, map_mandelbrotTower,
        map_qgtPlus, map_qgtMinus]
  · unfold simplicialEdge
    simp only [map_mul]
  · unfold simplicialCycleOp simplicialEdge
    simp only [map_add, map_mul]

/-- Both `stageEmbed n : Stage n →ₐ[ℝ] Stage (n + 1)` and `ofStage n : Stage n →+* Limit`
intertwine the Stage `D₂₂` operators `sheafWeitzenboeckDefect`, `sheafHodgeComplement`,
`sheafGreenPolynomial2`, `fractalHodgeComplement`, `simplicialEdge`, and `simplicialCycleOp`,
with exact stage-bonding coherence in `Limit`. -/
theorem stageEmbed_and_ofStage_intertwine_stage_D22_operators
    (n k : ℕ) (P A D d₀ d₁ P₁ P₂ P₃ A₁₂ A₂₃ A₃₁ : Stage n) :
    (ofStage n (sheafWeitzenboeckDefect d₀ d₁) =
       sheafWeitzenboeckDefect (ofStage n d₀) (ofStage n d₁) ∧
     ofStage n (sheafHodgeComplement d₀ d₁) =
       sheafHodgeComplement (ofStage n d₀) (ofStage n d₁) ∧
     ofStage n (sheafGreenPolynomial2 d₀ d₁) =
       sheafGreenPolynomial2 (ofStage n d₀) (ofStage n d₁) ∧
     ofStage n (fractalHodgeComplement k P A D) =
       fractalHodgeComplement k (ofStage n P) (ofStage n A) (ofStage n D) ∧
     ofStage n (simplicialEdge P₁ P₂ A₁₂) =
       simplicialEdge (ofStage n P₁) (ofStage n P₂) (ofStage n A₁₂) ∧
     ofStage n (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) =
       simplicialCycleOp (ofStage n P₁) (ofStage n P₂) (ofStage n P₃)
         (ofStage n A₁₂) (ofStage n A₂₃) (ofStage n A₃₁)) ∧
    ofStage (n + 1) (sheafHodgeComplement (stageEmbed n d₀) (stageEmbed n d₁)) =
      ofStage n (sheafHodgeComplement d₀ d₁) ∧
    ofStage (n + 1)
        (fractalHodgeComplement k (stageEmbed n P) (stageEmbed n A) (stageEmbed n D)) =
      ofStage n (fractalHodgeComplement k P A D) := by
  let f : Stage n →+* Stage (n + 1) := (stageEmbed n).toRingHom
  rcases map_stage_D22_sheaf_and_simplicial_operators f (stageEmbed_star n)
    k P A D d₀ d₁ P₁ P₂ P₃ A₁₂ A₂₃ A₃₁ with ⟨_, hCompEmb, _, hFracEmb, _, _⟩
  refine ⟨map_stage_D22_sheaf_and_simplicial_operators (ofStage n) (ofStage_star n)
            k P A D d₀ d₁ P₁ P₂ P₃ A₁₂ A₂₃ A₃₁, ?_, ?_⟩
  · change ofStage (n + 1) (sheafHodgeComplement (f d₀) (f d₁)) =
      ofStage n (sheafHodgeComplement d₀ d₁)
    rw [← hCompEmb]
    exact ofStage_apply_bond n _
  · change ofStage (n + 1) (fractalHodgeComplement k (f P) (f A) (f D)) =
      ofStage n (fractalHodgeComplement k P A D)
    rw [← hFracEmb]
    exact ofStage_apply_bond n _

/-! ## 5. Colimit Intertwining and Trace Positivity of `peirceBdGHamiltonian` -/

section ColimitPeirceBdGAndPositivity

open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge

/-- Both `stageEmbed n : Stage n →ₐ[ℝ] Stage (n + 1)` and `ofStage n : Stage n →+* Limit`
intertwine the massive Peirce–BdG operator `peirceBdGHamiltonian`, with exact stage-bonding
coherence in `Limit`. -/
theorem stageEmbed_and_ofStage_intertwine_peirceBdGHamiltonian
    (n : ℕ) (P D A C : Stage n) :
    stageEmbed n (peirceBdGHamiltonian P D A C) =
      peirceBdGHamiltonian (stageEmbed n P) (stageEmbed n D) (stageEmbed n A) (stageEmbed n C) ∧
    ofStage n (peirceBdGHamiltonian P D A C) =
      peirceBdGHamiltonian (ofStage n P) (ofStage n D) (ofStage n A) (ofStage n C) ∧
    ofStage (n + 1)
        (peirceBdGHamiltonian (stageEmbed n P) (stageEmbed n D) (stageEmbed n A) (stageEmbed n C)) =
      ofStage n (peirceBdGHamiltonian P D A C) := by
  let f : Stage n →+* Stage (n + 1) := (stageEmbed n).toRingHom
  have hEmb : f (peirceBdGHamiltonian P D A C) =
      peirceBdGHamiltonian (f P) (f D) (f A) (f C) :=
    (map_peirceBdGHamiltonian f P D A C).2.2
  refine ⟨hEmb, (map_peirceBdGHamiltonian (ofStage n) P D A C).2.2, ?_⟩
  change ofStage (n + 1) (peirceBdGHamiltonian (f P) (f D) (f A) (f C)) =
    ofStage n (peirceBdGHamiltonian P D A C)
  rw [← hEmb]
  exact ofStage_apply_bond n _

/-- **Inductive-Colimit Peirce–BdG Non-Commutative Square and Trace Positivity**:
At the inductive colimit `Limit`, for any `P D A X : Limit` with `P * P = P`, `star P = P`,
`star D = D`:
1. The general non-commutative square of `peirceBdGHamiltonian P D A (star A)` is
   `evenGrade P D * evenGrade P D + genV P A (star A) + comm (evenGrade P D) (genJ P A (star A))`;
2. `peirceBdGHamiltonian P D A (star A)` is self-adjoint (`star (...) = ...`);
3. Whenever `comm (evenGrade P D) (genJ P A (star A)) = 0` and `tau : Limit →ₗ[ℝ] ℝ`
   extends `normalizedTrace n`, the Peirce–BdG quadratic form decomposes as the sum of the
   kinetic and pairing Gram forms and is non-negative:
   `0 ≤ tau (star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X)`. -/
theorem limit_peirceBdGHamiltonian_noncomm_sq_and_trace_positivity
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (a : Stage n), tau (ofStage n a) = normalizedTrace n a)
    {P D : Limit} (hP : P * P = P) (hPs : star P = P) (hDs : star D = D)
    (A X : Limit)
    (hComm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm (evenGrade P D) (genJ P A (star A)) = 0) :
    let H_BdG := peirceBdGHamiltonian P D A (star A)
    H_BdG * H_BdG =
      evenGrade P D * evenGrade P D + genV P A (star A) +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (evenGrade P D) (genJ P A (star A)) ∧
    star H_BdG = H_BdG ∧
    tau (star X * (H_BdG * H_BdG) * X) =
      tau (star (evenGrade P D * X) * (evenGrade P D * X)) +
        tau (star X * genV P A (star A) * X) ∧
    0 ≤ tau (star X * (H_BdG * H_BdG) * X) := by
  dsimp only
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  rcases peirceBdGHamiltonian_selfAdjoint_and_quadratic_form hP hPs hDs A X hComm with
    ⟨_, hStarBdG, hGramV, hQuad⟩
  have hTauQuad :
      tau (star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X) =
        tau (star (evenGrade P D * X) * (evenGrade P D * X)) +
          tau (star X * genV P A (star A) * X) := by
    rw [hQuad, map_add]
  have hNonneg :
      0 ≤ tau (star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X) := by
    rw [hQuad, hGramV, map_add, map_add]
    exact add_nonneg (hPos (evenGrade P D * X))
      (add_nonneg (hPos (coneMinus P (star A) * X)) (hPos (conePlus P A * X)))
  exact ⟨peirceBdGHamiltonian_sq hP D A (star A), hStarBdG, hTauQuad, hNonneg⟩

/-- **Normalized Stage Surprisal (`-2⁻ⁿ log |det A|`)**:
At finite matrix tower stage `Stage n = MatStage n` (size `2ⁿ × 2ⁿ`), the normalized
surprisal (free-energy / log-partition density) is `-normalizedLogAbsDet n A`. -/
noncomputable def normalizedSurprisal (n : ℕ) (A : Stage n) : ℝ :=
  -normalizedLogAbsDet n A

/-- **Finite-Stage Additive vs. Multiplicative Induction Law across the Tensor Tower**:
1. **Multiplicative Determinant Law**: Products multiply determinants (`(A * B).det = A.det * B.det`),
   while tensor-tower stage bonding `stageEmbed n A = A ⊗ₖ 1` squares the determinant:
   `(stageEmbed n A).det = A.det ^ 2`;
2. **Additive Trace / Energy / Surprisal Law**: For nonsingular `A, B : Stage n`,
   `normalizedSurprisal n (A * B) = normalizedSurprisal n A + normalizedSurprisal n B`,
   raw trace and log-determinant double under `stageEmbed n` (`+ + → 2 *`), and both
   `normalizedTrace` and `normalizedSurprisal` are strictly invariant under `stageEmbed n`. -/
theorem normalizedSurprisal_mul_add_and_stageEmbed_invariant
    (n : ℕ) (A B : Stage n) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B).det = A.det * B.det ∧
    (stageEmbed n A).det = A.det ^ 2 ∧
    Matrix.trace (stageEmbed n (A + B)) =
      2 * Matrix.trace A + 2 * Matrix.trace B ∧
    Real.log |(stageEmbed n A).det| = 2 * Real.log |A.det| ∧
    normalizedTrace (n + 1) (stageEmbed n A) = normalizedTrace n A ∧
    normalizedSurprisal n (A * B) = normalizedSurprisal n A + normalizedSurprisal n B ∧
    normalizedSurprisal (n + 1) (stageEmbed n A) = normalizedSurprisal n A := by
  refine ⟨Matrix.det_mul A B, matStageEmbed_det n A, ?_,
    matStageEmbed_logAbsDet_double n A,
    normalizedTrace_matStageEmbed n A, ?_, ?_⟩
  · rw [map_add, Matrix.trace_add]
    have hTrA : Matrix.trace (stageEmbed n A) = 2 * Matrix.trace A :=
      matStageEmbed_trace n A
    have hTrB : Matrix.trace (stageEmbed n B) = 2 * Matrix.trace B :=
      matStageEmbed_trace n B
    rw [hTrA, hTrB]
  · unfold normalizedSurprisal normalizedLogAbsDet
      InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet
    rw [Matrix.det_mul, abs_mul, Real.log_mul (abs_ne_zero.mpr hA) (abs_ne_zero.mpr hB)]
    ring
  · unfold normalizedSurprisal
    have hLog : normalizedLogAbsDet (n + 1) (stageEmbed n A) = normalizedLogAbsDet n A :=
      normalizedLogAbsDet_matStageEmbed n A
    rw [hLog]

/-- **Multi-Step Inductive Invariance of `normalizedTrace` and `normalizedSurprisal`**:
By induction along `n ≤ m` in the tensor tower
`bondMap stageBond n m hnm : Stage n →+* Stage m`,
both the normalized trace energy `normalizedTrace` and normalized surprisal
`normalizedSurprisal` are preserved at every finite stage `m ≥ n`, while the determinant
satisfies `(bondMap stageBond n m hnm A).det ≠ 0` whenever `A.det ≠ 0`. -/
theorem bondMap_normalizedTrace_and_normalizedSurprisal_invariant
    {n m : ℕ} (hnm : n ≤ m) (A : Stage n) (hA : A.det ≠ 0) :
    let bMap := bondMap stageBond n m hnm
    normalizedTrace m (bMap A) = normalizedTrace n A ∧
    (bMap A).det ≠ 0 ∧
    normalizedSurprisal m (bMap A) = normalizedSurprisal n A := by
  dsimp only
  refine Nat.le_induction
    (m := n)
    (P := fun m hnm =>
      normalizedTrace m (bondMap stageBond n m hnm A) = normalizedTrace n A ∧
      (bondMap stageBond n m hnm A).det ≠ 0 ∧
      normalizedSurprisal m (bondMap stageBond n m hnm A) = normalizedSurprisal n A)
    ?base ?succ m hnm
  · simp [bondMap_refl, hA]
  · intro k hnk ih
    rcases ih with ⟨hTr, hDet, hSurp⟩
    rw [bondMap_succ stageBond n k hnk]
    let bMapK := bondMap stageBond n k hnk
    change normalizedTrace (k + 1) (stageEmbed k (bMapK A)) = normalizedTrace n A ∧
      (stageEmbed k (bMapK A)).det ≠ 0 ∧
      normalizedSurprisal (k + 1) (stageEmbed k (bMapK A)) = normalizedSurprisal n A
    refine ⟨?_, ?_, ?_⟩
    · have hTrK : normalizedTrace (k + 1) (stageEmbed k (bMapK A)) =
          normalizedTrace k (bMapK A) :=
        normalizedTrace_matStageEmbed k (bMapK A)
      rw [hTrK, hTr]
    · have hDetK : (stageEmbed k (bMapK A)).det = (bMapK A).det ^ 2 :=
        matStageEmbed_det k (bMapK A)
      rw [hDetK]
      exact pow_ne_zero 2 hDet
    · unfold normalizedSurprisal
      have hLogK : normalizedLogAbsDet (k + 1) (stageEmbed k (bMapK A)) =
          normalizedLogAbsDet k (bMapK A) :=
        normalizedLogAbsDet_matStageEmbed k (bMapK A)
      rw [hLogK]
      exact hSurp

/-! ## 4b. Additivity of finite-channel Peirce mass energy in the colimit trace -/

/-- Orthogonal Peirce channels have additive Jordan mass, and therefore additive
finite normalized mass energy. The same identity is preserved by any linear
trace extension `tau` to the inductive colimit. The hypotheses eliminate only
the four cross-channel products; the within-channel operator products remain
noncommutative. -/
theorem orthogonal_channel_mass_energy_additive_in_colimit
    (n : ℕ) (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (P A₁ C₁ A₂ C₂ X : Stage n)
    (h₁₂ : conePlus P A₁ * coneMinus P C₂ = 0)
    (h₂₁ : conePlus P A₂ * coneMinus P C₁ = 0)
    (h₁₂' : coneMinus P C₁ * conePlus P A₂ = 0)
    (h₂₁' : coneMinus P C₂ * conePlus P A₁ = 0) :
    normalizedTrace n
        (star X *
          (genV P (A₁ + A₂) (C₁ + C₂) * X +
            X * genV P (A₁ + A₂) (C₁ + C₂))) =
      normalizedTrace n
          (star X * (genV P A₁ C₁ * X + X * genV P A₁ C₁)) +
        normalizedTrace n
          (star X * (genV P A₂ C₂ * X + X * genV P A₂ C₂)) ∧
    tau (ofStage n
        (star X *
          (genV P (A₁ + A₂) (C₁ + C₂) * X +
            X * genV P (A₁ + A₂) (C₁ + C₂))) : Limit) =
      tau (ofStage n (star X * (genV P A₁ C₁ * X + X * genV P A₁ C₁))) +
        tau (ofStage n (star X * (genV P A₂ C₂ * X + X * genV P A₂ C₂))) := by
  have hMass : genV P (A₁ + A₂) (C₁ + C₂) = genV P A₁ C₁ + genV P A₂ C₂ :=
    (InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge.two_channel_Peirce_additivity_of_cross_products_zero
      P A₁ C₁ A₂ C₂ h₁₂ h₂₁ h₁₂' h₂₁').2.1
  let massEnergy12 : Stage n := star X *
    (genV P (A₁ + A₂) (C₁ + C₂) * X + X * genV P (A₁ + A₂) (C₁ + C₂))
  let massEnergy1 : Stage n := star X * (genV P A₁ C₁ * X + X * genV P A₁ C₁)
  let massEnergy2 : Stage n := star X * (genV P A₂ C₂ * X + X * genV P A₂ C₂)
  have hEnergy :
      massEnergy12 = massEnergy1 + massEnergy2 := by
    dsimp [massEnergy12, massEnergy1, massEnergy2]
    rw [hMass]
    noncomm_ring
  have hTraceAdd :
      normalizedTrace n massEnergy12 =
        normalizedTrace n massEnergy1 + normalizedTrace n massEnergy2 := by
    rw [hEnergy]
    unfold normalizedTrace
    rw [Matrix.trace_add]
    ring
  refine ⟨hTraceAdd, ?_⟩
  change tau (ofStage n massEnergy12) =
    tau (ofStage n massEnergy1) + tau (ofStage n massEnergy2)
  calc
    tau (ofStage n massEnergy12) = normalizedTrace n massEnergy12 := htau n massEnergy12
    _ = normalizedTrace n massEnergy1 + normalizedTrace n massEnergy2 := hTraceAdd
    _ = tau (ofStage n massEnergy1) + tau (ofStage n massEnergy2) := by
      rw [← htau n massEnergy1, ← htau n massEnergy2]

/-- **Fock Spinor Principal Left Ideal at the Real Bott Periodicity Boundary (`n = 5`, `32 = 2⁵`)**:
In the split Clifford algebra `Cl(5, 5)` (where the real Bott periodicity shift `Δn = 8`
corresponds to matrix dimension `2^(8/2) = 16` and the first post-Bott stage `n = 8 / 2 + 1 = 5`
has spinor dimension `2⁵ = 32`):
1. `cl55VacuumIdempotent` is a genuine idempotent in `Cl(5, 5)` (`ω * ω = ω`);
2. The spinor space realized as the principal left ideal `cl55VacuumIdeal` inside the Clifford
   algebra has exact real dimension `Module.finrank ℝ cl55VacuumIdeal = 32 = 2 ^ 5`;
3. Left Clifford multiplication on the spinor ideal `cl55VacuumIdeal` is intertwined
   via `cl55VacuumIdealSpinorEquiv` with the neutral exterior spinor representation. -/
theorem cl55_spinor_ideal_and_bott_32d_boundary
    (a : InfoGeometry.Clifford.Clifford55.Cl55)
    (v : InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdeal) :
    2 ^ (8 / 2 + 1) = 32 ∧
    InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent *
      InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent =
      InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent ∧
    Module.finrank ℝ InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdeal = 32 ∧
    InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv
        (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction a v) =
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.neutralCliffordRep
        (InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm a)
        (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv v) :=
  ⟨by norm_num,
   InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent_idempotent,
   InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdeal_finrank,
   InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction_intertwines a v⟩

/-- **Multi-Step and 8-Step Real Bott Periodicity Intertwining of `peirceBdGHamiltonian`**:
For every `n ≤ m` (and in particular along the 8-step Real Bott Periodicity subsequence
`m = n + 8 * k`), the directed bonding map
`bondMap stageBond n m hnm : Stage n →+* Stage m` and the
inductive colimit map `ofStage m : Stage m →+* Limit` intertwine `peirceBdGHamiltonian`,
so finite-stage mass operators stabilize canonically in `Limit`. -/
theorem bondMap_and_bott_period_intertwine_peirceBdGHamiltonian
    {n m : ℕ} (hnm : n ≤ m) (k : ℕ) (P D A C : Stage n) :
    let bMap := bondMap stageBond n m hnm
    let bBott := bondMap stageBond n (n + 8 * k) (Nat.le_add_right n (8 * k))
    bMap (peirceBdGHamiltonian P D A C) =
      peirceBdGHamiltonian (bMap P) (bMap D) (bMap A) (bMap C) ∧
    ofStage m
        (peirceBdGHamiltonian (bMap P) (bMap D) (bMap A) (bMap C)) =
      ofStage n (peirceBdGHamiltonian P D A C) ∧
    ofStage (n + 8 * k)
        (peirceBdGHamiltonian (bBott P) (bBott D) (bBott A) (bBott C)) =
      ofStage n (peirceBdGHamiltonian P D A C) := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  let bBott := bondMap stageBond n (n + 8 * k) (Nat.le_add_right n (8 * k))
  have hBond :
      bMap (peirceBdGHamiltonian P D A C) =
        peirceBdGHamiltonian (bMap P) (bMap D) (bMap A) (bMap C) :=
    (map_peirceBdGHamiltonian bMap P D A C).2.2
  have hBott :
      bBott (peirceBdGHamiltonian P D A C) =
        peirceBdGHamiltonian (bBott P) (bBott D) (bBott A) (bBott C) :=
    (map_peirceBdGHamiltonian bBott P D A C).2.2
  refine ⟨hBond, ?_, ?_⟩
  · rw [← hBond]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hBott]
    exact directLimitOf_bondMap stageBond n (n + 8 * k) (Nat.le_add_right n (8 * k)) _

/-- **Inductive-Colimit Peirce–BdG Mass-Gap Amplification**:
At the inductive colimit `Limit`, for any `P D A X : Limit` with `P * P = P`, `star P = P`,
`star D = D`, and `comm (evenGrade P D) (genJ P A (star A)) = 0`, if the
off-diagonal mass coupling `genV P A (star A)` satisfies a lower bound
`m_gap ≤ tau (star X * genV P A (star A) * X)`, then the full Peirce–BdG energy
`tau (star X * (H_BdG * H_BdG) * X)` dominates both the kinetic energy
`tau (star (evenGrade P D * X) * (evenGrade P D * X)) + m_gap` and `m_gap` itself. -/
theorem limit_peirceBdGHamiltonian_mass_gap_amplification
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (a : Stage n), tau (ofStage n a) = normalizedTrace n a)
    {P D : Limit} (hP : P * P = P) (hPs : star P = P) (hDs : star D = D)
    (A X : Limit)
    (hComm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm (evenGrade P D) (genJ P A (star A)) = 0)
    {m_gap : ℝ} (hMass : m_gap ≤ tau (star X * genV P A (star A) * X)) :
    let H_BdG := peirceBdGHamiltonian P D A (star A)
    tau (star (evenGrade P D * X) * (evenGrade P D * X)) + m_gap ≤
      tau (star X * (H_BdG * H_BdG) * X) ∧
    m_gap ≤ tau (star X * (H_BdG * H_BdG) * X) := by
  dsimp only
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  rcases limit_peirceBdGHamiltonian_noncomm_sq_and_trace_positivity
    tau htau hP hPs hDs A X hComm with ⟨_, _, hDecomp, _⟩
  have hKinPos : 0 ≤ tau (star (evenGrade P D * X) * (evenGrade P D * X)) :=
    hPos (evenGrade P D * X)
  refine ⟨?_, ?_⟩
  · linarith [hDecomp, hMass]
  · linarith [hDecomp, hMass, hKinPos]

/-- Any ring homomorphism `f : B →+* C` intertwines the Stage `D₂₅` golden inverse,
polygon Lucas/Fibonacci operators (`n = 5, 6, 7`), and Penrose Kite/Dart operators. -/
theorem map_polygon_and_klein_penrose_operators
    {B C_ring : Type*} [Ring B] [Ring C_ring]
    (f : B →+* C_ring) (P A C : B) :
    f (opGoldenInverse P A C) = opGoldenInverse (f P) (f A) (f C) ∧
    f (polygonLucas5 P A C) = polygonLucas5 (f P) (f A) (f C) ∧
    f (polygonLucas6 P A C) = polygonLucas6 (f P) (f A) (f C) ∧
    f (polygonLucas7 P A C) = polygonLucas7 (f P) (f A) (f C) ∧
    f (penroseKiteOp P A C) = penroseKiteOp (f P) (f A) (f C) ∧
    f (penroseDartOp P A C) = penroseDartOp (f P) (f A) (f C) := by
  have hT : f (peirceTransfer P A C) = peirceTransfer (f P) (f A) (f C) := by
    unfold peirceTransfer
    rw [map_add, map_genPhi]
  have hTbar : f (peirceTransferComplement P A C) =
      peirceTransferComplement (f P) (f A) (f C) := by
    unfold peirceTransferComplement
    rw [map_sub, map_sub, map_one, map_genPhi]
  refine ⟨?_, ?_, ?_, ?_, hT, map_genV f P A C⟩
  · unfold opGoldenInverse
    rw [map_sub, map_one, hT]
  · unfold polygonLucas5
    rw [map_add, map_pow, map_pow, hT, hTbar]
  · unfold polygonLucas6
    rw [map_add, map_pow, map_pow, hT, hTbar]
  · unfold polygonLucas7
    rw [map_add, map_pow, map_pow, hT, hTbar]

/-- **Inductive-Colimit Pentagon, Hexagon, Heptagon Braiding & Klein-Bottle Penrose Tiling Synthesis**:
For any finite stage `n : ℕ`, `n ≤ m`, idempotent `P : Stage n` (`P * P = P`), and `A C : Stage n`:
1. Both the multi-step tensor-tower bonding map `bondMap stageBond n m hnm : Stage n →+* Stage m`
   and the colimit canonical map `ofStage n : Stage n →+* Limit` intertwine `opGoldenInverse`,
   `polygonLucas5`, `polygonLucas6`, `polygonLucas7`, `penroseKiteOp`, and `penroseDartOp`,
   with exact stage-bonding coherence in `Limit`;
2. At `Limit`, the lifted operators `Pinf = ofStage n P`, `Ainf = ofStage n A`, `Cinf = ofStage n C`
   satisfy the full 17-conjunct Stage `D₂₅` Pentagon–Hexagon–Heptagon braiding and Klein-bottle
   Penrose tiling synthesis. -/
theorem limit_pentagon_hexagon_heptagon_braiding_and_klein_penrose
    {n m : ℕ} (hnm : n ≤ m) {P : Stage n} (hP : P * P = P) (A C : Stage n) :
    let bMap := bondMap stageBond n m hnm
    let Pinf := ofStage n P
    let Ainf := ofStage n A
    let Cinf := ofStage n C
    ofStage m (polygonLucas5 (bMap P) (bMap A) (bMap C)) = polygonLucas5 Pinf Ainf Cinf ∧
    ofStage m (polygonLucas6 (bMap P) (bMap A) (bMap C)) = polygonLucas6 Pinf Ainf Cinf ∧
    ofStage m (polygonLucas7 (bMap P) (bMap A) (bMap C)) = polygonLucas7 Pinf Ainf Cinf ∧
    ofStage m (penroseKiteOp (bMap P) (bMap A) (bMap C)) = penroseKiteOp Pinf Ainf Cinf ∧
    ofStage m (penroseDartOp (bMap P) (bMap A) (bMap C)) = penroseDartOp Pinf Ainf Cinf ∧
    (opGoldenInverse Pinf Ainf Cinf * opGoldenInverse Pinf Ainf Cinf +
        opGoldenInverse Pinf Ainf Cinf = genV Pinf Ainf Cinf ∧
     genV Pinf Ainf Cinf * opGoldenInverse Pinf Ainf Cinf -
        opGoldenInverse Pinf Ainf Cinf * opGoldenInverse Pinf Ainf Cinf *
          opGoldenInverse Pinf Ainf Cinf =
       peirceTransferComplement Pinf Ainf Cinf * peirceTransferComplement Pinf Ainf Cinf ∧
     polygonLucas5 Pinf Ainf Cinf - 1 = (5 : ℤ) • (genV Pinf Ainf Cinf * (1 + genV Pinf Ainf Cinf)) ∧
     polygonLucas6 Pinf Ainf Cinf =
       1 + (6 : ℤ) • genV Pinf Ainf Cinf + (9 : ℤ) • (genV Pinf Ainf Cinf * genV Pinf Ainf Cinf) +
         (2 : ℤ) • (genV Pinf Ainf Cinf * genV Pinf Ainf Cinf * genV Pinf Ainf Cinf) ∧
     polygonLucas7 Pinf Ainf Cinf - 1 =
       (7 : ℤ) • (genV Pinf Ainf Cinf * ((1 + genV Pinf Ainf Cinf) * (1 + genV Pinf Ainf Cinf))) ∧
     polygonLucas7 Pinf Ainf Cinf =
       polygonLucas6 Pinf Ainf Cinf + genV Pinf Ainf Cinf * polygonLucas5 Pinf Ainf Cinf ∧
     (peirceTransfer Pinf Ainf Cinf) ^ 7 - (peirceTransferComplement Pinf Ainf Cinf) ^ 7 =
       polygonFib7 Pinf Ainf Cinf * radicalLetterPlus Pinf Ainf Cinf ∧
     (1 + conePlus Pinf Ainf) * (1 + coneMinus Pinf Cinf) * (1 + conePlus Pinf Ainf) -
        (1 + coneMinus Pinf Cinf) * (1 + conePlus Pinf Ainf) * (1 + coneMinus Pinf Cinf) =
       (1 + genV Pinf Ainf Cinf) * genJ Pinf Ainf Cinf ∧
     peircePermutedTwist Pinf Ainf Cinf (polygonLucas5 Pinf Ainf Cinf) =
       polygonLucas5 Pinf Ainf Cinf ∧
     peircePermutedTwist Pinf Ainf Cinf (polygonLucas6 Pinf Ainf Cinf) =
       polygonLucas6 Pinf Ainf Cinf ∧
     peircePermutedTwist Pinf Ainf Cinf (polygonLucas7 Pinf Ainf Cinf) =
       polygonLucas7 Pinf Ainf Cinf ∧
     peirceTransfer Pinf Ainf Cinf * penroseKiteOp Pinf Ainf Cinf =
       penroseKiteOp Pinf Ainf Cinf + penroseDartOp Pinf Ainf Cinf ∧
     peirceTransfer Pinf Ainf Cinf * penroseDartOp Pinf Ainf Cinf =
       penroseDartOp Pinf Ainf Cinf * penroseKiteOp Pinf Ainf Cinf ∧
     genPhi Pinf Ainf Cinf * parityConj Pinf (penroseKiteOp Pinf Ainf Cinf) =
       peirceTransferComplement Pinf Ainf Cinf * genPhi Pinf Ainf Cinf ∧
     parityConj Pinf (polygonLucas5 Pinf Ainf Cinf) = polygonLucas5 Pinf Ainf Cinf ∧
     parityConj Pinf (polygonLucas6 Pinf Ainf Cinf) = polygonLucas6 Pinf Ainf Cinf ∧
     parityConj Pinf (polygonLucas7 Pinf Ainf Cinf) = polygonLucas7 Pinf Ainf Cinf) := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  rcases map_polygon_and_klein_penrose_operators bMap P A C with
    ⟨_, hB5, hB6, hB7, hBKite, hBDart⟩
  rcases map_polygon_and_klein_penrose_operators (ofStage n) P A C with
    ⟨_, hO5, hO6, hO7, hOKite, hODart⟩
  have hPinf : ofStage n P * ofStage n P = ofStage n P :=
    map_idempotent (ofStage n) hP
  refine ⟨?_, ?_, ?_, ?_, ?_,
    stage_D25_pentagon_hexagon_heptagon_braiding_and_klein_penrose_master_synthesis
      hPinf (ofStage n A) (ofStage n C)⟩
  · rw [← hB5, ← hO5]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hB6, ← hO6]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hB7, ← hO7]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hBKite, ← hOKite]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hBDart, ← hODart]
    exact directLimitOf_bondMap stageBond n m hnm _

/-- **Inductive-Colimit Pentagon (`L₅`), Hexagon (`L₆`), and Heptagon (`L₇`) Trace Coercivity Hierarchy**:
At the inductive colimit `Limit`, for any linear trace extension `tau : Limit →ₗ[ℝ] ℝ` of
`normalizedTrace`, any self-adjoint idempotent `P : Limit` (`P * P = P`, `star P = P`), and
any `A X : Limit`:
1. With `Φ = genPhi P A (star A)` and `V = genV P A (star A)`, the powers `V`, `V²`, and `V³`
   have exact Hermitian-square factorizations:
   - `star X * V * X = star (Φ * X) * (Φ * X)`,
   - `star X * (V * V) * X = star (V * X) * (V * X)`,
   - `star X * (V * V * V) * X = star (Φ * V * X) * (Φ * V * X)`;
2. Consequently, the Pentagon (`L₅`), Hexagon (`L₆`), and Heptagon (`L₇`) Lucas operators at
   `C = star A` satisfy the monotone trace coercivity chain:
   `0 ≤ tau (star X * X) ≤ tau (star X * X) + 5 * tau (star X * V * X) ≤ tau (star X * L₅ * X) ≤ tau (star X * L₆ * X) ≤ tau (star X * L₇ * X)`. -/
theorem limit_polygon_lucas_trace_coercivity_hierarchy
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (a : Stage n), tau (ofStage n a) = normalizedTrace n a)
    {P : Limit} (hP : P * P = P) (hPs : star P = P) (A X : Limit) :
    let Φ := genPhi P A (star A)
    let V := genV P A (star A)
    let L₅ := polygonLucas5 P A (star A)
    let L₆ := polygonLucas6 P A (star A)
    let L₇ := polygonLucas7 P A (star A)
    star X * V * X = star (Φ * X) * (Φ * X) ∧
    star X * (V * V) * X = star (V * X) * (V * X) ∧
    star X * (V * V * V) * X = star (Φ * V * X) * (Φ * V * X) ∧
    0 ≤ tau (star X * X) ∧
    tau (star X * X) ≤ tau (star X * X) + 5 * tau (star X * V * X) ∧
    tau (star X * X) + 5 * tau (star X * V * X) ≤ tau (star X * L₅ * X) ∧
    tau (star X * L₅ * X) ≤ tau (star X * L₆ * X) ∧
    tau (star X * L₆ * X) ≤ tau (star X * L₇ * X) := by
  dsimp only
  let Φ := genPhi P A (star A)
  let V := genV P A (star A)
  let L₅ := polygonLucas5 P A (star A)
  let L₆ := polygonLucas6 P A (star A)
  let L₇ := polygonLucas7 P A (star A)
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  have hStarPhi : star Φ = Φ := by
    change star (P * A * (1 - P) + (1 - P) * star A * P) =
      P * A * (1 - P) + (1 - P) * star A * P
    simp only [star_add, star_mul, star_sub, star_one, star_star, hPs, mul_assoc]
    exact add_comm _ _
  have hPhiSq : Φ * Φ = V := by
    dsimp [Φ, V]
    peirce_nf hP
  have hStarV : star V = V := by
    rw [← hPhiSq, star_mul, hStarPhi]
  have hPhiV : Φ * V = V * Φ := by
    rw [← hPhiSq, mul_assoc]
  have hV1 : star X * V * X = star (Φ * X) * (Φ * X) := by
    rw [star_mul, hStarPhi, ← hPhiSq]
    noncomm_ring
  have hV2 : star X * (V * V) * X = star (V * X) * (V * X) := by
    rw [star_mul, hStarV]
    noncomm_ring
  have hV3 : star X * (V * V * V) * X = star (Φ * V * X) * (Φ * V * X) := by
    have hCube : V * V * V = V * Φ * (Φ * V) := by
      calc
        V * V * V = V * (Φ * Φ) * V := by rw [hPhiSq]
        _ = V * Φ * (Φ * V) := by noncomm_ring
    rw [star_mul, star_mul, hStarV, hStarPhi, hCube]
    noncomm_ring
  have hPos0 : 0 ≤ tau (star X * X) := hPos X
  have hPos1 : 0 ≤ tau (star X * V * X) := by
    rw [hV1]; exact hPos (Φ * X)
  have hPos2 : 0 ≤ tau (star X * (V * V) * X) := by
    rw [hV2]; exact hPos (V * X)
  have hPos3 : 0 ≤ tau (star X * (V * V * V) * X) := by
    rw [hV3]; exact hPos (Φ * V * X)
  rcases pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy hP A (star A) with
    ⟨hL5, _, hL6, hL7, _, _, _, _, _, _, _, _⟩
  have hTau5 :
      tau (star X * L₅ * X) =
        tau (star X * X) + 5 * tau (star X * V * X) +
          5 * tau (star X * (V * V) * X) := by
    dsimp only [L₅, V]
    rw [hL5]
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
  have hTau6 :
      tau (star X * L₆ * X) =
        tau (star X * X) + 6 * tau (star X * V * X) +
          9 * tau (star X * (V * V) * X) +
          2 * tau (star X * (V * V * V) * X) := by
    dsimp only [L₆, V]
    rw [hL6]
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
  have hTau7 :
      tau (star X * L₇ * X) =
        tau (star X * X) + 7 * tau (star X * V * X) +
          14 * tau (star X * (V * V) * X) +
          7 * tau (star X * (V * V * V) * X) := by
    dsimp only [L₇, V]
    rw [hL7]
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
  refine ⟨hV1, hV2, hV3, hPos0, ?_, ?_, ?_, ?_⟩
  · linarith [hPos1]
  · linarith [hTau5, hPos2]
  · linarith [hTau5, hTau6, hPos1, hPos2, hPos3]
  · linarith [hTau6, hTau7, hPos1, hPos2, hPos3]

/-- **Canonical `Cl(5, 5)` to `Stage 5` (`Mat 5 ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ`) Ring Homomorphism**:
Composes `neutralCliffordAlgEquiv.symm : Cl55 ≃ₐ[ℝ] NeutralClifford`, the faithful
Fock coordinate matrix representation `neutralCliffordCoordinateMatrixRep : NeutralClifford →ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ`,
and the tensor-stage reindexing equivalence `(matEquivFinPowTwo 5).symm : Matrix (Fin 32) (Fin 32) ℝ ≃ₐ[ℝ] Stage 5`. -/
noncomputable def cl55ToStage5 :
    InfoGeometry.Clifford.Clifford55.Cl55 →+* Stage 5 :=
  ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm.toAlgHom.comp
    (InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.neutralCliffordCoordinateMatrixRep.comp
      InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm.toAlgHom)).toRingHom

/-- **`Cl(5, 5)` Bott-Boundary Spinor Ideal & Fock Matrix Intertwiner Bridge to Peirce–BdG & Klein-Penrose**:
At the Real Bott Periodicity boundary (`n = 5`, `Stage 5 = Mat 5 ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ`):
1. `cl55ToStage5` is injective (`Function.Injective cl55ToStage5`), embedding `Cl(5, 5)`
   faithfully onto the 32×32 spinor matrix stage `Stage 5`;
2. The `Cl(5, 5)` vacuum spinor idempotent `cl55VacuumIdempotent` maps to a genuine idempotent
   `P₅ = cl55ToStage5 cl55VacuumIdempotent` in `Stage 5` and `P_lim = ofStage 5 P₅` in `Limit`;
3. For any `D_cl A_cl C_cl : Cl55`, both `cl55ToStage5` and `ofStage 5 ∘ cl55ToStage5` intertwine
   `peirceBdGHamiltonian`, `polygonLucas5`, `polygonLucas6`, `polygonLucas7`, `penroseKiteOp`,
   and `penroseDartOp`, transporting the Stage `D₂₅` Pentagon–Hexagon–Heptagon braiding and
   Klein-bottle Penrose tiling identities from `Cl(5, 5)` through `Stage 5` into `Limit`. -/
theorem cl55_bott_spinor_stage5_peirce_bdg_and_klein_penrose_bridge
    (D_cl A_cl C_cl : InfoGeometry.Clifford.Clifford55.Cl55) :
    let ω := InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent
    let P₅ := cl55ToStage5 ω
    let D₅ := cl55ToStage5 D_cl
    let A₅ := cl55ToStage5 A_cl
    let C₅ := cl55ToStage5 C_cl
    let P_lim := ofStage 5 P₅
    let A_lim := ofStage 5 A₅
    let C_lim := ofStage 5 C₅
    Function.Injective cl55ToStage5 ∧
    P₅ * P₅ = P₅ ∧
    P_lim * P_lim = P_lim ∧
    cl55ToStage5 (peirceBdGHamiltonian ω D_cl A_cl C_cl) =
      peirceBdGHamiltonian P₅ D₅ A₅ C₅ ∧
    ofStage 5 (cl55ToStage5 (peirceBdGHamiltonian ω D_cl A_cl C_cl)) =
      peirceBdGHamiltonian P_lim (ofStage 5 D₅) A_lim C_lim ∧
    ofStage 5 (cl55ToStage5 (polygonLucas5 ω A_cl C_cl)) =
      polygonLucas5 P_lim A_lim C_lim ∧
    ofStage 5 (cl55ToStage5 (polygonLucas6 ω A_cl C_cl)) =
      polygonLucas6 P_lim A_lim C_lim ∧
    ofStage 5 (cl55ToStage5 (polygonLucas7 ω A_cl C_cl)) =
      polygonLucas7 P_lim A_lim C_lim ∧
    ofStage 5 (cl55ToStage5 (penroseKiteOp ω A_cl C_cl)) =
      penroseKiteOp P_lim A_lim C_lim ∧
    ofStage 5 (cl55ToStage5 (penroseDartOp ω A_cl C_cl)) =
      penroseDartOp P_lim A_lim C_lim ∧
    polygonLucas7 P_lim A_lim C_lim =
      polygonLucas6 P_lim A_lim C_lim + genV P_lim A_lim C_lim * polygonLucas5 P_lim A_lim C_lim ∧
    peirceTransfer P_lim A_lim C_lim * penroseKiteOp P_lim A_lim C_lim =
      penroseKiteOp P_lim A_lim C_lim + penroseDartOp P_lim A_lim C_lim ∧
    genPhi P_lim A_lim C_lim * parityConj P_lim (penroseKiteOp P_lim A_lim C_lim) =
      peirceTransferComplement P_lim A_lim C_lim * genPhi P_lim A_lim C_lim := by
  dsimp only
  let ω := InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent
  have hω : ω * ω = ω :=
    InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent_idempotent
  have hInj : Function.Injective cl55ToStage5 :=
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm.injective.comp
      (InfoGeometry.Clifford.Cl55FockMatrixIntertwiner.neutralCliffordCoordinateMatrixRep_injective.comp
        InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm.injective)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPlim : ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
      ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have hBdG5 : cl55ToStage5 (peirceBdGHamiltonian ω D_cl A_cl C_cl) =
      peirceBdGHamiltonian (cl55ToStage5 ω) (cl55ToStage5 D_cl)
        (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) :=
    (map_peirceBdGHamiltonian cl55ToStage5 ω D_cl A_cl C_cl).2.2
  have hBdGLim : ofStage 5 (cl55ToStage5 (peirceBdGHamiltonian ω D_cl A_cl C_cl)) =
      peirceBdGHamiltonian (ofStage 5 (cl55ToStage5 ω)) (ofStage 5 (cl55ToStage5 D_cl))
        (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hBdG5]
    exact (map_peirceBdGHamiltonian (ofStage 5) (cl55ToStage5 ω)
      (cl55ToStage5 D_cl) (cl55ToStage5 A_cl) (cl55ToStage5 C_cl)).2.2
  rcases map_polygon_and_klein_penrose_operators
    ((ofStage 5).comp cl55ToStage5) ω A_cl C_cl with
    ⟨_, hL5, hL6, hL7, hKite, hDart⟩
  rcases stage_D25_pentagon_hexagon_heptagon_braiding_and_klein_penrose_master_synthesis
    hPlim (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) with
    ⟨_, _, _, _, _, hRec, _, _, _, _, _, hInfK, _, hInter, _, _, _⟩
  exact ⟨hInj, hP5, hPlim, hBdG5, hBdGLim, hL5, hL6, hL7, hKite, hDart, hRec, hInfK, hInter⟩

/-! ## 6. Nontrivial Tensor-Tower Krein Pairing, Definite Sheet Polarization, & Self-Dual Yang–Mills in `Limit` -/

open InfoGeometry.OperatorAlgebra.PeirceDefectBridge

/-- **Finite-Stage Indefinite Hestenes–Krein Pairing (`stageKreinPairing`)**:
At finite tensor-tower stage `Stage n` (`2ⁿ × 2ⁿ` real matrices), for any idempotent `P`
with Krein fundamental symmetry `invS P = P - (1 - P)`, the indefinite Krein pairing is
`normalizedTrace n (star X * invS P * Y)`. -/
noncomputable def stageKreinPairing (n : ℕ) (P X Y : Stage n) : ℝ :=
  normalizedTrace n (star X * invS P * Y)

/-- **Inductive-Colimit Indefinite Hestenes–Krein Pairing (`limitKreinPairing`)**:
At `Limit`, for any linear trace extension `tau : Limit →ₗ[ℝ] ℝ` of `normalizedTrace`,
the colimit Krein pairing is `tau (star X * invS P * Y)`. -/
noncomputable def limitKreinPairing (tau : Limit →ₗ[ℝ] ℝ) (P X Y : Limit) : ℝ :=
  tau (star X * invS P * Y)

/-- Pure `*`-ring Krein sheet polarization, Maurer–Cartan curvature, and Bianchi identities
over any abstract `[Ring B] [StarRing B]`, plus ring-homomorphism transport of
`peirceMaurerCartanCurvature`. -/
theorem krein_sheet_polarization_ring_identities
    {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPs : star P = P) (A C X : B) :
    invS P * invS P = 1 ∧
    star (invS P) = invS P ∧
    star X * invS P * X =
      star (P * X) * (P * X) - star ((1 - P) * X) * ((1 - P) * X) ∧
    star (P * X) * invS P * (P * X) = star (P * X) * (P * X) ∧
    star ((1 - P) * X) * invS P * ((1 - P) * X) =
      -(star ((1 - P) * X) * ((1 - P) * X)) ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    peirceCovariantDeriv P A C (genV P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold invS; noncomm_ring [hP]
  · unfold invS; rw [star_sub, star_sub, star_one, hPs]
  · rw [star_mul, star_mul, star_sub, star_one, hPs]
    unfold invS; noncomm_ring [hP]
  · rw [star_mul, hPs]
    unfold invS; noncomm_ring [hP]
  · rw [star_mul, star_sub, star_one, hPs]
    unfold invS; noncomm_ring [hP]
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv
    peirce_nf hP
  · unfold peirceCovariantDeriv peirceGradingDeriv
    peirce_nf hP

/-- Any ring homomorphism `f : B →+* D` intertwines `peirceMaurerCartanCurvature`. -/
theorem map_peirceMaurerCartanCurvature
    {B D : Type*} [Ring B] [Ring D] (f : B →+* D) (P₀ A₀ C₀ : B) :
    f (peirceMaurerCartanCurvature P₀ A₀ C₀) =
      peirceMaurerCartanCurvature (f P₀) (f A₀) (f C₀) := by
  unfold peirceMaurerCartanCurvature peirceGradingDeriv
  rw [map_add, map_comm, map_mul, map_genPhi]

/-- Multi-step tensor-tower bonding `bondMap stageBond n m hnm` commutes with `star`
and preserves `normalizedTrace` without any determinant nonvanishing hypothesis. -/
theorem bondMap_star_and_normalizedTrace {n m : ℕ} (hnm : n ≤ m) (A : Stage n) :
    let bMap := bondMap stageBond n m hnm
    bMap (star A) = star (bMap A) ∧
    normalizedTrace m (bMap A) = normalizedTrace n A := by
  dsimp only
  refine Nat.le_induction
    (m := n)
    (P := fun m hnm =>
      bondMap stageBond n m hnm (star A) = star (bondMap stageBond n m hnm A) ∧
      normalizedTrace m (bondMap stageBond n m hnm A) = normalizedTrace n A)
    ?base ?succ m hnm
  · simp [bondMap_refl]
  · intro k hnk ih
    rcases ih with ⟨hStar, hTr⟩
    rw [bondMap_succ stageBond n k hnk]
    let bMapK := bondMap stageBond n k hnk
    change stageEmbed k (bMapK (star A)) = star (stageEmbed k (bMapK A)) ∧
      normalizedTrace (k + 1) (matStageEmbed k (bMapK A)) = normalizedTrace n A
    refine ⟨?_, ?_⟩
    · rw [hStar, stageEmbed_star k (bMapK A)]
    · rw [normalizedTrace_matStageEmbed k (bMapK A), hTr]

/-- **Multi-Step Tensor-Tower Invariance & Colimit Descent of the Krein Pairing
(`stageKreinPairing_bondMap_and_limit_descent`)**:
For any `n ≤ m` and `P, X, Y : Stage n`:
1. The multi-step bonding map `bMap = bondMap stageBond n m hnm : Stage n →+* Stage m`
   preserves `stageKreinPairing` identically;
2. The colimit map `ofStage n : Stage n →+* Limit` intertwines `stageKreinPairing` with
   `limitKreinPairing`. -/
theorem stageKreinPairing_bondMap_and_limit_descent
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {n m : ℕ} (hnm : n ≤ m) (P X Y : Stage n) :
    let bMap := bondMap stageBond n m hnm
    stageKreinPairing m (bMap P) (bMap X) (bMap Y) = stageKreinPairing n P X Y ∧
    limitKreinPairing tau (ofStage n P) (ofStage n X) (ofStage n Y) =
      stageKreinPairing n P X Y := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  have hStarB : bMap (star X) = star (bMap X) :=
    (bondMap_star_and_normalizedTrace hnm X).1
  have hTrB :
      normalizedTrace m (bMap (star X * invS P * Y)) =
        normalizedTrace n (star X * invS P * Y) :=
    (bondMap_star_and_normalizedTrace hnm (star X * invS P * Y)).2
  refine ⟨?_, ?_⟩
  · unfold stageKreinPairing
    have hMap :
        bMap (star X * invS P * Y) = star (bMap X) * invS (bMap P) * bMap Y := by
      rw [map_mul, map_mul, hStarB, map_invS]
    rw [← hMap, hTrB]
  · unfold limitKreinPairing stageKreinPairing
    have hMap :
        ofStage n (star X * invS P * Y) =
          star (ofStage n X) * invS (ofStage n P) * ofStage n Y := by
      rw [map_mul, map_mul, ofStage_star n X, map_invS]
    rw [← hMap, htau n (star X * invS P * Y)]

/-- **Inductive-Colimit Krein Polarization into Positive/Negative Definite Peirce Sheets
& Self-Dual Yang–Mills / Bianchi Identity (`limit_krein_polarization_and_self_dual_yang_mills`)**:
Upgrades the constant-diagram `TwoSheetKreinStageSystem` theorem to the genuine `2ⁿ × 2ⁿ`
tensor-tower inductive colimit `Limit`:
For any trace extension `tau : Limit →ₗ[ℝ] ℝ` of `normalizedTrace`, any self-adjoint
idempotent `P : Limit` (`P * P = P`, `star P = P`), and any `A C X : Limit`:
1. `invS P * invS P = 1` and `star (invS P) = invS P`;
2. **Krein Sheet Polarization:**
   `star X * invS P * X = star (P * X) * (P * X) - star ((1 - P) * X) * ((1 - P) * X)`,
   so `limitKreinPairing tau P X X = tau (star (P * X) * (P * X)) - tau (star ((1 - P) * X) * ((1 - P) * X))`,
   with `0 ≤ limitKreinPairing tau P (P * X) (P * X)` (positive-definite upper sheet) and
   `limitKreinPairing tau P ((1 - P) * X) ((1 - P) * X) ≤ 0` (negative-definite lower sheet);
3. **Nontrivial Colimit Peirce Pinching–Defect & Self-Dual Yang–Mills / Bianchi Identity:**
   `evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X`,
   `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`, and
   `peirceCovariantDeriv P A C (genV P A C) = 0`, with exact `bondMap` and
   stage-to-colimit transport of the Peirce connection, curvature, and covariant derivative. -/
theorem limit_krein_polarization_and_self_dual_yang_mills
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPs : star P = P)
    (A C X : Limit) (n : ℕ) {m : ℕ} (hnm : n ≤ m)
    (P₀ A₀ C₀ X₀ : Stage n) :
    invS P * invS P = 1 ∧
    star (invS P) = invS P ∧
    star X * invS P * X =
      star (P * X) * (P * X) - star ((1 - P) * X) * ((1 - P) * X) ∧
    limitKreinPairing tau P X X =
      tau (star (P * X) * (P * X)) - tau (star ((1 - P) * X) * ((1 - P) * X)) ∧
    0 ≤ limitKreinPairing tau P (P * X) (P * X) ∧
    limitKreinPairing tau P ((1 - P) * X) ((1 - P) * X) ≤ 0 ∧
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) =
      genV P X X ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    peirceCovariantDeriv P A C (genV P A C) = 0 ∧
    bondMap stageBond n m hnm (genPhi P₀ A₀ C₀) =
      genPhi (bondMap stageBond n m hnm P₀)
        (bondMap stageBond n m hnm A₀) (bondMap stageBond n m hnm C₀) ∧
    bondMap stageBond n m hnm (peirceMaurerCartanCurvature P₀ A₀ C₀) =
      peirceMaurerCartanCurvature (bondMap stageBond n m hnm P₀)
        (bondMap stageBond n m hnm A₀) (bondMap stageBond n m hnm C₀) ∧
    bondMap stageBond n m hnm (peirceCovariantDeriv P₀ A₀ C₀ X₀) =
      peirceCovariantDeriv (bondMap stageBond n m hnm P₀)
        (bondMap stageBond n m hnm A₀) (bondMap stageBond n m hnm C₀)
        (bondMap stageBond n m hnm X₀) ∧
    ofStage n (genPhi P₀ A₀ C₀) =
      genPhi (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) ∧
    ofStage n (peirceMaurerCartanCurvature P₀ A₀ C₀) =
      peirceMaurerCartanCurvature (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) ∧
    ofStage n (peirceCovariantDeriv P₀ A₀ C₀ X₀) =
      peirceCovariantDeriv (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) (ofStage n X₀) := by
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  rcases krein_sheet_polarization_ring_identities hP hPs A C X with
    ⟨hS2, hStarS, hPolar, hUpperId, hLowerId, hMC, hBianchi⟩
  have hTauPolar :
      limitKreinPairing tau P X X =
        tau (star (P * X) * (P * X)) - tau (star ((1 - P) * X) * ((1 - P) * X)) := by
    unfold limitKreinPairing
    rw [hPolar, tau.map_sub]
  refine ⟨hS2, hStarS, hPolar, hTauPolar, ?_, ?_,
    even_idempotencyDefect_sub P X hP, hMC, hBianchi,
    map_genPhi (bondMap stageBond n m hnm) P₀ A₀ C₀,
    map_peirceMaurerCartanCurvature (bondMap stageBond n m hnm) P₀ A₀ C₀,
    (by
      unfold peirceCovariantDeriv peirceGradingDeriv
      rw [map_add, map_comm, map_comm, map_genPhi]),
    map_genPhi (ofStage n) P₀ A₀ C₀,
    map_peirceMaurerCartanCurvature (ofStage n) P₀ A₀ C₀,
    (by
      unfold peirceCovariantDeriv peirceGradingDeriv
      rw [map_add, map_comm, map_comm, map_genPhi])⟩
  · unfold limitKreinPairing
    rw [hUpperId]
    exact hPos (P * X)
  · unfold limitKreinPairing
    rw [hLowerId, tau.map_neg]
    exact neg_nonpos.mpr (hPos ((1 - P) * X))

/-! ## 7. Inductive-Colimit Transport of Log-CFT Jordan Monodromy & `FibonacciGrothendieckRing` (`K₀(Fib)`) -/

/-- **Inductive-Colimit Log-CFT Virasoro Jordan Monodromy & `FibonacciGrothendieckRing` (`K₀(Fib)`) Bridge
(`limit_logCft_jordan_monodromy_and_fibonacciK0_penrose_bridge`)**:
For any finite stage `n ≤ m`, idempotent `P : Stage n` (`P * P = P`), `A C : Stage n`,
winding/power exponent `k : ℕ`, and Grothendieck classes `z₁, z₂ : FibonacciK0`:
1. Both `bMap = bondMap stageBond n m hnm` and `ofStage n` intertwine `opVirasoroL0Cell`,
   `opLogMonodromy`, and `fibK0ToPeirceOp`, with exact stage-bonding coherence in `Limit`;
2. At `Limit`, `Pinf = ofStage n P`, `Ainf = ofStage n A`, `Cinf = ofStage n C` satisfy:
   - the truncated binomial power laws for `plabicWhiteShear`, `opVirasoroL0Cell`, and `opLogMonodromy`,
   - the exact off-shell `FibonacciK0` multiplication defect law
     `fibK0ToPeirceOp Pinf Ainf Cinf z₁ * fibK0ToPeirceOp Pinf Ainf Cinf z₂ - fibK0ToPeirceOp Pinf Ainf Cinf (k0Mul z₁ z₂) = ((k0ToModel z₁).2 * (k0ToModel z₂).2) • (penroseDartOp Pinf Ainf Cinf - 1)`,
   - and exact `k0Mul` / `tensorTauK0` multiplicativity on the Golden/Penrose shell `genV Pinf Ainf Cinf = 1`. -/
theorem limit_logCft_jordan_monodromy_and_fibonacciK0_penrose_bridge
    {n m : ℕ} (hnm : n ≤ m) {P : Stage n} (hP : P * P = P) (A C : Stage n) (k : ℕ)
    (z₁ z₂ : InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciK0) :
    let bMap := bondMap stageBond n m hnm
    let Pinf := ofStage n P
    let Ainf := ofStage n A
    let Cinf := ofStage n C
    let k0ToModel := InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel
    let k0Mul := InfoGeometry.Algebra.FibonacciGrothendieckRing.k0Mul
    let tensorTauK0 := InfoGeometry.Algebra.FibonacciGrothendieckRing.tensorTauK0
    ofStage m (opVirasoroL0Cell (bMap P) (bMap A) (bMap C)) =
      opVirasoroL0Cell Pinf Ainf Cinf ∧
    ofStage m (opLogMonodromy (bMap P) (bMap A) (bMap C)) =
      opLogMonodromy Pinf Ainf Cinf ∧
    ofStage m (fibK0ToPeirceOp (bMap P) (bMap A) (bMap C) z₁) =
      fibK0ToPeirceOp Pinf Ainf Cinf z₁ ∧
    (plabicWhiteShear Pinf Ainf) ^ k = 1 + (k : ℤ) • conePlus Pinf Ainf ∧
    (opVirasoroL0Cell Pinf Ainf Cinf) ^ (k + 1) =
      (genV Pinf Ainf Cinf) ^ (k + 1) +
        ((k + 1 : ℕ) : ℤ) • ((genV Pinf Ainf Cinf) ^ k * conePlus Pinf Ainf) ∧
    (opLogMonodromy Pinf Ainf Cinf) ^ k =
      (genV Pinf Ainf Cinf) ^ k * (1 + (k : ℤ) • conePlus Pinf Ainf) ∧
    fibK0ToPeirceOp Pinf Ainf Cinf z₁ * fibK0ToPeirceOp Pinf Ainf Cinf z₂ -
        fibK0ToPeirceOp Pinf Ainf Cinf (k0Mul z₁ z₂) =
      ((k0ToModel z₁).2 * (k0ToModel z₂).2) • (penroseDartOp Pinf Ainf Cinf - 1) ∧
    (genV Pinf Ainf Cinf = 1 →
      fibK0ToPeirceOp Pinf Ainf Cinf (k0Mul z₁ z₂) =
        fibK0ToPeirceOp Pinf Ainf Cinf z₁ * fibK0ToPeirceOp Pinf Ainf Cinf z₂ ∧
      fibK0ToPeirceOp Pinf Ainf Cinf (tensorTauK0 z₁) =
        fibK0ToPeirceOp Pinf Ainf Cinf z₁ * penroseKiteOp Pinf Ainf Cinf) := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  have hPinf : ofStage n P * ofStage n P = ofStage n P :=
    map_idempotent (ofStage n) hP
  have hMapL0 : ∀ {B D : Type} [Ring B] [Ring D] (f : B →+* D) (P₀ A₀ C₀ : B),
      f (opVirasoroL0Cell P₀ A₀ C₀) = opVirasoroL0Cell (f P₀) (f A₀) (f C₀) := by
    intro B D _ _ f P₀ A₀ C₀
    unfold opVirasoroL0Cell
    rw [map_add, map_genV, map_conePlus]
  have hMapMono : ∀ {B D : Type} [Ring B] [Ring D] (f : B →+* D) (P₀ A₀ C₀ : B),
      f (opLogMonodromy P₀ A₀ C₀) = opLogMonodromy (f P₀) (f A₀) (f C₀) := by
    intro B D _ _ f P₀ A₀ C₀
    unfold opLogMonodromy plabicWhiteShear
    rw [map_mul, map_genV, map_add, map_one, map_conePlus]
  rcases plabicWhiteShear_pow_and_opVirasoroL0Cell_binomial_pow
      hPinf (ofStage n A) (ofStage n C) k with
    ⟨hPowShear, hPowL0, hPowMono⟩
  rcases fibonacciK0_peirce_penrose_representation_bridge
      (RingHom.id Limit) hPinf (ofStage n A) (ofStage n C) z₁ z₂ with
    ⟨_, _, _, hMulDef, _, hGoldShell, _⟩
  have hFibB :=
    (fibonacciK0_peirce_penrose_representation_bridge bMap hP A C z₁ z₂).2.2.2.2.2.2
  have hFibO :=
    (fibonacciK0_peirce_penrose_representation_bridge (ofStage n) hP A C z₁ z₂).2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, hPowShear, hPowL0, hPowMono, hMulDef, hGoldShell⟩
  · rw [← hMapL0 bMap P A C, ← hMapL0 (ofStage n) P A C]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hMapMono bMap P A C, ← hMapMono (ofStage n) P A C]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hFibB, ← hFibO]
    exact directLimitOf_bondMap stageBond n m hnm _

/-- **Inductive-Colimit Clifford–Exterior–Interior Tetraktys & Paracomplex/Hypercomplex
Cayley–Dickson Boost Doubling Bridge (`limit_tetraktys_clifford_exterior_and_cayley_dickson_boost_bridge`)**:
For any finite stage `n ≤ m`, idempotent `P : Stage n` (`P * P = P`), `A C : Stage n`,
split-complex pairs `z₁, z₂ : SplitComplex.Carrier ℤ`, and `a b : ℤ`:
1. Both `bMap = bondMap stageBond n m hnm` and `ofStage n` intertwine `splitComplexToInvSOp`,
   `splitComplexToBoostOp`, and `hypercomplexToRotOp`, with exact stage-bonding coherence in `Limit`;
2. At `Limit`, the lifted operators `Pinf = ofStage n P`, `Ainf = ofStage n A`, `Cinf = ofStage n C`
   satisfy the complete Clifford–Exterior–Interior Tetraktys identities (`anticomm Φ J = 0`,
   `J * Φ = Σ`, `Φ * Σ = -V * J`, `J * Σ = -V * Φ`, `Σ * Σ = V * V`) together with the
   Paracomplex Boost (`γ = +1`) and Elliptic Hypercomplex (`γ = -1`) Cayley–Dickson doubling
   product and norm laws. -/
theorem limit_tetraktys_clifford_exterior_and_cayley_dickson_boost_bridge
    {n m : ℕ} (hnm : n ≤ m) {P : Stage n} (hP : P * P = P) (A C : Stage n)
    (z₁ z₂ : InfoGeometry.Canonical.SplitComplex.Carrier ℤ) (a b : ℤ) :
    let bMap := bondMap stageBond n m hnm
    let Pinf := ofStage n P
    let Ainf := ofStage n A
    let Cinf := ofStage n C
    ofStage m (splitComplexToInvSOp (bMap P) z₁) = splitComplexToInvSOp Pinf z₁ ∧
    ofStage m (splitComplexToBoostOp (bMap P) (bMap A) (bMap C) z₁) =
      splitComplexToBoostOp Pinf Ainf Cinf z₁ ∧
    ofStage m (hypercomplexToRotOp (bMap P) (bMap A) (bMap C) a b) =
      hypercomplexToRotOp Pinf Ainf Cinf a b ∧
    anticomm (genPhi Pinf Ainf Cinf) (genJ Pinf Ainf Cinf) = 0 ∧
    genJ Pinf Ainf Cinf * genPhi Pinf Ainf Cinf = genSig Pinf Ainf Cinf ∧
    genSig Pinf Ainf Cinf * genSig Pinf Ainf Cinf =
      genV Pinf Ainf Cinf * genV Pinf Ainf Cinf ∧
    splitComplexToInvSOp Pinf (z₁ * z₂) =
      splitComplexToInvSOp Pinf z₁ * splitComplexToInvSOp Pinf z₂ ∧
    splitComplexToBoostOp Pinf Ainf Cinf z₁ * splitComplexToBoostOp Pinf Ainf Cinf z₂ -
        splitComplexToBoostOp Pinf Ainf Cinf (z₁ * z₂) =
      (z₁.im * z₂.im) • (genV Pinf Ainf Cinf - 1) ∧
    splitComplexToBoostOp Pinf Ainf Cinf ⟨a, b⟩ *
        splitComplexToBoostOp Pinf Ainf Cinf ⟨a, -b⟩ =
      (a * a) • (1 : Limit) - (b * b) • genV Pinf Ainf Cinf ∧
    hypercomplexToRotOp Pinf Ainf Cinf a b *
        hypercomplexToRotOp Pinf Ainf Cinf a (-b) =
      (a * a) • (1 : Limit) + (b * b) • genV Pinf Ainf Cinf := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  have hPinf : ofStage n P * ofStage n P = ofStage n P :=
    map_idempotent (ofStage n) hP
  have hMapInvS : ∀ {B D : Type} [Ring B] [Ring D] (f : B →+* D) (P₀ : B),
      f (splitComplexToInvSOp P₀ z₁) = splitComplexToInvSOp (f P₀) z₁ := by
    intro B D _ _ f P₀
    unfold splitComplexToInvSOp
    rw [map_add, map_zsmul, map_zsmul, map_one, map_invS]
  have hMapBoost : ∀ {B D : Type} [Ring B] [Ring D] (f : B →+* D) (P₀ A₀ C₀ : B),
      f (splitComplexToBoostOp P₀ A₀ C₀ z₁) =
        splitComplexToBoostOp (f P₀) (f A₀) (f C₀) z₁ := by
    intro B D _ _ f P₀ A₀ C₀
    unfold splitComplexToBoostOp
    rw [map_add, map_zsmul, map_zsmul, map_one, map_genPhi]
  have hMapRot : ∀ {B D : Type} [Ring B] [Ring D] (f : B →+* D) (P₀ A₀ C₀ : B),
      f (hypercomplexToRotOp P₀ A₀ C₀ a b) =
        hypercomplexToRotOp (f P₀) (f A₀) (f C₀) a b := by
    intro B D _ _ f P₀ A₀ C₀
    unfold hypercomplexToRotOp
    rw [map_add, map_zsmul, map_zsmul, map_one, map_genJ]
  rcases tetraktys_clifford_interior_exterior_and_cayley_dickson_boost_bridge
      hPinf (ofStage n A) (ofStage n C) (ofStage n A) (ofStage n C) z₁ z₂ a b with
    ⟨_, _, ⟨_, _, hAnti, hJPhi, _, _, _⟩, ⟨_, _, _, _, hSigSq⟩,
     ⟨hInvSMul, _, _, hBoostDef, hBoostNorm, hRotNorm⟩⟩
  refine ⟨?_, ?_, ?_, hAnti, hJPhi, hSigSq, hInvSMul, hBoostDef, hBoostNorm, hRotNorm⟩
  · rw [← hMapInvS bMap P, ← hMapInvS (ofStage n) P]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hMapBoost bMap P A C, ← hMapBoost (ofStage n) P A C]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hMapRot bMap P A C, ← hMapRot (ofStage n) P A C]
    exact directLimitOf_bondMap stageBond n m hnm _

/-- **Inductive-Colimit Kantor Triple Product, 5-Graded BdG Anomaly Generators, &
Operator Cyclotomic Characteristic Polynomials (`limit_kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge`)**:
For any finite stage `n ≤ m`, idempotent `P : Stage n` (`P * P = P`), and `A C D X : Stage n`:
1. Both `bMap = bondMap stageBond n m hnm` and `ofStage n` intertwine `bdgUpperAnomaly`,
   `bdgLowerAnomaly`, `opKantorTriple`, and `opKantorAnomaly`, with exact stage-bonding coherence
   in `Limit`;
2. At `Limit`, the lifted operators `Pinf = ofStage n P`, `Ainf = ofStage n A`, `Cinf = ofStage n C`,
   `Dinf = ofStage n D`, `Xinf = ofStage n X` satisfy the Kantor 5-grade adjoint cubic equation
   `ad_S³ - 4 • ad_S = 0`, the Grade `+2` / `-2` anomaly splitting of `[evenGrade Pinf Dinf, genJ Pinf Ainf Cinf]`,
   and the exact zero-shell operator cyclotomic characteristic equations `opCharPolyPhi6 = 0`,
   `opCharPolyPhi3 = 0`, and `opCharPolyTransfer = 0`. -/
theorem limit_kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge
    {n m : ℕ} (hnm : n ≤ m) {P : Stage n} (hP : P * P = P) (A C D X : Stage n) :
    let bMap := bondMap stageBond n m hnm
    let Pinf := ofStage n P
    let Ainf := ofStage n A
    let Cinf := ofStage n C
    let Dinf := ofStage n D
    let Xinf := ofStage n X
    let Sinf := invS Pinf
    ofStage m (bdgUpperAnomaly (bMap P) (bMap D) (bMap A)) = bdgUpperAnomaly Pinf Dinf Ainf ∧
    ofStage m (bdgLowerAnomaly (bMap P) (bMap D) (bMap C)) = bdgLowerAnomaly Pinf Dinf Cinf ∧
    comm Sinf (comm Sinf (comm Sinf Xinf)) - (4 : ℤ) • comm Sinf Xinf = 0 ∧
    comm (evenGrade Pinf Dinf) (genJ Pinf Ainf Cinf) =
      bdgUpperAnomaly Pinf Dinf Ainf + bdgLowerAnomaly Pinf Dinf Cinf ∧
    comm Sinf (bdgUpperAnomaly Pinf Dinf Ainf) =
      (2 : ℤ) • bdgUpperAnomaly Pinf Dinf Ainf ∧
    comm Sinf (bdgLowerAnomaly Pinf Dinf Cinf) =
      -(2 : ℤ) • bdgLowerAnomaly Pinf Dinf Cinf ∧
    opKantorTriple (conePlus Pinf Ainf) (coneMinus Pinf Cinf) (conePlus Pinf Ainf) =
      (2 : ℤ) • (genV Pinf Ainf Cinf * conePlus Pinf Ainf) ∧
    opKantorAnomaly (conePlus Pinf Ainf) (coneMinus Pinf Cinf) 1 =
      genSig Pinf Ainf Cinf ∧
    opKantorAnomaly (conePlus Pinf Ainf) (coneMinus Pinf Cinf) Sinf =
      -genV Pinf Ainf Cinf ∧
    opCharPolyPhi6 Pinf Ainf Cinf (peirceTransferJ Pinf Ainf Cinf) = 0 ∧
    opCharPolyPhi3 Pinf Ainf Cinf (cubeRootOp Pinf Ainf Cinf) = 0 ∧
    opCharPolyTransfer Pinf Ainf Cinf (peirceTransfer Pinf Ainf Cinf) = 0 := by
  dsimp only
  let bMap := bondMap stageBond n m hnm
  have hPinf : ofStage n P * ofStage n P = ofStage n P :=
    map_idempotent (ofStage n) hP
  have hMapUp : ∀ {B E : Type} [Ring B] [Ring E] (f : B →+* E) (P₀ D₀ A₀ : B),
      f (bdgUpperAnomaly P₀ D₀ A₀) = bdgUpperAnomaly (f P₀) (f D₀) (f A₀) := by
    intro B E _ _ f P₀ D₀ A₀
    simp only [bdgUpperAnomaly, map_sub, map_mul, map_one, map_conePlus]
  have hMapLow : ∀ {B E : Type} [Ring B] [Ring E] (f : B →+* E) (P₀ D₀ C₀ : B),
      f (bdgLowerAnomaly P₀ D₀ C₀) = bdgLowerAnomaly (f P₀) (f D₀) (f C₀) := by
    intro B E _ _ f P₀ D₀ C₀
    simp only [bdgLowerAnomaly, map_sub, map_mul, map_one, map_coneMinus]
  rcases kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge
      hPinf (ofStage n A) (ofStage n C) (ofStage n D) (ofStage n X) with
    ⟨⟨_, _, _, _, _, hCubic⟩,
     ⟨hSplitJ, _, hEigUp, hEigLow⟩,
     ⟨hTriplePlus, _, hAnom1, hAnomS⟩,
     ⟨hPhi6, _, hPhi3, _, hTrans, _, _, _⟩⟩
  refine ⟨?_, ?_, hCubic, hSplitJ, hEigUp, hEigLow,
    hTriplePlus, hAnom1, hAnomS, hPhi6, hPhi3, hTrans⟩
  · rw [← hMapUp bMap P D A, ← hMapUp (ofStage n) P D A]
    exact directLimitOf_bondMap stageBond n m hnm _
  · rw [← hMapLow bMap P D C, ← hMapLow (ofStage n) P D C]
    exact directLimitOf_bondMap stageBond n m hnm _

/-! ## Finite Hilbert–Schmidt realization of the Peirce Jordan energy

The Dirichlet spectral-gap owner works with sums of squared Hilbert-space
operator images, while the colimit owner uses the normalized trace pairing
with the two-sided Jordan action.  The identity below is the finite matrix
bridge between those forms: for `V = R R* + R* R`, the Jordan energy is the
sum of the four left/right multiplication energies generated by `R` and
`R*`.  It is an equality of the actual matrix forms and makes no gap or
uniformity claim by itself.
-/

/-- The Peirce Jordan quadratic form is exactly the Hilbert–Schmidt energy of
the four left/right multiplication actions generated by `R` and its adjoint.
The identity is valid at every finite matrix stage and retains all
noncommutative cross-ordering. -/
theorem normalizedTrace_jordan_gram_eq_left_right_energy
    (n : ℕ) (R X : Stage n) :
    normalizedTrace n
        (star X *
          ((R * star R + star R * R) * X + X * (R * star R + star R * R))) =
      normalizedTrace n
        (star (star R * X) * (star R * X) +
          star (R * X) * (R * X) +
          star (X * R) * (X * R) +
          star (X * star R) * (X * star R)) := by
  have hcyc₁ : Matrix.trace (star X * R * star R * X) =
      Matrix.trace (star (star R * X) * (star R * X)) := by
    simp only [star_mul, star_star, mul_assoc]
  have hcyc₂ : Matrix.trace (star X * star R * R * X) =
      Matrix.trace (star (R * X) * (R * X)) := by
    simp only [star_mul, mul_assoc]
  have hcyc₃ : Matrix.trace (star X * X * R * star R) =
      Matrix.trace (star (X * R) * (X * R)) := by
    calc
      Matrix.trace (star X * X * R * star R) =
          Matrix.trace ((star X * X * R) * star R) := by congr 1
      _ = Matrix.trace (star R * (star X * X * R)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (star (X * R) * (X * R)) := by
        simp only [star_mul, mul_assoc]
  have hcyc₄ : Matrix.trace (star X * X * star R * R) =
      Matrix.trace (star (X * star R) * (X * star R)) := by
    calc
      Matrix.trace (star X * X * star R * R) =
          Matrix.trace ((star X * X * star R) * R) := by congr 1
      _ = Matrix.trace (R * (star X * X * star R)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (star (X * star R) * (X * star R)) := by
        simp only [star_mul, star_star, mul_assoc]
  unfold normalizedTrace
  congr 1
  rw [show star X * ((R * star R + star R * R) * X +
      X * (R * star R + star R * R)) =
      star X * R * star R * X + star X * star R * R * X +
        star X * X * R * star R + star X * X * star R * R by noncomm_ring]
  have htraceSum : Matrix.trace
      (star X * R * star R * X +
        (star X * star R * R * X +
          (star X * X * R * star R + star X * X * star R * R))) =
      Matrix.trace (star X * R * star R * X) +
        (Matrix.trace (star X * star R * R * X) +
          (Matrix.trace (star X * X * R * star R) +
            Matrix.trace (star X * X * star R * R))) := by
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  have htraceEnergy : Matrix.trace
      (star (star R * X) * (star R * X) +
        (star (R * X) * (R * X) +
          (star (X * R) * (X * R) +
            star (X * star R) * (X * star R)))) =
      Matrix.trace (star (star R * X) * (star R * X)) +
        (Matrix.trace (star (R * X) * (R * X)) +
          (Matrix.trace (star (X * R) * (X * R)) +
            Matrix.trace (star (X * star R) * (X * star R)))) := by
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  calc
    Matrix.trace (star X * R * star R * X + star X * star R * R * X +
        star X * X * R * star R + star X * X * star R * R) =
        Matrix.trace (star X * R * star R * X +
          (star X * star R * R * X +
            (star X * X * R * star R + star X * X * star R * R))) := by
      congr 1; abel
    _ = Matrix.trace (star X * R * star R * X) +
        (Matrix.trace (star X * star R * R * X) +
          (Matrix.trace (star X * X * R * star R) +
            Matrix.trace (star X * X * star R * R))) := htraceSum
    _ = Matrix.trace (star (star R * X) * (star R * X)) +
        (Matrix.trace (star (R * X) * (R * X)) +
          (Matrix.trace (star (X * R) * (X * R)) +
            Matrix.trace (star (X * star R) * (X * star R)))) := by
      rw [hcyc₁, hcyc₂, hcyc₃, hcyc₄]
    _ = Matrix.trace (star (star R * X) * (star R * X) +
        (star (R * X) * (R * X) +
          (star (X * R) * (X * R) +
            star (X * star R) * (X * star R)))) := htraceEnergy.symm
    _ = Matrix.trace (star (star R * X) * (star R * X) +
        star (R * X) * (R * X) + star (X * R) * (X * R) +
          star (X * star R) * (X * star R)) := by
      congr 1; abel

end ColimitPeirceBdGAndPositivity

end InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
