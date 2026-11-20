/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
import InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Clifford.HestenesDirac

/-!
# Doubled Minkowski / Chiral Krein Bridge for Circular Split-Octonion Yang–Mills

This module constructs the explicit typed bridges connecting the circular
split-octonion Peirce carrier, the real doubled chiral Krein frame, the
double-Minkowski Pauli spinor soldering, the noncommutative operator-valued
Peirce tetraktys, exterior-algebra gauge connections and self-dual Yang–Mills
identities, and inductive star-ring colimits:

1. **Doubled Minkowski / Chiral Krein Carrier & Metric**:
   Constructs explicit linear equivalences
   `circularCoordToKreinFrame : Coordinate ≃ₗ[ℝ] KreinFrame4` and
   `zornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4` from the circular
   Peirce basis (`SplitOctonionEllCircularPeirceBasis`) to `KreinFrame4`
   (`RealDoubledChiralKreinFrame`), proves exact transport of the 8 circular
   Peirce basis vectors onto `±plusFrame` / `±minusFrame`, proves the bilinear
   and quadratic metric soldering `chiralKreinForm v v = 2 * wittNorm v` and its
   match with `pauliSolder2x2` determinant difference (`doubleMinkowskiSolder`),
   and specializes the Minkowski dual-connection compatibility theorem with
   `minkowskiEta4 = diag(1, -1, -1, -1)`.
2. **Chiral Sheet Projectors, Grading, & Sheet Flip**:
   Proves `zornToKreinFrame` intertwines left multiplication by `uPlus`, `uMinus`,
   and `lUnit` with `leftChiralProjector`, `rightChiralProjector`, and
   `chirality` (`gamma5`), and intertwines the signed chiral reflection
   `signedKappa` with `sheetFlip` (`etaChiral`).
3. **Two Chiral Weyl Representations & Noncommutative Peirce Channels**:
   Maps circular coordinates `Coordinate` to two noncommuting $2 \times 2$
   complex Weyl matrix blocks `(weylUpperMat, weylLowerMat)` via `pauliSolder2x2`,
   computes their exact ordered products in terms of `wittNorm`,
   `chiralBoostVec`, and `chiralVorticityVec` (`[U, L]` proportional to
   `chiralVorticityVec`), exhibits a noncommuting two-sheet witness, and embeds
   them into `TetraktysZornYangMillsBridge.SheetAlgebra (Fin 2 → ℂ)`.
4. **Gauge Connection, Curvature, Yang–Mills Equation, Action & Colimit Transport**:
   Constructs $4 \times 4$ block-off-diagonal connections over both `ℂ` and
   `ExteriorAlgebra ℂ V`, instantiates
   `SelfDualConnectionCurvatureYangMillsBridge.peirce_defect_connection_curvature_and_yang_mills_bridge`,
   proves the Hilbert–Schmidt action identity
   `Tr(Fᴴ F) = 4 (N(x)² + ‖boost‖² + ‖vorticity‖²)` and the two-sheet
   vorticity action gap `Tr(Fᴴ F) - Tr(F²) = 8 ‖vorticity‖²`, and transports
   the entire Peirce tetraktys along `TwoSheetedYangMillsInductiveColimit.InductiveStarColimitCone`.

## Scope boundary
These are finite-dimensional, noncommutative algebraic, Krein-bilinear,
exterior-algebra, and star-ring inductive-colimit theorems. They do not claim
smooth 4-manifold PDE existence, analytic continuum limit convergence as lattice
spacing `a → 0`, or construction of a nonzero differential `d` satisfying
`matrixExteriorDerivative d A = peirceGradingDeriv P A`.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Matrix ComplexConjugate

namespace InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian

abbrev CanonicalZorn := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn
abbrev Coordinate := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.Coordinate
abbrev FourSpace := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
abbrev KreinFrame4 := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-! ## Real Hestenes carrier on both circular Peirce sheets

The Hestenes realification is used here as a real matrix carrier with its
complex structure represented by an endomorphism.  Each of the two four-entry
circular Peirce sheets is sent to its own realified Minkowski slice.  This
keeps all eight basis coordinates and does not change scalars to `ℂ`.
-/

open InfoGeometry.Clifford.HestenesDirac

/-- Real circular Pauli soldering on a single four-coordinate sheet.  The
ordered basis is `(1, σ₁, ε, σ₃)`, with `ε` the real elliptic generator; no
complex scalar field is used. -/
def realPauliSoldering (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v 0 + v 3, v 1 - v 2;
     v 1 + v 2, v 0 - v 3]

/-- Inverse coordinate readout for the real circular Pauli soldering. -/
def realPauliUnsoldering (A : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → ℝ :=
  ![(A 0 0 + A 1 1) / 2,
    (A 0 1 + A 1 0) / 2,
    (A 1 0 - A 0 1) / 2,
    (A 0 0 - A 1 1) / 2]

/-- The four real coordinates on one Peirce sheet are linearly equivalent to
real `2 × 2` matrices, with the real elliptic generator represented by
`[[0,-1],[1,0]]`. -/
def realPauliSolderingEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := realPauliSoldering
  invFun := realPauliUnsoldering
  left_inv v := by
    funext i
    fin_cases i <;> simp [realPauliSoldering, realPauliUnsoldering]
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realPauliSoldering, realPauliUnsoldering] <;> ring
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realPauliSoldering] <;> ring
  map_smul' r v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realPauliSoldering] <;> ring

/-- The real soldering's ordered basis is the scalar, hyperbolic, elliptic,
and longitudinal Pauli frame `(σ₀, σ₁, ε, σ₃)`. -/
theorem realPauliSoldering_basis_table :
    realPauliSoldering (Pi.single 0 (1 : ℝ)) = !![1, 0; 0, 1] ∧
    realPauliSoldering (Pi.single 1 (1 : ℝ)) = !![0, 1; 1, 0] ∧
    realPauliSoldering (Pi.single 2 (1 : ℝ)) = !![0, -1; 1, 0] ∧
    realPauliSoldering (Pi.single 3 (1 : ℝ)) = !![1, 0; 0, -1] := by
  simp [realPauliSoldering]

/-- Determinant of the real Pauli soldering.  Its signature is `(2,2)`; the
physical `(1,3)` interval is supplied by the real `4 × 4` Hestenes slice and
its complex-structure operator, not by this single-sheet `2 × 2` determinant. -/
theorem realPauliSoldering_det (v : Fin 4 → ℝ) :
    (realPauliSoldering v).det =
      v 0 ^ 2 - v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2 := by
  simp [realPauliSoldering, Matrix.det_fin_two]
  ring

/-- First four entries of the ordered circular Peirce coordinates, in the
Hestenes real spacetime coordinate order `(t,x,y,z)`. -/
def circularPlusHestenesCoordinates (x : Coordinate) : MinkowskiCoordinates :=
  ⟨x 0, x 1, x 2, x 3⟩

/-- Last four entries of the ordered circular Peirce coordinates, in the
Hestenes real spacetime coordinate order `(t,x,y,z)`. -/
def circularMinusHestenesCoordinates (x : Coordinate) : MinkowskiCoordinates :=
  ⟨x 4, x 5, x 6, x 7⟩

/-- Realified Hestenes spacetime matrices for both four-coordinate sheets of
the full eight-dimensional circular Peirce carrier. -/
def circularHestenesRealification (x : Coordinate) : RealMatrix4 × RealMatrix4 :=
  (concreteSpacetimeMatrix (circularPlusHestenesCoordinates x),
   concreteSpacetimeMatrix (circularMinusHestenesCoordinates x))

/-- Each sheet of the eight-coordinate carrier lands in the real symmetric
slice commuting with the real complex-structure operator `J`; the Pfaffian
readout recovers the signed Minkowski interval on each sheet. -/
theorem circularHestenesRealification_laws (x : Coordinate) :
    (let cPlus := circularPlusHestenesCoordinates x
     let cMinus := circularMinusHestenesCoordinates x
     let (SPlus, SMinus) := circularHestenesRealification x
     SPlus * concreteComplexStructureJ = concreteComplexStructureJ * SPlus ∧
     SMinus * concreteComplexStructureJ = concreteComplexStructureJ * SMinus ∧
     RealMatrix4.transpose SPlus = SPlus ∧
     RealMatrix4.transpose SMinus = SMinus ∧
     RealMatrix4.pfaffianSkew4 (SPlus * concreteComplexStructureJ) = -cPlus.interval ∧
     RealMatrix4.pfaffianSkew4 (SMinus * concreteComplexStructureJ) = -cMinus.interval) := by
  dsimp [circularHestenesRealification]
  exact ⟨concreteSpacetimeMatrix_commutes_with_J _,
    concreteSpacetimeMatrix_commutes_with_J _,
    concreteSpacetimeMatrix_symmetric _, concreteSpacetimeMatrix_symmetric _,
    concrete_pfaffianSJ_eq_neg_interval _, concrete_pfaffianSJ_eq_neg_interval _⟩

/-! ## 1. Doubled Minkowski / Chiral Krein Carrier & Metric Soldering -/

/-- Upper 4-vector coordinates `(x₀, x₁, x₂, x₃)` in the circular Peirce basis. -/
def circularPlusCoord (x : Coordinate) : Fin 4 → ℝ :=
  ![x 0, x 1, x 2, x 3]

/-- Signed lower 4-vector coordinates `(x₄, -x₅, -x₆, -x₇)` matching the Minkowski signature `(+,-,-,-)` under `chiralKreinForm`. -/
def circularSignedMinusCoord (x : Coordinate) : Fin 4 → ℝ :=
  ![x 4, -x 5, -x 6, -x 7]

private lemma circularPlusCoord_add (x y : Coordinate) :
    circularPlusCoord (x + y) = circularPlusCoord x + circularPlusCoord y := by
  ext i
  fin_cases i <;> rfl

private lemma circularPlusCoord_smul (c : ℝ) (x : Coordinate) :
    circularPlusCoord (c • x) = c • circularPlusCoord x := by
  ext i
  fin_cases i <;> rfl

private lemma circularSignedMinusCoord_add (x y : Coordinate) :
    circularSignedMinusCoord (x + y) =
      circularSignedMinusCoord x + circularSignedMinusCoord y := by
  ext i
  fin_cases i <;> simp [circularSignedMinusCoord] <;> ring

private lemma circularSignedMinusCoord_smul (c : ℝ) (x : Coordinate) :
    circularSignedMinusCoord (c • x) = c • circularSignedMinusCoord x := by
  ext i
  fin_cases i <;> simp [circularSignedMinusCoord, smul_eq_mul]

private lemma fourSpace_basis_expansion (v : FourSpace) :
    ∑ j : Fin 4, inner ℝ (frameBasis j) v • frameBasis j = v := by
  have hbasis := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  have hcoord (j : Fin 4) :
      (EuclideanSpace.basisFun (Fin 4) ℝ).repr v j = inner ℝ (frameBasis j) v := by
    have hid := congrArg (fun z : FourSpace => inner ℝ (frameBasis j) z) hbasis
    rw [inner_sum] at hid
    have hid' :
        ∑ k : Fin 4,
            ((EuclideanSpace.basisFun (Fin 4) ℝ).repr v k) *
              inner ℝ (frameBasis j) (frameBasis k) =
          inner ℝ (frameBasis j) v := by
      simpa [frameBasis, real_inner_smul_right] using hid
    simp_rw [frameBasis_inner] at hid'
    simp at hid'
    exact hid'
  calc
    ∑ j : Fin 4, inner ℝ (frameBasis j) v • frameBasis j =
        ∑ j : Fin 4, (EuclideanSpace.basisFun (Fin 4) ℝ).repr v j • frameBasis j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcoord j]
    _ = v := by simpa [frameBasis] using hbasis

private lemma withLp_fst_sum_plus_minus (a b : Fin 4 → ℝ) :
    WithLp.fst (∑ j : Fin 4, a j • plusFrame j + ∑ j : Fin 4, b j • minusFrame j) =
      ∑ j : Fin 4, a j • frameBasis j := by
  change (InfoGeometry.Krein.fst_L (E := FourSpace))
      (∑ j : Fin 4, a j • plusFrame j + ∑ j : Fin 4, b j • minusFrame j) = _
  rw [map_add, map_sum, map_sum]
  have h1 : ∀ j : Fin 4, (InfoGeometry.Krein.fst_L (E := FourSpace)) (a j • plusFrame j) =
      a j • frameBasis j := by
    intro j
    rw [map_smul]
    rfl
  have h2 : ∑ j : Fin 4, (InfoGeometry.Krein.fst_L (E := FourSpace)) (b j • minusFrame j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul]
    simp [minusFrame, InfoGeometry.Krein.fst_L]
  simp_rw [h1]
  rw [h2, add_zero]

private lemma withLp_snd_sum_plus_minus (a b : Fin 4 → ℝ) :
    WithLp.snd (∑ j : Fin 4, a j • plusFrame j + ∑ j : Fin 4, b j • minusFrame j) =
      ∑ j : Fin 4, b j • frameBasis j := by
  change (InfoGeometry.Krein.snd_L (E := FourSpace))
      (∑ j : Fin 4, a j • plusFrame j + ∑ j : Fin 4, b j • minusFrame j) = _
  rw [map_add, map_sum, map_sum]
  have h1 : ∑ j : Fin 4, (InfoGeometry.Krein.snd_L (E := FourSpace)) (a j • plusFrame j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul]
    simp [plusFrame, InfoGeometry.Krein.snd_L]
  have h2 : ∀ j : Fin 4, (InfoGeometry.Krein.snd_L (E := FourSpace)) (b j • minusFrame j) =
      b j • frameBasis j := by
    intro j
    rw [map_smul]
    rfl
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun j _ => h2 j

/-- Explicit linear isomorphism identifying circular Peirce coordinates `Fin 8 → ℝ`
with the real doubled chiral Krein carrier `KreinFrame4 = WithLp 2 (FourSpace × FourSpace)`. -/
def circularCoordToKreinFrame : Coordinate ≃ₗ[ℝ] KreinFrame4 where
  toFun x :=
    ∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
      ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j
  invFun u := fun i => match i with
    | 0 => inner ℝ (frameBasis 0) (WithLp.fst u)
    | 1 => inner ℝ (frameBasis 1) (WithLp.fst u)
    | 2 => inner ℝ (frameBasis 2) (WithLp.fst u)
    | 3 => inner ℝ (frameBasis 3) (WithLp.fst u)
    | 4 => inner ℝ (frameBasis 0) (WithLp.snd u)
    | 5 => -inner ℝ (frameBasis 1) (WithLp.snd u)
    | 6 => -inner ℝ (frameBasis 2) (WithLp.snd u)
    | 7 => -inner ℝ (frameBasis 3) (WithLp.snd u)
    | _ => 0
  left_inv x := by
    ext i
    have hfst := withLp_fst_sum_plus_minus (circularPlusCoord x) (circularSignedMinusCoord x)
    have hsnd := withLp_snd_sum_plus_minus (circularPlusCoord x) (circularSignedMinusCoord x)
    have hPlus (k : Fin 4) :
        inner ℝ (frameBasis k)
            (WithLp.fst (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
              ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)) =
          circularPlusCoord x k := by
      rw [hfst, inner_sum]
      simp_rw [real_inner_smul_right, frameBasis_inner]
      simp
    have hMinus (k : Fin 4) :
        inner ℝ (frameBasis k)
            (WithLp.snd (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
              ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)) =
          circularSignedMinusCoord x k := by
      rw [hsnd, inner_sum]
      simp_rw [real_inner_smul_right, frameBasis_inner]
      simp
    dsimp only
    fin_cases i
    · simpa [circularPlusCoord] using hPlus 0
    · simpa [circularPlusCoord] using hPlus 1
    · simpa [circularPlusCoord] using hPlus 2
    · simpa [circularPlusCoord] using hPlus 3
    · simpa [circularSignedMinusCoord] using hMinus 0
    · have h : circularSignedMinusCoord x 1 = -x 5 := by simp [circularSignedMinusCoord]
      rw [show (match (⟨5, by decide⟩ : Fin 8) with
          | 0 => inner ℝ (frameBasis 0) (WithLp.fst _)
          | 1 => inner ℝ (frameBasis 1) (WithLp.fst _)
          | 2 => inner ℝ (frameBasis 2) (WithLp.fst _)
          | 3 => inner ℝ (frameBasis 3) (WithLp.fst _)
          | 4 => inner ℝ (frameBasis 0) (WithLp.snd _)
          | 5 => -inner ℝ (frameBasis 1) (WithLp.snd _)
          | 6 => -inner ℝ (frameBasis 2) (WithLp.snd _)
          | 7 => -inner ℝ (frameBasis 3) (WithLp.snd _)
          | _ => 0) =
          -inner ℝ (frameBasis 1) (WithLp.snd (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
            ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)) from rfl]
      rw [hMinus 1, h, neg_neg]
      rfl
    · have h : circularSignedMinusCoord x 2 = -x 6 := by simp [circularSignedMinusCoord]
      rw [show (match (⟨6, by decide⟩ : Fin 8) with
          | 0 => inner ℝ (frameBasis 0) (WithLp.fst _)
          | 1 => inner ℝ (frameBasis 1) (WithLp.fst _)
          | 2 => inner ℝ (frameBasis 2) (WithLp.fst _)
          | 3 => inner ℝ (frameBasis 3) (WithLp.fst _)
          | 4 => inner ℝ (frameBasis 0) (WithLp.snd _)
          | 5 => -inner ℝ (frameBasis 1) (WithLp.snd _)
          | 6 => -inner ℝ (frameBasis 2) (WithLp.snd _)
          | 7 => -inner ℝ (frameBasis 3) (WithLp.snd _)
          | _ => 0) =
          -inner ℝ (frameBasis 2) (WithLp.snd (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
            ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)) from rfl]
      rw [hMinus 2, h, neg_neg]
      rfl
    · have h : circularSignedMinusCoord x 3 = -x 7 := by simp [circularSignedMinusCoord]
      rw [show (match (⟨7, by decide⟩ : Fin 8) with
          | 0 => inner ℝ (frameBasis 0) (WithLp.fst _)
          | 1 => inner ℝ (frameBasis 1) (WithLp.fst _)
          | 2 => inner ℝ (frameBasis 2) (WithLp.fst _)
          | 3 => inner ℝ (frameBasis 3) (WithLp.fst _)
          | 4 => inner ℝ (frameBasis 0) (WithLp.snd _)
          | 5 => -inner ℝ (frameBasis 1) (WithLp.snd _)
          | 6 => -inner ℝ (frameBasis 2) (WithLp.snd _)
          | 7 => -inner ℝ (frameBasis 3) (WithLp.snd _)
          | _ => 0) =
          -inner ℝ (frameBasis 3) (WithLp.snd (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
            ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)) from rfl]
      rw [hMinus 3, h, neg_neg]
      rfl
  right_inv u := by
    apply InfoGeometry.Krein.DoubledSpace.ext
    · rw [withLp_fst_sum_plus_minus]
      rw [Fin.sum_univ_four]
      have h := fourSpace_basis_expansion (WithLp.fst u)
      rw [Fin.sum_univ_four] at h
      simpa [circularPlusCoord] using h
    · rw [withLp_snd_sum_plus_minus]
      rw [Fin.sum_univ_four]
      have h := fourSpace_basis_expansion (WithLp.snd u)
      rw [Fin.sum_univ_four] at h
      simpa [circularSignedMinusCoord] using h
  map_add' x y := by
    rw [circularPlusCoord_add, circularSignedMinusCoord_add]
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    rw [circularPlusCoord_smul, circularSignedMinusCoord_smul]
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, smul_add,
      Finset.smul_sum, smul_smul]

/-- Explicit linear equivalence identifying the split-octonion carrier `CanonicalZorn`
with `KreinFrame4` through the circular Peirce basis. -/
def zornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  coordinateEquiv.trans circularCoordToKreinFrame

@[simp] theorem zornToKreinFrame_apply (X : CanonicalZorn) :
    zornToKreinFrame X = circularCoordToKreinFrame (coordinateEquiv X) :=
  rfl

theorem circularCoordToKreinFrame_single_0 :
    circularCoordToKreinFrame (Pi.single 0 1) = plusFrame 0 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_1 :
    circularCoordToKreinFrame (Pi.single 1 1) = plusFrame 1 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_2 :
    circularCoordToKreinFrame (Pi.single 2 1) = plusFrame 2 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_3 :
    circularCoordToKreinFrame (Pi.single 3 1) = plusFrame 3 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_4 :
    circularCoordToKreinFrame (Pi.single 4 1) = minusFrame 0 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_5 :
    circularCoordToKreinFrame (Pi.single 5 1) = -minusFrame 1 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_6 :
    circularCoordToKreinFrame (Pi.single 6 1) = -minusFrame 2 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

theorem circularCoordToKreinFrame_single_7 :
    circularCoordToKreinFrame (Pi.single 7 1) = -minusFrame 3 := by
  simp [circularCoordToKreinFrame, circularPlusCoord, circularSignedMinusCoord, Fin.sum_univ_four]

/-- Transport of all 8 circular Peirce basis vectors into `KreinFrame4`. -/
theorem zornToKreinFrame_frame (i : Fin 8) :
    zornToKreinFrame (frame i) =
      match i with
      | 0 => plusFrame 0
      | 1 => plusFrame 1
      | 2 => plusFrame 2
      | 3 => plusFrame 3
      | 4 => minusFrame 0
      | 5 => -minusFrame 1
      | 6 => -minusFrame 2
      | 7 => -minusFrame 3
      | _ => 0 := by
  rw [zornToKreinFrame_apply, coordinateEquiv_apply_frame]
  fin_cases i
  · exact circularCoordToKreinFrame_single_0
  · exact circularCoordToKreinFrame_single_1
  · exact circularCoordToKreinFrame_single_2
  · exact circularCoordToKreinFrame_single_3
  · exact circularCoordToKreinFrame_single_4
  · exact circularCoordToKreinFrame_single_5
  · exact circularCoordToKreinFrame_single_6
  · exact circularCoordToKreinFrame_single_7

/-- Bilinear compatibility: under `circularCoordToKreinFrame`, the off-block
chiral Krein form `chiralKreinForm` evaluates to the polarized split-octonion Witt
form (twice the polarized `(4,4)` inner product). -/
theorem chiralKreinForm_circularCoordToKreinFrame (x y : Coordinate) :
    chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame y) =
      x 0 * y 4 + y 0 * x 4 -
        (x 1 * y 5 + y 1 * x 5 + x 2 * y 6 + y 2 * x 6 + x 3 * y 7 + y 3 * x 7) := by
  have hx : circularCoordToKreinFrame x =
      InfoGeometry.Krein.to_doubled
        (∑ j : Fin 4, circularPlusCoord x j • frameBasis j)
        (∑ j : Fin 4, circularSignedMinusCoord x j • frameBasis j) := by
    apply InfoGeometry.Krein.DoubledSpace.ext
    · exact withLp_fst_sum_plus_minus (circularPlusCoord x) (circularSignedMinusCoord x)
    · exact withLp_snd_sum_plus_minus (circularPlusCoord x) (circularSignedMinusCoord x)
  have hy : circularCoordToKreinFrame y =
      InfoGeometry.Krein.to_doubled
        (∑ j : Fin 4, circularPlusCoord y j • frameBasis j)
        (∑ j : Fin 4, circularSignedMinusCoord y j • frameBasis j) := by
    apply InfoGeometry.Krein.DoubledSpace.ext
    · exact withLp_fst_sum_plus_minus (circularPlusCoord y) (circularSignedMinusCoord y)
    · exact withLp_snd_sum_plus_minus (circularPlusCoord y) (circularSignedMinusCoord y)
  rw [hx, hy, chiralKreinForm_to_doubled]
  simp_rw [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    frameBasis_inner]
  simp [Fin.sum_univ_four, circularPlusCoord, circularSignedMinusCoord]
  ring

/-- Quadratic compatibility: on the diagonal, `chiralKreinForm` equals `2 * wittNorm`. -/
theorem chiralKreinForm_diag_eq_two_wittNorm (x : Coordinate) :
    chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) =
      2 * wittNorm x := by
  rw [chiralKreinForm_circularCoordToKreinFrame]
  simp only [wittNorm]
  ring

/-- Combined metric and Pauli soldering bridge: on any two-sheeted spacetime point
`v = symmSection t x1 x2 x3 + antiSection tau y1 y2 y3`, half the `chiralKreinForm`
agrees simultaneously with `wittNorm v`, the `(1,3) ⊕ (3,1)` Minkowski norm difference,
and the determinant difference of the two `2 × 2` Pauli soldering blocks. -/
theorem doubledMinkowski_krein_pauli_soldering_bridge
    (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    let v := symmSection t x1 x2 x3 + antiSection tau y1 y2 y3
    (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame v) (circularCoordToKreinFrame v) =
      (t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) - (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) ∧
    (pauliSolder2x2 t x1 x2 x3).det - (pauliSolder2x2 tau y1 y2 y3).det =
      (((1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
          (circularCoordToKreinFrame v) (circularCoordToKreinFrame v) : ℝ) : ℂ) := by
  intro v
  have hk : (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
      (circularCoordToKreinFrame v) (circularCoordToKreinFrame v) = wittNorm v := by
    rw [chiralKreinForm_diag_eq_two_wittNorm]
    ring
  refine ⟨?_, ?_⟩
  · rw [hk]
    exact wittNorm_direct_sum t x1 x2 x3 tau y1 y2 y3
  · rw [hk, doubleMinkowskiSolder_det_diff, wittNorm_eq_circularWitt]

/-- Canonical $4 \times 4$ Lorentzian Minkowski signature matrix `diag(1, -1, -1, -1)`. -/
def minkowskiEta4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

theorem minkowskiEta4_mul_self : minkowskiEta4 * minkowskiEta4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiEta4, Matrix.mul_apply, Fin.sum_univ_four]

theorem minkowskiEta4_det : minkowskiEta4.det = -1 := by
  simp [minkowskiEta4, Matrix.det_diagonal, Fin.prod_univ_four]

theorem isUnit_minkowskiEta4_det : IsUnit minkowskiEta4.det := by
  rw [minkowskiEta4_det]
  exact isUnit_one.neg

/-- Uniqueness of the metric-dual chiral connection with respect to the
invertible Minkowski metric `minkowskiEta4`. -/
theorem minkowski_dualConnection_unique
    (omegaPlus omegaMinus : Matrix (Fin 4) (Fin 4) ℝ)
    (hcompat : omegaPlus.transpose * minkowskiEta4 + minkowskiEta4 * omegaMinus = 0) :
    omegaMinus = dualConnectionWithMetric minkowskiEta4 omegaPlus :=
  dualConnectionWithMetric_unique minkowskiEta4 omegaPlus omegaMinus
    isUnit_minkowskiEta4_det hcompat

/-- Explicit noncommutativity witness for `Matrix (Fin 4) (Fin 4) ℝ`: the Minkowski
signature `minkowskiEta4` fails to commute with the boost off-diagonal matrix unit. -/
theorem minkowskiEta4_mat4R_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  refine ⟨minkowskiEta4, B, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [minkowskiEta4, B, Matrix.mul_apply] at h01
  norm_num at h01

/-! ## 2. Chiral Sheet Projectors, Grading, and Sheet-Flip Intertwining -/

private lemma zornToKreinFrame_uPlus_frame (i : Fin 8) :
    zornToKreinFrame (leftMultiplication uPlus (frame i)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame i)) := by
  fin_cases i
  · change zornToKreinFrame (leftMultiplication uPlus (frame 0)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 0))
    have hL : leftMultiplication uPlus (frame 0) = frame 0 := by
      simpa [frame] using leftMultiplication_uPlus_frame 0
    rw [hL, zornToKreinFrame_frame]
    simp [plusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 1)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 1))
    have hL : leftMultiplication uPlus (frame 1) = frame 1 := by
      simpa [frame] using leftMultiplication_uPlus_frame 1
    rw [hL, zornToKreinFrame_frame]
    simp [plusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 2)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 2))
    have hL : leftMultiplication uPlus (frame 2) = frame 2 := by
      simpa [frame] using leftMultiplication_uPlus_frame 2
    rw [hL, zornToKreinFrame_frame]
    simp [plusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 3)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 3))
    have hL : leftMultiplication uPlus (frame 3) = frame 3 := by
      simpa [frame] using leftMultiplication_uPlus_frame 3
    rw [hL, zornToKreinFrame_frame]
    simp [plusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 4)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 4))
    have hL : leftMultiplication uPlus (frame 4) = 0 := by
      simpa using leftMultiplication_uPlus_frame 4
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [minusFrame, leftChiralProjector_to_doubled]
    apply InfoGeometry.Krein.DoubledSpace.ext <;> rfl
  · change zornToKreinFrame (leftMultiplication uPlus (frame 5)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 5))
    have hL : leftMultiplication uPlus (frame 5) = 0 := by
      simpa using leftMultiplication_uPlus_frame 5
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [minusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 6)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 6))
    have hL : leftMultiplication uPlus (frame 6) = 0 := by
      simpa using leftMultiplication_uPlus_frame 6
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [minusFrame, leftChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uPlus (frame 7)) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame (frame 7))
    have hL : leftMultiplication uPlus (frame 7) = 0 := by
      simpa using leftMultiplication_uPlus_frame 7
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [minusFrame, leftChiralProjector_to_doubled]

private lemma zornToKreinFrame_uMinus_frame (i : Fin 8) :
    zornToKreinFrame (leftMultiplication uMinus (frame i)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame i)) := by
  fin_cases i
  · change zornToKreinFrame (leftMultiplication uMinus (frame 0)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 0))
    have hL : leftMultiplication uMinus (frame 0) = 0 := by
      simpa using leftMultiplication_uMinus_frame 0
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [plusFrame, rightChiralProjector_to_doubled]
    apply InfoGeometry.Krein.DoubledSpace.ext <;> rfl
  · change zornToKreinFrame (leftMultiplication uMinus (frame 1)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 1))
    have hL : leftMultiplication uMinus (frame 1) = 0 := by
      simpa using leftMultiplication_uMinus_frame 1
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [plusFrame, rightChiralProjector_to_doubled]
    apply InfoGeometry.Krein.DoubledSpace.ext <;> rfl
  · change zornToKreinFrame (leftMultiplication uMinus (frame 2)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 2))
    have hL : leftMultiplication uMinus (frame 2) = 0 := by
      simpa using leftMultiplication_uMinus_frame 2
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [plusFrame, rightChiralProjector_to_doubled]
    apply InfoGeometry.Krein.DoubledSpace.ext <;> rfl
  · change zornToKreinFrame (leftMultiplication uMinus (frame 3)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 3))
    have hL : leftMultiplication uMinus (frame 3) = 0 := by
      simpa using leftMultiplication_uMinus_frame 3
    rw [hL, map_zero, zornToKreinFrame_frame]
    simp [plusFrame, rightChiralProjector_to_doubled]
    apply InfoGeometry.Krein.DoubledSpace.ext <;> rfl
  · change zornToKreinFrame (leftMultiplication uMinus (frame 4)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 4))
    have hL : leftMultiplication uMinus (frame 4) = frame 4 := by
      simpa [frame] using leftMultiplication_uMinus_frame 4
    rw [hL, zornToKreinFrame_frame]
    simp [minusFrame, rightChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uMinus (frame 5)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 5))
    have hL : leftMultiplication uMinus (frame 5) = frame 5 := by
      simpa [frame] using leftMultiplication_uMinus_frame 5
    rw [hL, zornToKreinFrame_frame]
    simp [minusFrame, rightChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uMinus (frame 6)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 6))
    have hL : leftMultiplication uMinus (frame 6) = frame 6 := by
      simpa [frame] using leftMultiplication_uMinus_frame 6
    rw [hL, zornToKreinFrame_frame]
    simp [minusFrame, rightChiralProjector_to_doubled]
  · change zornToKreinFrame (leftMultiplication uMinus (frame 7)) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame (frame 7))
    have hL : leftMultiplication uMinus (frame 7) = frame 7 := by
      simpa [frame] using leftMultiplication_uMinus_frame 7
    rw [hL, zornToKreinFrame_frame]
    simp [minusFrame, rightChiralProjector_to_doubled]

/-- `zornToKreinFrame` intertwines left multiplication by the positive axial
idempotent `uPlus` with `leftChiralProjector`. -/
theorem zornToKreinFrame_intertwines_uPlus (X : CanonicalZorn) :
    zornToKreinFrame (leftMultiplication uPlus X) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame X) := by
  rw [← sum_coord_smul_frame X]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zornToKreinFrame_uPlus_frame i]

/-- `zornToKreinFrame` intertwines left multiplication by the negative axial
idempotent `uMinus` with `rightChiralProjector`. -/
theorem zornToKreinFrame_intertwines_uMinus (X : CanonicalZorn) :
    zornToKreinFrame (leftMultiplication uMinus X) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame X) := by
  rw [← sum_coord_smul_frame X]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zornToKreinFrame_uMinus_frame i]

private lemma leftChiral_sub_rightChiral (u : KreinFrame4) :
    leftChiralProjector (E := FourSpace) u - rightChiralProjector (E := FourSpace) u =
      chirality u := by
  apply InfoGeometry.Krein.DoubledSpace.ext
  · simp [leftChiralProjector, rightChiralProjector,
      chirality, gamma5, InfoGeometry.Krein.spectral_epsilon]
    module
  · simp [leftChiralProjector, rightChiralProjector,
      chirality, gamma5, InfoGeometry.Krein.spectral_epsilon]
    module

/-- `zornToKreinFrame` intertwines left multiplication by the distinguished
split-octonion axis `lUnit` with the doubled chiral grading `chirality` (`gamma5`). -/
theorem zornToKreinFrame_intertwines_chirality (X : CanonicalZorn) :
    zornToKreinFrame (leftMultiplication lUnit X) =
      chirality (zornToKreinFrame X) := by
  have hl : lUnit * X = uPlus * X - uMinus * X := by
    rw [← uPlus_sub_uMinus, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.sub_mul]
  change zornToKreinFrame (lUnit * X) = _
  rw [hl, map_sub]
  change zornToKreinFrame (leftMultiplication uPlus X) -
      zornToKreinFrame (leftMultiplication uMinus X) = _
  rw [zornToKreinFrame_intertwines_uPlus, zornToKreinFrame_intertwines_uMinus,
    leftChiral_sub_rightChiral]

/-- Signed chiral sheet-exchange involution on circular Peirce coordinates:
exchanges `(x₀, x₁, x₂, x₃)` with `(x₄, -x₅, -x₆, -x₇)` so that spatial signs
preserve the Minkowski signature under `circularCoordToKreinFrame`. -/
def signedKappa : Coordinate →ₗ[ℝ] Coordinate where
  toFun x := ![x 4, -x 5, -x 6, -x 7, x 0, -x 1, -x 2, -x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]

theorem signedKappa_involutive (x : Coordinate) :
    signedKappa (signedKappa x) = x := by
  ext i
  fin_cases i <;> simp [signedKappa]

/-- `circularCoordToKreinFrame` intertwines `signedKappa` with `sheetFlip` (`etaChiral`). -/
theorem circularCoordToKreinFrame_intertwines_sheetFlip (x : Coordinate) :
    circularCoordToKreinFrame (signedKappa x) =
      sheetFlip (circularCoordToKreinFrame x) := by
  have hP : circularPlusCoord (signedKappa x) = circularSignedMinusCoord x := by
    ext j
    fin_cases j <;> simp [circularPlusCoord, circularSignedMinusCoord, signedKappa]
  have hM : circularSignedMinusCoord (signedKappa x) = circularPlusCoord x := by
    ext j
    fin_cases j <;> simp [circularPlusCoord, circularSignedMinusCoord, signedKappa]
  have hL :
      circularCoordToKreinFrame (signedKappa x) =
        ∑ j : Fin 4, circularSignedMinusCoord x j • plusFrame j +
          ∑ j : Fin 4, circularPlusCoord x j • minusFrame j := by
    change ∑ j : Fin 4, circularPlusCoord (signedKappa x) j • plusFrame j +
        ∑ j : Fin 4, circularSignedMinusCoord (signedKappa x) j • minusFrame j = _
    rw [hP, hM]
  rw [hL]
  change _ = sheetFlip (∑ j : Fin 4, circularPlusCoord x j • plusFrame j +
      ∑ j : Fin 4, circularSignedMinusCoord x j • minusFrame j)
  rw [map_add, map_sum, map_sum]
  simp_rw [map_smul, sheetFlip_plusFrame, sheetFlip_minusFrame]
  rw [add_comm]

/-! ## 3. Two Chiral Weyl Representations & Noncommutative Peirce Channels -/

/-- Upper (`+`) chiral $2 \times 2$ complex Weyl matrix representation of circular coordinates. -/
def weylUpperMat (x : Coordinate) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliSolder2x2 (x 0) (x 1) (x 2) (x 3)

/-- Lower (`-`) chiral $2 \times 2$ complex Weyl matrix representation of circular coordinates,
incorporating the opposite spatial sign matching `minkowskiEta4` and `circularSignedMinusCoord`. -/
def weylLowerMat (x : Coordinate) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliSolder2x2 (x 4) (-x 5) (-x 6) (-x 7)

theorem weylUpperMat_uPlus : weylUpperMat (coordinateEquiv uPlus) = σ0 := by
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]

theorem weylUpperMat_rootPlus (a : Fin 3) :
    weylUpperMat (coordinateEquiv (rootPlus a)) =
      match a with
      | 0 => σ1
      | 1 => σ2
      | 2 => σ3 := by
  fin_cases a <;> dsimp
  · have hc : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 1
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  · have hc : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 2
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  · have hc : coordinateEquiv (rootPlus 2) = Pi.single 3 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 3
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]

theorem weylLowerMat_uMinus : weylLowerMat (coordinateEquiv uMinus) = σ0 := by
  have hc : coordinateEquiv uMinus = Pi.single 4 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 4
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]

theorem weylLowerMat_rootMinus (a : Fin 3) :
    weylLowerMat (coordinateEquiv (rootMinus a)) =
      match a with
      | 0 => -σ1
      | 1 => -σ2
      | 2 => -σ3 := by
  fin_cases a <;> dsimp
  · have hc : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 5
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  · have hc : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 6
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  · have hc : coordinateEquiv (rootMinus 2) = Pi.single 7 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 7
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]

/-- Noncommutativity witness within the upper Weyl representation: the image of
`rootPlus 0` and `rootPlus 1` obeys `[σ₁, σ₂] = 2i σ₃ ≠ 0`. -/
theorem weylUpperMat_rootPlus_comm :
    weylUpperMat (coordinateEquiv (rootPlus 0)) * weylUpperMat (coordinateEquiv (rootPlus 1)) -
        weylUpperMat (coordinateEquiv (rootPlus 1)) * weylUpperMat (coordinateEquiv (rootPlus 0)) =
      (2 * Complex.I) • weylUpperMat (coordinateEquiv (rootPlus 2)) ∧
    weylUpperMat (coordinateEquiv (rootPlus 0)) * weylUpperMat (coordinateEquiv (rootPlus 1)) ≠
      weylUpperMat (coordinateEquiv (rootPlus 1)) * weylUpperMat (coordinateEquiv (rootPlus 0)) := by
  rw [weylUpperMat_rootPlus 0, weylUpperMat_rootPlus 1, weylUpperMat_rootPlus 2]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [σ1, σ2, σ3, Complex.ext_iff] <;> ring
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [σ1, σ2, Complex.ext_iff] at h00
    norm_num at h00

/-- Boost 3-vector coupling time/scale slots `(x₀, x₄)` with spatial circular channels. -/
def chiralBoostVec (x : Coordinate) : Fin 3 → ℝ :=
  ![x 4 * x 1 - x 0 * x 5, x 4 * x 2 - x 0 * x 6, x 4 * x 3 - x 0 * x 7]

/-- Non-Abelian cross-product vorticity 3-vector `(u × (-v))` between the two circular chiral sectors. -/
def chiralVorticityVec (x : Coordinate) : Fin 3 → ℝ :=
  ![x 2 * x 7 - x 3 * x 6, x 3 * x 5 - x 1 * x 7, x 1 * x 6 - x 2 * x 5]

/-- Euclidean norm squared of a 3-vector in `Fin 3 → ℝ`. -/
def normSq3 (v : Fin 3 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

theorem weylUpperMat_mul_weylLowerMat (x : Coordinate) :
    weylUpperMat x * weylLowerMat x =
      solder
        ( (wittNorm x : ℂ)
        , (chiralBoostVec x 0 : ℂ) - Complex.I * (chiralVorticityVec x 0 : ℂ)
        , (chiralBoostVec x 1 : ℂ) - Complex.I * (chiralVorticityVec x 1 : ℂ)
        , (chiralBoostVec x 2 : ℂ) - Complex.I * (chiralVorticityVec x 2 : ℂ) ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [weylUpperMat, weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3,
      wittNorm, chiralBoostVec, chiralVorticityVec, Matrix.mul_apply] <;>
    ring

theorem weylLowerMat_mul_weylUpperMat (x : Coordinate) :
    weylLowerMat x * weylUpperMat x =
      solder
        ( (wittNorm x : ℂ)
        , (chiralBoostVec x 0 : ℂ) + Complex.I * (chiralVorticityVec x 0 : ℂ)
        , (chiralBoostVec x 1 : ℂ) + Complex.I * (chiralVorticityVec x 1 : ℂ)
        , (chiralBoostVec x 2 : ℂ) + Complex.I * (chiralVorticityVec x 2 : ℂ) ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [weylUpperMat, weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3,
      wittNorm, chiralBoostVec, chiralVorticityVec, Matrix.mul_apply] <;>
    ring

theorem weylChannel_commutator_eq_vorticity (x : Coordinate) :
    weylUpperMat x * weylLowerMat x - weylLowerMat x * weylUpperMat x =
      (-2 * Complex.I) •
        solder (0, (chiralVorticityVec x 0 : ℂ), (chiralVorticityVec x 1 : ℂ),
          (chiralVorticityVec x 2 : ℂ)) := by
  rw [weylUpperMat_mul_weylLowerMat, weylLowerMat_mul_weylUpperMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [solder, σ0, σ1, σ2, σ3] <;>
    ring

/-- Noncommutativity between upper and lower chiral blocks at `x = rootPlus 0 + rootMinus 1`. -/
theorem weylChannel_noncomm_sheet_blocks_witness :
    let x : Coordinate := coordinateEquiv (rootPlus 0 + rootMinus 1)
    weylUpperMat x * weylLowerMat x ≠ weylLowerMat x * weylUpperMat x := by
  intro x h
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 1
  have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 6
  have hx : x = Pi.single 1 1 + Pi.single 6 1 := by
    change coordinateEquiv (rootPlus 0 + rootMinus 1) = Pi.single 1 1 + Pi.single 6 1
    rw [LinearEquiv.map_add, hc1, hc6]
  have h00 := congrFun (congrFun h 0) 0
  simp [hx, weylUpperMat, weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3,
    Matrix.mul_apply, Complex.ext_iff] at h00
  norm_num at h00

/-- Explicit noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℂ` realized by
circular Weyl channel operators `weylUpperMat` on `rootPlus 0` and `rootPlus 1`. -/
theorem weylUpperMat_mat2C_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨weylUpperMat (coordinateEquiv (rootPlus 0)),
    weylUpperMat (coordinateEquiv (rootPlus 1)),
    weylUpperMat_rootPlus_comm.2⟩

/-- Clifford closure on the symmetric fixed section: along `symmSection t x1 x2 x3`,
the two chiral blocks cancel vorticity/boost and square to the Lorentzian scalar invariant. -/
theorem weylChannel_symmSection_clifford_closure (t x1 x2 x3 : ℝ) :
    let v := symmSection t x1 x2 x3
    weylUpperMat v * weylLowerMat v = (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) : ℝ) : ℂ) • 1 ∧
    weylLowerMat v * weylUpperMat v = (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) : ℝ) : ℂ) • 1 := by
  intro v
  have hv1 : weylUpperMat v * weylLowerMat v =
      solder (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) : ℝ) : ℂ), 0, 0, 0) := by
    rw [weylUpperMat_mul_weylLowerMat]
    simp [v, symmSection, wittNorm, chiralBoostVec, chiralVorticityVec]
    ring_nf
  have hv2 : weylLowerMat v * weylUpperMat v =
      solder (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) : ℝ) : ℂ), 0, 0, 0) := by
    rw [weylLowerMat_mul_weylUpperMat]
    simp [v, symmSection, wittNorm, chiralBoostVec, chiralVorticityVec]
    ring_nf
  have hs : solder (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) : ℝ) : ℂ), 0, 0, 0) =
      (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [solder, σ0, σ1, σ2, σ3]
  exact ⟨hv1.trans hs, hv2.trans hs⟩

/-- Operator-valued two-sheet carrier element in `SheetAlgebra (Fin 2 → ℂ)`
induced by the circular Weyl representations. -/
def circularSheetOperator (x : Coordinate) : SheetAlgebra (Fin 2 → ℂ) :=
  !![0, Matrix.toLin' (weylUpperMat x);
     Matrix.toLin' (weylLowerMat x), 0]

/-- Explicit causal operator coordinates of `circularSheetOperator x`. -/
def circularCausalCoords (x : Coordinate) :
    InfoGeometry.Clifford.CausalOperatorCoordinates (Operator (Fin 2 → ℂ)) :=
  InfoGeometry.Clifford.causalCoordinates (circularSheetOperator x)

theorem reconstruct_circularCausalCoords (x : Coordinate) :
    InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x) =
      circularSheetOperator x :=
  InfoGeometry.Clifford.reconstruct_causalCoordinates (circularSheetOperator x)

/-- Complete ordered Peirce tetraktys table on `SheetAlgebra (Fin 2 → ℂ)`
driven by circular Weyl channels `x` and `y` without any commutation assumption. -/
theorem circularSheet_tetraktys_table (x y : Coordinate) :
    genPhi (firstSheetProjection (W := Fin 2 → ℂ))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords y)) =
      !![0, Matrix.toLin' (weylUpperMat x); Matrix.toLin' (weylLowerMat y), 0] ∧
    genJ (firstSheetProjection (W := Fin 2 → ℂ))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords y)) =
      !![0, Matrix.toLin' (weylUpperMat x); -(Matrix.toLin' (weylLowerMat y)), 0] ∧
    genV (firstSheetProjection (W := Fin 2 → ℂ))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords y)) =
      !![Matrix.toLin' (weylUpperMat x * weylLowerMat y), 0;
         0, Matrix.toLin' (weylLowerMat y * weylUpperMat x)] ∧
    genSig (firstSheetProjection (W := Fin 2 → ℂ))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords y)) =
      !![Matrix.toLin' (weylUpperMat x * weylLowerMat y), 0;
         0, -(Matrix.toLin' (weylLowerMat y * weylUpperMat x))] := by
  have hP : firstSheetProjection (W := Fin 2 → ℂ) * firstSheetProjection (W := Fin 2 → ℂ) =
      firstSheetProjection (W := Fin 2 → ℂ) := firstSheetProjection_idempotent
  have hUpper (z : Coordinate) :
      conePlus (firstSheetProjection (W := Fin 2 → ℂ))
          (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords z)) =
        !![0, Matrix.toLin' (weylUpperMat z); 0, 0] := by
    rw [reconstruct_circularCausalCoords z]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conePlus, firstSheetProjection, circularSheetOperator, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  have hLower (z : Coordinate) :
      coneMinus (firstSheetProjection (W := Fin 2 → ℂ))
          (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords z)) =
        !![0, 0; Matrix.toLin' (weylLowerMat z), 0] := by
    rw [reconstruct_circularCausalCoords z]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coneMinus, firstSheetProjection, circularSheetOperator, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  have hMulUL :
      Matrix.toLin' (weylUpperMat x) * Matrix.toLin' (weylLowerMat y) =
        Matrix.toLin' (weylUpperMat x * weylLowerMat y) :=
    (Matrix.toLin'_mul (weylUpperMat x) (weylLowerMat y)).symm
  have hMulLU :
      Matrix.toLin' (weylLowerMat y) * Matrix.toLin' (weylUpperMat x) =
        Matrix.toLin' (weylLowerMat y * weylUpperMat x) :=
    (Matrix.toLin'_mul (weylLowerMat y) (weylUpperMat x)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [genPhi, hUpper x, hLower y]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [genJ, hUpper x, hLower y]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [genV, anticomm, hUpper x, hLower y]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hMulUL, hMulLU]
  · rw [genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm, hUpper x, hLower y]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hMulUL, hMulLU]

/-! ## 4. Gauge Connection, Curvature, Yang–Mills Equation, Action & Colimit Transport -/

/-- Block-off-diagonal $4 \times 4$ embedding over any ring `R`. -/
def chiralOffBlock4 {R : Type*} [Ring R] (u l : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![0,     0,     u 0 0, u 0 1;
     0,     0,     u 1 0, u 1 1;
     l 0 0, l 0 1, 0,     0;
     l 1 0, l 1 1, 0,     0]

/-- Block-diagonal $4 \times 4$ embedding over any ring `R`. -/
def chiralDiagBlock4 {R : Type*} [Ring R] (d1 d2 : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![d1 0 0, d1 0 1, 0,      0;
     d1 1 0, d1 1 1, 0,      0;
     0,      0,      d2 0 0, d2 0 1;
     0,      0,      d2 1 0, d2 1 1]

/-- First-sheet chiral projector `P = diag(1, 1, 0, 0)` over any ring `R`. -/
def chiralProj4 (R : Type*) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  chiralDiagBlock4 (1 : Matrix (Fin 2) (Fin 2) R) (0 : Matrix (Fin 2) (Fin 2) R)

theorem chiralProj4_idempotent (R : Type*) [Ring R] :
    chiralProj4 R * chiralProj4 R = chiralProj4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProj4, chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_four]

theorem chiralOffBlock4_mul {R : Type*} [Ring R]
    (u l u' l' : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 u l * chiralOffBlock4 u' l' =
      chiralDiagBlock4 (u * l') (l * u') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralOffBlock4, chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two]

/-- Noncommutativity witness over any nontrivial ring `R` in `Matrix (Fin 2) (Fin 2) R`. -/
theorem mat2R_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Noncommutativity witness over any nontrivial ring `R` in `Matrix (Fin 4) (Fin 4) R`,
realized by the chiral projector `chiralProj4 R` and off-diagonal block `chiralOffBlock4 1 1`. -/
theorem chiralProj4_mat4R_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 4) (Fin 4) R, A * B ≠ B * A := by
  refine ⟨chiralProj4 R, chiralOffBlock4 (1 : Matrix (Fin 2) (Fin 2) R) 1, ?_⟩
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [chiralProj4, chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four] at h02

theorem chiralDiagBlock4_mul {R : Type*} [Ring R]
    (a1 a2 b1 b2 : Matrix (Fin 2) (Fin 2) R) :
    chiralDiagBlock4 a1 a2 * chiralDiagBlock4 b1 b2 =
      chiralDiagBlock4 (a1 * b1) (a2 * b2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem chiralDiagBlock4_trace {R : Type*} [Ring R]
    (d1 d2 : Matrix (Fin 2) (Fin 2) R) :
    (chiralDiagBlock4 d1 d2).trace = d1.trace + d2.trace := by
  simp [chiralDiagBlock4, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_two, add_assoc]

theorem chiralDiagBlock4_conjTranspose {R : Type*} [Ring R] [StarRing R]
    (d1 d2 : Matrix (Fin 2) (Fin 2) R) :
    (chiralDiagBlock4 d1 d2)ᴴ = chiralDiagBlock4 d1ᴴ d2ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4, Matrix.conjTranspose_apply]

theorem conePlus_chiralOffBlock4 {R : Type*} [Ring R] (u l : Matrix (Fin 2) (Fin 2) R) :
    conePlus (chiralProj4 R) (chiralOffBlock4 u l) = chiralOffBlock4 u 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conePlus, chiralProj4, chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.sub_apply, Matrix.one_apply]

theorem coneMinus_chiralOffBlock4 {R : Type*} [Ring R] (u l : Matrix (Fin 2) (Fin 2) R) :
    coneMinus (chiralProj4 R) (chiralOffBlock4 u l) = chiralOffBlock4 0 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMinus, chiralProj4, chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.sub_apply, Matrix.one_apply]

theorem genPhi_chiralOffBlock4 {R : Type*} [Ring R] (u l : Matrix (Fin 2) (Fin 2) R) :
    genPhi (chiralProj4 R) (chiralOffBlock4 u l) (chiralOffBlock4 u l) =
      chiralOffBlock4 u l := by
  rw [genPhi, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-- Complex $4 \times 4$ chiral projector `P = diag(1, 1, 0, 0)`. -/
def chiralProjMat4 : Matrix (Fin 4) (Fin 4) ℂ :=
  chiralProj4 ℂ

theorem chiralProjMat4_idempotent : chiralProjMat4 * chiralProjMat4 = chiralProjMat4 :=
  chiralProj4_idempotent ℂ

theorem chiralProjMat4_star : star chiralProjMat4 = chiralProjMat4 := by
  change (chiralDiagBlock4 (1 : Matrix (Fin 2) (Fin 2) ℂ) 0)ᴴ =
    chiralDiagBlock4 1 0
  rw [chiralDiagBlock4_conjTranspose]
  simp

/-- Circular complex $4 \times 4$ gauge connection combining the upper and lower Weyl blocks. -/
def circularConnectionMat4 (x : Coordinate) : Matrix (Fin 4) (Fin 4) ℂ :=
  chiralOffBlock4 (weylUpperMat x) (weylLowerMat x)

/-- Explicit $4 \times 4$ complex noncommutativity witness realized by the chiral projector
`chiralProjMat4` and circular connection `circularConnectionMat4 (coordinateEquiv uPlus)`. -/
theorem circularConnectionMat4_mat4C_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  refine ⟨chiralProjMat4, circularConnectionMat4 (coordinateEquiv uPlus), ?_⟩
  intro h
  have h02 := congrFun (congrFun h 0) 2
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  simp [chiralProjMat4, chiralProj4, chiralDiagBlock4, circularConnectionMat4,
    chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four] at h02
  rw [hc] at h02
  simp [weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3] at h02

/-- Exterior-algebra upper chiral $2 \times 2$ block driven by 4 circular forms `ω₀..ω₃`. -/
def weylUpperExt {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a0 a1 a2 a3 : ExteriorAlgebra ℂ V) :
    Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ V) :=
  !![a0 + a3, a1 - Complex.I • a2; a1 + Complex.I • a2, a0 - a3]

/-- Exterior-algebra lower chiral $2 \times 2$ block driven by 4 circular forms `ω₄..ω₇` with Minkowski spatial sign. -/
def weylLowerExt {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b0 b1 b2 b3 : ExteriorAlgebra ℂ V) :
    Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ V) :=
  !![b0 - b3, -b1 + Complex.I • b2; -b1 - Complex.I • b2, b0 + b3]

/-- $4 \times 4$ chiral projector valued in `ExteriorAlgebra ℂ V`. -/
def chiralExteriorProj4 (V : Type*) [AddCommGroup V] [Module ℂ V] :
    Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ V) :=
  chiralProj4 (ExteriorAlgebra ℂ V)

/-- Exterior-algebra $4 \times 4$ gauge connection built directly from 8 circular form components. -/
def circularGaugeConnection4 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ω : Fin 8 → ExteriorAlgebra ℂ V) :
    Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ V) :=
  chiralOffBlock4
    (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3))
    (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7))

/-- On scalar 0-forms `ω i = algebraMap ℂ (ExteriorAlgebra ℂ V) (x i)`,
`circularGaugeConnection4 ω` specializes entrywise to `circularConnectionMat4 x`. -/
theorem circularGaugeConnection4_evalScalar {V : Type*} [AddCommGroup V] [Module ℂ V]
    (x : Coordinate) :
    circularGaugeConnection4 (fun i => algebraMap ℂ (ExteriorAlgebra ℂ V) (x i : ℂ)) =
      (circularConnectionMat4 x).map (algebraMap ℂ (ExteriorAlgebra ℂ V)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularGaugeConnection4, circularConnectionMat4, chiralOffBlock4,
      weylUpperExt, weylLowerExt, weylUpperMat, weylLowerMat, pauliSolder2x2,
      solder_explicit] <;>
    simp only [Algebra.smul_def, ← map_neg, ← map_mul, ← map_add, ← map_sub] <;>
    exact congrArg (algebraMap ℂ (ExteriorAlgebra ℂ V)) (by ring)

/-- Yang–Mills connection curvature and self-dual Bianchi bridge instantiated on
the circular split-octonion $4 \times 4$ gauge connection `circularGaugeConnection4 ω`. -/
theorem circularGaugeConnection4_yang_mills_bridge
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (star d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (ω : Fin 8 → ExteriorAlgebra ℂ V)
    (X : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ V)) :
    let P := chiralExteriorProj4 V
    let A := circularGaugeConnection4 ω
    genPhi P A A = A ∧
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
    (matrixExteriorDerivative d A = peirceGradingDeriv P A →
      curvatureFromConnection d A = genJ P A A + genV P A A ∧
      evenGrade P (curvatureFromConnection d A) = genV P A A) ∧
    curvatureFromConnection 0 A = genV P A A ∧
    covariantDerivative A 0 (genV P A A) = 0 ∧
    (isSelfDualCurvature star (genV P A A) →
      covariantDerivative A 0 (matrixHodgeStar star (curvatureFromConnection 0 A)) = 0) := by
  intro P A
  have hP : P * P = P := chiralProj4_idempotent (ExteriorAlgebra ℂ V)
  have hPhi : genPhi P A A = A :=
    genPhi_chiralOffBlock4 (weylUpperExt (ω 0) (ω 1) (ω 2) (ω 3))
      (weylLowerExt (ω 4) (ω 5) (ω 6) (ω 7))
  have hBridge := peirce_defect_connection_curvature_and_yang_mills_bridge
    (R := ℂ) (V := V) (n := 4) star d hP A A X
  rw [hPhi] at hBridge
  exact ⟨hPhi, hBridge.1, hBridge.2.1, hBridge.2.2.1, hBridge.2.2.2.1, hBridge.2.2.2.2⟩

/-- Purely algebraic curvature `F = A²` of the circular complex $4 \times 4$ connection. -/
def circularCurvatureMat4 (x : Coordinate) : Matrix (Fin 4) (Fin 4) ℂ :=
  circularConnectionMat4 x * circularConnectionMat4 x

theorem circularCurvatureMat4_eq_genV (x : Coordinate) :
    circularCurvatureMat4 x =
      genV chiralProjMat4 (circularConnectionMat4 x) (circularConnectionMat4 x) := by
  unfold chiralProjMat4 circularConnectionMat4
  rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
    circularCurvatureMat4, circularConnectionMat4, chiralOffBlock4_mul,
    chiralOffBlock4_mul, chiralOffBlock4_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]

theorem circularCurvatureMat4_eq_diagBlocks (x : Coordinate) :
    circularCurvatureMat4 x =
      chiralDiagBlock4 (weylUpperMat x * weylLowerMat x) (weylLowerMat x * weylUpperMat x) :=
  chiralOffBlock4_mul (weylUpperMat x) (weylLowerMat x) (weylUpperMat x) (weylLowerMat x)

/-- Curvature trace reads out both the split-octonion Witt norm and the doubled Krein form. -/
theorem circularCurvatureMat4_trace (x : Coordinate) :
    (circularCurvatureMat4 x).trace = 4 * (wittNorm x : ℂ) ∧
    (circularCurvatureMat4 x).trace =
      2 * (chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) : ℂ) := by
  have htr : (circularCurvatureMat4 x).trace = 4 * (wittNorm x : ℂ) := by
    rw [circularCurvatureMat4_eq_diagBlocks, chiralDiagBlock4_trace,
      weylUpperMat_mul_weylLowerMat, weylLowerMat_mul_weylUpperMat,
      solder_trace_formula, solder_trace_formula]
    ring
  refine ⟨htr, ?_⟩
  rw [htr, chiralKreinForm_diag_eq_two_wittNorm]
  push_cast
  ring

private lemma solder_complexVec_hilbertSchmidt_trace (n : ℝ) (b v : Fin 3 → ℝ) :
    let S := solder ((n : ℂ), (b 0 : ℂ) + Complex.I * (v 0 : ℂ),
      (b 1 : ℂ) + Complex.I * (v 1 : ℂ), (b 2 : ℂ) + Complex.I * (v 2 : ℂ))
    (Sᴴ * S).trace = ((2 * (n ^ 2 + normSq3 b + normSq3 v) : ℝ) : ℂ) := by
  intro S
  have hS : S = !![((n + b 2 : ℝ) : ℂ) + Complex.I * ((v 2 : ℝ) : ℂ),
      ((b 0 + v 1 : ℝ) : ℂ) + Complex.I * ((v 0 - b 1 : ℝ) : ℂ);
      ((b 0 - v 1 : ℝ) : ℂ) + Complex.I * ((b 1 + v 0 : ℝ) : ℂ),
      ((n - b 2 : ℝ) : ℂ) + Complex.I * ((-v 2 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [S, solder, σ0, σ1, σ2, σ3] <;>
      ring
  rw [hS]
  apply Complex.ext <;>
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      normSq3, sq] <;>
    ring

private lemma solder_complexVec_square_trace (n : ℝ) (b v : Fin 3 → ℝ) :
    let S := solder ((n : ℂ), (b 0 : ℂ) + Complex.I * (v 0 : ℂ),
      (b 1 : ℂ) + Complex.I * (v 1 : ℂ), (b 2 : ℂ) + Complex.I * (v 2 : ℂ))
    (S * S).trace =
      ((2 * (n ^ 2 + normSq3 b - normSq3 v) : ℝ) : ℂ) +
        4 * Complex.I * ((b 0 * v 0 + b 1 * v 1 + b 2 * v 2 : ℝ) : ℂ) := by
  intro S
  have hS : S = !![((n + b 2 : ℝ) : ℂ) + Complex.I * ((v 2 : ℝ) : ℂ),
      ((b 0 + v 1 : ℝ) : ℂ) + Complex.I * ((v 0 - b 1 : ℝ) : ℂ);
      ((b 0 - v 1 : ℝ) : ℂ) + Complex.I * ((b 1 + v 0 : ℝ) : ℂ),
      ((n - b 2 : ℝ) : ℂ) + Complex.I * ((-v 2 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [S, solder, σ0, σ1, σ2, σ3] <;>
      ring
  rw [hS]
  apply Complex.ext <;>
    simp [Matrix.trace, Fin.sum_univ_two, normSq3, sq] <;>
    ring

private lemma weylUpper_neg_vec (x : Coordinate) :
    solder
        ( (wittNorm x : ℂ)
        , (chiralBoostVec x 0 : ℂ) - Complex.I * (chiralVorticityVec x 0 : ℂ)
        , (chiralBoostVec x 1 : ℂ) - Complex.I * (chiralVorticityVec x 1 : ℂ)
        , (chiralBoostVec x 2 : ℂ) - Complex.I * (chiralVorticityVec x 2 : ℂ) ) =
      solder
        ( (wittNorm x : ℂ)
        , (chiralBoostVec x 0 : ℂ) + Complex.I * ((-chiralVorticityVec x) 0 : ℂ)
        , (chiralBoostVec x 1 : ℂ) + Complex.I * ((-chiralVorticityVec x) 1 : ℂ)
        , (chiralBoostVec x 2 : ℂ) + Complex.I * ((-chiralVorticityVec x) 2 : ℂ) ) := by
  simp [Pi.neg_apply, Complex.ofReal_neg, mul_neg, sub_eq_add_neg]

private lemma normSq3_neg (v : Fin 3 → ℝ) : normSq3 (-v) = normSq3 v := by
  simp [normSq3, Pi.neg_apply]

/-- Exact Hilbert–Schmidt Yang–Mills action identity: sums the squared magnitudes of the
Witt norm, chiral boost 3-vector, and non-Abelian chiral vorticity 3-vector across both sheets. -/
theorem circularCurvatureMat4_hilbertSchmidt_action (x : Coordinate) :
    ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace =
      ((4 * (wittNorm x ^ 2 + normSq3 (chiralBoostVec x) + normSq3 (chiralVorticityVec x)) : ℝ) : ℂ) := by
  rw [circularCurvatureMat4_eq_diagBlocks, chiralDiagBlock4_conjTranspose,
    chiralDiagBlock4_mul, chiralDiagBlock4_trace]
  rw [weylUpperMat_mul_weylLowerMat, weylLowerMat_mul_weylUpperMat, weylUpper_neg_vec]
  rw [solder_complexVec_hilbertSchmidt_trace (wittNorm x) (chiralBoostVec x) (-chiralVorticityVec x)]
  rw [solder_complexVec_hilbertSchmidt_trace (wittNorm x) (chiralBoostVec x) (chiralVorticityVec x)]
  rw [normSq3_neg]
  push_cast
  ring

/-- Exact Chern–Weil / Pontryagin-type quadratic trace across both sheets: the opposite imaginary
cross terms `∓ 4i (boost · vorticity)` cancel between the upper and lower Weyl blocks. -/
theorem circularCurvatureMat4_square_trace (x : Coordinate) :
    (circularCurvatureMat4 x * circularCurvatureMat4 x).trace =
      ((4 * (wittNorm x ^ 2 + normSq3 (chiralBoostVec x) - normSq3 (chiralVorticityVec x)) : ℝ) : ℂ) := by
  rw [circularCurvatureMat4_eq_diagBlocks, chiralDiagBlock4_mul, chiralDiagBlock4_trace]
  rw [weylUpperMat_mul_weylLowerMat, weylLowerMat_mul_weylUpperMat, weylUpper_neg_vec]
  rw [solder_complexVec_square_trace (wittNorm x) (chiralBoostVec x) (-chiralVorticityVec x)]
  rw [solder_complexVec_square_trace (wittNorm x) (chiralBoostVec x) (chiralVorticityVec x)]
  rw [normSq3_neg]
  simp only [Pi.neg_apply, mul_neg]
  push_cast
  ring

/-- Non-Abelian vorticity action gap: the difference between the positive-definite
Hilbert–Schmidt curvature action and the quadratic curvature trace isolates strictly
`8 * ‖chiralVorticityVec x‖²` (which vanishes iff upper and lower chiral blocks commute). -/
theorem circularCurvatureMat4_vorticity_action_gap (x : Coordinate) :
    ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace -
        (circularCurvatureMat4 x * circularCurvatureMat4 x).trace =
      ((8 * normSq3 (chiralVorticityVec x) : ℝ) : ℂ) := by
  rw [circularCurvatureMat4_hilbertSchmidt_action, circularCurvatureMat4_square_trace]
  push_cast
  ring

/-- Star-colimit transport along any `CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone`:
embeds `circularConnectionMat4 x` and its self-adjoint projector `chiralProjMat4` via any
stage `CanonicalTwoSheetedInductiveColimit.StarRingHom` into the inductive star-ring colimit
`B_inf`, preserving all two-sheet operators and one-step cocycle coherence. -/
theorem circularConnection_starColimit_transport
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom (Matrix (Fin 4) (Fin 4) ℂ) (A_tower k))
    (x : Coordinate) :
    let ψ : Matrix (Fin 4) (Fin 4) ℂ →+* B_inf :=
      (cone.toColimit k).toRingHom.comp ι.toRingHom
    ψ chiralProjMat4 * ψ chiralProjMat4 = ψ chiralProjMat4 ∧
    star (ψ chiralProjMat4) = ψ chiralProjMat4 ∧
    CanonicalTwoSheetedInductiveColimit.opElectron
        (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      ψ (circularConnectionMat4 x) ∧
    CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling
        (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      ψ (circularCurvatureMat4 x) ∧
    (cone.toColimit (k + 1)).toRingHom
        ((cone.stepHom k).toRingHom (ι.toRingHom (circularCurvatureMat4 x))) =
      ψ (circularCurvatureMat4 x) ∧
    CanonicalTwoSheetedInductiveColimit.opSpinDipole
        (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      CanonicalTwoSheetedInductiveColimit.opBitGrading (ψ chiralProjMat4) *
        ψ (circularCurvatureMat4 x) := by
  intro ψ
  have hStar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ, ψ (star M) = star (ψ M) := by
    intro M
    change (cone.toColimit k).toRingHom (ι.toRingHom (star M)) =
      star ((cone.toColimit k).toRingHom (ι.toRingHom M))
    rw [ι.map_star', (cone.toColimit k).map_star']
  have hComp := CanonicalTwoSheetedInductiveColimit.star_hom_two_sheeted_operator_identities
    ψ hStar chiralProjMat4 (circularConnectionMat4 x)
    chiralProjMat4_idempotent chiralProjMat4_star
  have hOp := CanonicalTwoSheetedInductiveColimit.starRingHom_intertwines_two_sheeted_operators
    ψ hStar chiralProjMat4 (circularConnectionMat4 x) (circularConnectionMat4 x)
  have hPψ : ψ chiralProjMat4 * ψ chiralProjMat4 = ψ chiralProjMat4 := by
    rw [← map_mul, chiralProjMat4_idempotent]
  have hStarP : star (ψ chiralProjMat4) = ψ chiralProjMat4 := by
    rw [← hStar, chiralProjMat4_star]
  have hElec : CanonicalTwoSheetedInductiveColimit.opElectron
      (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      ψ (circularConnectionMat4 x) := by
    rw [← hOp.2.2.2.1]
    change ψ (genPhi chiralProjMat4 (circularConnectionMat4 x) (circularConnectionMat4 x)) = _
    unfold chiralProjMat4 circularConnectionMat4
    rw [genPhi_chiralOffBlock4]
  have hQuad : CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling
      (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      ψ (circularCurvatureMat4 x) := by
    rw [← hOp.2.2.2.2.2.1]
    change ψ (genV chiralProjMat4 (circularConnectionMat4 x) (circularConnectionMat4 x)) = _
    rw [← circularCurvatureMat4_eq_genV]
  have hCocycle : (cone.toColimit (k + 1)).toRingHom
      ((cone.stepHom k).toRingHom (ι.toRingHom (circularCurvatureMat4 x))) =
      ψ (circularCurvatureMat4 x) := by
    exact cone.compat k (ι.toRingHom (circularCurvatureMat4 x))
  have hSpin : CanonicalTwoSheetedInductiveColimit.opSpinDipole
      (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) =
      CanonicalTwoSheetedInductiveColimit.opBitGrading (ψ chiralProjMat4) *
        ψ (circularCurvatureMat4 x) := by
    have _ := hComp.2.2.2.2.2.1
    change CanonicalTwoSheetedInductiveColimit.opSpinDipole
        (ψ chiralProjMat4) (ψ (circularConnectionMat4 x)) (ψ (circularConnectionMat4 x)) = _
    rw [← hQuad]
    have hP' := hPψ
    dsimp [CanonicalTwoSheetedInductiveColimit.opSpinDipole,
      CanonicalTwoSheetedInductiveColimit.opBitGrading,
      CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling]
    peirce_nf hP'
  exact ⟨hPψ, hStarP, hElec, hQuad, hCocycle, hSpin⟩


end InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
