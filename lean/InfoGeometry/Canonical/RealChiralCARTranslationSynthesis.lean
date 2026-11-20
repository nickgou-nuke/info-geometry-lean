/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.RealGradedZornCARBridge
import InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
import InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
import InfoGeometry.Canonical.SouriauKillingLipschitzBridge
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Quantum.Realification
import InfoGeometry.Quantum.RealificationCategory

/-!
# Shared real carrier synthesis: circular CAR and Peirce translations

Both constructions act on the same real doubled-Krein carrier through the
three-factor Koszul-graded product of real `2 × 2` matrices. At unit time-like
momentum, their anticommutators have the same value, the identity. This is an
operator-level comparison of anticommutators; it does not identify the two
charge pairs term by term.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealChiralCARTranslationSynthesis

open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
open InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
open InfoGeometry.Canonical.SouriauKillingLipschitzBridge
open InfoGeometry.Superalgebra.RealGradedZornCARBridge
open InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.GradedTensorWeylBridge
open Matrix
open scoped TensorProduct GradedTensorProduct

local notation "FourSpace" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
local notation "KreinFrame4" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-! ### Rindler flow transported to the real Majorana Clifford contraction

The Rindler boost is already an isometry of physical real `(1,3)` spacetime,
and the Majorana contraction already represents the corresponding quadratic
form in the genuine three-factor real Koszul tensor. The following bridge
states the resulting operator-level invariant. It asserts equality of
quadratic contractions, not equality of the underlying Clifford vectors. -/

/-- The real Majorana contraction of a Rindler-boosted Minkowski vector has
the same square as the contraction before the boost. This joins the physical
Rindler flow to the actual three-mode real graded-matrix carrier. -/
theorem realMinkowskiMajorana_rindlerBoost_square
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (s : ℝ) :
    realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) ^ 2 =
      realMinkowskiMajorana X ^ 2 := by
  calc
    realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) ^ 2 =
        InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) •
            (1 : realThreeMatrixGradedTensor) := by
          simpa [pow_two] using realMinkowskiMajorana_square
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X •
          (1 : realThreeMatrixGradedTensor) := by
          exact congrArg
            (fun r : ℝ => r • (1 : realThreeMatrixGradedTensor))
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_flow_isometry X s)
    _ = realMinkowskiMajorana X ^ 2 := by
          simpa [pow_two] using (realMinkowskiMajorana_square X).symm

/-! ### Weyl soldering and the real three-mode Majorana contraction

The circular Yang--Mills owner uses two Weyl blocks over `ℂ`, while the
Hestenes/CAR owner uses the real Koszul tensor of three `M₂(ℝ)` factors.  We
identify the shared real Minkowski vector by duplicating its four coordinates
on the two circular sheets, then compare the squares after realification on
`KreinFrame4`.  This is a quadratic Clifford comparison; it does not assert
an equality of the two unsquared matrix representations or use `ℂ` as scalar
field on the doubled carrier.
-/

/-- Put a physical real `(1,3)` vector into both circular chiral sheets. -/
def realMinkowskiCircularCoordinate
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    Coordinate := ![X.t, X.x, X.y, X.z, X.t, X.x, X.y, X.z]

/-- The duplicated circular Witt norm is the physical real Minkowski interval. -/
theorem realMinkowskiCircularCoordinate_wittNorm
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm
        (realMinkowskiCircularCoordinate X) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X := by
  cases X with
  | mk t x y z =>
      simp [realMinkowskiCircularCoordinate,
        InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]; ring

/-! ### Realification of the Yang--Mills operator on the doubled carrier

The source Yang--Mills owner writes its finite connection and curvature as
complex `4 × 4` matrices.  Here the coefficients are realified using the
existing faithful realification owner, with real and imaginary coordinates
identified with the two components of `KreinFrame4`.  The induced phase
operator is proved to be the existing doubled real complex structure. -/

/-- Coordinates on `KreinFrame4` ordered as the real and imaginary blocks of
the realification of a complex four-vector. -/
noncomputable def realificationKreinFrameEquiv :
    (Fin 4 ⊕ Fin 4 → ℝ) ≃ₗ[ℝ] KreinFrame4 where
  toFun x := InfoGeometry.Krein.to_doubled
    (WithLp.toLp 2 (fun i => x (.inl i)))
    (WithLp.toLp 2 (fun i => x (.inr i)))
  invFun u := Sum.elim (fun i => (WithLp.fst u).ofLp i)
    (fun i => (WithLp.snd u).ofLp i)
  left_inv x := by
    funext i
    cases i <;> simp
  right_inv u := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp
  map_add' x y := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp only [InfoGeometry.Krein.to_doubled, WithLp.add_fst, WithLp.add_snd]
    all_goals
      rw [← WithLp.toLp_add]
      congr 1
  map_smul' r x := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp only [InfoGeometry.Krein.to_doubled, WithLp.smul_fst, WithLp.smul_snd]
    all_goals
      rw [← WithLp.toLp_smul]
      congr 1

/-- A complex matrix acting on `ℂ⁴`, transported through realification to a
real-linear endomorphism of the existing doubled Krein carrier. -/
def realifiedCircularMatrixEnd (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Module.End ℝ KreinFrame4 :=
  (realificationKreinFrameEquiv.conjAlgEquiv ℝ)
    (Matrix.toLinAlgEquiv'
      (InfoGeometry.Quantum.Realification.realify A))

/-- Realification and the real coordinate equivalence preserve ordered
matrix composition on `KreinFrame4`. -/
theorem realifiedCircularMatrixEnd_mul
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A * B) =
      realifiedCircularMatrixEnd A * realifiedCircularMatrixEnd B := by
  simp [realifiedCircularMatrixEnd,
    InfoGeometry.Quantum.Realification.realify_mul]

/-- The internal realification phase is exactly the existing doubled real
complex structure after the real/imaginary coordinate identification. -/
theorem realificationKreinFrameEquiv_internalJ :
    (realificationKreinFrameEquiv.conjAlgEquiv ℝ)
      (Matrix.toLinAlgEquiv'
        (InfoGeometry.Quantum.Realification.internalJ (n := Fin 4))) =
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap := by
  apply LinearMap.ext
  intro u
  have hcoord : realificationKreinFrameEquiv.symm u =
      Sum.elim (fun i => (WithLp.fst u).ofLp i)
        (fun i => (WithLp.snd u).ofLp i) := rfl
  change realificationKreinFrameEquiv
      (Matrix.toLinAlgEquiv'
        (InfoGeometry.Quantum.Realification.internalJ (n := Fin 4))
        (realificationKreinFrameEquiv.symm u)) = _
  rw [hcoord, Matrix.toLinAlgEquiv'_apply]
  have hmul :
      InfoGeometry.Quantum.Realification.internalJ (n := Fin 4) *ᵥ
          Sum.elim (fun i => (WithLp.fst u).ofLp i)
            (fun i => (WithLp.snd u).ofLp i) =
        Sum.elim (fun i => -(WithLp.snd u).ofLp i)
          (fun i => (WithLp.fst u).ofLp i) := by
    calc
      _ = InfoGeometry.Quantum.Realification.internalJ *ᵥ
          InfoGeometry.Quantum.Realification.realifyVector
            (InfoGeometry.Quantum.Realification.unrealifyVector
              (Sum.elim (fun i => (WithLp.fst u).ofLp i)
                (fun i => (WithLp.snd u).ofLp i))) := by
              rw [InfoGeometry.Quantum.Realification.realifyVector_unrealifyVector]
      _ = InfoGeometry.Quantum.Realification.realifyVector
          (Complex.I • InfoGeometry.Quantum.Realification.unrealifyVector
            (Sum.elim (fun i => (WithLp.fst u).ofLp i)
              (fun i => (WithLp.snd u).ofLp i))) :=
            InfoGeometry.Quantum.Realification.internalJ_realifyVector _
      _ = _ := by
        ext i
        cases i <;>
          simp [InfoGeometry.Quantum.Realification.realifyVector,
            InfoGeometry.Quantum.Realification.unrealifyVector,
            Complex.I_mul]
  rw [hmul]
  change InfoGeometry.Krein.to_doubled
      (WithLp.toLp 2 (fun i => -(WithLp.snd u).ofLp i))
      (WithLp.toLp 2 (fun i => (WithLp.fst u).ofLp i)) = _
  exact (InfoGeometry.Krein.complex_i_to_doubled
    (WithLp.fst u) (WithLp.snd u)).symm

/-- Every realified Yang--Mills matrix commutes with the actual doubled real
complex structure; no complex scalar action is introduced on `KreinFrame4`. -/
theorem realifiedCircularMatrixEnd_commutes_complexStructure
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Commute (realifiedCircularMatrixEnd A)
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap := by
  have h := InfoGeometry.Quantum.Realification.realify_commutes_internalJ A
  have h' := congrArg
    (fun M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ =>
      (realificationKreinFrameEquiv.conjAlgEquiv ℝ) (Matrix.toLinAlgEquiv' M)) h.eq
  have hJ := realificationKreinFrameEquiv_internalJ
  change realifiedCircularMatrixEnd A *
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap =
    InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap *
      realifiedCircularMatrixEnd A
  simpa [realifiedCircularMatrixEnd, hJ] using h'

/-- The real operator curvature of the existing circular Yang--Mills
connection is the ordered square of its realified connection on `KreinFrame4`.
This is a curvature bridge on the real carrier, before any trace/action
readout. -/
theorem realifiedCircularCurvature_eq_connection_square (x : Coordinate) :
    realifiedCircularMatrixEnd (circularCurvatureMat4 x) =
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        realifiedCircularMatrixEnd (circularConnectionMat4 x) := by
  rw [circularCurvatureMat4, realifiedCircularMatrixEnd_mul]

@[simp] theorem realifiedCircularMatrixEnd_add
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A + B) =
      realifiedCircularMatrixEnd A + realifiedCircularMatrixEnd B := by
  simp [realifiedCircularMatrixEnd, InfoGeometry.Quantum.Realification.realify_add]

@[simp] theorem realifiedCircularMatrixEnd_one :
    realifiedCircularMatrixEnd (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  simp [realifiedCircularMatrixEnd, InfoGeometry.Quantum.Realification.realify_one]

@[simp] theorem realifiedCircularMatrixEnd_sub
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A - B) =
      realifiedCircularMatrixEnd A - realifiedCircularMatrixEnd B := by
  simp [sub_eq_add_neg, realifiedCircularMatrixEnd]

/-- The realified circular chiral connection and the real graded-tensor
Majorana slash have identical squares on the doubled Krein carrier. Both
sides equal the Minkowski interval times the identity endomorphism. -/
theorem realifiedCircularWeyl_majorana_square
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) =
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) := by
  have hWeyl :
      circularConnectionMat4 (realMinkowskiCircularCoordinate X) *
          circularConnectionMat4 (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [circularConnectionMat4, chiralOffBlock4_mul]
    have hUL' : weylUpperMat (realMinkowskiCircularCoordinate X) *
          weylLowerMat (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [weylUpperMat_mul_weylLowerMat]
      cases X with
      | mk t x y z =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [realMinkowskiCircularCoordinate, chiralBoostVec,
              chiralVorticityVec,
              InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
              InfoGeometry.Canonical.RealSpacetime4x4Closure.interval,
              solder, σ0, σ1, σ2, σ3] <;> ring
    have hLU' : weylLowerMat (realMinkowskiCircularCoordinate X) *
          weylUpperMat (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [weylLowerMat_mul_weylUpperMat]
      cases X with
      | mk t x y z =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [realMinkowskiCircularCoordinate, chiralBoostVec,
              chiralVorticityVec,
              InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
              InfoGeometry.Canonical.RealSpacetime4x4Closure.interval,
              solder, σ0, σ1, σ2, σ3] <;> ring
    rw [hUL', hLU']
    cases X with
    | mk t x y z =>
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [chiralDiagBlock4, Matrix.smul_apply,
            InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]
  calc
    _ = realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X) *
          circularConnectionMat4 (realMinkowskiCircularCoordinate X)) := by
            rw [realifiedCircularMatrixEnd_mul]
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X •
          (1 : Module.End ℝ KreinFrame4) := by
            rw [hWeyl]
            simp [realifiedCircularMatrixEnd]
    _ = realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) := by
            symm
            exact realMinkowskiMajorana_onKrein_square X

/-- The two real Clifford realizations have the same polarized bilinear
operator relation, not only the same vector squares.  Thus their symmetric
operator product on any pair of real Minkowski vectors is identical on the
existing doubled Krein carrier.  This is a genuine compatibility of the
circular Weyl and three-mode Majorana representations; it does not assert
equality of the individual slash operators or identify the Peirce translation
generator with a Majorana generator. -/
private def realSpacetimeAdd
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨X.t + Y.t, X.x + Y.x, X.y + Y.y, X.z + Y.z⟩

private lemma anticommutator_eq_square_sub {A : Type*} [Ring A] (a b : A) :
    a * b + b * a = (a + b) * (a + b) - a * a - b * b := by
  noncomm_ring

private theorem weylUpperMat_add (x y : Coordinate) :
    weylUpperMat (x + y) = weylUpperMat x + weylUpperMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylUpperMat,
      InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring

private theorem weylLowerMat_add (x y : Coordinate) :
    weylLowerMat (x + y) = weylLowerMat x + weylLowerMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylLowerMat,
      InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring

private theorem chiralOffBlock4_add {R : Type*} [Ring R]
    (u₁ u₂ l₁ l₂ : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 (u₁ + u₂) (l₁ + l₂) =
      chiralOffBlock4 u₁ l₁ + chiralOffBlock4 u₂ l₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

private theorem circularConnectionMat4_add (x y : Coordinate) :
    circularConnectionMat4 (x + y) =
      circularConnectionMat4 x + circularConnectionMat4 y := by
  change chiralOffBlock4 (weylUpperMat (x + y)) (weylLowerMat (x + y)) =
    chiralOffBlock4 (weylUpperMat x) (weylLowerMat x) +
      chiralOffBlock4 (weylUpperMat y) (weylLowerMat y)
  rw [weylUpperMat_add, weylLowerMat_add, chiralOffBlock4_add]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem realifiedCircularWeyl_majorana_polarization
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let circularSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
      realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate Z))
    let majoranaSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana Z)
    circularSlash X * circularSlash Y + circularSlash Y * circularSlash X =
      majoranaSlash X * majoranaSlash Y + majoranaSlash Y * majoranaSlash X := by
  dsimp
  let circularSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
    realifiedCircularMatrixEnd
      (circularConnectionMat4 (realMinkowskiCircularCoordinate Z))
  let majoranaSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
    realThreeMatrixTensorOnH4 (realMinkowskiMajorana Z)
  have hCircularAdd (U V :
      InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
      circularSlash (realSpacetimeAdd U V) = circularSlash U + circularSlash V := by
    dsimp [circularSlash]
    have hConn : circularConnectionMat4
        (realMinkowskiCircularCoordinate (realSpacetimeAdd U V)) =
        circularConnectionMat4 (realMinkowskiCircularCoordinate U) +
          circularConnectionMat4 (realMinkowskiCircularCoordinate V) := by
      cases U with
      | mk ut ux uy uz =>
        cases V with
        | mk vt vx vy vz =>
          have hcoord :
              realMinkowskiCircularCoordinate
                  (realSpacetimeAdd ⟨ut, ux, uy, uz⟩ ⟨vt, vx, vy, vz⟩) =
                realMinkowskiCircularCoordinate ⟨ut, ux, uy, uz⟩ +
                  realMinkowskiCircularCoordinate ⟨vt, vx, vy, vz⟩ := by
            funext i
            fin_cases i <;> rfl
          rw [hcoord, circularConnectionMat4_add]
    rw [hConn, realifiedCircularMatrixEnd_add]
  have hMajoranaAdd (U V :
      InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
      majoranaSlash (realSpacetimeAdd U V) = majoranaSlash U + majoranaSlash V := by
    dsimp [majoranaSlash]
    cases U with
    | mk ut ux uy uz =>
      cases V with
      | mk vt vx vy vz =>
        have hMajorana :
            realMinkowskiMajorana (realSpacetimeAdd ⟨ut, ux, uy, uz⟩
                ⟨vt, vx, vy, vz⟩) =
              realMinkowskiMajorana ⟨ut, ux, uy, uz⟩ +
                realMinkowskiMajorana ⟨vt, vx, vy, vz⟩ := by
          simp only [realMinkowskiMajorana, realSpacetimeAdd, add_smul]
          abel
        calc
          _ = realThreeMatrixTensorOnH4
              (realMinkowskiMajorana ⟨ut, ux, uy, uz⟩ +
                realMinkowskiMajorana ⟨vt, vx, vy, vz⟩) :=
                congrArg realThreeMatrixTensorOnH4 hMajorana
          _ = _ := map_add _ _ _
  calc
    circularSlash X * circularSlash Y + circularSlash Y * circularSlash X =
        (circularSlash X + circularSlash Y) * (circularSlash X + circularSlash Y) -
          circularSlash X * circularSlash X - circularSlash Y * circularSlash Y :=
      anticommutator_eq_square_sub _ _
    _ = circularSlash (realSpacetimeAdd X Y) * circularSlash (realSpacetimeAdd X Y) -
          circularSlash X * circularSlash X - circularSlash Y * circularSlash Y := by
      rw [← hCircularAdd]
    _ = majoranaSlash (realSpacetimeAdd X Y) * majoranaSlash (realSpacetimeAdd X Y) -
          majoranaSlash X * majoranaSlash X - majoranaSlash Y * majoranaSlash Y := by
      rw [realifiedCircularWeyl_majorana_square]
      rw [realifiedCircularWeyl_majorana_square X,
        realifiedCircularWeyl_majorana_square Y]
    _ = (majoranaSlash X + majoranaSlash Y) * (majoranaSlash X + majoranaSlash Y) -
          majoranaSlash X * majoranaSlash X - majoranaSlash Y * majoranaSlash Y := by
      rw [← hMajoranaAdd]
    _ = majoranaSlash X * majoranaSlash Y + majoranaSlash Y * majoranaSlash X :=
      (anticommutator_eq_square_sub _ _).symm

/-- Realification preserves the chiral Peirce splitting of the circular
connection. This uses the source owner's off-block connection and transports
its projector identity to the actual doubled real carrier. -/
theorem realifiedCircularConnection_peirceDecomposition (x : Coordinate) :
    let P := realifiedCircularMatrixEnd chiralProjMat4
    let A := realifiedCircularMatrixEnd (circularConnectionMat4 x)
    P * A * (1 - P) + (1 - P) * A * P = A := by
  have hSource :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi chiralProjMat4
        (circularConnectionMat4 x) (circularConnectionMat4 x) =
          circularConnectionMat4 x := by
    simpa [chiralProjMat4, circularConnectionMat4] using
      genPhi_chiralOffBlock4 (weylUpperMat x) (weylLowerMat x)
  have hComplement :
      1 - realifiedCircularMatrixEnd chiralProjMat4 =
        realifiedCircularMatrixEnd (1 - chiralProjMat4) := by
    calc
      _ = realifiedCircularMatrixEnd 1 - realifiedCircularMatrixEnd chiralProjMat4 := by
        rw [realifiedCircularMatrixEnd_one]
      _ = realifiedCircularMatrixEnd (1 - chiralProjMat4) :=
        (realifiedCircularMatrixEnd_sub _ _).symm
  have hCornerPlus :
      realifiedCircularMatrixEnd chiralProjMat4 *
          realifiedCircularMatrixEnd (circularConnectionMat4 x) *
          (1 - realifiedCircularMatrixEnd chiralProjMat4) =
        realifiedCircularMatrixEnd
          (chiralProjMat4 * circularConnectionMat4 x * (1 - chiralProjMat4)) := by
    rw [hComplement, ← realifiedCircularMatrixEnd_mul, ← realifiedCircularMatrixEnd_mul]
  have hCornerMinus :
      (1 - realifiedCircularMatrixEnd chiralProjMat4) *
          realifiedCircularMatrixEnd (circularConnectionMat4 x) *
          realifiedCircularMatrixEnd chiralProjMat4 =
        realifiedCircularMatrixEnd
          ((1 - chiralProjMat4) * circularConnectionMat4 x * chiralProjMat4) := by
    rw [hComplement, ← realifiedCircularMatrixEnd_mul, ← realifiedCircularMatrixEnd_mul]
  change realifiedCircularMatrixEnd chiralProjMat4 *
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        (1 - realifiedCircularMatrixEnd chiralProjMat4) +
    (1 - realifiedCircularMatrixEnd chiralProjMat4) *
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        realifiedCircularMatrixEnd chiralProjMat4 =
      realifiedCircularMatrixEnd (circularConnectionMat4 x)
  rw [hCornerPlus, hCornerMinus]
  have h := congrArg realifiedCircularMatrixEnd hSource
  simpa [InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus] using h

/-- The existing three-mode real CAR equivalence transports the circular
connection square identity to its inverse image in the genuine Koszul tensor
algebra. No replacement multiplication or carrier is introduced. -/
theorem circularConnection_square_eq_curvatureInRealCAR (x : Coordinate) :
    realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
      (circularConnectionMat4 x)) *
        realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
          (circularConnectionMat4 x)) =
      realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
        (circularCurvatureMat4 x)) := by
  apply realThreeMatrixTensorOnH4.injective
  simp only [realThreeMatrixTensorOnH4.apply_symm_apply]
  rw [map_mul, realThreeMatrixTensorOnH4.apply_symm_apply]
  exact (realifiedCircularCurvature_eq_connection_square x).symm

/-- In the existing real three-mode CAR algebra, the inverse images under its
owner equivalence preserve the source chiral Peirce decomposition. The source
projection remains distinct from CAR parity and Krein-frame chirality. -/
theorem realCAR_circularConnection_peirceDecomposition (x : Coordinate) :
    realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd chiralProjMat4) *
        realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd (circularConnectionMat4 x)) *
        (1 - realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd chiralProjMat4)) +
      (1 - realThreeMatrixTensorOnH4.symm
        (realifiedCircularMatrixEnd chiralProjMat4)) *
        realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd (circularConnectionMat4 x)) *
        realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd chiralProjMat4) =
      realThreeMatrixTensorOnH4.symm
        (realifiedCircularMatrixEnd (circularConnectionMat4 x)) := by
  apply realThreeMatrixTensorOnH4.injective
  simpa [map_mul, map_add, map_sub, map_one] using
      realifiedCircularConnection_peirceDecomposition x

/-! ### Real Weyl channel in the two-factor Koszul tensor

The circular Weyl matrix is realified and represented in the existing native
`M₂(ℝ) ᵍ⊗ M₂(ℝ)` carrier. The elliptic Pauli direction is retained as the
odd-odd tensor term, so the displayed representation uses the Koszul sign
rather than an ungraded block embedding.
-/

private def realPauliX : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixE01 + matrixE10

private def realPauliEpsilon : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixE10 - matrixE01

private def realPauliZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def realWeylUpperTensor (x : Coordinate) : twoMatrixGradedTensor :=
  x 0 • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
  x 1 • (realPauliZ ᵍ⊗ₜ[ℝ] realPauliX) +
  x 2 • (realPauliX ᵍ⊗ₜ[ℝ] realPauliEpsilon) +
  x 3 • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      realPauliZ)

theorem realWeylUpperTensor_represents_weylUpperMat (x : Coordinate) :
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv (realWeylUpperTensor x)) =
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify
        (weylUpperMat x) := by
  rw [show weylUpperMat x =
      !![(x 0 : ℂ) + x 3, (x 1 : ℂ) - Complex.I * x 2;
        (x 1 : ℂ) + Complex.I * x 2, (x 0 : ℂ) - x 3] by
        simp [weylUpperMat, pauliSolder2x2, solder_explicit]]
  simp only [realWeylUpperTensor, map_add, map_smul,
    twoMatrixGradedTensorMoritaEquiv_tmul]
  let e : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  have hto (A : Matrix (Fin 2) (Fin 2) M2R) (i j : Fin 4) :
      realNestedMatrixToFin4 A i j =
        A (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 := by
    rfl
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, hto]
  simp only [InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify_apply]
  fin_cases i <;> fin_cases j <;>
    dsimp [e, finProdFinEquiv] <;>
    simp [InfoGeometry.Clifford.Cl11GradedTensorMorita.head,
      matrixE01, matrixE10,
      realPauliX, realPauliEpsilon, realPauliZ,
      AlgEquiv.coe_toAlgHom,
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.blockRealify,
      Matrix.single,
      Fin.divNat, Fin.modNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The unit time-like vector in the real `FourSpace` coordinate convention. -/
def unitTimeMomentum : FourSpace :=
  fourSpaceEquivVec22.symm (1, 0, 0, 0)

/-- Real Pauli soldering sends unit time momentum to the identity matrix. -/
theorem realMomentum_unitTime : realMomentum unitTimeMomentum = 1 := by
  unfold realMomentum unitTimeMomentum
  rw [fourSpaceEquivVec22.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Soldering.soldering,
    InfoGeometry.Clifford.Soldering.sigma0,
    InfoGeometry.Clifford.Soldering.sigma1,
    InfoGeometry.Clifford.Soldering.sigma3,
    InfoGeometry.Clifford.Soldering.epsilon]

/-- The diagonal momentum block at unit time is the identity on the two
Peirce sheets. -/
theorem diagonalMomentumOperator_unitTime :
    diagonalMomentumOperator unitTimeMomentum =
      (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [diagonalMomentumOperator, realMomentum_unitTime,
      Matrix.zero_apply]

/-- The three-mode doubled-Krein representation of unit-time diagonal
momentum is the identity operator. -/
theorem realThreeKrein_unitTimeMomentum_is_one :
    realThreeMatrixTensorOnH4 (realTwoMatrixPairIntoThreeMode
      (twoMatrixGradedTensorMoritaEquiv.symm
        (diagonalMomentumOperator unitTimeMomentum))) = 1 := by
  rw [diagonalMomentumOperator_unitTime]
  simp

/-- On the common real doubled-Krein carrier, the circular split-octonion
root CAR anticommutator equals the anticommutator of the real Peirce
translation and its complementary charge at unit time-like momentum.

The theorem identifies the resulting operator-valued momentum readout (the
identity at this normalized point), not the individual root and translation
operators. -/
theorem circularRootCAR_matches_unitTime_translation (i : Fin 3) :
    realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) +
      realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) =
      realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor unitTimeMomentum)) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) +
      realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor unitTimeMomentum)) := by
  rw [threeMode_supercolor_root_CAR i,
    realKrein_gradedPair_translationCharge_anticommutator_eq_diagonalMomentum,
    realThreeKrein_unitTimeMomentum_is_one]

/-- A circular time-Majorana generator cannot equal a Peirce translation
generator in the existing three-mode real Koszul algebra: the former squares
to one, while the latter squares to zero. Thus the unit-time anticommutator
identity above is genuinely a relation between pairs, not a generator
identification. -/
theorem circularMajoranaTime_ne_PeirceTranslation
    (i : Fin 3) (p : FourSpace) :
    circularMajoranaTime i ≠
      realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) := by
  intro h
  have hsq := congrArg
    (fun A : realThreeMatrixGradedTensor => A * A) h
  have hMajoranaSq := (circularMajorana_splitClifford_relations i).1
  have hTranslationSq :
      realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) *
          realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) = 0 := by
    calc
      _ = realTwoMatrixPairIntoThreeMode
          (translationInGradedTensor p * translationInGradedTensor p) := by
            rw [map_mul]
      _ = 0 := by rw [translationInGradedTensor_square, map_zero]
  rw [hMajoranaSq, hTranslationSq] at hsq
  have hEnd :
      (1 : Module.End ℝ KreinFrame4) = 0 := by
    have h' := congrArg realThreeMatrixTensorOnH4 hsq
    rw [map_one, map_zero] at h'
    exact h'
  exact one_ne_zero hEnd

end InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
