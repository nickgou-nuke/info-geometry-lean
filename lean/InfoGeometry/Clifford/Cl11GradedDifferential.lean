/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ChiralityAlgebra
import InfoGeometry.Clifford.Cl11ColimitDimension
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import InfoGeometry.Clifford.Cl11HomogeneousChains
import InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Clifford.SplitCliffordMatrixEquiv

/-!
# Jordan--Wigner graded differentials on the infinite algebraic colimit

The stage and site indices select a charge; each endomorphism acts on every
element of the existing `Cl11TensorTowerLimit.Limit`. Its infinite dimension
is established separately by `Cl11ColimitDimension.not_finiteDimensional`.
The operators use the actual global chirality action and ordered products.

Creation square-zero and the same-site CAR relation give a nonzero differential
and a square-zero contracting homotopy. Their anticommutator is the identity,
so the differential's range equals its kernel. This is an algebraic contraction
with zero projection. No norm, Hilbert adjoint, vacuum, or spectral gap is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11GradedDifferential

open Cl11TensorTower Cl11TensorTowerLimit Cl11ChiralityAlgebra
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

/-- Exact finite-representative readback, retaining both multiplication orders. -/
theorem gradedAdjoint_ofStage (n : ℕ) (Q X : Stage n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n Q) (ofStage n X) =
      ofStage n (Q * X - (globalChirality n * X * globalChirality n) * Q) := by
  simp only [gradedAdjoint_apply, limitChiralityAlgEquiv_apply,
    limitChiralityConj_ofStage, ofStage_sub, ofStage_mul]

/-- The creation charge induces a native endomorphism of the entire colimit. -/
def jwDifferential (n : ℕ) (k : Fin n) : Module.End ℝ Limit :=
  gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k))

/-- Nilpotency follows from the charge square, in addition to its oddness. -/
theorem jwDifferential_sq (n : ℕ) (k : Fin n) :
    jwDifferential n k * jwDifferential n k = 0 := by
  have hsq : ofStage n (jwCreation n k) * ofStage n (jwCreation n k) = 0 :=
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.creation_sq n k)
  unfold jwDifferential
  rw [gradedAdjoint_square limitChiralityAlgEquiv
    limitChiralityConj_involutive _ (limitChiralityConj_jwCreation n k)]
  simp [hsq]

/-- The actual annihilation generator detects the nonzero differential. -/
theorem jwDifferential_annihilation (n : ℕ) (k : Fin n) :
    jwDifferential n k (ofStage n (jwAnnihilation n k)) = 1 := by
  unfold jwDifferential
  rw [gradedAdjoint_of_odd limitChiralityAlgEquiv _ _
    (limitChiralityConj_jwAnnihilation n k)]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add,
    InfoGeometry.Canonical.Cl55WittCAR.same_site_car, ofStage_one]

theorem jwDifferential_ne_zero (n : ℕ) (k : Fin n) : jwDifferential n k ≠ 0 := by
  intro h
  have hz := congrArg (fun T : Module.End ℝ Limit =>
    T (ofStage n (jwAnnihilation n k))) h
  change jwDifferential n k (ofStage n (jwAnnihilation n k)) = 0 at hz
  rw [jwDifferential_annihilation] at hz
  exact one_ne_zero hz

/-- Left multiplication by the matching annihilator contracts the differential. -/
def jwHomotopy (n : ℕ) (k : Fin n) : Module.End ℝ Limit :=
  LinearMap.mulLeft ℝ (ofStage n (jwAnnihilation n k))

theorem jwHomotopy_sq (n : ℕ) (k : Fin n) :
    jwHomotopy n k * jwHomotopy n k = 0 := by
  apply LinearMap.ext
  intro X
  change ofStage n (jwAnnihilation n k) *
    (ofStage n (jwAnnihilation n k) * X) = 0
  rw [← mul_assoc,
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.annihilation_sq n k), zero_mul]

/-- The graded Leibniz rule and CAR give an identity on every colimit element. -/
theorem jwDifferential_homotopy (n : ℕ) (k : Fin n) :
    jwDifferential n k * jwHomotopy n k +
      jwHomotopy n k * jwDifferential n k = 1 := by
  apply LinearMap.ext
  intro X
  change jwDifferential n k (ofStage n (jwAnnihilation n k) * X) +
    ofStage n (jwAnnihilation n k) * jwDifferential n k X = X
  have hder := gradedAdjoint_leibniz limitChiralityAlgEquiv
    (ofStage n (jwCreation n k)) (ofStage n (jwAnnihilation n k)) X
  change jwDifferential n k (ofStage n (jwAnnihilation n k) * X) =
    jwDifferential n k (ofStage n (jwAnnihilation n k)) * X +
      limitChiralityConj (ofStage n (jwAnnihilation n k)) * jwDifferential n k X at hder
  rw [hder, jwDifferential_annihilation, limitChiralityConj_jwAnnihilation,
    one_mul, neg_mul]
  abel

/-- Every closed element has the explicit primitive supplied by the homotopy. -/
theorem jwDifferential_range_eq_ker (n : ℕ) (k : Fin n) :
    LinearMap.range (jwDifferential n k) = LinearMap.ker (jwDifferential n k) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (jwDifferential_sq n k)
  · intro X hX
    apply LinearMap.mem_range.mpr
    refine ⟨jwHomotopy n k X, ?_⟩
    have hcon := congrArg (fun T : Module.End ℝ Limit => T X)
      (jwDifferential_homotopy n k)
    change jwDifferential n k (jwHomotopy n k X) +
      jwHomotopy n k (jwDifferential n k X) = X at hcon
    have hzero : jwDifferential n k X = 0 := LinearMap.mem_ker.mp hX
    rw [hzero, map_zero, add_zero] at hcon
    exact hcon

section CanonicalUHFAndSplitLimitSoldering

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Clifford.SplitCliffordMatrixEquiv
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open scoped Matrix Kronecker

/-- `canonicalCliffordUHFColimitEquiv` (`Cl11TensorTowerLimit.Limit ≃+* PrimonUHFAlgebra`)
is `ℝ`-linear.
Note: `SplitCliffordMatrixLimitSoldering.matrixLimitMap : SplitCliffordInfinity →+* Limit`
is gated on `BondCoherence`, which is false for `spinorRepresentation` by
`gradedTensorSuccessor_not_algHom`; the genuine colimit isomorphism with
`SplitCliffordInfinity` is constructed unconditionally below via Jordan–Wigner strings. -/
theorem canonicalCliffordUHFColimitEquiv_smul (r : ℝ) (x : Cl11TensorTowerLimit.Limit) :
    canonicalCliffordUHFColimitEquiv (r • x) = r • canonicalCliffordUHFColimitEquiv x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      have halg : algebraMap ℝ Cl11TensorTowerLimit.Limit r = realAlgebraMap r := rfl
      have hsmul : r • (ofStage n A : Cl11TensorTowerLimit.Limit) = ofStage n (r • A) := by
        rw [Algebra.smul_def, halg, realAlgebraMap_stage n r, ← ofStage_mul, Algebra.smul_def]
      change canonicalCliffordUHFColimitEquiv (r • (ofStage n A : Cl11TensorTowerLimit.Limit)) =
        r • canonicalCliffordUHFColimitEquiv (ofStage n A)
      rw [hsmul, canonicalCliffordUHFColimitEquiv_ofStage,
        canonicalCliffordUHFColimitEquiv_ofStage, map_smul]
      change InfoGeometry.Algebra.PrimonColimitAlgebra.toColimitLinear n
          (r • canonicalClStageEquiv n A) =
        r • InfoGeometry.Algebra.PrimonColimitAlgebra.toColimitLinear n
          (canonicalClStageEquiv n A)
      exact map_smul (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimitLinear n) r _

/-- `canonicalCliffordUHFColimitEquiv` upgraded to an `ℝ`-linear equivalence
`Cl11TensorTowerLimit.Limit ≃ₗ[ℝ] InfoGeometry.Algebra.PrimonColimitAlgebra.PrimonUHFAlgebra`. -/
def canonicalCliffordUHFColimitLinearEquiv :
    Cl11TensorTowerLimit.Limit ≃ₗ[ℝ]
      InfoGeometry.Algebra.PrimonColimitAlgebra.PrimonUHFAlgebra where
  __ := canonicalCliffordUHFColimitEquiv
  map_smul' r x := canonicalCliffordUHFColimitEquiv_smul r x

private def splitCoordFun : (n : ℕ) → Fin n → (ℝ × ℝ) → SplitSpace n
  | 0, k, _ => Fin.elim0 k
  | n + 1, k, x =>
      if h : (k : ℕ) < n then
        ((0, 0), splitCoordFun n ⟨k, h⟩ x)
      else
        (x, 0)

private theorem splitCoordFun_add (n : ℕ) (k : Fin n) (x y : ℝ × ℝ) :
    splitCoordFun n k (x + y) = splitCoordFun n k x + splitCoordFun n k y := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      dsimp [splitCoordFun]
      split_ifs with h
      · exact Prod.ext (by simp) (ih ⟨k, h⟩)
      · exact Prod.ext rfl (by simp)

private theorem splitCoordFun_smul (n : ℕ) (k : Fin n) (r : ℝ) (x : ℝ × ℝ) :
    splitCoordFun n k (r • x) = r • splitCoordFun n k x := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      dsimp [splitCoordFun]
      split_ifs with h
      · exact Prod.ext (by simp) (ih ⟨k, h⟩)
      · exact Prod.ext rfl (by simp)

/-- Embed `(a, b) : ℝ × ℝ` into the `k`-th split Clifford coordinate (`0` innermost,
`n - 1` outermost) of `SplitSpace n`. -/
def splitCoord (n : ℕ) (k : Fin n) : (ℝ × ℝ) →ₗ[ℝ] SplitSpace n where
  toFun := splitCoordFun n k
  map_add' := splitCoordFun_add n k
  map_smul' := splitCoordFun_smul n k

@[simp] theorem splitCoord_castSucc (n : ℕ) (k : Fin n) (x : ℝ × ℝ) :
    splitCoord (n + 1) k.castSucc x = tailLift n (splitCoord n k x) := by
  change splitCoordFun (n + 1) k.castSucc x = ((0, 0), splitCoordFun n k x)
  simp [splitCoordFun, k.isLt]

@[simp] theorem splitCoord_last (n : ℕ) (x : ℝ × ℝ) :
    splitCoord (n + 1) (Fin.last n) x = headPair n x := by
  change splitCoordFun (n + 1) (Fin.last n) x = (x, 0)
  simp [splitCoordFun]

private def splitToJWRaw : (n : ℕ) → SplitSpace n → (Fin n ⊕ Fin n → ℝ)
  | 0, _, s => match s with | .inl i => Fin.elim0 i | .inr i => Fin.elim0 i
  | n + 1, ⟨x, xs⟩, s =>
      match s with
      | .inl k => if h : (k : ℕ) < n then splitToJWRaw n xs (.inl ⟨k, h⟩) else x.1
      | .inr k => if h : (k : ℕ) < n then splitToJWRaw n xs (.inr ⟨k, h⟩) else x.2

private theorem splitToJWRaw_add (n : ℕ) (u v : SplitSpace n) :
    splitToJWRaw n (u + v) = splitToJWRaw n u + splitToJWRaw n v := by
  induction n with
  | zero =>
      funext s; cases s with | inl i => exact Fin.elim0 i | inr i => exact Fin.elim0 i
  | succ n ih =>
      rcases u with ⟨x, xs⟩
      rcases v with ⟨y, ys⟩
      have hfst : ((x, xs) + (y, ys) : SplitSpace (n + 1)).1 = x + y := rfl
      have hsnd : ((x, xs) + (y, ys) : SplitSpace (n + 1)).2 = xs + ys := rfl
      funext s
      have hsplit : ((x, xs) + (y, ys) : SplitSpace (n + 1)) = (x + y, xs + ys) := rfl
      rw [hsplit]
      cases s with
      | inl k =>
          dsimp [splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih xs ys) (.inl ⟨k, h⟩)
          · rfl
      | inr k =>
          dsimp [splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih xs ys) (.inr ⟨k, h⟩)
          · rfl

private theorem splitToJWRaw_smul (n : ℕ) (r : ℝ) (u : SplitSpace n) :
    splitToJWRaw n (r • u) = r • splitToJWRaw n u := by
  induction n with
  | zero =>
      funext s; cases s with | inl i => exact Fin.elim0 i | inr i => exact Fin.elim0 i
  | succ n ih =>
      rcases u with ⟨x, xs⟩
      have hsplit : (r • (x, xs) : SplitSpace (n + 1)) = (r • x, r • xs) := rfl
      funext s
      rw [hsplit]
      cases s with
      | inl k =>
          dsimp [splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih xs) (.inl ⟨k, h⟩)
          · rfl
      | inr k =>
          dsimp [splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih xs) (.inr ⟨k, h⟩)
          · rfl

private def splitToJWFun (n : ℕ) : SplitSpace n →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun := splitToJWRaw n
  map_add' := splitToJWRaw_add n
  map_smul' := splitToJWRaw_smul n

private def jwToSplitFun : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → SplitSpace n
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, f =>
      ((f (.inl (Fin.last n)), f (.inr (Fin.last n))),
        jwToSplitFun n (fun s => match s with
          | .inl k => f (.inl k.castSucc)
          | .inr k => f (.inr k.castSucc)))

private theorem splitToJW_left_inv (n : ℕ) (v : SplitSpace n) :
    jwToSplitFun n (splitToJWFun n v) = v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      rcases v with ⟨⟨a, b⟩, xs⟩
      dsimp [splitToJWFun]
      change ((splitToJWRaw (n + 1) ((a, b), xs) (.inl (Fin.last n)),
          splitToJWRaw (n + 1) ((a, b), xs) (.inr (Fin.last n))),
        jwToSplitFun n _) = ((a, b), xs)
      have hfst : splitToJWRaw (n + 1) ((a, b), xs) (.inl (Fin.last n)) = a := by
        simp [splitToJWRaw]
      have hsnd : splitToJWRaw (n + 1) ((a, b), xs) (.inr (Fin.last n)) = b := by
        simp [splitToJWRaw]
      have htail : (fun s : Fin n ⊕ Fin n =>
          match s with
          | .inl k => splitToJWRaw (n + 1) ((a, b), xs) (.inl k.castSucc)
          | .inr k => splitToJWRaw (n + 1) ((a, b), xs) (.inr k.castSucc)) =
          splitToJWRaw n xs := by
        funext s; cases s with
        | inl k => simp [splitToJWRaw, k.isLt]
        | inr k => simp [splitToJWRaw, k.isLt]
      rw [hfst, hsnd, htail]
      exact congrArg (fun z => ((a, b), z)) (ih xs)

private theorem splitToJW_right_inv (n : ℕ) (f : Fin n ⊕ Fin n → ℝ) :
    splitToJWFun n (jwToSplitFun n f) = f := by
  induction n with
  | zero =>
      funext s; cases s with | inl i => exact Fin.elim0 i | inr i => exact Fin.elim0 i
  | succ n ih =>
      funext s
      change splitToJWRaw (n + 1) (jwToSplitFun (n + 1) f) s = f s
      cases s with
      | inl k =>
          dsimp [jwToSplitFun, splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih _) (.inl ⟨k, h⟩)
          · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
            subst hk; rfl
      | inr k =>
          dsimp [jwToSplitFun, splitToJWRaw]
          split_ifs with h
          · exact congrFun (ih _) (.inr ⟨k, h⟩)
          · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
            subst hk; rfl

/-- Linear isomorphism aligning `SplitSpace n` (site `0` innermost, `n-1` outermost)
with `(Fin n ⊕ Fin n → ℝ)` for the Jordan–Wigner representation. -/
def splitSpaceToJWEquiv (n : ℕ) : SplitSpace n ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  __ := splitToJWFun n
  invFun := jwToSplitFun n
  left_inv := splitToJW_left_inv n
  right_inv := splitToJW_right_inv n

private theorem splitToJW_quad (n : ℕ) (v : SplitSpace n) :
    QuadraticMap.weightedSumSquares ℝ (jwCliffordWeight (n := n)) (splitSpaceToJWEquiv n v) =
      Qsplit n v := by
  induction n with
  | zero =>
      simp [QuadraticMap.weightedSumSquares_apply, Qsplit]
  | succ n ih =>
      rcases v with ⟨⟨a, b⟩, xs⟩
      rw [Qsplit_succ_apply, ← ih xs]
      simp only [QuadraticMap.weightedSumSquares_apply]
      change (∑ s : Fin (n + 1) ⊕ Fin (n + 1),
          jwCliffordWeight s • (splitToJWRaw (n + 1) ((a, b), xs) s *
            splitToJWRaw (n + 1) ((a, b), xs) s)) =
        InfoGeometry.CliffordTower.Q11 (a, b) + ∑ s : Fin n ⊕ Fin n,
          jwCliffordWeight s • (splitToJWRaw n xs s * splitToJWRaw n xs s)
      rw [Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [Fintype.sum_sum_type]
      have hL : (∑ i : Fin n, jwCliffordWeight (Sum.inl i.castSucc) •
          (splitToJWRaw (n + 1) ((a, b), xs) (.inl i.castSucc) *
            splitToJWRaw (n + 1) ((a, b), xs) (.inl i.castSucc))) =
          ∑ i : Fin n, jwCliffordWeight (Sum.inl i) •
            (splitToJWRaw n xs (.inl i) * splitToJWRaw n xs (.inl i)) := by
        congr 1; funext i
        simp [splitToJWRaw, i.isLt, jwCliffordWeight]
      have hR : (∑ i : Fin n, jwCliffordWeight (Sum.inr i.castSucc) •
          (splitToJWRaw (n + 1) ((a, b), xs) (.inr i.castSucc) *
            splitToJWRaw (n + 1) ((a, b), xs) (.inr i.castSucc))) =
          ∑ i : Fin n, jwCliffordWeight (Sum.inr i) •
            (splitToJWRaw n xs (.inr i) * splitToJWRaw n xs (.inr i)) := by
        congr 1; funext i
        simp [splitToJWRaw, i.isLt, jwCliffordWeight]
      rw [hL, hR]
      simp [splitToJWRaw, jwCliffordWeight, InfoGeometry.CliffordTower.Q11, splitQ11]
      ring

/-- Quadratic isometry equivalence `Qsplit n ≃qᵢ weightedSumSquares jwCliffordWeight`. -/
def splitSpaceToJWIsometry (n : ℕ) :
    (Qsplit n).IsometryEquiv (QuadraticMap.weightedSumSquares ℝ (jwCliffordWeight (n := n))) where
  toLinearEquiv := splitSpaceToJWEquiv n
  map_app' := splitToJW_quad n

/-- Unconditional `ℝ`-algebra homomorphism `Clsplit n →ₐ[ℝ] Stage n` via the
Jordan–Wigner representation (respecting the `stageEmbed` bond). -/
def jwSplitStageHom (n : ℕ) : Clsplit n →ₐ[ℝ] Stage n :=
  (jwCliffordRepresentation n).comp
    (CliffordAlgebra.equivOfIsometry (splitSpaceToJWIsometry n)).toAlgHom

private theorem splitToJW_splitCoord (n : ℕ) (k : Fin n) (x : ℝ × ℝ) :
    splitSpaceToJWEquiv n (splitCoord n k x) =
      x.1 • Pi.single (Sum.inl k) 1 + x.2 • Pi.single (Sum.inr k) 1 := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      funext s
      change splitToJWRaw (n + 1) (splitCoordFun (n + 1) k x) s = _
      by_cases hk : (k : ℕ) < n
      · have hcoord : splitCoordFun (n + 1) k x = ((0, 0), splitCoordFun n ⟨k, hk⟩ x) := by
          simp [splitCoordFun, hk]
        rw [hcoord]
        cases s with
        | inl j =>
            dsimp [splitToJWRaw]
            split_ifs with hj
            · have ihk := congrFun (ih ⟨k, hk⟩) (.inl ⟨j, hj⟩)
              change splitToJWRaw n (splitCoordFun n ⟨k, hk⟩ x) (.inl ⟨j, hj⟩) = _ at ihk
              rw [ihk]
              simp [Pi.single_apply, Fin.ext_iff]
            · simp [Fin.ext_iff, show (j : ℕ) ≠ (k : ℕ) by omega]
        | inr j =>
            dsimp [splitToJWRaw]
            split_ifs with hj
            · have ihk := congrFun (ih ⟨k, hk⟩) (.inr ⟨j, hj⟩)
              change splitToJWRaw n (splitCoordFun n ⟨k, hk⟩ x) (.inr ⟨j, hj⟩) = _ at ihk
              rw [ihk]
              simp [Pi.single_apply, Fin.ext_iff]
            · simp [Fin.ext_iff, show (j : ℕ) ≠ (k : ℕ) by omega]
      · have hk_last : k = Fin.last n := Fin.eq_last_of_not_lt hk
        subst hk_last
        have hcoord : splitCoordFun (n + 1) (Fin.last n) x = (x, 0) := by
          simp [splitCoordFun]
        rw [hcoord]
        cases s with
        | inl j =>
            dsimp [splitToJWRaw]
            split_ifs with hj
            · have hzero : splitToJWRaw n (0 : SplitSpace n) (.inl ⟨j, hj⟩) = 0 :=
                congrFun (splitToJWFun n).map_zero (.inl ⟨j, hj⟩)
              rw [hzero]
              simp [Fin.ext_iff, show (j : ℕ) ≠ n by omega]
            · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
              subst hj_last
              simp
        | inr j =>
            dsimp [splitToJWRaw]
            split_ifs with hj
            · have hzero : splitToJWRaw n (0 : SplitSpace n) (.inr ⟨j, hj⟩) = 0 :=
                congrFun (splitToJWFun n).map_zero (.inr ⟨j, hj⟩)
              rw [hzero]
              simp [Fin.ext_iff, show (j : ℕ) ≠ n by omega]
            · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
              subst hj_last
              simp

@[simp] theorem jwSplitStageHom_splitCoord (n : ℕ) (k : Fin n) (x : ℝ × ℝ) :
    jwSplitStageHom n (CliffordAlgebra.ι (Qsplit n) (splitCoord n k x)) =
      x.1 • jwMajoranaPlus n k + x.2 • jwMajoranaMinus n k := by
  dsimp [jwSplitStageHom]
  rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  change jwCliffordRepresentation n (CliffordAlgebra.ι _ (splitSpaceToJWEquiv n (splitCoord n k x))) = _
  rw [splitToJW_splitCoord, map_add, map_smul, map_smul]
  rw [map_add, map_smul, map_smul, jwCliffordRepresentation_basis, jwCliffordRepresentation_basis]
  rfl

/-- Native `Clsplit n` creation generator at site `k : Fin n`. -/
def nativeJWCreation (n : ℕ) (k : Fin n) : Clsplit n :=
  CliffordAlgebra.ι (Qsplit n) (splitCoord n k (1 / 2, 1 / 2))

/-- Native `Clsplit n` annihilation generator at site `k : Fin n`. -/
def nativeJWAnnihilation (n : ℕ) (k : Fin n) : Clsplit n :=
  CliffordAlgebra.ι (Qsplit n) (splitCoord n k (1 / 2, -1 / 2))

@[simp] theorem jwSplitStageHom_nativeJWCreation (n : ℕ) (k : Fin n) :
    jwSplitStageHom n (nativeJWCreation n k) = jwCreation n k := by
  rw [nativeJWCreation, jwSplitStageHom_splitCoord]
  dsimp [jwMajoranaPlus, jwMajoranaMinus]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

@[simp] theorem jwSplitStageHom_nativeJWAnnihilation (n : ℕ) (k : Fin n) :
    jwSplitStageHom n (nativeJWAnnihilation n k) = jwAnnihilation n k := by
  rw [nativeJWAnnihilation, jwSplitStageHom_splitCoord]
  dsimp [jwMajoranaPlus, jwMajoranaMinus]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

private theorem jwSplitStageHom_tailLift (n : ℕ) (xs : SplitSpace n) :
    jwSplitStageHom (n + 1) (splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) xs)) =
      Cl11TensorTower.stageEmbed n (jwSplitStageHom n (CliffordAlgebra.ι (Qsplit n) xs)) := by
  have hstep : splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) xs) =
      CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n xs) := by
    apply (InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv n).injective
    rw [splitCliffordStep_tensorFactor]
    exact (InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStep_tailFactor n xs).symm
  rw [hstep]
  dsimp [jwSplitStageHom]
  rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  change jwCliffordRepresentation (n + 1)
      (CliffordAlgebra.ι _ (splitSpaceToJWEquiv (n + 1) (tailLift n xs))) =
    Cl11TensorTower.stageEmbed n
      (jwCliffordRepresentation n (CliffordAlgebra.ι _ (splitSpaceToJWEquiv n xs)))
  rw [jwCliffordRepresentation_ι, jwCliffordRepresentation_ι, map_sum]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlast1 : splitSpaceToJWEquiv (n + 1) (tailLift n xs) (.inl (Fin.last n)) = 0 := by
    change splitToJWRaw (n + 1) ((0, 0), xs) (.inl (Fin.last n)) = 0
    simp [splitToJWRaw]
  have hlast2 : splitSpaceToJWEquiv (n + 1) (tailLift n xs) (.inr (Fin.last n)) = 0 := by
    change splitToJWRaw (n + 1) ((0, 0), xs) (.inr (Fin.last n)) = 0
    simp [splitToJWRaw]
  rw [hlast1, hlast2, zero_smul, zero_smul, add_zero, add_zero]
  congr 1
  · congr 1; funext k
    have hval : splitSpaceToJWEquiv (n + 1) (tailLift n xs) (.inl k.castSucc) =
        splitSpaceToJWEquiv n xs (.inl k) := by
      change splitToJWRaw (n + 1) ((0, 0), xs) (.inl k.castSucc) = splitToJWRaw n xs (.inl k)
      simp [splitToJWRaw, k.isLt]
    rw [hval, map_smul]
    congr 1
    change jwMajoranaPlus (n + 1) k.castSucc = Cl11TensorTower.stageEmbed n (jwMajoranaPlus n k)
    dsimp [jwMajoranaPlus]
    change jwCreation (n + 1) k.castSucc + jwAnnihilation (n + 1) k.castSucc =
      Cl11TensorTower.stageEmbed n (jwCreation n k + jwAnnihilation n k)
    rw [map_add]
    exact congrArg₂ (· + ·) (matStageEmbed_jwCreation k).symm (matStageEmbed_jwAnnihilation k).symm
  · congr 1; funext k
    have hval : splitSpaceToJWEquiv (n + 1) (tailLift n xs) (.inr k.castSucc) =
        splitSpaceToJWEquiv n xs (.inr k) := by
      change splitToJWRaw (n + 1) ((0, 0), xs) (.inr k.castSucc) = splitToJWRaw n xs (.inr k)
      simp [splitToJWRaw, k.isLt]
    rw [hval, map_smul]
    congr 1
    change jwMajoranaMinus (n + 1) k.castSucc = Cl11TensorTower.stageEmbed n (jwMajoranaMinus n k)
    dsimp [jwMajoranaMinus]
    change jwCreation (n + 1) k.castSucc - jwAnnihilation (n + 1) k.castSucc =
      Cl11TensorTower.stageEmbed n (jwCreation n k - jwAnnihilation n k)
    rw [map_sub]
    exact congrArg₂ (· - ·) (matStageEmbed_jwCreation k).symm (matStageEmbed_jwAnnihilation k).symm

/-- Exact unconditional bond compatibility: `jwSplitStageHom (n + 1) ∘ splitCliffordStep n =
stageEmbed n ∘ jwSplitStageHom n`. -/
theorem jwSplitStageHom_bond (n : ℕ) :
    (jwSplitStageHom (n + 1)).comp (splitCliffordStep n) =
      (Cl11TensorTower.stageEmbed n).comp (jwSplitStageHom n) := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro xs
  exact jwSplitStageHom_tailLift n xs

private abbrev kronStage (n : ℕ) (A : Stage n) (B : Matrix (Fin 2) (Fin 2) ℝ) : Stage (n + 1) :=
  A ⊗ₖ B

private theorem kronStage_mul (n : ℕ) (A₁ A₂ : Stage n) (B₁ B₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    kronStage n A₁ B₁ * kronStage n A₂ B₂ = kronStage n (A₁ * A₂) (B₁ * B₂) :=
  (Matrix.mul_kronecker_mul A₁ A₂ B₁ B₂).symm

private theorem kronStage_add_right (n : ℕ) (A : Stage n) (B₁ B₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    kronStage n A (B₁ + B₂) = kronStage n A B₁ + kronStage n A B₂ := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  dsimp [kronStage]
  change (A i i') * (B₁ j j' + B₂ j j') = (A i i' * B₁ j j') + (A i i' * B₂ j j')
  ring

private theorem kronStage_sub_right (n : ℕ) (A : Stage n) (B₁ B₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    kronStage n A (B₁ - B₂) = kronStage n A B₁ - kronStage n A B₂ := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  dsimp [kronStage]
  change (A i i') * (B₁ j j' - B₂ j j') = (A i i' * B₁ j j') - (A i i' * B₂ j j')
  ring

private theorem kronStage_neg_right (n : ℕ) (A : Stage n) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    kronStage n A (-B) = -kronStage n A B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  dsimp [kronStage]
  change A i i' * (-B j j') = -(A i i' * B j j')
  ring

private theorem kronStage_smul_right (n : ℕ) (r : ℝ) (A : Stage n) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    kronStage n A (r • B) = r • kronStage n A B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  dsimp [kronStage]
  change A i i' * (r * B j j') = r * (A i i' * B j j')
  ring

theorem jwSplitStageHom_surjective (n : ℕ) :
    Function.Surjective (jwSplitStageHom n) := by
  induction n with
  | zero =>
      intro M
      have hM : M = (M ⟨0, by decide⟩ ⟨0, by decide⟩) • (1 : Stage 0) := by
        ext i j
        have hi : i = ⟨0, by decide⟩ := Subsingleton.elim _ _
        have hj : j = ⟨0, by decide⟩ := Subsingleton.elim _ _
        subst hi; subst hj
        change M ⟨0, by decide⟩ ⟨0, by decide⟩ =
          M ⟨0, by decide⟩ ⟨0, by decide⟩ * ((1 : Stage 0) ⟨0, by decide⟩ ⟨0, by decide⟩)
        erw [Matrix.one_apply_eq]
        rw [mul_one]
      refine ⟨algebraMap ℝ (Clsplit 0) (M ⟨0, by decide⟩ ⟨0, by decide⟩), ?_⟩
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, ← hM]
  | succ n ih =>
      let S : Subalgebra ℝ (Stage (n + 1)) := (jwSplitStageHom (n + 1)).range
      have hstep : ∀ A : Stage n, kronStage n A (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ S := by
        intro A
        obtain ⟨a, ha⟩ := ih A
        refine ⟨splitCliffordStep n a, ?_⟩
        have hb := AlgHom.congr_fun (jwSplitStageHom_bond n) a
        change jwSplitStageHom (n + 1) (splitCliffordStep n a) =
          Cl11TensorTower.stageEmbed n (jwSplitStageHom n a) at hb
        change jwSplitStageHom (n + 1) (splitCliffordStep n a) = kronStage n A 1
        rw [hb, ha]
        rfl
      have hGamma : kronStage n (globalChirality n) (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ S :=
        hstep (globalChirality n)
      have h0 : kronStage n (globalChirality n) gamma_0_base ∈ S := by
        refine ⟨CliffordAlgebra.ι (Qsplit (n + 1)) (splitCoord (n + 1) (Fin.last n) (1, 0)), ?_⟩
        change jwSplitStageHom (n + 1)
            (CliffordAlgebra.ι (Qsplit (n + 1)) (splitCoord (n + 1) (Fin.last n) (1, 0))) =
          kronStage n (globalChirality n) gamma_0_base
        rw [jwSplitStageHom_splitCoord]
        simp only [one_smul, zero_smul, add_zero]
        dsimp [jwMajoranaPlus, jwCreation, jwAnnihilation]
        have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := rfl
        rw [hlast, jwStringWithBase_last, jwStringWithBase_last]
        change kronStage n (globalChirality n) wittCreationBase +
            kronStage n (globalChirality n) wittAnnihilationBase =
          kronStage n (globalChirality n) gamma_0_base
        rw [← kronStage_add_right]
        congr 1
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [wittCreationBase, wittAnnihilationBase, gamma_0_base, J1]
      have h1 : kronStage n (globalChirality n) gamma_1_base ∈ S := by
        refine ⟨CliffordAlgebra.ι (Qsplit (n + 1)) (splitCoord (n + 1) (Fin.last n) (0, 1)), ?_⟩
        change jwSplitStageHom (n + 1)
            (CliffordAlgebra.ι (Qsplit (n + 1)) (splitCoord (n + 1) (Fin.last n) (0, 1))) =
          kronStage n (globalChirality n) gamma_1_base
        rw [jwSplitStageHom_splitCoord]
        simp only [zero_smul, one_smul, zero_add]
        dsimp [jwMajoranaMinus, jwCreation, jwAnnihilation]
        have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := rfl
        rw [hlast, jwStringWithBase_last, jwStringWithBase_last]
        change kronStage n (globalChirality n) wittCreationBase -
            kronStage n (globalChirality n) wittAnnihilationBase =
          kronStage n (globalChirality n) gamma_1_base
        rw [← kronStage_sub_right]
        congr 1
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [wittCreationBase, wittAnnihilationBase, gamma_1_base, Eminus]
      have hsq : globalChirality n * globalChirality n = 1 :=
        InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
      have hg0 : kronStage n (1 : Stage n) J1 ∈ S := by
        have hm := S.mul_mem hGamma h0
        rw [kronStage_mul, hsq, one_mul] at hm
        simpa [gamma_0_base] using hm
      have hg1 : kronStage n (1 : Stage n) Eminus ∈ S := by
        have hm := S.mul_mem hGamma h1
        rw [kronStage_mul, hsq, one_mul] at hm
        simpa [gamma_1_base] using hm
      have hep : kronStage n (1 : Stage n) Eplus ∈ S := by
        have hm := S.mul_mem hg0 hg1
        rw [kronStage_mul, mul_one] at hm
        have hneg : J1 * Eminus = -Eplus := by
          ext i j; fin_cases i <;> fin_cases j <;>
            norm_num [J1, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two]
        rw [hneg, kronStage_neg_right] at hm
        simpa using S.neg_mem hm
      have hone : kronStage n (1 : Stage n) (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ S := by
        have h11 : kronStage n (1 : Stage n) (1 : Matrix (Fin 2) (Fin 2) ℝ) = (1 : Stage (n + 1)) :=
          Matrix.one_kronecker_one
        rw [h11]
        exact S.one_mem
      have hB : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, kronStage n (1 : Stage n) B ∈ S := by
        intro B
        have hdec := mat2_decompose B
        rw [hdec, kronStage_add_right, kronStage_add_right, kronStage_add_right,
          kronStage_smul_right, kronStage_smul_right,
          kronStage_smul_right, kronStage_smul_right]
        exact S.add_mem (S.add_mem (S.add_mem
          (S.smul_mem hone _) (S.smul_mem hep _)) (S.smul_mem hg1 _)) (S.smul_mem hg0 _)
      have hAB : ∀ (A : Stage n) (B : Matrix (Fin 2) (Fin 2) ℝ), kronStage n A B ∈ S := by
        intro A B
        have hm := S.mul_mem (hstep A) (hB B)
        rwa [kronStage_mul, mul_one, one_mul] at hm
      intro M
      let e := Matrix.kroneckerAlgEquiv (TowerMatrix.Idx n) (Fin 2) ℝ
      have hM : M ∈ S := by
        rw [← e.apply_symm_apply M]
        induction (e.symm M) using TensorProduct.inductionOn with
        | tmul A B => exact hAB A B
        | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
      exact hM

theorem jwSplitStageHom_bijective (n : ℕ) :
    Function.Bijective (jwSplitStageHom n) := by
  have _inst := splitClNNAlg_finiteDimensional n
  have hdim_split := splitClNNAlg_finrank n
  have hdim : Module.finrank ℝ (Clsplit n) = Module.finrank ℝ (Stage n) := by
    rw [hdim_split]
    simp [Stage, Cl11TensorTower.MatStage, TowerMatrix.Mat, Module.finrank_matrix,
      TowerMatrix.idx_card_pow_two]
    rw [← mul_pow]; norm_num
  have hsurj : Function.Surjective (jwSplitStageHom n).toLinearMap :=
    jwSplitStageHom_surjective n
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- Unconditional finite-stage `ℝ`-algebra isomorphism `Clsplit n ≃ₐ[ℝ] Stage n` via
Jordan–Wigner strings, compatible with `splitCliffordStep n` and `stageEmbed n`. -/
def jwSplitStageEquiv (n : ℕ) : Clsplit n ≃ₐ[ℝ] Stage n :=
  AlgEquiv.ofBijective (jwSplitStageHom n) (jwSplitStageHom_bijective n)

@[simp] theorem jwSplitStageEquiv_apply (n : ℕ) (x : Clsplit n) :
    jwSplitStageEquiv n x = jwSplitStageHom n x := rfl

@[simp] theorem jwSplitStageEquiv_nativeJWCreation (n : ℕ) (k : Fin n) :
    jwSplitStageEquiv n (nativeJWCreation n k) = jwCreation n k :=
  jwSplitStageHom_nativeJWCreation n k

@[simp] theorem jwSplitStageEquiv_nativeJWAnnihilation (n : ℕ) (k : Fin n) :
    jwSplitStageEquiv n (nativeJWAnnihilation n k) = jwAnnihilation n k :=
  jwSplitStageHom_nativeJWAnnihilation n k

theorem jwSplitStageEquiv_bond (n : ℕ) (x : Clsplit n) :
    jwSplitStageEquiv (n + 1) (splitCliffordStep n x) =
      Cl11TensorTower.stageEmbed n (jwSplitStageEquiv n x) :=
  AlgHom.congr_fun (jwSplitStageHom_bond n) x

private theorem jwSplitStageEquiv_bond_iter (m n : ℕ) (h : m ≤ n) (x : Clsplit m) :
    (ofStage n).comp (jwSplitStageEquiv n).toAlgHom.toRingHom (splitCliffordMap m n h x) =
      (ofStage m).comp (jwSplitStageEquiv m).toAlgHom.toRingHom x := by
  induction n, h using Nat.le_induction with
  | base => simp [splitCliffordMap_refl]
  | succ n hn ih =>
      rw [splitCliffordMap_succ (m := m) (n := n) hn]
      change ofStage (n + 1) (jwSplitStageEquiv (n + 1)
          (splitCliffordStep n (splitCliffordMap m n hn x))) = _
      rw [jwSplitStageEquiv_bond, ofStage_apply_bond]
      exact ih

/-- Canonical stage embedding into `SplitCliffordInfinity` as an `ℝ`-algebra hom. -/
def ofSplitStage (n : ℕ) : Clsplit n →ₐ[ℝ] SplitCliffordInfinity :=
  DirectLimit.Algebra.of SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) n

private def ofStageAlgHom (n : ℕ) : Stage n →ₐ[ℝ] Limit where
  toRingHom := ofStage n
  commutes' r := (realAlgebraMap_stage n r).symm

private theorem jwSplitToLimit_compat (m n : ℕ) (h : m ≤ n) (x : Clsplit m) :
    (ofStageAlgHom n).comp (jwSplitStageEquiv n).toAlgHom (splitCliffordMap m n h x) =
      (ofStageAlgHom m).comp (jwSplitStageEquiv m).toAlgHom x := by
  exact jwSplitStageEquiv_bond_iter m n h x

private def splitInfToLimitHom : SplitCliffordInfinity →ₐ[ℝ] Limit :=
  DirectLimit.Algebra.lift SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) Limit
    (fun n => (ofStageAlgHom n).comp (jwSplitStageEquiv n).toAlgHom)
    jwSplitToLimit_compat

@[simp] private theorem splitInfToLimitHom_ofSplitStage (n : ℕ) (x : Clsplit n) :
    splitInfToLimitHom (ofSplitStage n x) = ofStage n (jwSplitStageEquiv n x) :=
  DirectLimit.Algebra.lift_of _ _ _ n x

private theorem limitToSplitInf_compat (m n : ℕ) (h : m ≤ n) (A : Stage m) :
    ((ofSplitStage n).comp (jwSplitStageEquiv n).symm.toAlgHom).toRingHom
        (bondMap stageBond m n h A) =
      ((ofSplitStage m).comp (jwSplitStageEquiv m).symm.toAlgHom).toRingHom A := by
  induction n, h using Nat.le_induction with
  | base => simp [bondMap_refl]
  | succ n hn ih =>
      rw [bondMap_succ]
      change ofSplitStage (n + 1) ((jwSplitStageEquiv (n + 1)).symm
          (Cl11TensorTower.stageEmbed n (bondMap stageBond m n hn A))) = _
      have hstep : (jwSplitStageEquiv (n + 1)).symm
          (Cl11TensorTower.stageEmbed n (bondMap stageBond m n hn A)) =
          splitCliffordStep n ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A)) := by
        apply (jwSplitStageEquiv (n + 1)).injective
        rw [AlgEquiv.apply_symm_apply, jwSplitStageEquiv_bond, AlgEquiv.apply_symm_apply]
      rw [hstep]
      have hmap : splitCliffordStep n ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A)) =
          splitCliffordMap n (n + 1) (Nat.le_succ n)
            ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A)) := by
        rw [splitCliffordMap_succ (m := n) (n := n) le_rfl, splitCliffordMap_refl]
        rfl
      have hof : ofSplitStage (n + 1)
          (splitCliffordStep n ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A))) =
          ofSplitStage n ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A)) := by
        rw [hmap]
        exact DirectLimit.Algebra.of_f (f := fun i j hij => splitCliffordMap i j hij)
          (Nat.le_succ n) ((jwSplitStageEquiv n).symm (bondMap stageBond m n hn A))
      rw [hof]
      exact ih

private def limitToSplitInfHom : Limit →ₐ[ℝ] SplitCliffordInfinity where
  toRingHom := DirectLimit.Ring.lift Stage (fun m n h => bondMap stageBond m n h)
    SplitCliffordInfinity
    (fun n => ((ofSplitStage n).comp (jwSplitStageEquiv n).symm.toAlgHom).toRingHom)
    limitToSplitInf_compat
  commutes' r := by
    change DirectLimit.Ring.lift Stage (fun m n h => bondMap stageBond m n h)
      SplitCliffordInfinity
      (fun n => ((ofSplitStage n).comp (jwSplitStageEquiv n).symm.toAlgHom).toRingHom)
      limitToSplitInf_compat (DirectLimit.Ring.of Stage (fun m n h => bondMap stageBond m n h) 0
        (algebraMap ℝ (Stage 0) r)) = algebraMap ℝ SplitCliffordInfinity r
    rw [DirectLimit.Ring.lift_of]
    exact ((ofSplitStage 0).comp (jwSplitStageEquiv 0).symm.toAlgHom).commutes r

@[simp] private theorem limitToSplitInfHom_ofStage (n : ℕ) (A : Stage n) :
    limitToSplitInfHom (ofStage n A) = ofSplitStage n ((jwSplitStageEquiv n).symm A) :=
  DirectLimit.Ring.lift_of _ _ limitToSplitInf_compat n A

/-- Unconditional `ℝ`-algebra isomorphism between the native direct limit
`SplitCliffordInfinity` and the matrix direct limit `Cl11TensorTowerLimit.Limit`,
built from `jwSplitStageEquiv` (unlike `SplitCliffordMatrixLimitSoldering.matrixLimitMap`,
which requires the false `BondCoherence` hypothesis for `spinorRepresentation`). -/
def splitCliffordInfinityEquivLimit : SplitCliffordInfinity ≃ₐ[ℝ] Limit :=
  AlgEquiv.ofAlgHom splitInfToLimitHom limitToSplitInfHom
    (by
      apply AlgHom.ext; intro y
      induction y using DirectLimit.induction with
      | _ n A =>
          change splitInfToLimitHom (limitToSplitInfHom (ofStage n A)) = ofStage n A
          rw [limitToSplitInfHom_ofStage, splitInfToLimitHom_ofSplitStage, AlgEquiv.apply_symm_apply])
    (by
      apply DirectLimit.Algebra.hom_ext
      intro n
      apply AlgHom.ext; intro x
      change limitToSplitInfHom (splitInfToLimitHom (ofSplitStage n x)) = ofSplitStage n x
      rw [splitInfToLimitHom_ofSplitStage, limitToSplitInfHom_ofStage, AlgEquiv.symm_apply_apply])

@[simp] theorem splitCliffordInfinityEquivLimit_ofSplitStage (n : ℕ) (x : Clsplit n) :
    splitCliffordInfinityEquivLimit (ofSplitStage n x) = ofStage n (jwSplitStageEquiv n x) :=
  splitInfToLimitHom_ofSplitStage n x

@[simp] theorem splitCliffordInfinityEquivLimit_symm_ofStage (n : ℕ) (A : Stage n) :
    splitCliffordInfinityEquivLimit.symm (ofStage n A) =
      ofSplitStage n ((jwSplitStageEquiv n).symm A) :=
  limitToSplitInfHom_ofStage n A

/-- `splitCliffordInfinityInvolute` upgraded to an `ℝ`-algebra equivalence. -/
def splitCliffordInfinityInvoluteEquiv :
    SplitCliffordInfinity ≃ₐ[ℝ] SplitCliffordInfinity :=
  AlgEquiv.ofBijective splitCliffordInfinityInvolute
    (Function.Involutive.bijective splitCliffordInfinityInvolute_involutive)

@[simp] theorem splitCliffordInfinityInvoluteEquiv_apply (x : SplitCliffordInfinity) :
    splitCliffordInfinityInvoluteEquiv x = splitCliffordInfinityInvolute x := rfl

private def stageChiralityConjAlgHom (n : ℕ) : Stage n →ₐ[ℝ] Stage n where
  toRingHom := stageChiralityConj n
  commutes' r := by
    change globalChirality n * algebraMap ℝ (Stage n) r * globalChirality n =
      algebraMap ℝ (Stage n) r
    have hcomm : globalChirality n * algebraMap ℝ (Stage n) r =
        algebraMap ℝ (Stage n) r * globalChirality n :=
      (Algebra.commutes r (globalChirality n)).symm
    rw [hcomm, mul_assoc, InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n, mul_one]

private theorem stageChiralityConj_jwMajoranaPlus (n : ℕ) (k : Fin n) :
    stageChiralityConj n (jwMajoranaPlus n k) = -jwMajoranaPlus n k := by
  have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
  have hc :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwCreation n k
  have ha :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwAnnihilation n k
  have h1 : stageChiralityConj n (jwCreation n k) = -jwCreation n k := by
    change globalChirality n * jwCreation n k * globalChirality n = -jwCreation n k
    calc globalChirality n * jwCreation n k * globalChirality n
        = -(jwCreation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left hc, neg_mul, mul_assoc]
      _ = -jwCreation n k := by rw [hΓ, mul_one]
  have h2 : stageChiralityConj n (jwAnnihilation n k) = -jwAnnihilation n k := by
    change globalChirality n * jwAnnihilation n k * globalChirality n = -jwAnnihilation n k
    calc globalChirality n * jwAnnihilation n k * globalChirality n
        = -(jwAnnihilation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left ha, neg_mul, mul_assoc]
      _ = -jwAnnihilation n k := by rw [hΓ, mul_one]
  dsimp [jwMajoranaPlus]
  rw [map_add, h1, h2, neg_add]

private theorem stageChiralityConj_jwMajoranaMinus (n : ℕ) (k : Fin n) :
    stageChiralityConj n (jwMajoranaMinus n k) = -jwMajoranaMinus n k := by
  have hΓ := InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq n
  have hc :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwCreation n k
  have ha :=
    InfoGeometry.Canonical.Cl11TensorTowerGlobalParity.globalChirality_anticomm_jwAnnihilation n k
  have h1 : stageChiralityConj n (jwCreation n k) = -jwCreation n k := by
    change globalChirality n * jwCreation n k * globalChirality n = -jwCreation n k
    calc globalChirality n * jwCreation n k * globalChirality n
        = -(jwCreation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left hc, neg_mul, mul_assoc]
      _ = -jwCreation n k := by rw [hΓ, mul_one]
  have h2 : stageChiralityConj n (jwAnnihilation n k) = -jwAnnihilation n k := by
    change globalChirality n * jwAnnihilation n k * globalChirality n = -jwAnnihilation n k
    calc globalChirality n * jwAnnihilation n k * globalChirality n
        = -(jwAnnihilation n k * (globalChirality n * globalChirality n)) := by
          rw [eq_neg_of_add_eq_zero_left ha, neg_mul, mul_assoc]
      _ = -jwAnnihilation n k := by rw [hΓ, mul_one]
  dsimp [jwMajoranaMinus]
  rw [map_sub, h1, h2]
  abel

theorem jwSplitStageEquiv_involute (n : ℕ) (x : Clsplit n) :
    jwSplitStageEquiv n (CliffordAlgebra.involute x) =
      stageChiralityConj n (jwSplitStageEquiv n x) := by
  have hhom :
      (jwSplitStageEquiv n).toAlgHom.comp (CliffordAlgebra.involute (Q := Qsplit n)) =
        (stageChiralityConjAlgHom n).comp (jwSplitStageEquiv n).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      CliffordAlgebra.involute_ι, map_neg]
    change -(jwSplitStageHom n (CliffordAlgebra.ι (Qsplit n) v)) =
      stageChiralityConjAlgHom n (jwSplitStageHom n (CliffordAlgebra.ι (Qsplit n) v))
    let f : Fin n ⊕ Fin n → ℝ := splitSpaceToJWEquiv n v
    have hf : f = ∑ s : Fin n ⊕ Fin n, f s • Pi.single s (1 : ℝ) := by
      funext t
      simp [f, Finset.sum_apply, Pi.single_apply]
    have hι : CliffordAlgebra.ι (Qsplit n) v =
        ∑ s : Fin n ⊕ Fin n, f s •
          CliffordAlgebra.ι (Qsplit n) ((splitSpaceToJWEquiv n).symm (Pi.single s (1 : ℝ))) := by
      have hv : v = ∑ s : Fin n ⊕ Fin n, f s •
          (splitSpaceToJWEquiv n).symm (Pi.single s (1 : ℝ)) := by
        apply (splitSpaceToJWEquiv n).injective
        rw [map_sum]
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        exact hf
      conv_lhs => rw [hv]
      rw [map_sum]
      simp only [map_smul]
    rw [hι, map_sum, map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [map_smul, map_smul, ← smul_neg]
    congr 1
    dsimp [jwSplitStageHom]
    rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
    change -(jwCliffordRepresentation n
      (CliffordAlgebra.ι _ (splitSpaceToJWEquiv n ((splitSpaceToJWEquiv n).symm (Pi.single s 1))))) =
      stageChiralityConjAlgHom n (jwCliffordRepresentation n
        (CliffordAlgebra.ι _ (splitSpaceToJWEquiv n ((splitSpaceToJWEquiv n).symm (Pi.single s 1)))))
    rw [LinearEquiv.apply_symm_apply, jwCliffordRepresentation_basis]
    cases s with
    | inl k => exact (stageChiralityConj_jwMajoranaPlus n k).symm
    | inr k => exact (stageChiralityConj_jwMajoranaMinus n k).symm
  exact AlgHom.congr_fun hhom x

theorem splitCliffordInfinityEquivLimit_involute (x : SplitCliffordInfinity) :
    splitCliffordInfinityEquivLimit (splitCliffordInfinityInvoluteEquiv x) =
      limitChiralityAlgEquiv (splitCliffordInfinityEquivLimit x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change splitCliffordInfinityEquivLimit (splitCliffordInfinityInvolute (ofSplitStage n a)) =
        limitChiralityConj (splitCliffordInfinityEquivLimit (ofSplitStage n a))
      dsimp only [ofSplitStage]
      rw [splitCliffordInfinityInvolute_ofStage]
      change splitCliffordInfinityEquivLimit (ofSplitStage n (CliffordAlgebra.involute a)) =
        limitChiralityConj (splitCliffordInfinityEquivLimit (ofSplitStage n a))
      rw [splitCliffordInfinityEquivLimit_ofSplitStage,
        splitCliffordInfinityEquivLimit_ofSplitStage, limitChiralityConj_ofStage]
      exact congrArg (ofStage n) (jwSplitStageEquiv_involute n a)

theorem splitCliffordInfinityEquivLimit_symm_involute (y : Limit) :
    splitCliffordInfinityEquivLimit.symm (limitChiralityAlgEquiv y) =
      splitCliffordInfinityInvoluteEquiv (splitCliffordInfinityEquivLimit.symm y) := by
  apply splitCliffordInfinityEquivLimit.injective
  rw [AlgEquiv.apply_symm_apply, splitCliffordInfinityEquivLimit_involute,
    AlgEquiv.apply_symm_apply]

/-- Transported Jordan–Wigner graded differential on the native split Clifford direct limit
`SplitCliffordInfinity`. -/
def splitJWDifferential (n : ℕ) (k : Fin n) : Module.End ℝ SplitCliffordInfinity :=
  gradedAdjoint splitCliffordInfinityInvoluteEquiv (ofSplitStage n (nativeJWCreation n k))

/-- Transported Jordan–Wigner contracting homotopy on `SplitCliffordInfinity`. -/
def splitJWHomotopy (n : ℕ) (k : Fin n) : Module.End ℝ SplitCliffordInfinity :=
  LinearMap.mulLeft ℝ (ofSplitStage n (nativeJWAnnihilation n k))

theorem splitJWDifferential_intertwines (n : ℕ) (k : Fin n) (x : SplitCliffordInfinity) :
    splitCliffordInfinityEquivLimit (splitJWDifferential n k x) =
      jwDifferential n k (splitCliffordInfinityEquivLimit x) := by
  unfold splitJWDifferential jwDifferential
  rw [gradedAdjoint_apply, gradedAdjoint_apply, map_sub, map_mul, map_mul,
    splitCliffordInfinityEquivLimit_involute, splitCliffordInfinityEquivLimit_ofSplitStage,
    jwSplitStageEquiv_nativeJWCreation]

theorem splitJWDifferential_conj (n : ℕ) (k : Fin n) :
    splitCliffordInfinityEquivLimit.toLinearEquiv.conjAlgEquiv ℝ (splitJWDifferential n k) =
      jwDifferential n k := by
  ext y
  rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change splitCliffordInfinityEquivLimit
    (splitJWDifferential n k (splitCliffordInfinityEquivLimit.symm y)) = jwDifferential n k y
  rw [splitJWDifferential_intertwines, AlgEquiv.apply_symm_apply]

theorem splitJWHomotopy_intertwines (n : ℕ) (k : Fin n) (x : SplitCliffordInfinity) :
    splitCliffordInfinityEquivLimit (splitJWHomotopy n k x) =
      jwHomotopy n k (splitCliffordInfinityEquivLimit x) := by
  change splitCliffordInfinityEquivLimit (ofSplitStage n (nativeJWAnnihilation n k) * x) =
    ofStage n (jwAnnihilation n k) * splitCliffordInfinityEquivLimit x
  rw [map_mul, splitCliffordInfinityEquivLimit_ofSplitStage, jwSplitStageEquiv_nativeJWAnnihilation]

theorem splitJWDifferential_sq (n : ℕ) (k : Fin n) :
    splitJWDifferential n k * splitJWDifferential n k = 0 := by
  apply (splitCliffordInfinityEquivLimit.toLinearEquiv.conjAlgEquiv ℝ).injective
  rw [map_mul, map_zero, splitJWDifferential_conj, jwDifferential_sq]

theorem splitJWHomotopy_sq (n : ℕ) (k : Fin n) :
    splitJWHomotopy n k * splitJWHomotopy n k = 0 := by
  apply LinearMap.ext; intro x
  apply splitCliffordInfinityEquivLimit.injective
  have hx : splitCliffordInfinityEquivLimit ((splitJWHomotopy n k * splitJWHomotopy n k) x) =
      (jwHomotopy n k * jwHomotopy n k) (splitCliffordInfinityEquivLimit x) := by
    change splitCliffordInfinityEquivLimit (splitJWHomotopy n k (splitJWHomotopy n k x)) =
      jwHomotopy n k (jwHomotopy n k (splitCliffordInfinityEquivLimit x))
    rw [splitJWHomotopy_intertwines, splitJWHomotopy_intertwines]
  rw [hx, jwHomotopy_sq, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem splitJWDifferential_annihilation (n : ℕ) (k : Fin n) :
    splitJWDifferential n k (ofSplitStage n (nativeJWAnnihilation n k)) = 1 := by
  apply splitCliffordInfinityEquivLimit.injective
  rw [splitJWDifferential_intertwines, splitCliffordInfinityEquivLimit_ofSplitStage,
    jwSplitStageEquiv_nativeJWAnnihilation, jwDifferential_annihilation, map_one]

theorem splitJWDifferential_ne_zero (n : ℕ) (k : Fin n) : splitJWDifferential n k ≠ 0 := by
  intro h
  have hz := congrArg (fun T : Module.End ℝ SplitCliffordInfinity =>
    T (ofSplitStage n (nativeJWAnnihilation n k))) h
  change splitJWDifferential n k (ofSplitStage n (nativeJWAnnihilation n k)) = 0 at hz
  rw [splitJWDifferential_annihilation] at hz
  exact one_ne_zero hz

theorem splitJWDifferential_homotopy (n : ℕ) (k : Fin n) :
    splitJWDifferential n k * splitJWHomotopy n k +
      splitJWHomotopy n k * splitJWDifferential n k = 1 := by
  apply LinearMap.ext; intro x
  apply splitCliffordInfinityEquivLimit.injective
  have h1 : splitCliffordInfinityEquivLimit
      ((splitJWDifferential n k * splitJWHomotopy n k +
        splitJWHomotopy n k * splitJWDifferential n k) x) =
      (jwDifferential n k * jwHomotopy n k +
        jwHomotopy n k * jwDifferential n k) (splitCliffordInfinityEquivLimit x) := by
    change splitCliffordInfinityEquivLimit
      (splitJWDifferential n k (splitJWHomotopy n k x) +
        splitJWHomotopy n k (splitJWDifferential n k x)) =
      jwDifferential n k (jwHomotopy n k (splitCliffordInfinityEquivLimit x)) +
        jwHomotopy n k (jwDifferential n k (splitCliffordInfinityEquivLimit x))
    rw [map_add, splitJWDifferential_intertwines, splitJWHomotopy_intertwines,
      splitJWHomotopy_intertwines, splitJWDifferential_intertwines]
  rw [h1, jwDifferential_homotopy]
  rfl

theorem splitJWDifferential_range_eq_ker (n : ℕ) (k : Fin n) :
    LinearMap.range (splitJWDifferential n k) = LinearMap.ker (splitJWDifferential n k) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (splitJWDifferential_sq n k)
  · intro x hx
    apply LinearMap.mem_range.mpr
    refine ⟨splitJWHomotopy n k x, ?_⟩
    have hcon := congrArg (fun T : Module.End ℝ SplitCliffordInfinity => T x)
      (splitJWDifferential_homotopy n k)
    change splitJWDifferential n k (splitJWHomotopy n k x) +
      splitJWHomotopy n k (splitJWDifferential n k x) = x at hcon
    have hzero : splitJWDifferential n k x = 0 := LinearMap.mem_ker.mp hx
    rw [hzero, map_zero, add_zero] at hcon
    exact hcon

theorem splitJWDifferential_leibniz (n : ℕ) (k : Fin n) (x y : SplitCliffordInfinity) :
    splitJWDifferential n k (x * y) =
      splitJWDifferential n k x * y +
        splitCliffordInfinityInvolute x * splitJWDifferential n k y := by
  unfold splitJWDifferential
  exact gradedAdjoint_leibniz splitCliffordInfinityInvoluteEquiv
    (ofSplitStage n (nativeJWCreation n k)) x y

/-- Explicit non-commutativity witness for the local `Cl(1,1)` matrix algebra `M₂(ℝ)`
underlying the Jordan–Wigner spinor stages. -/
theorem mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨J1, Eminus, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h00

end CanonicalUHFAndSplitLimitSoldering

section FiniteStageNativeChainDifferentials

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Canonical.SplitCliffordDirectLimit

/-- `nativeParity n` (`CliffordAlgebra.involute (Q := Qsplit n)`) as an `ℝ`-algebra
equivalence on `Clsplit n`. -/
def nativeParityAlgEquiv (n : ℕ) : Clsplit n ≃ₐ[ℝ] Clsplit n :=
  AlgEquiv.ofBijective (nativeParity n)
    (Function.Involutive.bijective (CliffordAlgebra.involute_involutive (Q := Qsplit n)))

@[simp] theorem nativeParityAlgEquiv_apply (n : ℕ) (x : Clsplit n) :
    nativeParityAlgEquiv n x = nativeParity n x := rfl

/-- Finite-stage graded differential on `Clsplit n` induced by the null creation chain
`singleSiteChain n k nullPlus`. -/
def nativeChainDifferential (n : ℕ) (k : Fin n) : Module.End ℝ (Clsplit n) :=
  gradedAdjoint (nativeParityAlgEquiv n) (singleSiteChain n k nullPlus)

/-- Finite-stage contracting homotopy on `Clsplit n` induced by left multiplication by
`singleSiteChain n k nullMinus`. -/
def nativeChainHomotopy (n : ℕ) (k : Fin n) : Module.End ℝ (Clsplit n) :=
  LinearMap.mulLeft ℝ (singleSiteChain n k nullMinus)

theorem nativeParity_singleSiteChain_nullPlus (n : ℕ) (k : Fin n) :
    nativeParity n (singleSiteChain n k nullPlus) = -(singleSiteChain n k nullPlus) := by
  simpa using singleSiteChain_homogeneous n k nullPlus true (by simp [involute_nullPlus])

theorem nativeParity_singleSiteChain_nullMinus (n : ℕ) (k : Fin n) :
    nativeParity n (singleSiteChain n k nullMinus) = -(singleSiteChain n k nullMinus) := by
  simpa using singleSiteChain_homogeneous n k nullMinus true (by simp [involute_nullMinus])

theorem nativeChainDifferential_sq (n : ℕ) (k : Fin n) :
    nativeChainDifferential n k * nativeChainDifferential n k = 0 := by
  unfold nativeChainDifferential
  rw [gradedAdjoint_square (nativeParityAlgEquiv n)
    (CliffordAlgebra.involute_involutive (Q := Qsplit n)) _
    (nativeParity_singleSiteChain_nullPlus n k)]
  simp [singleSiteChain_nullPlus_sq]

theorem nativeChainHomotopy_sq (n : ℕ) (k : Fin n) :
    nativeChainHomotopy n k * nativeChainHomotopy n k = 0 := by
  apply LinearMap.ext; intro x
  change singleSiteChain n k nullMinus * (singleSiteChain n k nullMinus * x) = 0
  rw [← mul_assoc, singleSiteChain_nullMinus_sq, zero_mul]

theorem nativeChainDifferential_annihilation (n : ℕ) (k : Fin n) :
    nativeChainDifferential n k (singleSiteChain n k nullMinus) = 1 := by
  unfold nativeChainDifferential
  rw [gradedAdjoint_of_odd (nativeParityAlgEquiv n) _ _
    (nativeParity_singleSiteChain_nullMinus n k)]
  exact singleSiteChain_null_car n k

theorem nativeChainDifferential_ne_zero (n : ℕ) (k : Fin n) :
    nativeChainDifferential n k ≠ 0 := by
  intro h
  have hz := congrArg (fun T : Module.End ℝ (Clsplit n) => T (singleSiteChain n k nullMinus)) h
  change nativeChainDifferential n k (singleSiteChain n k nullMinus) = 0 at hz
  rw [nativeChainDifferential_annihilation] at hz
  exact one_ne_zero hz

theorem nativeChainDifferential_homotopy (n : ℕ) (k : Fin n) :
    nativeChainDifferential n k * nativeChainHomotopy n k +
      nativeChainHomotopy n k * nativeChainDifferential n k = 1 := by
  apply LinearMap.ext; intro x
  change nativeChainDifferential n k (singleSiteChain n k nullMinus * x) +
    singleSiteChain n k nullMinus * nativeChainDifferential n k x = x
  have hder := gradedAdjoint_leibniz (nativeParityAlgEquiv n)
    (singleSiteChain n k nullPlus) (singleSiteChain n k nullMinus) x
  change nativeChainDifferential n k (singleSiteChain n k nullMinus * x) =
    nativeChainDifferential n k (singleSiteChain n k nullMinus) * x +
      nativeParity n (singleSiteChain n k nullMinus) * nativeChainDifferential n k x at hder
  rw [hder, nativeChainDifferential_annihilation, nativeParity_singleSiteChain_nullMinus,
    one_mul, neg_mul]
  abel

theorem nativeChainDifferential_range_eq_ker (n : ℕ) (k : Fin n) :
    LinearMap.range (nativeChainDifferential n k) =
      LinearMap.ker (nativeChainDifferential n k) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (nativeChainDifferential_sq n k)
  · intro x hx
    apply LinearMap.mem_range.mpr
    refine ⟨nativeChainHomotopy n k x, ?_⟩
    have hcon := congrArg (fun T : Module.End ℝ (Clsplit n) => T x)
      (nativeChainDifferential_homotopy n k)
    change nativeChainDifferential n k (nativeChainHomotopy n k x) +
      nativeChainHomotopy n k (nativeChainDifferential n k x) = x at hcon
    have hzero : nativeChainDifferential n k x = 0 := LinearMap.mem_ker.mp hx
    rw [hzero, map_zero, add_zero] at hcon
    exact hcon

theorem nativeChainDifferential_leibniz (n : ℕ) (k : Fin n) (x y : Clsplit n) :
    nativeChainDifferential n k (x * y) =
      nativeChainDifferential n k x * y + nativeParity n x * nativeChainDifferential n k y := by
  unfold nativeChainDifferential
  exact gradedAdjoint_leibniz (nativeParityAlgEquiv n) (singleSiteChain n k nullPlus) x y

private theorem nativeChain_update_sub (n : ℕ) (k : Fin n)
    (a : Fin n → CliffordAlgebra q11) (u v : CliffordAlgebra q11) :
    nativeChain n (Function.update a k (u - v)) =
      nativeChain n (Function.update a k u) - nativeChain n (Function.update a k v) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · rw [nativeChain, nativeChain, nativeChain]
        have htail : ∀ w, Fin.tail (Function.update a 0 w) = Fin.tail a := fun w => by
          funext i; simp [Fin.tail, Function.update]
        rw [htail (u - v), htail u, htail v, Function.update_self, Function.update_self,
          Function.update_self, sub_eq_add_neg, consNative_add_head, consNative_neg_head,
          ← sub_eq_add_neg]
      · intro k'
        rw [nativeChain, nativeChain, nativeChain]
        have h0 : ∀ w, Function.update a k'.succ w 0 = a 0 := fun w =>
          Function.update_of_ne (Fin.succ_ne_zero k').symm _ _
        have htail : ∀ w, Fin.tail (Function.update a k'.succ w) =
            Function.update (Fin.tail a) k' w := fun w => by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        rw [h0 (u - v), h0 u, h0 v, htail (u - v), htail u, htail v, ih k', map_sub]

private theorem nativeChain_update_neg (n : ℕ) (k : Fin n)
    (a : Fin n → CliffordAlgebra q11) (u : CliffordAlgebra q11) :
    nativeChain n (Function.update a k (-u)) =
      -(nativeChain n (Function.update a k u)) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · rw [nativeChain, nativeChain]
        have htail : ∀ w, Fin.tail (Function.update a 0 w) = Fin.tail a := fun w => by
          funext i; simp [Fin.tail, Function.update]
        rw [htail (-u), htail u, Function.update_self, Function.update_self, consNative_neg_head]
      · intro k'
        rw [nativeChain, nativeChain]
        have h0 : ∀ w, Function.update a k'.succ w 0 = a 0 := fun w =>
          Function.update_of_ne (Fin.succ_ne_zero k').symm _ _
        have htail : ∀ w, Fin.tail (Function.update a k'.succ w) =
            Function.update (Fin.tail a) k' w := fun w => by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        rw [h0 (-u), h0 u, htail (-u), htail u, ih k', map_neg]

/-- Action of `nativeChainDifferential n k` on any homogeneous `nativeChain n a`, exposing the
Jordan–Wigner `prefixParity` sign and the single-site supercommutator at `k`. -/
theorem nativeChainDifferential_nativeChain (n : ℕ) (k : Fin n)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (ha : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    nativeChainDifferential n k (nativeChain n a) =
      (if prefixParity n p k then (-1 : ℝ) else 1) •
        nativeChain n (Function.update a k
          (nullPlus * a k - (if p k then -(a k) else a k) * nullPlus)) := by
  unfold nativeChainDifferential
  rw [gradedAdjoint_apply, nativeParityAlgEquiv_apply]
  have h1 := singleSiteChain_mul_nativeChain_homogeneous n k nullPlus involute_nullPlus a p ha
  have h2 := nativeChain_mul_singleSiteChain_homogeneous n k nullPlus involute_nullPlus a p ha
  have hpar := nativeChain_homogeneous n a p ha
  have htot_xor := totalParity_xor_suffixParity n p k
  rw [h1, hpar]
  have hterm2 : (if totalParity n p then -nativeChain n a else nativeChain n a) *
      singleSiteChain n k nullPlus =
      (if prefixParity n p k then (-1 : ℝ) else 1) •
        nativeChain n (Function.update a k ((if p k then -(a k) else a k) * nullPlus)) := by
    cases htot : totalParity n p <;> cases hsuf : suffixParity n p k <;>
      cases hpre : prefixParity n p k <;> cases hpk : p k <;>
      simp [htot, hsuf, hpre, hpk] at htot_xor <;>
      simp [hsuf, h2, nativeChain_update_neg, neg_mul]
  rw [hterm2, nativeChain_update_sub, smul_sub]

/-- Matrix readback of `nativeChainDifferential n k` on a homogeneous chain via
`nativeChain_matrix_suffixParity`. -/
theorem leftMatrixEquiv_nativeChainDifferential_homogeneous (n : ℕ) (k : Fin n)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (ha : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    leftMatrixEquiv n (nativeChainDifferential n k (nativeChain n a)) =
      (if prefixParity n p k then (-1 : ℝ) else 1) •
        ordinaryChain n (fun j =>
          cl11EquivMat
            (Function.update a k (nullPlus * a k - (if p k then -(a k) else a k) * nullPlus) j *
              J1_cl ^ (suffixParity n (Function.update p k !(p k)) j).toNat)) := by
  rw [nativeChainDifferential_nativeChain n k a p ha, map_smul]
  congr 1
  apply nativeChain_matrix_suffixParity
  intro i
  by_cases hi : i = k
  · subst hi
    simp only [Function.update_self]
    cases hp : p i
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.not_false, map_sub, map_mul,
        involute_nullPlus, ha i]
      noncomm_ring
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.not_true, map_sub, map_mul, map_neg,
        involute_nullPlus, ha i]
      noncomm_ring
  · simp [Function.update_of_ne hi, ha i]

/-- Site-order duality: `singleSiteChain n k` (site `0` outermost left) agrees with
`splitCoord n (Fin.rev k)` (site `0` innermost right). -/
theorem singleSiteChain_iota_eq_splitCoord_rev (n : ℕ) (k : Fin n) (v : ℝ × ℝ) :
    singleSiteChain n k (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι (Qsplit n) (splitCoord n (Fin.rev k) v) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · rw [singleSiteChain_zero, Fin.rev_zero, splitCoord_last]
        change (headTensorEquiv n).symm (CliffordAlgebra.ι q11 v ᵍ⊗ₜ 1) =
          CliffordAlgebra.ι (Qsplit (n + 1)) (v, 0)
        apply (headTensorEquiv n).injective
        rw [AlgEquiv.apply_symm_apply]
        symm
        rw [headTensorEquiv_ι]
        simp
      · intro k'
        rw [singleSiteChain_succ, ih k', Fin.rev_succ, splitCoord_castSucc]
        apply (headTensorEquiv n).injective
        change headTensorEquiv n (consNative n 1 (CliffordAlgebra.ι (Qsplit n) (splitCoord n (Fin.rev k') v))) =
          headTensorEquiv n (CliffordAlgebra.ι (Qsplit (n + 1)) (InfoGeometry.Clifford.ClNN.tailLift n (splitCoord n (Fin.rev k') v)))
        rw [consNative_apply, AlgEquiv.apply_symm_apply, headTensorEquiv_ι]
        dsimp [InfoGeometry.Clifford.ClNN.tailLift]
        have hz0 : CliffordAlgebra.ι q11 ((0 : ℝ), (0 : ℝ)) = 0 := by
          rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, map_zero]
        rw [hz0]
        change 1 ᵍ⊗ₜ[ℝ] _ =
          GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
            ((0 : CliffordAlgebra q11) ⊗ₜ[ℝ] (1 : Clsplit n)) + 1 ᵍ⊗ₜ[ℝ] _
        rw [TensorProduct.zero_tmul, map_zero, zero_add]

theorem singleSiteChain_nullPlus_eq_nativeJWCreation_rev (n : ℕ) (k : Fin n) :
    singleSiteChain n k nullPlus = nativeJWCreation n (Fin.rev k) :=
  singleSiteChain_iota_eq_splitCoord_rev n k (1 / 2, 1 / 2)

theorem singleSiteChain_nullMinus_eq_nativeJWAnnihilation_rev (n : ℕ) (k : Fin n) :
    singleSiteChain n k nullMinus = nativeJWAnnihilation n (Fin.rev k) :=
  singleSiteChain_iota_eq_splitCoord_rev n k (1 / 2, -1 / 2)

/-- `ofSplitStage n` intertwines the finite-stage `nativeChainDifferential n k` with the colimit
`splitJWDifferential n (Fin.rev k)` (reflecting site-order duality between `consNative` and
`splitCliffordStep`). -/
theorem ofSplitStage_nativeChainDifferential (n : ℕ) (k : Fin n) (x : Clsplit n) :
    ofSplitStage n (nativeChainDifferential n k x) =
      splitJWDifferential n (Fin.rev k) (ofSplitStage n x) := by
  unfold nativeChainDifferential splitJWDifferential
  rw [gradedAdjoint_apply, gradedAdjoint_apply, map_sub, map_mul, map_mul]
  rw [singleSiteChain_nullPlus_eq_nativeJWCreation_rev]
  congr 2

/-- `ofSplitStage n` intertwines the finite-stage `nativeChainHomotopy n k` with
`splitJWHomotopy n (Fin.rev k)`. -/
theorem ofSplitStage_nativeChainHomotopy (n : ℕ) (k : Fin n) (x : Clsplit n) :
    ofSplitStage n (nativeChainHomotopy n k x) =
      splitJWHomotopy n (Fin.rev k) (ofSplitStage n x) := by
  change ofSplitStage n (singleSiteChain n k nullMinus * x) =
    ofSplitStage n (nativeJWAnnihilation n (Fin.rev k)) * ofSplitStage n x
  rw [map_mul, singleSiteChain_nullMinus_eq_nativeJWAnnihilation_rev]

end FiniteStageNativeChainDifferentials

end InfoGeometry.Clifford.Cl11GradedDifferential
