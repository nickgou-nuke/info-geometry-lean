import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Jordan-Wigner Cantor colimit lift

This file lifts the already verified finite real matrix/operator equivalences
to the direct-limit level.

The honest content is:

* the stagewise matrix-to-Cantor equivalences commute with the one-step bonds;
* this induces a canonical map from the matrix direct limit to the real
  Cantor direct limit;
* the inverse stagewise equivalences commute as well;
* therefore the two direct limits are canonically ring-equivalent.
-/

noncomputable section

namespace InfoGeometry.Canonical.JordanWignerCantorColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.MatToCantorOperator
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The matrix direct-limit carrier. -/
abbrev MatLimit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- The canonical finite-stage map into the matrix direct limit. -/
abbrev MatOfStage (n : ℕ) : MatStage n →+* MatLimit :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n

/-- The bonding map on the real Cantor operator tower. -/
abbrev realBond (n : ℕ) : RealCantorOp n →+* RealCantorOp (n + 1) :=
  (cantorOpEmbed n).toRingHom

/-- The real Cantor direct limit. -/
abbrev RealLimit : Type :=
  DirectLimitSuperClosure (Stage := RealCantorOp) realBond

/-- The canonical finite-stage map into the real Cantor direct limit. -/
def realOfStage (n : ℕ) : RealCantorOp n →+* RealLimit :=
  directLimitOf (Stage := RealCantorOp) realBond n

@[simp] theorem realOfStage_bond (n : ℕ) (x : RealCantorOp n) :
    realOfStage (n + 1) (realBond n x) = realOfStage n x := by
  simpa [realOfStage, realBond] using
    (directLimitOf_bond (Stage := RealCantorOp) realBond n x)

/-- Stagewise map from the matrix tower into the real Cantor direct limit. -/
def matToRealCone (n : ℕ) : MatStage n →+* RealLimit :=
  (realOfStage n).comp (matToCantor n).toRingHom

theorem matToRealCone_compat (n : ℕ) (A : MatStage n) :
    matToRealCone (n + 1) (matStageEmbed n A) = matToRealCone n A := by
  calc
    matToRealCone (n + 1) (matStageEmbed n A)
        = realOfStage (n + 1) (matToCantor (n + 1) (matStageEmbed n A)) := by
          rfl
    _ = realOfStage (n + 1) (cantorOpEmbed n (matToCantor n A)) := by
          rw [cantorOpEmbed_matToCantor]
    _ = realOfStage n (matToCantor n A) := by
          exact realOfStage_bond n (matToCantor n A)

/-- The matrix tower lifts canonically to the real Cantor direct limit. -/
def matToRealLimit : MatLimit →+* RealLimit :=
  directLimitLift (Stage := MatStage)
    (bond := InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond)
    matToRealCone matToRealCone_compat

@[simp] theorem matToRealLimit_ofStage (n : ℕ) (A : MatStage n) :
    matToRealLimit (MatOfStage n A) = realOfStage n (matToCantor n A) := by
  simpa [matToRealLimit, matToRealCone, MatOfStage] using
    (directLimitLift_of (Stage := MatStage)
      (bond := InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond)
      matToRealCone matToRealCone_compat n A)

/-- Stagewise inverse map from the real Cantor tower back to the matrix limit. -/
def realToMatCone (n : ℕ) : RealCantorOp n →+* MatLimit :=
  (MatOfStage n).comp (matToCantor n).symm.toRingHom

theorem realToMatCone_compat (n : ℕ) (B : RealCantorOp n) :
    realToMatCone (n + 1) (realBond n B) = realToMatCone n B := by
  have hs :
      (matToCantor (n + 1)).symm (realBond n B) =
        matStageEmbed n ((matToCantor n).symm B) := by
    apply (matToCantor (n + 1)).injective
    calc
      matToCantor (n + 1) ((matToCantor (n + 1)).symm (realBond n B)) = realBond n B := by
        simp
      _ = matToCantor (n + 1) (matStageEmbed n ((matToCantor n).symm B)) := by
        simpa [realBond] using
          (cantorOpEmbed_matToCantor (n := n) ((matToCantor n).symm B)).symm
  calc
    realToMatCone (n + 1) (realBond n B)
        = MatOfStage (n + 1) ((matToCantor (n + 1)).symm (realBond n B)) := by
            rfl
    _ = MatOfStage (n + 1) (matStageEmbed n ((matToCantor n).symm B)) := by
          rw [hs]
    _ = realToMatCone n B := by
          simpa [realToMatCone, MatOfStage]
            using (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond
              (n := n) (A := (matToCantor n).symm B))

/-- Stagewise inverse coherence for the finite bridge. -/
theorem inverse_coherence (n : ℕ) (B : RealCantorOp n) :
    matStageEmbed n ((matToCantor n).symm B) =
      (matToCantor (n + 1)).symm (realBond n B) := by
  apply (matToCantor (n + 1)).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa [realBond] using
    (cantorOpEmbed_matToCantor (n := n) ((matToCantor n).symm B)).symm

/-- The real Cantor tower lifts canonically back to the matrix direct limit. -/
def realToMatLimit : RealLimit →+* MatLimit :=
  directLimitLift (Stage := RealCantorOp) (bond := realBond) realToMatCone realToMatCone_compat

@[simp] theorem realToMatLimit_ofStage (n : ℕ) (B : RealCantorOp n) :
    realToMatLimit (realOfStage n B) = MatOfStage n ((matToCantor n).symm B) := by
  simpa [realToMatLimit, realToMatCone, MatOfStage] using
    (directLimitLift_of (Stage := RealCantorOp) (bond := realBond)
      realToMatCone realToMatCone_compat n B)

/-- The two colimit lifts are inverse on the real Cantor direct limit. -/
theorem matToRealLimit_comp_realToMatLimit :
    matToRealLimit.comp realToMatLimit = RingHom.id RealLimit := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext B
  show matToRealLimit (realToMatLimit (realOfStage n B)) = realOfStage n B
  rw [realToMatLimit_ofStage, matToRealLimit_ofStage]
  simp

/-- The two colimit lifts are inverse on the matrix direct limit. -/
theorem realToMatLimit_comp_matToRealLimit :
    realToMatLimit.comp matToRealLimit = RingHom.id MatLimit := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext A
  show realToMatLimit (matToRealLimit (MatOfStage n A)) = MatOfStage n A
  rw [matToRealLimit_ofStage, realToMatLimit_ofStage]
  exact congrArg (MatOfStage n) (AlgEquiv.symm_apply_apply (matToCantor n) A)

/-- The global direct-limit equivalence induced by the finite real bridge. -/
noncomputable def globalCantorInverseEquiv :
    RealLimit ≃+* MatLimit :=
  RingEquiv.ofBijective realToMatLimit
    ⟨by
      intro x y hxy
      have h := congrArg matToRealLimit hxy
      have hx : matToRealLimit (realToMatLimit x) = x := by
        have hx' := congrArg (fun f : RealLimit →+* RealLimit => f x)
          matToRealLimit_comp_realToMatLimit
        simpa using hx'
      have hy : matToRealLimit (realToMatLimit y) = y := by
        have hy' := congrArg (fun f : RealLimit →+* RealLimit => f y)
          matToRealLimit_comp_realToMatLimit
        simpa using hy'
      rw [hx, hy] at h
      exact h,
     by
      intro y
      refine ⟨matToRealLimit y, ?_⟩
      have hy := congrArg (fun f : MatLimit →+* MatLimit => f y)
        realToMatLimit_comp_matToRealLimit
      simpa using hy⟩

end InfoGeometry.Canonical.JordanWignerCantorColimit
