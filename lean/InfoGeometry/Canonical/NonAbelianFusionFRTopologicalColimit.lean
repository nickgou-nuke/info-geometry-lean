import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Colimit descent of the finite non-Abelian fusion actions

The finite fusion carrier is repeated along the categorical `ℕ` diagram with
identity transitions.  The continuous `F` and braid actions therefore descend
through the native `TopCat` direct colimit.  The stage equations are retained
explicitly; no sequence or analytic completion is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionFRTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.NonAbelianFusionFRBridge
open InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge
open FilteredColimit.Native.Topological

variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [ContinuousAdd K] [ContinuousMul K]

abbrev FusionCarrier (K : Type) := Matrix (Fin 2) (Fin 2) K

def fusionTopologicalDiagram : ℕ ⥤ TopCat :=
  (Functor.const ℕ).obj (TopCat.of (FusionCarrier K))

def fusionActionCocone
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K)) :
    Cocone (fusionTopologicalDiagram (K := K)) where
  pt := TopCat.of (FusionCarrier K)
  ι :=
    { app := fun _ => action
      naturality := by
        intro i j f
        change 𝟙 (TopCat.of (FusionCarrier K)) ≫ action = action
        simp }

noncomputable def fusionActionColimitMap
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K)) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      TopCat.of (FusionCarrier K) :=
  topologicalDirectDescend (fusionTopologicalDiagram (K := K))
    (fusionActionCocone (K := K) action)

theorem fusionActionColimitMap_stage
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K))
    (n : ℕ) (X : FusionCarrier K) :
    fusionActionColimitMap (K := K) action
        (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n X) =
      action X := by
  have h := topologicalDirectDescend_stage
    (fusionTopologicalDiagram (K := K))
    (fusionActionCocone (K := K) action) n
  exact congrArg (fun f => f X) h

def fusionActionColimitCocone
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K)) :
    Cocone (fusionTopologicalDiagram (K := K)) where
  pt := topologicalDirectColimit (fusionTopologicalDiagram (K := K))
  ι :=
    { app := fun n => action ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n
      naturality := by
        intro i j f
        have h := topologicalDirectInjection_naturality
          (fusionTopologicalDiagram (K := K)) f
        simpa only [fusionTopologicalDiagram, Category.id_comp,
          Category.comp_id, Category.assoc] using
          congrArg (fun q => action ≫ q) h }

noncomputable def fusionActionColimitEndomorphism
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K)) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTopologicalDiagram (K := K)) :=
  topologicalDirectDescend (fusionTopologicalDiagram (K := K))
    (fusionActionColimitCocone (K := K) action)

theorem fusionActionColimitEndomorphism_stage
    (action : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K))
    (n : ℕ) :
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
        fusionActionColimitEndomorphism (K := K) action =
      action ≫ topologicalDirectInjection
        (fusionTopologicalDiagram (K := K)) n := by
  exact topologicalDirectDescend_stage
    (fusionTopologicalDiagram (K := K))
    (fusionActionColimitCocone (K := K) action) n

def fusionFColimitAction (a b : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      TopCat.of (FusionCarrier K) :=
  fusionActionColimitMap (K := K) (fusionFLeftTopCatHom a b)

def fusionFColimitEndomorphism (a b : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTopologicalDiagram (K := K)) :=
  fusionActionColimitEndomorphism (K := K) (fusionFLeftTopCatHom a b)

def fusionBraid1ColimitAction (q1 q2 : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      TopCat.of (FusionCarrier K) :=
  fusionActionColimitMap (K := K) (fusionBraid1LeftTopCatHom q1 q2)

def fusionBraid2ColimitAction (a b q1 q2 : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      TopCat.of (FusionCarrier K) :=
  fusionActionColimitMap (K := K) (fusionBraid2LeftTopCatHom a b q1 q2)

def fusionBraid1ColimitEndomorphism (q1 q2 : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTopologicalDiagram (K := K)) :=
  fusionActionColimitEndomorphism (K := K) (fusionBraid1LeftTopCatHom q1 q2)

def fusionBraid2ColimitEndomorphism (a b q1 q2 : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTopologicalDiagram (K := K)) :=
  fusionActionColimitEndomorphism (K := K)
    (fusionBraid2LeftTopCatHom a b q1 q2)

/-! The composition is written in the order whose induced left matrix is
`(β₂ β₁)^3`; this matches the algebraic positive Coxeter lift. -/
def fusionFullTwistLeftTopCatHom (a b q1 q2 : K) :
    TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K) :=
    fusionBraid1LeftTopCatHom q1 q2 ≫
    fusionBraid2LeftTopCatHom a b q1 q2 ≫
    fusionBraid1LeftTopCatHom q1 q2 ≫
    fusionBraid2LeftTopCatHom a b q1 q2 ≫
    fusionBraid1LeftTopCatHom q1 q2 ≫
    fusionBraid2LeftTopCatHom a b q1 q2

def fusionFullTwistColimitEndomorphism (a b q1 q2 : K) :
    topologicalDirectColimit (fusionTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTopologicalDiagram (K := K)) :=
  fusionActionColimitEndomorphism (K := K)
    (fusionFullTwistLeftTopCatHom a b q1 q2)

theorem fusionFullTwistLeftTopCatHom_commutes_braid1
    (a b q1 q2 : K) (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionFullTwistLeftTopCatHom (K := K) a b q1 q2 ≫
        fusionBraid1LeftTopCatHom q1 q2 =
      fusionBraid1LeftTopCatHom q1 q2 ≫
        fusionFullTwistLeftTopCatHom (K := K) a b q1 q2 := by
  dsimp [fusionFullTwistLeftTopCatHom, fusionBraid1LeftTopCatHom,
    fusionBraid2LeftTopCatHom]
  simp only [matrixLeftTopCatHom_comp]
  congr 1
  let m1 : FusionCarrier K := braidGen1 K q1 q2
  let m2 : FusionCarrier K := braidGen2 K a b q1 q2
  have h := nonAbelian_artin_braid_relation K a b q1 q2 h_norm h_braid
  have hg1 : (m1 * m2 * m1) * m1 = m2 * (m1 * m2 * m1) := by
    calc
      _ = (m2 * m1 * m2) * m1 := by rw [h]
      _ = m2 * (m1 * m2 * m1) := by noncomm_ring
  have hg2 : (m1 * m2 * m1) * m2 = m1 * (m1 * m2 * m1) := by
    calc
      _ = m1 * (m2 * m1 * m2) := by noncomm_ring
      _ = m1 * (m1 * m2 * m1) := by rw [← h]
  have hfull : (m2 * m1) * (m2 * m1) * (m2 * m1) =
      (m1 * m2 * m1) * (m1 * m2 * m1) := by
    calc
      _ = (m2 * m1 * m2) * (m1 * m2 * m1) := by noncomm_ring
      _ = (m1 * m2 * m1) * (m1 * m2 * m1) := by rw [← h]
  have hcentral : (m1 * m2 * m1) * (m1 * m2 * m1) * m1 =
      m1 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by
    calc
      _ = (m1 * m2 * m1) * ((m1 * m2 * m1) * m1) := by noncomm_ring
      _ = (m1 * m2 * m1) * (m2 * (m1 * m2 * m1)) := by rw [hg1]
      _ = ((m1 * m2 * m1) * m2) * (m1 * m2 * m1) := by noncomm_ring
      _ = (m1 * (m1 * m2 * m1)) * (m1 * m2 * m1) := by rw [hg2]
      _ = m1 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by noncomm_ring
  have htarget : m1 * ((m2 * m1) * (m2 * m1) * (m2 * m1)) =
      ((m2 * m1) * (m2 * m1) * (m2 * m1)) * m1 := by
    calc
      _ = m1 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by rw [hfull]
      _ = ((m1 * m2 * m1) * (m1 * m2 * m1)) * m1 := hcentral.symm
      _ = _ := by rw [hfull]
  simpa only [Matrix.mul_assoc] using htarget

theorem fusionFullTwistLeftTopCatHom_commutes_braid2
    (a b q1 q2 : K) (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionFullTwistLeftTopCatHom (K := K) a b q1 q2 ≫
        fusionBraid2LeftTopCatHom a b q1 q2 =
      fusionBraid2LeftTopCatHom a b q1 q2 ≫
        fusionFullTwistLeftTopCatHom (K := K) a b q1 q2 := by
  dsimp [fusionFullTwistLeftTopCatHom, fusionBraid1LeftTopCatHom,
    fusionBraid2LeftTopCatHom]
  simp only [matrixLeftTopCatHom_comp]
  congr 1
  let m1 : FusionCarrier K := braidGen1 K q1 q2
  let m2 : FusionCarrier K := braidGen2 K a b q1 q2
  have h := nonAbelian_artin_braid_relation K a b q1 q2 h_norm h_braid
  have hg1 : (m1 * m2 * m1) * m1 = m2 * (m1 * m2 * m1) := by
    calc
      _ = (m2 * m1 * m2) * m1 := by rw [h]
      _ = m2 * (m1 * m2 * m1) := by noncomm_ring
  have hg2 : (m1 * m2 * m1) * m2 = m1 * (m1 * m2 * m1) := by
    calc
      _ = m1 * (m2 * m1 * m2) := by noncomm_ring
      _ = m1 * (m1 * m2 * m1) := by rw [← h]
  have hfull : (m2 * m1) * (m2 * m1) * (m2 * m1) =
      (m1 * m2 * m1) * (m1 * m2 * m1) := by
    calc
      _ = (m2 * m1 * m2) * (m1 * m2 * m1) := by noncomm_ring
      _ = (m1 * m2 * m1) * (m1 * m2 * m1) := by rw [← h]
  have hcentral : (m1 * m2 * m1) * (m1 * m2 * m1) * m2 =
      m2 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by
    calc
      _ = (m1 * m2 * m1) * ((m1 * m2 * m1) * m2) := by noncomm_ring
      _ = (m1 * m2 * m1) * (m1 * (m1 * m2 * m1)) := by rw [hg2]
      _ = ((m1 * m2 * m1) * m1) * (m1 * m2 * m1) := by noncomm_ring
      _ = (m2 * (m1 * m2 * m1)) * (m1 * m2 * m1) := by rw [hg1]
      _ = m2 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by noncomm_ring
  have htarget : m2 * ((m2 * m1) * (m2 * m1) * (m2 * m1)) =
      ((m2 * m1) * (m2 * m1) * (m2 * m1)) * m2 := by
    calc
      _ = m2 * ((m1 * m2 * m1) * (m1 * m2 * m1)) := by rw [hfull]
      _ = ((m1 * m2 * m1) * (m1 * m2 * m1)) * m2 := hcentral.symm
      _ = _ := by rw [hfull]
  simpa only [Matrix.mul_assoc] using htarget

theorem fusionFColimitAction_stage
    (a b : K) (n : ℕ) (X : FusionCarrier K) :
    fusionFColimitAction (K := K) a b
        (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n X) =
      fMatrix K a b * X := by
  exact fusionActionColimitMap_stage (K := K)
    (fusionFLeftTopCatHom a b) n X

theorem fusionFColimitEndomorphism_stage
    (a b : K) (n : ℕ) :
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
        fusionFColimitEndomorphism (K := K) a b =
      fusionFLeftTopCatHom a b ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
  exact fusionActionColimitEndomorphism_stage (K := K)
    (fusionFLeftTopCatHom a b) n

theorem fusionActionColimitEndomorphism_comp_stage
    (action₁ action₂ : TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K))
    (n : ℕ) :
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
        (fusionActionColimitEndomorphism (K := K) action₁ ≫
          fusionActionColimitEndomorphism (K := K) action₂) =
      (action₁ ≫ action₂) ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
  calc
    _ = (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
        fusionActionColimitEndomorphism (K := K) action₁) ≫
        fusionActionColimitEndomorphism (K := K) action₂ := by
          simp only [Category.assoc]
    _ = (action₁ ≫ topologicalDirectInjection
        (fusionTopologicalDiagram (K := K)) n) ≫
        fusionActionColimitEndomorphism (K := K) action₂ := by
          rw [fusionActionColimitEndomorphism_stage (K := K) action₁ n]
    _ = action₁ ≫ (topologicalDirectInjection
        (fusionTopologicalDiagram (K := K)) n ≫
        fusionActionColimitEndomorphism (K := K) action₂) := by
          simp only [Category.assoc]
    _ = action₁ ≫ (action₂ ≫ topologicalDirectInjection
        (fusionTopologicalDiagram (K := K)) n) := by
          rw [fusionActionColimitEndomorphism_stage (K := K) action₂ n]
    _ = (action₁ ≫ action₂) ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
          simp only [Category.assoc]

theorem fusionFullTwistColimitEndomorphism_stage
    (a b q1 q2 : K) (n : ℕ) :
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
        fusionFullTwistColimitEndomorphism (K := K) a b q1 q2 =
      fusionFullTwistLeftTopCatHom a b q1 q2 ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
  exact fusionActionColimitEndomorphism_stage (K := K)
    (fusionFullTwistLeftTopCatHom a b q1 q2) n

theorem fusionFullTwistColimitEndomorphism_commutes_braid1
    (a b q1 q2 : K) (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionFullTwistColimitEndomorphism (K := K) a b q1 q2 ≫
        fusionBraid1ColimitEndomorphism (K := K) q1 q2 =
      fusionBraid1ColimitEndomorphism (K := K) q1 q2 ≫
        fusionFullTwistColimitEndomorphism (K := K) a b q1 q2 := by
  apply colimit.hom_ext
  intro n
  change topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      (fusionActionColimitEndomorphism (K := K)
          (fusionFullTwistLeftTopCatHom a b q1 q2) ≫
        fusionActionColimitEndomorphism (K := K)
          (fusionBraid1LeftTopCatHom q1 q2)) =
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      (fusionActionColimitEndomorphism (K := K)
          (fusionBraid1LeftTopCatHom q1 q2) ≫
        fusionActionColimitEndomorphism (K := K)
          (fusionFullTwistLeftTopCatHom a b q1 q2))
  rw [fusionActionColimitEndomorphism_comp_stage,
    fusionActionColimitEndomorphism_comp_stage,
    fusionFullTwistLeftTopCatHom_commutes_braid1
      (K := K) a b q1 q2 h_norm h_braid]

theorem fusionFullTwistColimitEndomorphism_commutes_braid2
    (a b q1 q2 : K) (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionFullTwistColimitEndomorphism (K := K) a b q1 q2 ≫
        fusionBraid2ColimitEndomorphism (K := K) a b q1 q2 =
      fusionBraid2ColimitEndomorphism (K := K) a b q1 q2 ≫
        fusionFullTwistColimitEndomorphism (K := K) a b q1 q2 := by
  apply colimit.hom_ext
  intro n
  change topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      (fusionActionColimitEndomorphism (K := K)
          (fusionFullTwistLeftTopCatHom a b q1 q2) ≫
        fusionActionColimitEndomorphism (K := K)
          (fusionBraid2LeftTopCatHom a b q1 q2)) =
    topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      (fusionActionColimitEndomorphism (K := K)
          (fusionBraid2LeftTopCatHom a b q1 q2) ≫
        fusionActionColimitEndomorphism (K := K)
          (fusionFullTwistLeftTopCatHom a b q1 q2))
  rw [fusionActionColimitEndomorphism_comp_stage,
    fusionActionColimitEndomorphism_comp_stage,
    fusionFullTwistLeftTopCatHom_commutes_braid2
      (K := K) a b q1 q2 h_norm h_braid]

theorem fusionBraid1ColimitAction_stage
    (q1 q2 : K) (n : ℕ) (X : FusionCarrier K) :
    fusionBraid1ColimitAction (K := K) q1 q2
        (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n X) =
      braidGen1 K q1 q2 * X := by
  exact fusionActionColimitMap_stage (K := K)
    (fusionBraid1LeftTopCatHom q1 q2) n X

theorem fusionBraid2ColimitAction_stage
    (a b q1 q2 : K) (n : ℕ) (X : FusionCarrier K) :
    fusionBraid2ColimitAction (K := K) a b q1 q2
        (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n X) =
      braidGen2 K a b q1 q2 * X := by
  exact fusionActionColimitMap_stage (K := K)
    (fusionBraid2LeftTopCatHom a b q1 q2) n X

theorem fusionBraidColimitAction_artin
    (a b q1 q2 : K) (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionBraid1ColimitEndomorphism (K := K) q1 q2 ≫
        fusionBraid2ColimitEndomorphism (K := K) a b q1 q2 ≫
        fusionBraid1ColimitEndomorphism (K := K) q1 q2 =
      fusionBraid2ColimitEndomorphism (K := K) a b q1 q2 ≫
        fusionBraid1ColimitEndomorphism (K := K) q1 q2 ≫
        fusionBraid2ColimitEndomorphism (K := K) a b q1 q2 := by
  apply colimit.hom_ext
  intro n
  dsimp [fusionBraid1ColimitEndomorphism,
    fusionBraid2ColimitEndomorphism]
  change ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
        fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2) ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) =
    ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
        fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2) ≫
      fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2))
  have hs1 := fusionActionColimitEndomorphism_stage (K := K)
    (fusionBraid1LeftTopCatHom q1 q2) n
  have hs2 := fusionActionColimitEndomorphism_stage (K := K)
    (fusionBraid2LeftTopCatHom a b q1 q2) n
  calc
    ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
        fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2) =
      ((fusionBraid1LeftTopCatHom q1 q2 ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n) ≫
        fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2) := by rw [hs1]
    _ = (fusionBraid1LeftTopCatHom q1 q2 ≫
        (topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
          fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2))) ≫
        fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2) := by
          simp only [Category.assoc]
    _ = (fusionBraid1LeftTopCatHom q1 q2 ≫
        (fusionBraid2LeftTopCatHom a b q1 q2 ≫
          topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n)) ≫
        fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2) := by rw [hs2]
    _ = (fusionBraid1LeftTopCatHom q1 q2 ≫
        fusionBraid2LeftTopCatHom a b q1 q2 ≫
        fusionBraid1LeftTopCatHom q1 q2) ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
          simp only [Category.assoc]
          rw [hs1]
    _ = (fusionBraid2LeftTopCatHom a b q1 q2 ≫
        fusionBraid1LeftTopCatHom q1 q2 ≫
        fusionBraid2LeftTopCatHom a b q1 q2) ≫
        topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n := by
          rw [fusionBraidLeftTopCatHom_artin (K := K) a b q1 q2 h_norm h_braid]
    _ = ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
      fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
      fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
      fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2) := by
        symm
        calc
          ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
            fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
              fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
            fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2) =
            fusionBraid2LeftTopCatHom a b q1 q2 ≫
              (fusionBraid1LeftTopCatHom q1 q2 ≫
                (fusionBraid2LeftTopCatHom a b q1 q2 ≫
                  topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n)) := by
                    calc
                      ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
                        fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) ≫
                          fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
                        fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2) =
                        fusionBraid2LeftTopCatHom a b q1 q2 ≫
                          ((topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n ≫
                            fusionActionColimitEndomorphism (fusionBraid1LeftTopCatHom q1 q2)) ≫
                            fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) := by
                              rw [← Category.assoc]
                              rw [hs2]
                              simp only [Category.assoc]
                      _ = fusionBraid2LeftTopCatHom a b q1 q2 ≫
                          ((fusionBraid1LeftTopCatHom q1 q2 ≫
                            topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n) ≫
                            fusionActionColimitEndomorphism (fusionBraid2LeftTopCatHom a b q1 q2)) := by
                              rw [hs1]
                      _ = fusionBraid2LeftTopCatHom a b q1 q2 ≫
                          (fusionBraid1LeftTopCatHom q1 q2 ≫
                            (fusionBraid2LeftTopCatHom a b q1 q2 ≫
                              topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n)) := by
                              simp only [Category.assoc]
                              rw [hs2]
          _ = ((fusionBraid2LeftTopCatHom a b q1 q2 ≫
                fusionBraid1LeftTopCatHom q1 q2 ≫
                fusionBraid2LeftTopCatHom a b q1 q2) ≫
              topologicalDirectInjection (fusionTopologicalDiagram (K := K)) n) := by
                simp only [Category.assoc]

end InfoGeometry.Canonical.NonAbelianFusionFRTopologicalColimit
