import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge

/-!
# Hestenes--Krein split-quaternion transport through filtered colimits

This is the categorical companion of
`HestenesKreinSplitQuaternionBridge`.  A compatible pair of natural
endomorphisms `K, η` on a filtered `ModuleCat ℝ` diagram is transported by
Mathlib's `colim.map`.  The square, involution, and anticommutation relations
are then inherited on the colimit carrier, where the generic split-quaternion
packet applies verbatim.

No norm completion, convergence, spectrum, or analytic extension is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinFilteredColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge

variable {F : ℕ ⥤ ModuleCat ℝ}

abbrev ColimitCarrier (F : ℕ ⥤ ModuleCat ℝ) := colimit F
abbrev ColimitEnd (F : ℕ ⥤ ModuleCat ℝ) :=
  Module.End ℝ (ColimitCarrier F)

structure Datum where
  K : F ⟶ F
  eta : F ⟶ F
  K_sq : K ≫ K = -(𝟙 F)
  eta_sq : eta ≫ eta = 𝟙 F
  K_eta_anticomm : K ≫ eta = -(eta ≫ K)

def KColimit (D : Datum (F := F)) : ColimitEnd F :=
  (colim.map D.K).hom

def etaColimit (D : Datum (F := F)) : ColimitEnd F :=
  (colim.map D.eta).hom

theorem KColimit_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    KColimit D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom ((D.K.app j).hom x) := by
  have h := colimit.ι_map D.K j
  exact congrArg (fun f => f x) h

theorem etaColimit_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    etaColimit D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom ((D.eta.app j).hom x) := by
  have h := colimit.ι_map D.eta j
  exact congrArg (fun f => f x) h

theorem KColimit_sq (D : Datum (F := F)) :
    KColimit D * KColimit D = -(1 : ColimitEnd F) := by
  have hcat : colim.map D.K ≫ colim.map D.K =
      -(𝟙 (colimit F)) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext a
    change KColimit D (KColimit D ((colimit.ι F j).hom a)) =
      -((colimit.ι F j).hom a)
    rw [KColimit_on_stage D j, KColimit_on_stage D j]
    have hstage := congrArg (fun η : F ⟶ F => η.app j) D.K_sq
    simpa [KColimit, ModuleCat.comp_apply] using
      congrArg (fun f => (colimit.ι F j).hom f) (congrArg (fun f => f a) hstage)
  simpa [KColimit, Module.End.mul_apply, LinearMap.neg_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem etaColimit_sq (D : Datum (F := F)) :
    etaColimit D * etaColimit D = (1 : ColimitEnd F) := by
  have hcat : colim.map D.eta ≫ colim.map D.eta =
      𝟙 (colimit F) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext a
    change etaColimit D (etaColimit D ((colimit.ι F j).hom a)) =
      (colimit.ι F j).hom a
    rw [etaColimit_on_stage D j, etaColimit_on_stage D j]
    have hstage := congrArg (fun η : F ⟶ F => η.app j) D.eta_sq
    simpa [etaColimit, ModuleCat.comp_apply] using
      congrArg (fun f => (colimit.ι F j).hom f) (congrArg (fun f => f a) hstage)
  simpa [etaColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem KColimit_etaColimit_anticomm (D : Datum (F := F)) :
    KColimit D * etaColimit D =
      -(etaColimit D * KColimit D) := by
  have hbase : D.eta ≫ D.K = -(D.K ≫ D.eta) := by
    have h := congrArg Neg.neg D.K_eta_anticomm
    simpa only [neg_neg] using h.symm
  have hcat : colim.map D.eta ≫ colim.map D.K =
      -(colim.map D.K ≫ colim.map D.eta) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext a
    change KColimit D (etaColimit D ((colimit.ι F j).hom a)) =
      -(etaColimit D (KColimit D ((colimit.ι F j).hom a)))
    rw [etaColimit_on_stage D j, KColimit_on_stage D j,
      KColimit_on_stage D j, etaColimit_on_stage D j]
    have hstage := congrArg (fun η : F ⟶ F => η.app j) hbase
    simpa [KColimit, etaColimit, ModuleCat.comp_apply] using
      congrArg (fun f => (colimit.ι F j).hom f) (congrArg (fun f => f a) hstage)
  simpa [KColimit, etaColimit, Module.End.mul_apply, LinearMap.neg_apply] using
    congrArg ModuleCat.Hom.hom hcat

def colimitDatum (D : Datum (F := F)) :
    InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge.Datum
      (V := ColimitCarrier F) where
  K := KColimit D
  eta := etaColimit D
  K_sq := KColimit_sq D
  eta_sq := etaColimit_sq D
  K_eta_anticomm := KColimit_etaColimit_anticomm D

def stageH (D : Datum (F := F)) (j : ℕ) :
    Module.End ℝ (F.obj j) :=
  (D.K.app j).hom * (D.eta.app j).hom

def stageEPlus (D : Datum (F := F)) (j : ℕ) :
    Module.End ℝ (F.obj j) :=
  (1 / 2 : ℝ) • ((1 : Module.End ℝ (F.obj j)) + (D.eta.app j).hom)

def stageEMinus (D : Datum (F := F)) (j : ℕ) :
    Module.End ℝ (F.obj j) :=
  (1 / 2 : ℝ) • ((1 : Module.End ℝ (F.obj j)) - (D.eta.app j).hom)

def stageQPlus (D : Datum (F := F)) (j : ℕ) :
    Module.End ℝ (F.obj j) :=
  (1 / 2 : ℝ) • (stageH D j - (D.K.app j).hom)

def stageQMinus (D : Datum (F := F)) (j : ℕ) :
    Module.End ℝ (F.obj j) :=
  (1 / 2 : ℝ) • (stageH D j + (D.K.app j).hom)

theorem colimitH_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    H (colimitDatum D) ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom (stageH D j x) := by
  change KColimit D (etaColimit D ((colimit.ι F j).hom x)) = _
  rw [etaColimit_on_stage D j, KColimit_on_stage D j]
  rfl

theorem colimitEPlus_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    ePlus (colimitDatum D) ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom (stageEPlus D j x) := by
  change (1 / 2 : ℝ) •
      ((colimit.ι F j).hom x + etaColimit D ((colimit.ι F j).hom x)) = _
  rw [etaColimit_on_stage D j]
  simp [stageEPlus]

theorem colimitEMinus_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    eMinus (colimitDatum D) ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom (stageEMinus D j x) := by
  change (1 / 2 : ℝ) •
      ((colimit.ι F j).hom x - etaColimit D ((colimit.ι F j).hom x)) = _
  rw [etaColimit_on_stage D j]
  simp [stageEMinus]

theorem colimitQPlus_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    qPlus (colimitDatum D) ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom (stageQPlus D j x) := by
  change (1 / 2 : ℝ) •
      (H (colimitDatum D) ((colimit.ι F j).hom x) -
        KColimit D ((colimit.ι F j).hom x)) = _
  rw [colimitH_on_stage D j, KColimit_on_stage D j]
  simp [stageQPlus]

theorem colimitQMinus_on_stage (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    qMinus (colimitDatum D) ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom (stageQMinus D j x) := by
  change (1 / 2 : ℝ) •
      (H (colimitDatum D) ((colimit.ι F j).hom x) +
        KColimit D ((colimit.ι F j).hom x)) = _
  rw [colimitH_on_stage D j, KColimit_on_stage D j]
  simp [stageQMinus]

theorem colimitH_sq (D : Datum (F := F)) :
    H (colimitDatum D) * H (colimitDatum D) = (1 : ColimitEnd F) :=
  H_sq (colimitDatum D)

theorem colimitProjector_packet (D : Datum (F := F)) :
    ePlus (colimitDatum D) * ePlus (colimitDatum D) =
        ePlus (colimitDatum D) ∧
      eMinus (colimitDatum D) * eMinus (colimitDatum D) =
        eMinus (colimitDatum D) ∧
      ePlus (colimitDatum D) * eMinus (colimitDatum D) = 0 ∧
      eMinus (colimitDatum D) * ePlus (colimitDatum D) = 0 := by
  exact ⟨ePlus_sq _, eMinus_sq _, ePlus_mul_eMinus _, eMinus_mul_ePlus _⟩

theorem colimitProjector_complementary (D : Datum (F := F)) :
    ePlus (colimitDatum D) + eMinus (colimitDatum D) =
      (1 : ColimitEnd F) := by
  exact ePlus_add_eMinus (colimitDatum D)

theorem colimitNilpotent_packet (D : Datum (F := F)) :
    qPlus (colimitDatum D) * qPlus (colimitDatum D) = 0 ∧
      qMinus (colimitDatum D) * qMinus (colimitDatum D) = 0 := by
  exact ⟨qPlus_sq _, qMinus_sq _⟩

end InfoGeometry.Canonical.HestenesKreinFilteredColimitBridge
