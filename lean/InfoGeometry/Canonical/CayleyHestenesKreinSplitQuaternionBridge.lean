import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
import InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge
import InfoGeometry.Canonical.HestenesKreinFilteredColimitBridge

/-!
# Cayley--Hestenes--Krein split-quaternion realization

This owner instantiates the generic real split-quaternion packet on the doubled
Cayley exterior carrier.  The Cayley carrier already has the middle-degree
Krein symmetry `middleSignFlip`; on its real double we use the diagonal
opposite-sign lift as the Krein involution and the standard Hestenes rotation
as the real complex structure.

The result is deliberately an algebraic compatibility theorem.  It does not
identify the Krein involution with exterior chirality or with Cayley
conjugation, and it introduces no completion, exponential, or analytic
extension.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyHestenesKreinSplitQuaternionBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge
open InfoGeometry.Canonical.HestenesKreinFilteredColimitBridge

abbrev CayleyDoubled := Coord × Coord
abbrev CayleyDoubledEnd := Module.End ℝ CayleyDoubled

/-- The real Hestenes complex structure on the doubled Cayley carrier. -/
def cayleyHestenesK : CayleyDoubledEnd where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

@[simp] theorem cayleyHestenesK_apply (x : CayleyDoubled) :
    cayleyHestenesK x = (-x.2, x.1) := rfl

/-- The opposite-sign lift of the Cayley middle-degree Krein symmetry. -/
def cayleyKreinEta : CayleyDoubledEnd where
  toFun x := (middleSignFlip x.1, -(middleSignFlip x.2))
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

@[simp] theorem cayleyKreinEta_apply (x : CayleyDoubled) :
    cayleyKreinEta x = (middleSignFlip x.1, -(middleSignFlip x.2)) := rfl

theorem cayleyHestenesK_sq :
    cayleyHestenesK * cayleyHestenesK = -(1 : CayleyDoubledEnd) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyHestenesK]

theorem cayleyKreinEta_sq :
    cayleyKreinEta * cayleyKreinEta = (1 : CayleyDoubledEnd) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyKreinEta]

theorem cayleyHestenesK_eta_anticommute :
    cayleyHestenesK * cayleyKreinEta =
      -(cayleyKreinEta * cayleyHestenesK) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyHestenesK, cayleyKreinEta]

/-- The concrete Cayley/Hestenes datum consumed by the generic packet. -/
def cayleyHestenesKreinDatum :
    Datum (V := CayleyDoubled) where
  K := cayleyHestenesK
  eta := cayleyKreinEta
  K_sq := cayleyHestenesK_sq
  eta_sq := cayleyKreinEta_sq
  K_eta_anticomm := cayleyHestenesK_eta_anticommute

theorem cayleyHestenesKrein_H_sq :
    H cayleyHestenesKreinDatum * H cayleyHestenesKreinDatum =
      (1 : CayleyDoubledEnd) :=
  H_sq cayleyHestenesKreinDatum

theorem cayleyHestenesKrein_projector_packet :
    ePlus cayleyHestenesKreinDatum * ePlus cayleyHestenesKreinDatum =
        ePlus cayleyHestenesKreinDatum ∧
      eMinus cayleyHestenesKreinDatum * eMinus cayleyHestenesKreinDatum =
        eMinus cayleyHestenesKreinDatum ∧
      ePlus cayleyHestenesKreinDatum * eMinus cayleyHestenesKreinDatum = 0 ∧
      eMinus cayleyHestenesKreinDatum * ePlus cayleyHestenesKreinDatum = 0 := by
  exact ⟨ePlus_sq _, eMinus_sq _, ePlus_mul_eMinus _, eMinus_mul_ePlus _⟩

theorem cayleyHestenesKrein_nilpotent_packet :
    qPlus cayleyHestenesKreinDatum * qPlus cayleyHestenesKreinDatum = 0 ∧
      qMinus cayleyHestenesKreinDatum * qMinus cayleyHestenesKreinDatum = 0 := by
  exact ⟨qPlus_sq _, qMinus_sq _⟩

/-! ## Cayley conjugation on the doubled carrier

The following diagonal lift keeps the intrinsic Cayley involution separate
from both the Hestenes rotation and the opposite-sign Krein involution. -/

def cayleyConjDiagonal : CayleyDoubledEnd where
  toFun x := (cayleyConj x.1, cayleyConj x.2)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

@[simp] theorem cayleyConjDiagonal_apply (x : CayleyDoubled) :
    cayleyConjDiagonal x = (cayleyConj x.1, cayleyConj x.2) := rfl

theorem cayleyConjDiagonal_sq :
    cayleyConjDiagonal * cayleyConjDiagonal = (1 : CayleyDoubledEnd) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyConjDiagonal, cayleyConj_sq]

theorem cayleyConjDiagonal_commutes_K :
    cayleyConjDiagonal * cayleyHestenesK =
      cayleyHestenesK * cayleyConjDiagonal := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyConjDiagonal, cayleyHestenesK]

theorem cayleyConjDiagonal_commutes_eta :
    cayleyConjDiagonal * cayleyKreinEta =
      cayleyKreinEta * cayleyConjDiagonal := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [cayleyConjDiagonal, cayleyKreinEta]

theorem cayleyConjDiagonal_commutes_H :
    cayleyConjDiagonal * H cayleyHestenesKreinDatum =
      H cayleyHestenesKreinDatum * cayleyConjDiagonal := by
  change cayleyConjDiagonal *
      (cayleyHestenesK * cayleyKreinEta) =
    (cayleyHestenesK * cayleyKreinEta) * cayleyConjDiagonal
  calc
    cayleyConjDiagonal * (cayleyHestenesK * cayleyKreinEta) =
        (cayleyConjDiagonal * cayleyHestenesK) * cayleyKreinEta := by
          rw [mul_assoc]
    _ = (cayleyHestenesK * cayleyConjDiagonal) * cayleyKreinEta := by
          rw [cayleyConjDiagonal_commutes_K]
    _ = cayleyHestenesK * (cayleyConjDiagonal * cayleyKreinEta) := by
          rw [mul_assoc]
    _ = cayleyHestenesK * (cayleyKreinEta * cayleyConjDiagonal) := by
          rw [cayleyConjDiagonal_commutes_eta]
    _ = (cayleyHestenesK * cayleyKreinEta) * cayleyConjDiagonal := by
          rw [← mul_assoc]

theorem cayleyConjDiagonal_commutes_ePlus :
    cayleyConjDiagonal * ePlus cayleyHestenesKreinDatum =
      ePlus cayleyHestenesKreinDatum * cayleyConjDiagonal := by
  dsimp [ePlus, cayleyHestenesKreinDatum]
  rw [mul_smul_comm, smul_mul_assoc]
  simp [mul_add, add_mul, cayleyConjDiagonal_commutes_eta]

theorem cayleyConjDiagonal_commutes_eMinus :
    cayleyConjDiagonal * eMinus cayleyHestenesKreinDatum =
      eMinus cayleyHestenesKreinDatum * cayleyConjDiagonal := by
  dsimp [eMinus, cayleyHestenesKreinDatum]
  rw [mul_smul_comm, smul_mul_assoc]
  simp [mul_sub, sub_mul, cayleyConjDiagonal_commutes_eta]

theorem cayleyConjDiagonal_commutes_qPlus :
    cayleyConjDiagonal * qPlus cayleyHestenesKreinDatum =
      qPlus cayleyHestenesKreinDatum * cayleyConjDiagonal := by
  change cayleyConjDiagonal *
      ((1 / 2 : ℝ) •
        (H cayleyHestenesKreinDatum - cayleyHestenesK)) =
    ((1 / 2 : ℝ) •
        (H cayleyHestenesKreinDatum - cayleyHestenesK)) *
      cayleyConjDiagonal
  rw [mul_smul_comm, smul_mul_assoc]
  rw [mul_sub, sub_mul, cayleyConjDiagonal_commutes_H,
    cayleyConjDiagonal_commutes_K]

theorem cayleyConjDiagonal_commutes_qMinus :
    cayleyConjDiagonal * qMinus cayleyHestenesKreinDatum =
      qMinus cayleyHestenesKreinDatum * cayleyConjDiagonal := by
  change cayleyConjDiagonal *
      ((1 / 2 : ℝ) •
        (H cayleyHestenesKreinDatum + cayleyHestenesK)) =
    ((1 / 2 : ℝ) •
        (H cayleyHestenesKreinDatum + cayleyHestenesK)) *
      cayleyConjDiagonal
  rw [mul_smul_comm, smul_mul_assoc]
  rw [mul_add, add_mul, cayleyConjDiagonal_commutes_H,
    cayleyConjDiagonal_commutes_K]

/-! ## Native filtered-colimit instantiation -/

abbrev constantCayleyDoubledFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ CayleyDoubled)

def constantCayleyEndNatTrans (T : CayleyDoubledEnd) :
    constantCayleyDoubledFunctor ⟶ constantCayleyDoubledFunctor :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom T)
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      rfl)

def cayleyHestenesFilteredDatum :
    HestenesKreinFilteredColimitBridge.Datum
      (F := constantCayleyDoubledFunctor) where
  K := constantCayleyEndNatTrans cayleyHestenesK
  eta := constantCayleyEndNatTrans cayleyKreinEta
  K_sq := by
    ext j x
    simpa [constantCayleyEndNatTrans, ModuleCat.comp_apply] using
      congrArg (fun T => T x) cayleyHestenesK_sq
  eta_sq := by
    ext j x
    simpa [constantCayleyEndNatTrans, ModuleCat.comp_apply] using
      congrArg (fun T => T x) cayleyKreinEta_sq
  K_eta_anticomm := by
    ext j x
    have h := congrArg (fun T => T x) cayleyHestenesK_eta_anticommute
    have h' := congrArg Neg.neg h.symm
    simpa [constantCayleyEndNatTrans, ModuleCat.comp_apply] using h'

theorem cayleyHestenesKColimit_on_stage (j : ℕ) (x : CayleyDoubled) :
    KColimit cayleyHestenesFilteredDatum
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (cayleyHestenesK x) :=
  KColimit_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyKreinEtaColimit_on_stage (j : ℕ) (x : CayleyDoubled) :
    etaColimit cayleyHestenesFilteredDatum
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (cayleyKreinEta x) :=
  etaColimit_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesKColimit_sq :
    KColimit cayleyHestenesFilteredDatum *
        KColimit cayleyHestenesFilteredDatum =
      -(1 : ColimitEnd constantCayleyDoubledFunctor) :=
  KColimit_sq cayleyHestenesFilteredDatum

theorem cayleyKreinEtaColimit_sq :
    etaColimit cayleyHestenesFilteredDatum *
        etaColimit cayleyHestenesFilteredDatum =
      (1 : ColimitEnd constantCayleyDoubledFunctor) :=
  etaColimit_sq cayleyHestenesFilteredDatum

theorem cayleyHestenesKColimit_etaColimit_anticommute :
    KColimit cayleyHestenesFilteredDatum *
        etaColimit cayleyHestenesFilteredDatum =
      -(etaColimit cayleyHestenesFilteredDatum *
        KColimit cayleyHestenesFilteredDatum) :=
  KColimit_etaColimit_anticomm cayleyHestenesFilteredDatum

theorem cayleyHestenesColimit_projector_complementary :
    ePlus (colimitDatum cayleyHestenesFilteredDatum) +
        eMinus (colimitDatum cayleyHestenesFilteredDatum) =
      (1 : ColimitEnd constantCayleyDoubledFunctor) :=
  colimitProjector_complementary cayleyHestenesFilteredDatum

theorem cayleyHestenesColimit_H_on_stage (j : ℕ) (x : CayleyDoubled) :
    H (colimitDatum cayleyHestenesFilteredDatum)
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (stageH cayleyHestenesFilteredDatum j x) :=
  colimitH_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesColimit_ePlus_on_stage (j : ℕ) (x : CayleyDoubled) :
    ePlus (colimitDatum cayleyHestenesFilteredDatum)
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (stageEPlus cayleyHestenesFilteredDatum j x) :=
  colimitEPlus_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesColimit_eMinus_on_stage (j : ℕ) (x : CayleyDoubled) :
    eMinus (colimitDatum cayleyHestenesFilteredDatum)
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (stageEMinus cayleyHestenesFilteredDatum j x) :=
  colimitEMinus_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesColimit_qPlus_on_stage (j : ℕ) (x : CayleyDoubled) :
    qPlus (colimitDatum cayleyHestenesFilteredDatum)
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (stageQPlus cayleyHestenesFilteredDatum j x) :=
  colimitQPlus_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesColimit_qMinus_on_stage (j : ℕ) (x : CayleyDoubled) :
    qMinus (colimitDatum cayleyHestenesFilteredDatum)
        ((colimit.ι constantCayleyDoubledFunctor j).hom x) =
      (colimit.ι constantCayleyDoubledFunctor j).hom
        (stageQMinus cayleyHestenesFilteredDatum j x) :=
  colimitQMinus_on_stage cayleyHestenesFilteredDatum j x

theorem cayleyHestenesColimit_packet :
    H (colimitDatum cayleyHestenesFilteredDatum) *
          H (colimitDatum cayleyHestenesFilteredDatum) =
        (1 : ColimitEnd constantCayleyDoubledFunctor) ∧
      (ePlus (colimitDatum cayleyHestenesFilteredDatum) *
          ePlus (colimitDatum cayleyHestenesFilteredDatum) =
            ePlus (colimitDatum cayleyHestenesFilteredDatum) ∧
        eMinus (colimitDatum cayleyHestenesFilteredDatum) *
            eMinus (colimitDatum cayleyHestenesFilteredDatum) =
              eMinus (colimitDatum cayleyHestenesFilteredDatum) ∧
          ePlus (colimitDatum cayleyHestenesFilteredDatum) *
              eMinus (colimitDatum cayleyHestenesFilteredDatum) = 0 ∧
            eMinus (colimitDatum cayleyHestenesFilteredDatum) *
                ePlus (colimitDatum cayleyHestenesFilteredDatum) = 0) ∧
      (qPlus (colimitDatum cayleyHestenesFilteredDatum) *
          qPlus (colimitDatum cayleyHestenesFilteredDatum) = 0 ∧
        qMinus (colimitDatum cayleyHestenesFilteredDatum) *
            qMinus (colimitDatum cayleyHestenesFilteredDatum) = 0) := by
  exact ⟨colimitH_sq _, colimitProjector_packet _, colimitNilpotent_packet _⟩

end InfoGeometry.Canonical.CayleyHestenesKreinSplitQuaternionBridge
