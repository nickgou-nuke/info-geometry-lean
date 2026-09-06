import Mathlib.Tactic
import InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimit
import InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge
import InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks

/-!
# Chiral Hodge--Dirac blocks on a filtered `ModuleCat` colimit

The finite chiral block algebra is already owned by
`ExteriorAlgebraChiralHodgeDiracBlockBridge`.  This file only transports that
packet to the native categorical colimit.  The `.hom` projections below are
linear maps on the underlying colimit carrier; no norm completion or analytic
extension is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimitBlocks

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimit
open InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge
open InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks

variable {F : ℕ ⥤ ModuleCat ℝ}

abbrev ColimitCarrier (F : ℕ ⥤ ModuleCat ℝ) := (colimit F : ModuleCat ℝ)
abbrev ColimitEnd (F : ℕ ⥤ ModuleCat ℝ) := Module.End ℝ (ColimitCarrier F)

def colimitDiracEnd (D : Datum (F := F)) : ColimitEnd F :=
  (diracColimit D).hom

def colimitChiralityEnd (D : Datum (F := F)) : ColimitEnd F :=
  (chiralityColimit D).hom

def colimitLaplacianEnd (D : Datum (F := F)) : ColimitEnd F :=
  (laplacianColimit D).hom

def colimitPhaseEnd (D : HestenesDatum (F := F)) : ColimitEnd F :=
  (phaseColimit D).hom

def colimitChiralProjectorPlus (D : Datum (F := F)) : ColimitEnd F :=
  chiralProjectorPlus (colimitChiralityEnd D)

def colimitChiralProjectorMinus (D : Datum (F := F)) : ColimitEnd F :=
  chiralProjectorMinus (colimitChiralityEnd D)

def colimitChiralDiracPlus (D : Datum (F := F)) : ColimitEnd F :=
  chiralDiracPlus (colimitChiralityEnd D) (colimitDiracEnd D)

def colimitChiralDiracMinus (D : Datum (F := F)) : ColimitEnd F :=
  chiralDiracMinus (colimitChiralityEnd D) (colimitDiracEnd D)

theorem colimitChiralityEnd_sq (D : Datum (F := F)) :
    colimitChiralityEnd D * colimitChiralityEnd D = 1 := by
  simpa [colimitChiralityEnd] using
    congrArg ModuleCat.Hom.hom (chiralityColimit_sq D)

/-! The even chiral projectors and Laplacian blocks reconstructed on the
filtered colimit carrier. -/

def colimitChiralLaplacianPlus (D : Datum (F := F)) : ColimitEnd F :=
  chiralLaplacianPlus (colimitChiralityEnd D) (colimitLaplacianEnd D)

def colimitChiralLaplacianMinus (D : Datum (F := F)) : ColimitEnd F :=
  chiralLaplacianMinus (colimitChiralityEnd D) (colimitLaplacianEnd D)

theorem colimitChiralLaplacianPlus_eq_projected (D : Datum (F := F)) :
    colimitChiralProjectorPlus D * colimitLaplacianEnd D *
        colimitChiralProjectorPlus D = colimitChiralLaplacianPlus D := by
  rfl

theorem colimitChiralLaplacianMinus_eq_projected (D : Datum (F := F)) :
    colimitChiralProjectorMinus D * colimitLaplacianEnd D *
        colimitChiralProjectorMinus D = colimitChiralLaplacianMinus D := by
  rfl

theorem colimitChiralProjectorPlus_sq (D : Datum (F := F)) :
    colimitChiralProjectorPlus D * colimitChiralProjectorPlus D =
      colimitChiralProjectorPlus D :=
  chiralProjectorPlus_sq (colimitChiralityEnd_sq D)

theorem colimitChiralProjectorMinus_sq (D : Datum (F := F)) :
    colimitChiralProjectorMinus D * colimitChiralProjectorMinus D =
      colimitChiralProjectorMinus D :=
  chiralProjectorMinus_sq (colimitChiralityEnd_sq D)

theorem colimitChiralProjectors_orthogonal (D : Datum (F := F)) :
    colimitChiralProjectorPlus D * colimitChiralProjectorMinus D = 0 ∧
      colimitChiralProjectorMinus D * colimitChiralProjectorPlus D = 0 := by
  exact ⟨chiralProjector_orthogonal_plus_minus (colimitChiralityEnd_sq D),
    chiralProjector_orthogonal_minus_plus (colimitChiralityEnd_sq D)⟩

theorem colimitChiralProjectors_sum (D : Datum (F := F)) :
    colimitChiralProjectorPlus D + colimitChiralProjectorMinus D = 1 :=
  chiralProjector_sum (colimitChiralityEnd D)

theorem colimitDiracEnd_odd (D : Datum (F := F)) :
    colimitChiralityEnd D * colimitDiracEnd D =
      -(colimitDiracEnd D * colimitChiralityEnd D) := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f.hom x) (diracColimit_odd D)
  dsimp at h
  simp only [colimitChiralityEnd, colimitDiracEnd, Module.End.mul_apply,
    LinearMap.neg_apply] at h ⊢
  simpa [neg_neg] using (congrArg Neg.neg h).symm

theorem colimitPhaseEnd_dirac (D : HestenesDatum (F := F)) :
    colimitPhaseEnd D * colimitDiracEnd D.toDatum =
      colimitDiracEnd D.toDatum * colimitPhaseEnd D := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f.hom x) (diracColimit_phase D)
  dsimp at h
  simp only [colimitPhaseEnd, colimitDiracEnd, Module.End.mul_apply] at h ⊢
  exact h.symm

/-- A Hestenes packet with the additional, explicitly supplied commuting
    relation with the chiral grading.  The base `HestenesDatum` deliberately
    does not assume this relation. -/
structure ChiralHestenesDatum extends HestenesDatum (F := F) where
  phase_chirality : phase ≫ chirality = chirality ≫ phase

theorem colimitPhaseEnd_chirality_commute
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralityEnd D.toHestenesDatum.toDatum =
      colimitChiralityEnd D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  apply LinearMap.ext
  intro x
  have hcomp : colim.map D.phase ≫ colim.map D.chirality =
      colim.map D.chirality ≫ colim.map D.phase := by
    change colim.map D.phase ≫ colim.map D.chirality =
      colim.map D.chirality ≫ colim.map D.phase
    rw [← colim.map_comp, ← colim.map_comp, D.phase_chirality]
  have h := congrArg (fun f => f.hom x) hcomp
  dsimp at h
  simp only [colimitPhaseEnd, colimitChiralityEnd, Module.End.mul_apply] at h ⊢
  exact h.symm

theorem colimitPhaseEnd_commutes_chiralProjectorPlus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralProjectorPlus D.toHestenesDatum.toDatum =
      colimitChiralProjectorPlus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  exact hestenes_commutes_projectorPlus
    (colimitPhaseEnd_chirality_commute D).symm

theorem colimitPhaseEnd_commutes_chiralProjectorMinus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralProjectorMinus D.toHestenesDatum.toDatum =
      colimitChiralProjectorMinus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  exact hestenes_commutes_projectorMinus
    (colimitPhaseEnd_chirality_commute D).symm

theorem colimitPhaseEnd_commutes_chiralDiracPlus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralDiracPlus D.toHestenesDatum.toDatum =
      colimitChiralDiracPlus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  exact hestenes_commutes_chiralDiracPlus
    (colimitChiralityEnd_sq D.toHestenesDatum.toDatum)
    (colimitDiracEnd_odd D.toHestenesDatum.toDatum)
    (colimitPhaseEnd_chirality_commute D).symm
    (colimitPhaseEnd_dirac D.toHestenesDatum)

theorem colimitPhaseEnd_commutes_chiralDiracMinus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralDiracMinus D.toHestenesDatum.toDatum =
      colimitChiralDiracMinus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  exact hestenes_commutes_chiralDiracMinus
    (colimitChiralityEnd_sq D.toHestenesDatum.toDatum)
    (colimitDiracEnd_odd D.toHestenesDatum.toDatum)
    (colimitPhaseEnd_chirality_commute D).symm
    (colimitPhaseEnd_dirac D.toHestenesDatum)

theorem colimitPhaseEnd_sq (D : HestenesDatum (F := F)) :
    colimitPhaseEnd D * colimitPhaseEnd D = -1 := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f.hom x) (phaseColimit_sq D)
  dsimp at h
  simp only [colimitPhaseEnd, Module.End.mul_apply, LinearMap.neg_apply] at h ⊢
  exact h

/-! The composite colimit chiral-complex operator `Jχ = K∞ Γ∞`.

The explicit commutation hypothesis in `ChiralHestenesDatum` is used here;
the base `HestenesDatum` intentionally does not identify the phase with the
chiral grading.  This is an algebraic transport statement on the categorical
colimit carrier, with no completion or analytic interpretation.
-/

def colimitChiralComplexEnd
    (D : ChiralHestenesDatum (F := F)) : ColimitEnd F :=
  chiralComplexStructure (colimitPhaseEnd D.toHestenesDatum)
    (colimitChiralityEnd D.toHestenesDatum.toDatum)

theorem colimitChiralComplexEnd_sq
    (D : ChiralHestenesDatum (F := F)) :
    colimitChiralComplexEnd D * colimitChiralComplexEnd D =
      -(1 : ColimitEnd F) := by
  exact chiralComplexStructure_sq
    (colimitPhaseEnd_sq D.toHestenesDatum)
    (colimitChiralityEnd_sq D.toHestenesDatum.toDatum)
    (colimitPhaseEnd_chirality_commute D).symm

theorem colimitChiralComplexEnd_commutes_chirality
    (D : ChiralHestenesDatum (F := F)) :
    colimitChiralComplexEnd D *
        colimitChiralityEnd D.toHestenesDatum.toDatum =
      colimitChiralityEnd D.toHestenesDatum.toDatum *
        colimitChiralComplexEnd D := by
  dsimp [colimitChiralComplexEnd, chiralComplexStructure]
  have h_comm := colimitPhaseEnd_chirality_commute D
  calc colimitPhaseEnd D.toHestenesDatum * colimitChiralityEnd D.toHestenesDatum.toDatum *
        colimitChiralityEnd D.toHestenesDatum.toDatum
    _ = colimitPhaseEnd D.toHestenesDatum *
        (colimitChiralityEnd D.toHestenesDatum.toDatum * colimitChiralityEnd D.toHestenesDatum.toDatum) := by rw [mul_assoc]
    _ = colimitPhaseEnd D.toHestenesDatum * 1 := by rw [colimitChiralityEnd_sq]
    _ = colimitPhaseEnd D.toHestenesDatum := by rw [mul_one]
    _ = 1 * colimitPhaseEnd D.toHestenesDatum := by rw [one_mul]
    _ = (colimitChiralityEnd D.toHestenesDatum.toDatum * colimitChiralityEnd D.toHestenesDatum.toDatum) *
        colimitPhaseEnd D.toHestenesDatum := by rw [colimitChiralityEnd_sq]
    _ = colimitChiralityEnd D.toHestenesDatum.toDatum *
        (colimitChiralityEnd D.toHestenesDatum.toDatum * colimitPhaseEnd D.toHestenesDatum) := by rw [mul_assoc]
    _ = colimitChiralityEnd D.toHestenesDatum.toDatum *
        (colimitPhaseEnd D.toHestenesDatum * colimitChiralityEnd D.toHestenesDatum.toDatum) := by rw [← h_comm]

theorem colimitChiralComplexEnd_anticommutes_dirac
    (D : ChiralHestenesDatum (F := F)) :
    colimitChiralComplexEnd D *
        colimitDiracEnd D.toHestenesDatum.toDatum =
      -(colimitDiracEnd D.toHestenesDatum.toDatum *
        colimitChiralComplexEnd D) := by
  exact chiralComplexStructure_anticomm_dirac
    (colimitDiracEnd_odd D.toHestenesDatum.toDatum)
    (colimitPhaseEnd_dirac D.toHestenesDatum)

theorem colimitDiracEnd_sq_eq_laplacianEnd (D : Datum (F := F)) :
    colimitDiracEnd D * colimitDiracEnd D = colimitLaplacianEnd D := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f.hom x) (diracColimit_sq D)
  dsimp at h
  simp only [colimitDiracEnd, colimitLaplacianEnd, Module.End.mul_apply] at h ⊢
  exact h

theorem colimitChiralComplexEnd_commutes_laplacian
    (D : ChiralHestenesDatum (F := F)) :
    colimitChiralComplexEnd D *
        colimitLaplacianEnd D.toHestenesDatum.toDatum =
      colimitLaplacianEnd D.toHestenesDatum.toDatum *
        colimitChiralComplexEnd D := by
  have hJ := colimitChiralComplexEnd_anticommutes_dirac D
  calc
    colimitChiralComplexEnd D *
        colimitLaplacianEnd D.toHestenesDatum.toDatum =
        colimitChiralComplexEnd D *
          (colimitDiracEnd D.toHestenesDatum.toDatum *
            colimitDiracEnd D.toHestenesDatum.toDatum) := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]
    _ = (colimitChiralComplexEnd D *
          colimitDiracEnd D.toHestenesDatum.toDatum) *
          colimitDiracEnd D.toHestenesDatum.toDatum := by noncomm_ring
    _ = (-(colimitDiracEnd D.toHestenesDatum.toDatum *
          colimitChiralComplexEnd D)) *
          colimitDiracEnd D.toHestenesDatum.toDatum := by rw [hJ]
    _ = -(colimitDiracEnd D.toHestenesDatum.toDatum *
          (colimitChiralComplexEnd D *
            colimitDiracEnd D.toHestenesDatum.toDatum)) := by
          noncomm_ring
    _ = -(colimitDiracEnd D.toHestenesDatum.toDatum *
          (-(colimitDiracEnd D.toHestenesDatum.toDatum *
            colimitChiralComplexEnd D))) := by rw [hJ]
    _ = (colimitDiracEnd D.toHestenesDatum.toDatum *
          colimitDiracEnd D.toHestenesDatum.toDatum) *
          colimitChiralComplexEnd D := by noncomm_ring
    _ = colimitLaplacianEnd D.toHestenesDatum.toDatum *
          colimitChiralComplexEnd D := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]

/-! The Hestenes phase is even with respect to the transported Hodge
Laplacian.  This is the categorical colimit form of
`[K,D] = 0  ⟹  [K,D²] = 0`. -/

theorem colimitPhaseEnd_laplacian
    (D : HestenesDatum (F := F)) :
    colimitPhaseEnd D * colimitLaplacianEnd D.toDatum =
      colimitLaplacianEnd D.toDatum * colimitPhaseEnd D := by
  have hKD := colimitPhaseEnd_dirac D
  calc
    colimitPhaseEnd D * colimitLaplacianEnd D.toDatum =
        colimitPhaseEnd D *
          (colimitDiracEnd D.toDatum * colimitDiracEnd D.toDatum) := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]
    _ = (colimitPhaseEnd D * colimitDiracEnd D.toDatum) *
          colimitDiracEnd D.toDatum := by noncomm_ring
    _ = (colimitDiracEnd D.toDatum * colimitPhaseEnd D) *
          colimitDiracEnd D.toDatum := by rw [hKD]
    _ = colimitDiracEnd D.toDatum *
          (colimitPhaseEnd D * colimitDiracEnd D.toDatum) := by noncomm_ring
    _ = colimitDiracEnd D.toDatum *
          (colimitDiracEnd D.toDatum * colimitPhaseEnd D) := by rw [hKD]
    _ = (colimitDiracEnd D.toDatum * colimitDiracEnd D.toDatum) *
          colimitPhaseEnd D := by noncomm_ring
    _ = colimitLaplacianEnd D.toDatum * colimitPhaseEnd D := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]

theorem colimitPhaseDiracEnd_sq (D : HestenesDatum (F := F)) :
    (colimitPhaseEnd D * colimitDiracEnd D.toDatum) *
        (colimitPhaseEnd D * colimitDiracEnd D.toDatum) =
      -(colimitLaplacianEnd D.toDatum) := by
  have hK := colimitPhaseEnd_sq D
  have hKD := colimitPhaseEnd_dirac D
  calc
    (colimitPhaseEnd D * colimitDiracEnd D.toDatum) *
        (colimitPhaseEnd D * colimitDiracEnd D.toDatum) =
        colimitPhaseEnd D *
          (colimitDiracEnd D.toDatum * colimitPhaseEnd D) *
            colimitDiracEnd D.toDatum := by noncomm_ring
    _ = colimitPhaseEnd D *
          (colimitPhaseEnd D * colimitDiracEnd D.toDatum) *
            colimitDiracEnd D.toDatum := by rw [hKD]
    _ = (colimitPhaseEnd D * colimitPhaseEnd D) *
          (colimitDiracEnd D.toDatum * colimitDiracEnd D.toDatum) := by
          noncomm_ring
    _ = (-1) *
          (colimitDiracEnd D.toDatum * colimitDiracEnd D.toDatum) := by rw [hK]
    _ = -(colimitLaplacianEnd D.toDatum) := by
      rw [neg_one_mul, colimitDiracEnd_sq_eq_laplacianEnd]

theorem colimitChiralDiracPlus_sq_zero (D : Datum (F := F)) :
    colimitChiralDiracPlus D * colimitChiralDiracPlus D = 0 :=
  chiralDiracPlus_sq_zero (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitChiralDiracMinus_sq_zero (D : Datum (F := F)) :
    colimitChiralDiracMinus D * colimitChiralDiracMinus D = 0 :=
  chiralDiracMinus_sq_zero (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitDiracEnd_eq_chiral_blocks (D : Datum (F := F)) :
    colimitDiracEnd D =
      colimitChiralDiracPlus D + colimitChiralDiracMinus D :=
  chiralDirac_decomposition (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitDiracEnd_sq_eq_chiral_block_products (D : Datum (F := F)) :
    colimitDiracEnd D * colimitDiracEnd D =
      colimitChiralDiracMinus D * colimitChiralDiracPlus D +
        colimitChiralDiracPlus D * colimitChiralDiracMinus D :=
  dirac_sq_eq_chiral_sum (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitLaplacianEnd_eq_chiral_blocks (D : Datum (F := F)) :
    colimitLaplacianEnd D =
      colimitChiralDiracMinus D * colimitChiralDiracPlus D +
        colimitChiralDiracPlus D * colimitChiralDiracMinus D := by
  rw [← colimitDiracEnd_sq_eq_chiral_block_products D]
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f.hom x) (diracColimit_sq D)
  dsimp at h
  simp only [colimitLaplacianEnd, colimitDiracEnd,
    Module.End.mul_apply] at h ⊢
  exact h.symm

theorem colimitLaplacianEnd_eq_chiral_block_anticommutator
    (D : Datum (F := F)) :
    colimitLaplacianEnd D =
      colimitChiralDiracMinus D * colimitChiralDiracPlus D +
        colimitChiralDiracPlus D * colimitChiralDiracMinus D :=
  colimitLaplacianEnd_eq_chiral_blocks D

theorem colimitChiralLaplacianPlus_eq_block_product (D : Datum (F := F)) :
    colimitChiralLaplacianPlus D =
      colimitChiralDiracMinus D * colimitChiralDiracPlus D := by
  dsimp [colimitChiralLaplacianPlus]
  rw [← colimitDiracEnd_sq_eq_laplacianEnd D]
  exact laplacian_plus_eq_minus_plus
    (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitChiralLaplacianMinus_eq_block_product (D : Datum (F := F)) :
    colimitChiralLaplacianMinus D =
      colimitChiralDiracPlus D * colimitChiralDiracMinus D := by
  dsimp [colimitChiralLaplacianMinus]
  rw [← colimitDiracEnd_sq_eq_laplacianEnd D]
  exact laplacian_minus_eq_plus_minus
    (colimitChiralityEnd_sq D) (colimitDiracEnd_odd D)

theorem colimitLaplacianEnd_eq_chiral_laplacians (D : Datum (F := F)) :
    colimitLaplacianEnd D =
      colimitChiralLaplacianPlus D + colimitChiralLaplacianMinus D := by
  rw [colimitChiralLaplacianPlus_eq_block_product D,
    colimitChiralLaplacianMinus_eq_block_product D]
  exact colimitLaplacianEnd_eq_chiral_blocks D

theorem colimitChiralityEnd_laplacian
    (D : Datum (F := F)) :
    colimitChiralityEnd D * colimitLaplacianEnd D =
      colimitLaplacianEnd D * colimitChiralityEnd D := by
  have hodd := colimitDiracEnd_odd D
  calc
    colimitChiralityEnd D * colimitLaplacianEnd D =
        colimitChiralityEnd D * (colimitDiracEnd D * colimitDiracEnd D) := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]
    _ = (colimitChiralityEnd D * colimitDiracEnd D) * colimitDiracEnd D := by noncomm_ring
    _ = -(colimitDiracEnd D * colimitChiralityEnd D) * colimitDiracEnd D := by
      rw [hodd]
    _ = - (colimitDiracEnd D * (colimitChiralityEnd D * colimitDiracEnd D)) := by noncomm_ring
    _ = - (colimitDiracEnd D * -(colimitDiracEnd D * colimitChiralityEnd D)) := by
      rw [hodd]
    _ = (colimitDiracEnd D * colimitDiracEnd D) * colimitChiralityEnd D := by noncomm_ring
    _ = colimitLaplacianEnd D * colimitChiralityEnd D := by
      rw [colimitDiracEnd_sq_eq_laplacianEnd]

theorem colimitPhaseEnd_chiralLaplacianPlus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralLaplacianPlus D.toHestenesDatum.toDatum =
      colimitChiralLaplacianPlus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  have hP := colimitPhaseEnd_commutes_chiralDiracPlus D
  have hM := colimitPhaseEnd_commutes_chiralDiracMinus D
  rw [colimitChiralLaplacianPlus_eq_block_product]
  calc
    colimitPhaseEnd D.toHestenesDatum *
        (colimitChiralDiracMinus D.toHestenesDatum.toDatum *
          colimitChiralDiracPlus D.toHestenesDatum.toDatum) =
        (colimitPhaseEnd D.toHestenesDatum *
          colimitChiralDiracMinus D.toHestenesDatum.toDatum) *
          colimitChiralDiracPlus D.toHestenesDatum.toDatum := by noncomm_ring
    _ = (colimitChiralDiracMinus D.toHestenesDatum.toDatum *
          colimitPhaseEnd D.toHestenesDatum) *
          colimitChiralDiracPlus D.toHestenesDatum.toDatum := by rw [hM]
    _ = colimitChiralDiracMinus D.toHestenesDatum.toDatum *
          (colimitPhaseEnd D.toHestenesDatum *
            colimitChiralDiracPlus D.toHestenesDatum.toDatum) := by noncomm_ring
    _ = colimitChiralDiracMinus D.toHestenesDatum.toDatum *
          (colimitChiralDiracPlus D.toHestenesDatum.toDatum *
            colimitPhaseEnd D.toHestenesDatum) := by rw [hP]
    _ = (colimitChiralDiracMinus D.toHestenesDatum.toDatum *
          colimitChiralDiracPlus D.toHestenesDatum.toDatum) *
          colimitPhaseEnd D.toHestenesDatum := by noncomm_ring

theorem colimitPhaseEnd_chiralLaplacianMinus
    (D : ChiralHestenesDatum (F := F)) :
    colimitPhaseEnd D.toHestenesDatum *
        colimitChiralLaplacianMinus D.toHestenesDatum.toDatum =
      colimitChiralLaplacianMinus D.toHestenesDatum.toDatum *
        colimitPhaseEnd D.toHestenesDatum := by
  have hP := colimitPhaseEnd_commutes_chiralDiracPlus D
  have hM := colimitPhaseEnd_commutes_chiralDiracMinus D
  rw [colimitChiralLaplacianMinus_eq_block_product]
  calc
    colimitPhaseEnd D.toHestenesDatum *
        (colimitChiralDiracPlus D.toHestenesDatum.toDatum *
          colimitChiralDiracMinus D.toHestenesDatum.toDatum) =
        (colimitPhaseEnd D.toHestenesDatum *
          colimitChiralDiracPlus D.toHestenesDatum.toDatum) *
          colimitChiralDiracMinus D.toHestenesDatum.toDatum := by noncomm_ring
    _ = (colimitChiralDiracPlus D.toHestenesDatum.toDatum *
          colimitPhaseEnd D.toHestenesDatum) *
          colimitChiralDiracMinus D.toHestenesDatum.toDatum := by rw [hP]
    _ = colimitChiralDiracPlus D.toHestenesDatum.toDatum *
          (colimitPhaseEnd D.toHestenesDatum *
            colimitChiralDiracMinus D.toHestenesDatum.toDatum) := by noncomm_ring
    _ = colimitChiralDiracPlus D.toHestenesDatum.toDatum *
          (colimitChiralDiracMinus D.toHestenesDatum.toDatum *
            colimitPhaseEnd D.toHestenesDatum) := by rw [hM]
    _ = (colimitChiralDiracPlus D.toHestenesDatum.toDatum *
          colimitChiralDiracMinus D.toHestenesDatum.toDatum) *
          colimitPhaseEnd D.toHestenesDatum := by noncomm_ring

/-! The reconstructed chiral arrows are compatible with every colimit
injection.  Thus the block calculus is not merely defined after taking the
colimit; it is the stagewise chiral calculus transported through the cone. -/

theorem colimitChiralDiracPlus_on_stage
    (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    colimitChiralDiracPlus D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom
        (chiralDiracPlus (D.chirality.app j).hom (D.dirac.app j).hom x) := by
  dsimp [colimitChiralDiracPlus, chiralDiracPlus,
    chiralProjectorPlus, chiralProjectorMinus]
  have hχ (y : F.obj j) :
      colimitChiralityEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.chirality.app j).hom y) :=
    congrArg (fun f => f y) (chiralityColimit_on_stage D j)
  have hD (y : F.obj j) :
      colimitDiracEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.dirac.app j).hom y) :=
    congrArg (fun f => f y) (diracColimit_on_stage D j)
  simp only [LinearMap.map_smul, LinearMap.map_add]
  simp [hχ, hD]

theorem colimitChiralDiracMinus_on_stage
    (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    colimitChiralDiracMinus D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom
        (chiralDiracMinus (D.chirality.app j).hom (D.dirac.app j).hom x) := by
  dsimp [colimitChiralDiracMinus, chiralDiracMinus,
    chiralProjectorPlus, chiralProjectorMinus]
  have hχ (y : F.obj j) :
      colimitChiralityEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.chirality.app j).hom y) :=
    congrArg (fun f => f y) (chiralityColimit_on_stage D j)
  have hD (y : F.obj j) :
      colimitDiracEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.dirac.app j).hom y) :=
    congrArg (fun f => f y) (diracColimit_on_stage D j)
  simp only [LinearMap.map_smul, LinearMap.map_sub]
  simp [hχ, hD]

theorem colimitChiralLaplacianPlus_on_stage
    (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    colimitChiralLaplacianPlus D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom
        (chiralLaplacianPlus (D.chirality.app j).hom (D.laplacian.app j).hom x) := by
  dsimp [colimitChiralLaplacianPlus, chiralLaplacianPlus,
    chiralProjectorPlus, chiralProjectorMinus]
  have hχ (y : F.obj j) :
      colimitChiralityEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.chirality.app j).hom y) :=
    congrArg (fun f => f y) (chiralityColimit_on_stage D j)
  have hL (y : F.obj j) :
      colimitLaplacianEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.laplacian.app j).hom y) :=
    congrArg (fun f => f y) (laplacianColimit_on_stage D j)
  simp only [LinearMap.map_smul, LinearMap.map_add]
  simp [hχ, hL]

theorem colimitChiralLaplacianMinus_on_stage
    (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    colimitChiralLaplacianMinus D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom
        (chiralLaplacianMinus (D.chirality.app j).hom (D.laplacian.app j).hom x) := by
  dsimp [colimitChiralLaplacianMinus, chiralLaplacianMinus,
    chiralProjectorPlus, chiralProjectorMinus]
  have hχ (y : F.obj j) :
      colimitChiralityEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.chirality.app j).hom y) :=
    congrArg (fun f => f y) (chiralityColimit_on_stage D j)
  have hL (y : F.obj j) :
      colimitLaplacianEnd D ((colimit.ι F j).hom y) =
        (colimit.ι F j).hom ((D.laplacian.app j).hom y)
    := congrArg (fun f => f y) (laplacianColimit_on_stage D j)
  simp only [LinearMap.map_smul, LinearMap.map_sub]
  simp [hχ, hL]

end InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimitBlocks
