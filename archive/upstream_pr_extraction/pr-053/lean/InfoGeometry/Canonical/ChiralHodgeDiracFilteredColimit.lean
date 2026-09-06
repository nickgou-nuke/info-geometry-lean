import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic

/-!
# Filtered-colimit transport of a chiral Hodge--Dirac packet

This is the categorical replacement for an analytic extension hypothesis.  A
finite-stage Dirac, Laplacian, and chiral involution are supplied as natural
transformations of a filtered `ModuleCat` diagram.  Their relations descend
to the native categorical colimit by `colim.map`.

No norm completion, convergence, spectrum, or unbounded-operator statement is
introduced here.  The result is precisely an algebraic inductive-colimit
transport theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimit

open CategoryTheory CategoryTheory.Limits

variable {F : ℕ ⥤ ModuleCat ℝ}

structure Datum where
  dirac : F ⟶ F
  laplacian : F ⟶ F
  chirality : F ⟶ F
  dirac_sq : dirac ≫ dirac = laplacian
  chirality_sq : chirality ≫ chirality = 𝟙 F
  dirac_odd : chirality ≫ dirac = -(dirac ≫ chirality)

theorem Datum.chirality_laplacian (D : Datum (F := F)) :
    D.chirality ≫ D.laplacian = D.laplacian ≫ D.chirality := by
  rw [← D.dirac_sq]
  rw [← Category.assoc, D.dirac_odd, Preadditive.neg_comp, Category.assoc, D.dirac_odd,
    Preadditive.comp_neg, neg_neg, ← Category.assoc]

/-! The Hestenes phase is deliberately separate from the involutive chiral
grading.  It is the real doubled-space replacement for multiplication by `i`:
its square is `-I`, while the chiral grading below squares to `+I`. -/

structure HestenesDatum extends Datum (F := F) where
  phase : F ⟶ F
  phase_sq : phase ≫ phase = -(𝟙 F)
  dirac_phase : phase ≫ dirac = dirac ≫ phase

theorem HestenesDatum.phase_laplacian (D : HestenesDatum (F := F)) :
    D.phase ≫ D.toDatum.laplacian = D.toDatum.laplacian ≫ D.phase := by
  rw [← D.toDatum.dirac_sq]
  rw [← Category.assoc, D.dirac_phase, Category.assoc, D.dirac_phase, ← Category.assoc]

def diracColimit (D : Datum (F := F)) :
    colimit F ⟶ colimit F :=
  colim.map D.dirac

def laplacianColimit (D : Datum (F := F)) :
    colimit F ⟶ colimit F :=
  colim.map D.laplacian

def chiralityColimit (D : Datum (F := F)) :
    colimit F ⟶ colimit F :=
  colim.map D.chirality

def phaseColimit (D : HestenesDatum (F := F)) :
    colimit F ⟶ colimit F :=
  colim.map D.phase

@[simp] theorem diracColimit_on_stage (D : Datum (F := F)) (j : ℕ) :
    colimit.ι F j ≫ diracColimit D =
      D.dirac.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.dirac j

@[simp] theorem laplacianColimit_on_stage (D : Datum (F := F)) (j : ℕ) :
    colimit.ι F j ≫ laplacianColimit D =
      D.laplacian.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.laplacian j

@[simp] theorem chiralityColimit_on_stage (D : Datum (F := F)) (j : ℕ) :
    colimit.ι F j ≫ chiralityColimit D =
      D.chirality.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.chirality j

theorem diracColimit_sq (D : Datum (F := F)) :
    diracColimit D ≫ diracColimit D = laplacianColimit D := by
  change colim.map D.dirac ≫ colim.map D.dirac = colim.map D.laplacian
  rw [← colim.map_comp, D.dirac_sq]

theorem chiralityColimit_sq (D : Datum (F := F)) :
    chiralityColimit D ≫ chiralityColimit D = 𝟙 (colimit F) := by
  change colim.map D.chirality ≫ colim.map D.chirality = 𝟙 (colimit F)
  rw [← colim.map_comp, D.chirality_sq, colim.map_id]
  rfl

@[simp] theorem phaseColimit_on_stage
    (D : HestenesDatum (F := F)) (j : ℕ) :
    colimit.ι F j ≫ phaseColimit D =
      D.phase.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.phase j

theorem phaseColimit_sq
    (D : HestenesDatum (F := F)) :
    phaseColimit D ≫ phaseColimit D = -(𝟙 (colimit F)) := by
  apply colimit.hom_ext
  intro j
  apply ModuleCat.hom_ext
  ext a
  change phaseColimit D (phaseColimit D ((colimit.ι F j).hom a)) =
    -((colimit.ι F j).hom a)
  have hp (b : F.obj j) :
      phaseColimit D ((colimit.ι F j).hom b) =
        (colimit.ι F j).hom (D.phase.app j b) :=
    congrArg (fun f => f b) (colimit.ι_map D.phase j)
  rw [hp a, hp (D.phase.app j a)]
  have hstage := congrArg (fun f => f a) (congrArg (fun η : F ⟶ F => η.app j)
    D.phase_sq)
  simpa [ModuleCat.comp_apply] using congrArg (fun f => (colimit.ι F j).hom f) hstage

theorem diracColimit_phase
    (D : HestenesDatum (F := F)) :
    phaseColimit D ≫ diracColimit D.toDatum = diracColimit D.toDatum ≫ phaseColimit D := by
  change colim.map D.phase ≫ colim.map D.toDatum.dirac =
    colim.map D.toDatum.dirac ≫ colim.map D.phase
  rw [← colim.map_comp, ← colim.map_comp, D.dirac_phase]

theorem chiralityColimit_laplacian
    (D : Datum (F := F)) :
    chiralityColimit D ≫ laplacianColimit D =
      laplacianColimit D ≫ chiralityColimit D := by
  change colim.map D.chirality ≫ colim.map D.laplacian =
    colim.map D.laplacian ≫ colim.map D.chirality
  rw [← colim.map_comp, ← colim.map_comp, D.chirality_laplacian]

/-! The phase is also even for the transported Hodge Laplacian.  This is a
categorical consequence of phase--Dirac commutation and `D² = Δ`; no
completion or analytic functional calculus is used. -/

theorem phaseColimit_laplacian
    (D : HestenesDatum (F := F)) :
    phaseColimit D ≫ laplacianColimit D.toDatum =
      laplacianColimit D.toDatum ≫ phaseColimit D := by
  change colim.map D.phase ≫ colim.map D.toDatum.laplacian =
    colim.map D.toDatum.laplacian ≫ colim.map D.phase
  rw [← colim.map_comp, ← colim.map_comp, D.phase_laplacian]

/-- Inserting the real Hestenes phase into the odd colimit Dirac operator
changes the square by the sign `K² = -1`.  This is the native categorical
form of `(K D)² = -Δ`; no exponential or functional calculus is involved. -/
theorem phaseDiracColimit_sq
    (D : HestenesDatum (F := F)) :
    (phaseColimit D ≫ diracColimit D.toDatum) ≫
        (phaseColimit D ≫ diracColimit D.toDatum) =
      -(laplacianColimit D.toDatum) := by
  calc
    (phaseColimit D ≫ diracColimit D.toDatum) ≫
        (phaseColimit D ≫ diracColimit D.toDatum) =
        phaseColimit D ≫
          (diracColimit D.toDatum ≫
            (phaseColimit D ≫ diracColimit D.toDatum)) := by
              simp only [Category.assoc]
    _ = phaseColimit D ≫
          ((diracColimit D.toDatum ≫ phaseColimit D) ≫
            diracColimit D.toDatum) := by
              rw [Category.assoc]
    _ = phaseColimit D ≫
          ((phaseColimit D ≫ diracColimit D.toDatum) ≫
            diracColimit D.toDatum) := by
              rw [diracColimit_phase D]
    _ = (phaseColimit D ≫ phaseColimit D) ≫
          (diracColimit D.toDatum ≫ diracColimit D.toDatum) := by
              simp only [Category.assoc]
    _ = -(laplacianColimit D.toDatum) := by
              rw [phaseColimit_sq D, diracColimit_sq D.toDatum]
              simp

theorem diracColimit_odd (D : Datum (F := F)) :
    chiralityColimit D ≫ diracColimit D =
      -(diracColimit D ≫ chiralityColimit D) := by
  apply colimit.hom_ext
  intro j
  apply ModuleCat.hom_ext
  ext a
  change diracColimit D (chiralityColimit D ((colimit.ι F j).hom a)) =
    -(chiralityColimit D (diracColimit D ((colimit.ι F j).hom a)))
  have hχ (b : F.obj j) :
      chiralityColimit D ((colimit.ι F j).hom b) =
        (colimit.ι F j).hom (D.chirality.app j b) :=
    congrArg (fun f => f b) (colimit.ι_map D.chirality j)
  have hD (b : F.obj j) :
      diracColimit D ((colimit.ι F j).hom b) =
        (colimit.ι F j).hom (D.dirac.app j b) :=
    congrArg (fun f => f b) (colimit.ι_map D.dirac j)
  rw [hχ a, hD (D.chirality.app j a), hD a, hχ (D.dirac.app j a)]
  have hstage := congrArg (fun f => f a) (congrArg (fun η : F ⟶ F => η.app j)
    D.dirac_odd)
  simpa [ModuleCat.comp_apply] using congrArg (fun f => (colimit.ι F j).hom f) hstage

end InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimit
