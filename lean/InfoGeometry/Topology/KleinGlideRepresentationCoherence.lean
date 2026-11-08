import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
import InfoGeometry.Topology.TwistedCohomologyWeyl
import InfoGeometry.Topology.BrillouinKleinBottleManifold

/-!
# Finite glide-orbit coherence and the raw Klein-glide obstruction

The abstract `GlideBrillouinZone` API assumes an involutive glide.  Its
two-point orbit therefore intertwines canonically with the finite `glideFlip`
action.  The concrete Brillouin glide on the raw affine carrier `KPoint` is
not involutive: its square is a horizontal period translation.  We record
that obstruction explicitly rather than forcing the raw affine carrier into
the involutive API.  A quotient-by-period construction belongs downstream.
-/

namespace InfoGeometry.Topology.KleinGlideRepresentationCoherence

open InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
open InfoGeometry.Topology.BrillouinKleinBottleManifold
open InfoGeometry.Topology.Weyl

/-! ## The abstract two-point orbit -/

def glideOrbitMap {BZ : Type*} [TopologicalSpace BZ]
    (gbz : GlideBrillouinZone BZ) (k : BZ) : Fin 2 → BZ
  | 0 => k
  | 1 => gbz.glide k

theorem glideOrbitMap_comp_glideFlip
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : GlideBrillouinZone BZ) (k : BZ) (i : Fin 2) :
    glideOrbitMap gbz k (glideFlip i) =
      gbz.glide (glideOrbitMap gbz k i) := by
  fin_cases i <;> simp [glideOrbitMap, glideFlip, gbz.h_involution k]

/-! ## The concrete affine Klein glide -/

def horizontalPeriodShift (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 + 2 else p 1

theorem brillouinKlein_glide_sq (p : KPoint) :
    glide (glide p) = horizontalPeriodShift p := by
  ext i
  fin_cases i <;> simp [glide, horizontalPeriodShift] <;> ring

def kPointOrigin : KPoint := fun _ => 0

theorem brillouinKlein_glide_not_involutive :
    ¬ Function.Involutive glide := by
  intro hinv
  have h := congrFun (hinv kPointOrigin) 0
  norm_num [glide, kPointOrigin] at h

theorem no_raw_KPoint_GlideBrillouinZone_realization :
    ¬ ∃ gbz : GlideBrillouinZone KPoint,
        ∀ p, gbz.glide p = glide p := by
  rintro ⟨gbz, hglide⟩
  apply brillouinKlein_glide_not_involutive
  intro p
  rw [← hglide p, ← hglide (gbz.glide p)]
  exact gbz.h_involution p

/-! ## The algebraic horizontal-period quotient -/

def horizontalPeriodTranslate (n : ℤ) (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 + 2 * (n : ℚ) else p 1

def horizontalPeriodRel (p q : KPoint) : Prop :=
  ∃ n : ℤ, q = horizontalPeriodTranslate n p

theorem horizontalPeriodRel_refl (p : KPoint) :
    horizontalPeriodRel p p := by
  refine ⟨0, ?_⟩
  ext i
  fin_cases i <;> simp [horizontalPeriodTranslate]

theorem horizontalPeriodRel_symm {p q : KPoint} :
    horizontalPeriodRel p q → horizontalPeriodRel q p := by
  rintro ⟨n, rfl⟩
  refine ⟨-n, ?_⟩
  ext i
  fin_cases i <;> simp [horizontalPeriodTranslate] <;> ring

theorem horizontalPeriodRel_trans {p q r : KPoint} :
    horizontalPeriodRel p q →
      horizontalPeriodRel q r →
        horizontalPeriodRel p r := by
  rintro ⟨n, rfl⟩ ⟨m, rfl⟩
  refine ⟨n + m, ?_⟩
  ext i
  fin_cases i <;> simp [horizontalPeriodTranslate] <;> ring

noncomputable def horizontalPeriodSetoid : Setoid KPoint where
  r := horizontalPeriodRel
  iseqv := {
    refl := horizontalPeriodRel_refl
    symm := horizontalPeriodRel_symm
    trans := horizontalPeriodRel_trans
  }

noncomputable local instance horizontalPeriodSetoidInstance : Setoid KPoint :=
  horizontalPeriodSetoid

abbrev KleinKPoint := Quotient horizontalPeriodSetoidInstance

theorem glide_respects_horizontalPeriodRel {p q : KPoint} :
    horizontalPeriodRel p q →
      horizontalPeriodRel (glide p) (glide q) := by
  rintro ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  ext i
  fin_cases i <;> simp [glide, horizontalPeriodTranslate] <;> ring

noncomputable def quotientGlide : KleinKPoint → KleinKPoint :=
  Quotient.lift (fun p : KPoint => Quotient.mk' (glide p)) (by
    intro p q hpq
    exact Quotient.sound (glide_respects_horizontalPeriodRel hpq))

@[simp] theorem quotientGlide_mk (p : KPoint) :
    quotientGlide (Quotient.mk' p) = Quotient.mk' (glide p) := rfl

theorem quotientGlide_sq (p : KleinKPoint) :
    quotientGlide (quotientGlide p) = p := by
  refine Quotient.inductionOn p ?_
  intro q
  change Quotient.mk' (glide (glide q)) = Quotient.mk' q
  apply Quotient.sound
  have hshift : horizontalPeriodShift q = horizontalPeriodTranslate 1 q := by
    ext i
    fin_cases i <;>
      simp [horizontalPeriodShift, horizontalPeriodTranslate]
  have hsq : glide (glide q) = horizontalPeriodTranslate 1 q := by
    rw [brillouinKlein_glide_sq q, hshift]
  exact horizontalPeriodRel_symm ⟨1, hsq⟩

noncomputable def quotientGlideEquiv : KleinKPoint ≃ KleinKPoint where
  toFun := quotientGlide
  invFun := quotientGlide
  left_inv := quotientGlide_sq
  right_inv := quotientGlide_sq

theorem quotientGlideEquiv_involutive (p : KleinKPoint) :
    quotientGlideEquiv (quotientGlideEquiv p) = p :=
  quotientGlide_sq p

end InfoGeometry.Topology.KleinGlideRepresentationCoherence
