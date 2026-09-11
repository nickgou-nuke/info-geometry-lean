import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

/-!
# Incidence interface for the split Cayley hexagon geometry

The generalized-hexagon line orbit is supplied by a finite CAS export.  This
file contains the structural Lean layer: once each point has degree three, the
incident flag type has cardinality `63 * 3 = 189`.  No ambient automorphism
cardinality is used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2HexagonIncidence

open BigOperators
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

abbrev HexPoint := Fin 63
abbrev HexLine := Fin 63

structure IncidenceData where
  linePoints : HexLine → Finset HexPoint

def LineAt (C : IncidenceData) (p : HexPoint) :=
  {l : HexLine // p ∈ C.linePoints l}

noncomputable instance (C : IncidenceData) (p : HexPoint) : Fintype (LineAt C p) :=
  Fintype.subtype (Finset.univ.filter (fun l : HexLine => p ∈ C.linePoints l))
    (by
      intro l
      simp)

abbrev Flag (C : IncidenceData) := Σ p : HexPoint, LineAt C p

theorem flag_card (C : IncidenceData)
    (pointDegree : ∀ p : HexPoint,
      (Finset.univ.filter (fun l : HexLine => p ∈ C.linePoints l)).card = 3) :
    Fintype.card (Flag C) = 189 := by
  rw [Fintype.card_sigma]
  calc
    (∑ p : HexPoint, (Fintype.card (LineAt C p))) =
        ∑ p : HexPoint, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          calc
            Fintype.card (LineAt C p) =
                (Finset.univ.filter (fun l : HexLine => p ∈ C.linePoints l)).card := by
              simpa only [LineAt] using
                (Fintype.card_of_subtype
                  (Finset.univ.filter (fun l : HexLine => p ∈ C.linePoints l))
                  (by
                    intro l
                    simp))
            _ = 3 := pointDegree p
    _ = 189 := by norm_num [Fintype.card_fin]

/-- The repository's explicit 63-line certificate, with its kernel-checked
point-degree theorem, is an instance of the abstract flag certificate. -/
def parabolicLinePoints (l : HexLine) : Finset HexPoint :=
  Finset.univ.filter (fun p : HexPoint => l ∈ incidence p)

theorem parabolicLinePoints_card (l : HexLine) :
    (parabolicLinePoints l).card = 3 := by
  fin_cases l <;> native_decide

def parabolicIncidenceData : IncidenceData where
  linePoints := parabolicLinePoints

theorem parabolicPointDegree (p : HexPoint) :
    (Finset.univ.filter (fun l : HexLine => p ∈ parabolicIncidenceData.linePoints l)).card = 3 :=
  by
    fin_cases p <;> native_decide

theorem parabolic_flag_card : Fintype.card (Flag parabolicIncidenceData) = 189 := by
  exact flag_card parabolicIncidenceData parabolicPointDegree

/-- Canonical finite enumeration derived from the certified incidence flag type.
This is an enumeration of the geometric flags, not yet an enumeration of an
automorphism quotient; the latter additionally requires a concrete action and
stabilizer theorem. -/
noncomputable def parabolicFlagEnum : Fin 189 ≃ Flag parabolicIncidenceData :=
  (Fintype.equivFinOfCardEq parabolic_flag_card).symm

@[simp] theorem parabolicFlagEnum_apply_symm_apply (f : Flag parabolicIncidenceData) :
    parabolicFlagEnum (parabolicFlagEnum.symm f) = f :=
  parabolicFlagEnum.apply_symm_apply f

@[simp] theorem parabolicFlagEnum_symm_apply_apply (i : Fin 189) :
    parabolicFlagEnum.symm (parabolicFlagEnum i) = i :=
  parabolicFlagEnum.symm_apply_apply i

def incident (C : IncidenceData) (p : HexPoint) (l : HexLine) : Prop :=
  p ∈ C.linePoints l

def flag_mk (C : IncidenceData) (p : HexPoint) (l : HexLine)
    (h : incident C p l) : Flag C := ⟨p, ⟨l, h⟩⟩

end InfoGeometry.Algebra.Zorn.G2HexagonIncidence
