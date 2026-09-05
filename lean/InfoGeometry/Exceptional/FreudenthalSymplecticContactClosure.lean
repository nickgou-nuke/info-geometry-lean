import InfoGeometry.Exceptional.FreudenthalLegacyFiveGradedJacobiCounterexample
import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading
import InfoGeometry.Exceptional.FreudenthalSymplecticContactCommonCARCCR

/-!
# Corrected generic five-grade closure and representation capstone

The legacy `fiveGradedBracket` is explicitly non-Jacobi.  The canonical object
available from the repository's actual data is instead the symplectic contact
five-grading on

`R ⊕ FreudenthalCharge J ⊕ R`.

Its bracket is represented faithfully in an associative endomorphism algebra,
therefore has a native Lie-algebra structure.  The same representation lifts
to one common algebraic CAR--CCR carrier and preserves all adjoint grades.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Short name for the faithful block representation. -/
abbrev contactRho :
    FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactEnd (J := J) :=
  symplecticContactRepresentationLieHom D

/-- Short name for the faithful common CAR--CCR representation. -/
abbrev contactCommonRho :
    FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactCommonEnd (J := J) :=
  symplecticContactCommonRepresentation D

/-- The requested representation law on the canonical block target. -/
theorem contactRho_map_bracket
    (u v : FiveGradedCarrier D) :
    contactRho D ⁅u, v⁆ = ⁅contactRho D u, contactRho D v⁆ := by
  exact (contactRho D).map_lie u v

/-- The requested representation law on the common CAR--CCR target. -/
theorem contactCommonRho_map_bracket
    (u v : FiveGradedCarrier D) :
    contactCommonRho D ⁅u, v⁆ =
      ⁅contactCommonRho D u, contactCommonRho D v⁆ := by
  exact (contactCommonRho D).map_lie u v

/-- Faithfulness of the canonical block representation. -/
theorem contactRho_injective :
    Function.Injective (contactRho D) :=
  symplecticContactRepresentation_injective D

/-- Faithfulness survives the common CAR--CCR lift. -/
theorem contactCommonRho_injective :
    Function.Injective (contactCommonRho D) :=
  symplecticContactCommonRepresentation_injective D

/-- The operator image of each source grade belongs to the corresponding
operator grade. -/
theorem contactCommonRho_grade_preserving
    (k : ℤ) (u : symplecticContactGradeSpace D k) :
    contactCommonRho D u.1 ∈
      symplecticContactCommonGradeSpace D k :=
  symplecticContactCommonRepresentation_preserves_grade D u.2

/-- End-to-end theorem packet for the corrected generic lane. -/
theorem symplectic_contact_five_grade_closure_packet
    (k l : ℤ)
    (u : symplecticContactGradeSpace D k)
    (v : symplecticContactGradeSpace D l)
    (x y z : FiveGradedCarrier D) :
    (¬ (∀ a b c : FiveGradedCarrier D,
      fiveGradedBracket D a (fiveGradedBracket D b c) +
        fiveGradedBracket D b (fiveGradedBracket D c a) +
        fiveGradedBracket D c (fiveGradedBracket D a b) = 0)) ∧
      symplecticContactBracket D x (symplecticContactBracket D y z) +
          symplecticContactBracket D y (symplecticContactBracket D z x) +
          symplecticContactBracket D z (symplecticContactBracket D x y) = 0 ∧
      contactRho D ⁅x, y⁆ = ⁅contactRho D x, contactRho D y⁆ ∧
      contactCommonRho D ⁅x, y⁆ =
        ⁅contactCommonRho D x, contactCommonRho D y⁆ ∧
      ⁅u.1, v.1⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactCommonRho D u.1 ∈
        symplecticContactCommonGradeSpace D k ∧
      Function.Injective (contactCommonRho D) ∧
      symplecticContactFermionAnnihilation (J := J) *
          symplecticContactFermionCreation (J := J) +
        symplecticContactFermionCreation (J := J) *
          symplecticContactFermionAnnihilation (J := J) = 1 ∧
      symplecticContactBosonAnnihilation (J := J) *
          symplecticContactBosonCreation (J := J) -
        symplecticContactBosonCreation (J := J) *
          symplecticContactBosonAnnihilation (J := J) = 1 := by
  exact ⟨legacy_fiveGradedBracket_not_jacobi D,
    symplecticContactBracket_cyclic_jacobi D x y z,
    contactRho_map_bracket D x y,
    contactCommonRho_map_bracket D x y,
    symplecticContact_lie_mem_grade_add D u.2 v.2,
    contactCommonRho_grade_preserving D k u,
    contactCommonRho_injective D,
    symplecticContactFermion_CAR (J := J),
    symplecticContactBoson_CCR (J := J)⟩

end InfoGeometry.Exceptional.Freudenthal
