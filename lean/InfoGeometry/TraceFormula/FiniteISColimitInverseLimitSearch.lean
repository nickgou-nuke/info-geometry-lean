import InfoGeometry.TraceFormula.ItakuraSaitoMongeAmpere
import InfoGeometry.TraceFormula.ColimitTrace
import InfoGeometry.Topology.SymbolicLatentBoundaryInverseLimitCompHaus

/-!
# Finite Itakura--Saito search surface over direct and inverse limits

This file is deliberately a search interface, not a Hilbert--Pólya or zeta-zero
theorem.  It keeps the finite scalar candidate separate from the two limit
constructions already owned by the repository:

* the algebraic direct limit of the matrix stages and its normalized trace;
* the compact-Hausdorff inverse-limit comparison for symbolic boundary data.

No gradient, spectrum, or arithmetic zero correspondence is inferred here.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.TraceFormula.ColimitTrace
open InfoGeometry.TraceFormula.ItakuraSaito
open InfoGeometry.Topology

/-! ## Finite candidate energy -/

/-- The finite scalar Itakura--Saito candidate attached to two stage matrices. -/
def finiteISHamiltonian (n : ℕ) (P Q : MatrixStage n) : ℝ :=
  itakuraSaitoDivergence n P Q

theorem finiteISHamiltonian_self
    (n : ℕ) (P : MatrixStage n) (hP : IsUnit P.det) :
    finiteISHamiltonian n P P = -Real.log 1 :=
  itakuraSaito_self n P hP

theorem finiteISHamiltonian_scale_invariant
    (n : ℕ) (P Q : MatrixStage n) (c : ℝ) (hc : 0 < c)
    (hQ : IsUnit Q.det) :
    finiteISHamiltonian n (c • P) (c • Q) =
      finiteISHamiltonian n P Q :=
  itakuraSaito_scale_invariant n P Q c hc hQ

/-! ## Direct-limit readout -/

/-- The existing normalized trace is the finite observable readout on the
    algebraic matrix colimit. -/
def colimitISHamiltonianReadout (X : PrimonUHFAlgebra) : ℝ :=
  InfoGeometry.TraceFormula.ColimitTrace.tauInfinity X

@[simp]
theorem colimitISHamiltonianReadout_stage
    (n : ℕ) (M : MatrixStage n) :
    colimitISHamiltonianReadout (toColimit n M) = normalizedTrace n M := by
  exact tauInfinity_evaluate_ringhom n M

@[simp]
theorem colimitISHamiltonianReadout_one :
    colimitISHamiltonianReadout (1 : PrimonUHFAlgebra) = 1 := by
  exact InfoGeometry.TraceFormula.ColimitTrace.tauInfinity_one

/-! ## Inverse-limit readout -/

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- The finite-boundary carrier and its native inverse-limit carrier. -/
def inverseLimitSearchIso :
    symbolicBoundaryCompHaus (A := A) ≅
      symbolicBoundaryPrefixLimitCompHaus (A := A) :=
  symbolicBoundaryPrefixLimitCompHausIso (A := A)

theorem inverseLimitSearchIso_hom_inv_id :
    (inverseLimitSearchIso (A := A)).hom ≫
        (inverseLimitSearchIso (A := A)).inv = 𝟙 _ :=
  (inverseLimitSearchIso (A := A)).hom_inv_id

theorem inverseLimitSearchIso_inv_hom_id :
    (inverseLimitSearchIso (A := A)).inv ≫
        (inverseLimitSearchIso (A := A)).hom = 𝟙 _ :=
  (inverseLimitSearchIso (A := A)).inv_hom_id

end InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch
