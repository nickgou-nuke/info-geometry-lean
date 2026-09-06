import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# De Rham Cantor Cohomology and the Poincaré Lemma

This module formalizes the Non-Commutative De Rham Cohomology on the Cantor boundary
and proves the Poincaré Lemma (triviality of the cohomology).

Using the fact that the Hodge-Dirac Laplacian is exactly the identity (`Δ = Id`),
we show that every closed form on the Cantor boundary is exact.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeRhamCantorCohomology

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- A boundary state is 'closed' if it has no further boundary (it is a cycle). -/
def IsClosed (f : CantorBoundary → ℂ) : Prop :=
  UHF_boundary_op f = 0

/-- A boundary state is 'exact' if it is the boundary of another state. -/
def IsExact (f : CantorBoundary → ℂ) : Prop :=
  ∃ g, f = UHF_boundary_op g

/-- The Boundary of a Boundary is Zero.
    Every exact boundary state is intrinsically closed. -/
theorem exact_implies_closed (f : CantorBoundary → ℂ) (h : IsExact f) : IsClosed f := by
  rcases h with ⟨g, hg⟩
  rw [IsClosed, hg]
  exact UHF_boundary_op_sq_zero g

/-- The Poincaré Lemma for the Cantor Boundary.
    Because the Hodge-Dirac Laplacian is the identity (Δ = Id), the De Rham Cohomology
    is strictly trivial: Every closed boundary state is exact. -/
theorem cantor_de_rham_trivial (f : CantorBoundary → ℂ) (h : IsClosed f) : IsExact f := by
  use star_UHF_boundary_op f
  have h_zero : star_UHF_boundary_op (UHF_boundary_op f) = 0 := by
    rw [h]
    ext x
    dsimp [star_UHF_boundary_op, S_R_op, star_S_L_op]
    split <;> rfl
  symm
  have h_add : UHF_boundary_op (star_UHF_boundary_op f) = UHF_boundary_op (star_UHF_boundary_op f) + 0 := by
    rw [add_zero]
  rw [h_add, ← h_zero]
  exact UHF_Laplacian_op_eq_id f

def UHF_boundary_op_linear : (CantorBoundary → ℂ) →ₗ[ℂ] (CantorBoundary → ℂ) where
  toFun := UHF_boundary_op
  map_add' := by
    intro f g
    ext x
    dsimp [UHF_boundary_op, S_L_op, star_S_R_op]
    split <;> ring
  map_smul' := by
    intro c f
    ext x
    dsimp [UHF_boundary_op, S_L_op, star_S_R_op]
    split <;> ring

def closedSubmodule : Submodule ℂ (CantorBoundary → ℂ) :=
  LinearMap.ker UHF_boundary_op_linear

def exactInClosedSubmodule : Submodule ℂ closedSubmodule :=
  (LinearMap.range UHF_boundary_op_linear).comap closedSubmodule.subtype

abbrev DeRhamH1 := closedSubmodule ⧸ exactInClosedSubmodule

theorem isClosed_iff_mem_closedSubmodule (f : CantorBoundary → ℂ) :
    IsClosed f ↔ f ∈ closedSubmodule :=
  Iff.rfl

theorem exactSubmodule_le_closedSubmodule :
    LinearMap.range UHF_boundary_op_linear ≤ closedSubmodule := by
  rintro f ⟨g, rfl⟩
  exact UHF_boundary_op_sq_zero g

theorem closed_mem_exactInClosedSubmodule (f : closedSubmodule) :
    f ∈ exactInClosedSubmodule := by
  have hf : IsClosed f.1 := f.2
  rcases cantor_de_rham_trivial f.1 hf with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

theorem deRhamH1_subsingleton (x : DeRhamH1) : x = 0 := by
  refine Submodule.Quotient.induction_on exactInClosedSubmodule x ?_
  intro f
  exact (Submodule.Quotient.mk_eq_zero exactInClosedSubmodule).mpr
    (closed_mem_exactInClosedSubmodule f)

instance : Subsingleton DeRhamH1 :=
  ⟨fun x y => by rw [deRhamH1_subsingleton x, deRhamH1_subsingleton y]⟩

end InfoGeometry.Canonical.DeRhamCantorCohomology

end noncomputable section

