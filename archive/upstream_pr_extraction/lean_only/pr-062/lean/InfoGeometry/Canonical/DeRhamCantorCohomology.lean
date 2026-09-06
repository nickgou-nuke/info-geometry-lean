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
def IsClosed (f : (ℕ → Bool) → ℂ) : Prop :=
  UHF_boundary_op f = 0

/-- A boundary state is 'exact' if it is the boundary of another state. -/
def IsExact (f : (ℕ → Bool) → ℂ) : Prop :=
  ∃ g, f = UHF_boundary_op g

def IsCoClosed (f : (ℕ → Bool) → ℂ) : Prop :=
  star_UHF_boundary_op f = 0

def IsCoExact (f : (ℕ → Bool) → ℂ) : Prop :=
  ∃ g, f = star_UHF_boundary_op g

theorem isClosed_iff_mem_linearKer (f : (ℕ → Bool) → ℂ) :
    IsClosed f ↔ f ∈ LinearMap.ker UHF_boundary_op_linear := by
  rfl

theorem isExact_iff_mem_linearRange (f : (ℕ → Bool) → ℂ) :
    IsExact f ↔ f ∈ LinearMap.range UHF_boundary_op_linear := by
  constructor
  · rintro ⟨g, rfl⟩
    exact LinearMap.mem_range.mpr ⟨g, rfl⟩
  · intro h
    rcases LinearMap.mem_range.mp h with ⟨g, hg⟩
    exact ⟨g, hg.symm⟩

theorem isCoClosed_iff_mem_linearKer (f : (ℕ → Bool) → ℂ) :
    IsCoClosed f ↔ f ∈ LinearMap.ker star_UHF_boundary_op_linear := by
  rfl

theorem isCoExact_iff_mem_linearRange (f : (ℕ → Bool) → ℂ) :
    IsCoExact f ↔ f ∈ LinearMap.range star_UHF_boundary_op_linear := by
  constructor
  · rintro ⟨g, rfl⟩
    exact LinearMap.mem_range.mpr ⟨g, rfl⟩
  · intro h
    rcases LinearMap.mem_range.mp h with ⟨g, hg⟩
    exact ⟨g, hg.symm⟩

def closedSubmodule : Submodule ℂ ((ℕ → Bool) → ℂ) :=
  LinearMap.ker UHF_boundary_op_linear

def exactInClosedSubmodule : Submodule ℂ closedSubmodule :=
  (LinearMap.range UHF_boundary_op_linear).comap closedSubmodule.subtype

abbrev DeRhamH1 := closedSubmodule ⧸ exactInClosedSubmodule

theorem exactSubmodule_le_closedSubmodule :
    LinearMap.range UHF_boundary_op_linear ≤ closedSubmodule := by
  intro f hf
  rcases hf with ⟨g, rfl⟩
  exact UHF_boundary_op_sq_zero g

/-- The Boundary of a Boundary is Zero.
    Every exact boundary state is intrinsically closed. -/
theorem exact_implies_closed (f : (ℕ → Bool) → ℂ) (h : IsExact f) : IsClosed f := by
  rcases h with ⟨g, hg⟩
  rw [IsClosed, hg]
  exact UHF_boundary_op_sq_zero g

theorem coexact_implies_coclosed (f : (ℕ → Bool) → ℂ) (h : IsCoExact f) :
    IsCoClosed f := by
  rcases h with ⟨g, hg⟩
  rw [IsCoClosed, hg]
  exact star_UHF_boundary_op_sq_zero g

/-- The Poincaré Lemma for the Cantor Boundary.
    Because the Hodge-Dirac Laplacian is the identity (Δ = Id), the De Rham Cohomology
    is strictly trivial: Every closed boundary state is exact. -/
theorem cantor_de_rham_trivial (f : (ℕ → Bool) → ℂ) (h : IsClosed f) : IsExact f := by
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

theorem exactSubmodule_eq_closedSubmodule :
    LinearMap.range UHF_boundary_op_linear = closedSubmodule := by
  apply le_antisymm exactSubmodule_le_closedSubmodule
  intro f hf
  change IsClosed f at hf
  rcases cantor_de_rham_trivial f hf with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

theorem closed_mem_exactInClosedSubmodule (f : closedSubmodule) :
    f ∈ exactInClosedSubmodule := by
  rcases cantor_de_rham_trivial f.1 f.2 with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

theorem deRhamH1_subsingleton (x : DeRhamH1) : x = 0 := by
  refine Submodule.Quotient.induction_on exactInClosedSubmodule x ?_
  intro f
  exact (Submodule.Quotient.mk_eq_zero exactInClosedSubmodule).mpr
    (closed_mem_exactInClosedSubmodule f)

instance : Subsingleton DeRhamH1 :=
  ⟨fun x y => by rw [deRhamH1_subsingleton x, deRhamH1_subsingleton y]⟩

theorem isClosed_iff_isExact (f : (ℕ → Bool) → ℂ) :
    IsClosed f ↔ IsExact f := by
  constructor
  · exact cantor_de_rham_trivial f
  · exact exact_implies_closed f

theorem cantor_co_de_rham_trivial (f : (ℕ → Bool) → ℂ) (h : IsCoClosed f) :
    IsCoExact f := by
  refine ⟨UHF_boundary_op f, ?_⟩
  have h_zero : UHF_boundary_op (star_UHF_boundary_op f) = 0 := by
    rw [h]
    ext x
    dsimp [UHF_boundary_op, S_L_op, star_S_R_op]
    split <;> rfl
  have h_id := UHF_Laplacian_op_eq_id f
  rw [UHF_Laplacian_op, h_zero, zero_add] at h_id
  exact h_id.symm

theorem isCoClosed_iff_isCoExact (f : (ℕ → Bool) → ℂ) :
    IsCoClosed f ↔ IsCoExact f := by
  constructor
  · exact cantor_co_de_rham_trivial f
  · exact coexact_implies_coclosed f

end InfoGeometry.Canonical.DeRhamCantorCohomology

end noncomputable section
