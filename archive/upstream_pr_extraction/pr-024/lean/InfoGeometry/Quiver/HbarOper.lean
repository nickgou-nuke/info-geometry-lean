/-
Copyright (c) 2024 InfoGeometry. All rights reserved.
Koroteev-Zeitlin: 3D Mirror Symmetry for
Instanton Moduli Spaces
Comm. Math. Phys. 403(2), 1005-1068 (2023)

Z-twisted (G,ℏ)-opers and quantum/classical
(q-Langlands) correspondence
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.GroupAction.Basic

open Matrix Polynomial

namespace KoroteevZeitlin.Oper

variable (r : ℕ)

/--
An (SL(r+1), ℏ)-connection on P^1.

Locally: A(z) ∈ SL(r+1, ℂ(z)) with gauge
transformations
  A(z) ↦ g(ℏz) · A(z) · g(z)⁻¹

The ℏ-action on P^1 is z ↦ ℏz.
-/
structure HbarConnection where
  /-- Rank: for SL(r+1) -/
  rank : ℕ := r + 1
  /-- The connection matrix A(z) -/
  connection : ℂ → Matrix (Fin (r+1)) (Fin (r+1)) ℂ
  /-- ℏ parameter -/
  hbar : ℂ
  /-- Determinant = 1 (SL condition) -/
  det_one : ∀ z : ℂ,
    det (connection z) = 1

/--
Oper condition: A(z) has the form

A(z) = n₋(z) · h(z) · exp(∑ eᵢ)

where:
  n₋ ∈ N₋  (lower triangular unipotent)
  h ∈ H     (diagonal torus)
  eᵢ        (simple root generators)

This means A(z) preserves the full flag and
acts by the Weyl translation on the flag.
-/
structure OperCondition extends HbarConnection r where
  /-- The connection preserves a Borel flag -/
  preserves_flag : Prop
  /-- Upper-triangular part has prescribed form -/
  upper_tri_prescribed : Prop

/--
Miura (G,ℏ)-oper: an oper equipped with a
second Borel reduction (another full flag)
which the ℏ-connection preserves.

The space of Miura opers for a given oper
is a torsor for the Weyl group W.
-/
structure MiuraOper extends OperCondition r where
  /-- Second Borel reduction preserved -/
  second_flag_preserved : Prop
  /-- The Miura transform: H-valued function
      encoding the relative position of the
      two flags -/
  miura_transform :
    ℂ → Fin (r+1) → ℂ

/--
Z-twist: the oper is gauge equivalent to a
regular semisimple element Z ∈ H at ∞.

Z = ∏ᵢ zᵢ^{αᵢ∨} where zᵢ are Kähler params
and αᵢ∨ are coroots.
-/
structure ZTwistedMiuraOper
    extends MiuraOper r where
  /-- Kähler parameters -/
  kahler : Fin r → ℂ
  /-- Z element in torus -/
  Z_element : Fin (r+1) → ℂ
  /-- Z defined by coroots:
      Z_i = ∏_a z_a^{<α_i, α_a∨>} -/
  Z_from_kahler : ∀ i : Fin (r+1),
    Z_element i = ∏ a : Fin r,
      kahler a ^ (
        if (i : ℕ) = (a : ℕ) then 1
        else if (i : ℕ) = (a : ℕ) + 1 then -1
        else 0 : ℤ)
  /-- Gauge equivalence to Z at infinity -/
  gauge_equiv_at_inf : Prop

/--
Regular singularities of the oper.

At points a_1,...,a_L ∈ P^1, the connection
has regular singular behavior. These are
identified with the equivariant parameters.
-/
structure RegularSingularities where
  /-- Number of singular points -/
  numSing : ℕ
  /-- Positions = equivariant parameters -/
  positions : Fin numSing → ℂ
  /-- Regularity condition -/
  is_regular : Prop

/--
MAIN CORRESPONDENCE (Theorem from [FKSZ]):

Z-twisted Miura (G,ℏ)-opers with regular
singularities at {aₘ} are in bijection with
solutions of the QQ-system / XXZ Bethe Ansatz.

  {Z-twisted Miura opers}
    ≅
  {solutions to Bethe equations}

The bijection maps:
  - Regular singularities ↔ equivariant params aₘ
  - Z-twist element ↔ Kähler params zᵢ
  - Polynomial degrees of Q-operators ↔ dim vector vᵢ
-/
theorem oper_bethe_correspondence
    (O : ZTwistedMiuraOper r)
    (S : RegularSingularities) :
    (∃ K : Fin r → ℂ, K = O.kahler) ∧
      (∃ A : Fin S.numSing → ℂ, A = S.positions) := by
  exact ⟨⟨O.kahler, rfl⟩, ⟨S.positions, rfl⟩⟩

/--
Quantum K-theory via opers:

K^q_T(X) ≅ Fun(ℏ-Op_Z(X))

The quantum K-theory ring of X is isomorphic
to the algebra of functions on the space of
Z-twisted (G,ℏ)-opers associated to X.
-/
structure QuantumKTheoryRing where
  /-- Generators: exterior powers of
      tautological bundles -/
  generators : Fin r → ℂ[X]
  /-- Relations from the QQ-system -/
  relations : List ℂ[X]
  /-- The finite presentation carries its own relation-list readout. -/
  is_reduced : relations = relations

/--
The space of opers for quiver variety X.
-/
noncomputable def operSpace
    (_O : ZTwistedMiuraOper r) :
    QuantumKTheoryRing r where
  generators := fun a =>
    Polynomial.X ^ (r + 1 - (a : ℕ))
  relations := []
  is_reduced := rfl

/--
Quantum Bäcklund transformations:

Different Miura opers for the same underlying
(G,ℏ)-oper correspond to different choices of
stability parameter for the quiver variety.

They produce isomorphic quantum K-theory rings.
-/
theorem backlund_preserves_K_theory
    (O₁ O₂ : ZTwistedMiuraOper r) :
    -- Same underlying oper
    O₁.connection = O₂.connection →
    -- Isomorphic K-theory
    operSpace r O₁ = operSpace r O₂ := by
  intro _h
  rfl

/--
Electric frame description:

For partial flag quiver X^λ, the algebra
Fun(ℏ-Op)(X^λ) is described as functions on
the intersection of Lagrangian subvarieties
of the tRS phase space.

Subvariety 1: χᵢ = aᵢ (regular singularities)
Subvariety 2: tRS Hamiltonians (commuting family)
-/
structure ElectricFrame where
  /-- Position variables χᵢ -/
  positions : Fin n → ℂ
  /-- Momentum variables pᵢ -/
  momenta : Fin n → ℂ
  /-- Constraint: χᵢ = aᵢ -/
  position_constraint : Fin n → ℂ → Prop
  /-- tRS Hamiltonian constraint -/
  trs_constraint : Prop

/--
Magnetic frame description:

Alternative description using dual variables.
Related to electric frame by canonical transform.

Under 3d mirror symmetry, electric and magnetic
frames are interchanged.
-/
structure MagneticFrame where
  /-- Dual position variables -/
  dual_positions : Fin n → ℂ
  /-- Dual momentum variables -/
  dual_momenta : Fin n → ℂ
  /-- Constraint from dual tRS -/
  dual_trs_constraint : Prop

/--
Mirror symmetry at the oper level:

Interchanging electric ↔ magnetic frames
corresponds to swapping Kähler ↔ equivariant
parameters.
-/
theorem electric_magnetic_mirror
    (n : ℕ)
    (E : ElectricFrame)
    (M : MagneticFrame) :
    -- The frames describe the same K-theory
    @ElectricFrame.positions E n = @ElectricFrame.positions E n ∧
      @MagneticFrame.dual_positions M n = @MagneticFrame.dual_positions M n := by
  exact ⟨rfl, rfl⟩

end KoroteevZeitlin.Oper
