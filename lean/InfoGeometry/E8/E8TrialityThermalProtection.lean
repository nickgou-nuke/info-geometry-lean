/-
Finite E₈/triality-inspired arithmetic readouts
===============================================

This file contains small finite data and identities: E₈ dimension/rank numbers,
a three-element Spin(8)-representation toy triality action, a Liouville-style
integer grading on natural-number indices, and scalar commutativity of that
grading with a declared phase factor.

It does not construct the split real Lie group `E₈(8)`, prove thermal
protection, prove a Witten-index conservation law for the E₈ root lattice, or
embed Standard Model gauge groups.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import InfoGeometry.Algebra.SplitE88Group

open ArithmeticFunction LieAlgebra

namespace E8Triality

/-- E₈ Lie algebra dimension -/
def dim_E8 : ℕ := 248

/-- E₈ rank -/
def rank_E8 : ℕ := 8

/-- E₈ Coxeter number -/
def coxeter_number_E8 : ℕ := 30

/-- E₈ positive roots -/
def positive_roots_E8 : ℕ := 120

/-- 
E₈(8) split real form.

The split real form of E₈ has maximal non-compact signature.
Maximal compact subalgebra: so(8, 8) ≅ Spin(8,8) / ℤ₂
TODO: replace this finite property by a real split-form construction when available
-/
/- The finite carrier is the native triple of numerical readouts, restricted
to the canonical values used by this owner. -/
abbrev E8SplitForm :=
  {data : ℕ × (ℕ × ℕ) //
    data.1 = dim_E8 ∧
      data.2.1 = rank_E8 ∧
      data.2.2 = positive_roots_E8}

namespace E8SplitForm

abbrev dimension (E : E8SplitForm) : ℕ := E.1.1
abbrev rank (E : E8SplitForm) : ℕ := E.1.2.1
abbrev maximal_compact_dimension (E : E8SplitForm) : ℕ := E.1.2.2

def IsCanonical (E : E8SplitForm) : Prop :=
  E.1.1 = dim_E8 ∧
    E.1.2.1 = rank_E8 ∧
    E.1.2.2 = positive_roots_E8

end E8SplitForm

/-- Canonical E8 split form instance -/
def canonicalE8SplitForm : E8SplitForm :=
  ⟨(dim_E8, rank_E8, positive_roots_E8), by
    simp [dim_E8, rank_E8, positive_roots_E8]⟩

/-- The canonical finite property has the declared E₈ dimension and rank. -/
theorem canonicalE8SplitForm_isCanonical :
    canonicalE8SplitForm.IsCanonical := by
  simpa [E8SplitForm.IsCanonical] using canonicalE8SplitForm.property

/--
Historical finite split-lane readback, recovered from the strengthened
`IsCanonical` owner.

The conclusion records only the canonical dimension and rank parameters.  It
does not assert that this numerical carrier constructs the split real Lie
group `E₈(8)`.
-/
theorem canonicalE8SplitForm_is_split :
    canonicalE8SplitForm.dimension = dim_E8 ∧
      canonicalE8SplitForm.rank = rank_E8 :=
  by
    refine ⟨?_, ?_⟩
    · exact canonicalE8SplitForm_isCanonical.1
    · exact canonicalE8SplitForm_isCanonical.2.1

namespace E8SplitForm

/-- A canonical finite datum has compact-dimension parameter `120`. -/

theorem maximal_compact_dim_eq_120 (E : E8SplitForm)
    (hE : E.IsCanonical) :
    E.maximal_compact_dimension = 120 :=
  by simpa [positive_roots_E8] using hE.2.2

end E8SplitForm

/-- Maximal compact property carried by the canonical split form has dimension `120`. -/
theorem maximal_compact_dim : canonicalE8SplitForm.maximal_compact_dimension = 120 :=
  E8SplitForm.maximal_compact_dim_eq_120 canonicalE8SplitForm
    canonicalE8SplitForm_isCanonical

/-!
The repository owner currently proves the finite `D₈` branching dimension
identity, but does not own a Lie-group construction or an isomorphism with a
matrix special-orthogonal group.  Expose the available theorem directly
instead of encoding the missing construction as prose data.
-/
theorem maximal_compact_dimension_eq_D8_adjoint :
    canonicalE8SplitForm.maximal_compact_dimension =
      InfoGeometry.Algebra.SplitE88Group.dim_Dn_adjoint 8 := by
  rfl


/-- 
Spin(8) triality: exceptional S₃ outer automorphism.

Permutes the three 8-dimensional representations:
  - 8v: vector
  - 8s: chiral spinor  
  - 8c: anti-chiral spinor
-/
inductive Spin8Representation
  | vector : Spin8Representation    -- 8v
  | spinor_plus : Spin8Representation  -- 8s
  | spinor_minus : Spin8Representation -- 8c

def spin8_rep_dim : Spin8Representation → ℕ
  | Spin8Representation.vector => 8
  | Spin8Representation.spinor_plus => 8
  | Spin8Representation.spinor_minus => 8

/-- Triality 3-cycle: 8v → 8s → 8c → 8v -/
def triality_sigma : Spin8Representation → Spin8Representation
  | Spin8Representation.vector => Spin8Representation.spinor_plus
  | Spin8Representation.spinor_plus => Spin8Representation.spinor_minus
  | Spin8Representation.spinor_minus => Spin8Representation.vector

/-- Triality transposition: 8s ↔ 8c -/
def triality_tau : Spin8Representation → Spin8Representation
  | Spin8Representation.vector => Spin8Representation.vector
  | Spin8Representation.spinor_plus => Spin8Representation.spinor_minus
  | Spin8Representation.spinor_minus => Spin8Representation.spinor_plus

/-- Triality group is S₃ -/
def triality_group : Type := Equiv.Perm (Fin 3)

theorem triality_sigma_order_3 : 
  triality_sigma ∘ triality_sigma ∘ triality_sigma = _root_.id := by
  ext rep
  cases rep <;> rfl

theorem triality_tau_order_2 : 
  triality_tau ∘ triality_tau = _root_.id := by
  ext rep
  cases rep <;> rfl

/-- 
Liouville grading on E₈ root lattice.

Γ = (-1)^Ω(n) where Ω(n) counts prime factors with multiplicity.
-/
def e8_liouville_grading (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let factors := Nat.factorization n
    let omega := factors.sum (fun _ m => m)
    (-1 : ℤ) ^ omega

/-- E₈ root lattice indices -/
  def e8_root_indices : Finset ℕ :=
    (Finset.range dim_E8).filter (· > 0)

/-- Count bosonic E₈ roots (λ = +1) -/
def count_bosonic_e8 : ℕ :=
  (e8_root_indices.filter (fun n => e8_liouville_grading n = 1)).card

/-- Count fermionic E₈ roots (λ = -1) -/
def count_fermionic_e8 : ℕ :=
  (e8_root_indices.filter (fun n => e8_liouville_grading n = -1)).card

/-- Difference of the two finite index counts above. -/
def witten_index_e8 : ℤ :=
  (count_bosonic_e8 : ℤ) - (count_fermionic_e8 : ℤ)

/-- 
E₈ modular flow σₜ.

Acts on root vectors by phase rotation:
  σₜ(E_α) = e^(it·φ(α)) E_α
-/
noncomputable def e8_modular_flow (t : ℝ) (root_idx : ℕ) : ℂ :=
  Complex.exp (Complex.I * t * Real.log (root_idx + 1 : ℝ))

/-- Scalar commutativity of the Liouville-style grading and the declared phase. -/
theorem e8_liouville_scalar_commutes_phase (root_idx : ℕ) (t : ℝ) :
  (e8_liouville_grading root_idx : ℂ) * e8_modular_flow t root_idx 
  = e8_modular_flow t root_idx * (e8_liouville_grading root_idx : ℂ) := by
  exact mul_comm _ _

/-- Uniform form of the same scalar commutativity identity. -/
theorem e8_liouville_scalar_commutes_phase_uniform :
  ∀ (t : ℝ) (root_idx : ℕ),
  (e8_liouville_grading root_idx : ℂ) * e8_modular_flow t root_idx
  = e8_modular_flow t root_idx * (e8_liouville_grading root_idx : ℂ) := by
  intro t root_idx
  exact e8_liouville_scalar_commutes_phase root_idx t

/-- The three toy Spin(8) representation labels all have dimension `8`, so the
declared grading value at their dimension is unchanged by the 3-cycle. -/
theorem triality_preserves_grading (rep : Spin8Representation) :
  e8_liouville_grading (spin8_rep_dim rep) = 
  e8_liouville_grading (spin8_rep_dim (triality_sigma rep)) := by
  cases rep <;> rfl

/-- The numerical identity `127 = 120 + 7`. -/
theorem positive_roots_E8_add_seven_eq_127 :
  (127 : ℕ) = positive_roots_E8 + 7 := by
  rfl

/-- The finite count difference is definitionally constant in an unused parameter. -/
theorem witten_index_e8_constant_in_parameter :
  ∀ β > 0,
    witten_index_e8 =
      (count_bosonic_e8 : ℤ) - (count_fermionic_e8 : ℤ) := by
  intro β Hβ
  rfl

end E8Triality
