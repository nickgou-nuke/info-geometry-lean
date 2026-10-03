import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.DirectSum.Basic

namespace InfoGeometry.Canonical.PureSpinor

variable {R : Type*} [Field R] [Nontrivial R] [Invertible (2 : R)]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (Q : QuadraticForm R V)

/-!
# The Witt Decomposition and the Fock Vacuum

This file constructs the Fock vacuum for the split-signature `Cl(5,5)` algebra.
We assume the existence of a Witt decomposition: the spacetime `V` is the direct sum
of two maximal totally isotropic subspaces `W` (the creation sheet) and `W*` (the
annihilation sheet), each of dimension `5`.

Because `Q` vanishes on `W`, the Clifford algebra of the *restricted* form is
`ExteriorAlgebra R W`, and the spinor module is `⋀W`.  The vacuum is the unit `1`.

## What was removed, and why

This module previously carried two `axiom`s:

* `W_star_annihilates_vacuum` — asserted that an *arbitrary* linear map
  `interiorContraction : W* →ₗ[R] End R ⋀W` kills the vacuum.  This is not a
  theorem: the hypothesis never mentions the Clifford action, so taking
  `interiorContraction` to be any nonzero map falsifies it.  Moreover the intended
  statement — that *contraction* kills a degree-`0` element — is about interior
  contraction, which Mathlib does not provide for `ExteriorAlgebra` at all.
  `ExteriorAlgebra.ι` is exterior **multiplication**, and for it the claim is
  simply false: `ι w * 1 = ι w ≠ 0`.

* `fockVacuum_is_pure_spinor` — asserted purity of `1` for an *arbitrary*
  `cliffordAction : V →ₗ[R] End R ⋀W`.  Taking `cliffordAction = 0` makes the
  annihilator all of `V`, whose `finrank` is `10`, not `5`.  Even for the genuine
  Clifford action the claim fails, because `ι v * 1 = ι v`.

Both are now replaced by **proved** statements:

* `vacuum_annihilator_eq_bot` — the vacuum is annihilated by *nothing at all*.
  This is the exact opposite of the deleted axiom, and it is what the exterior
  algebra actually says.
* `vacuum_is_not_pure` — the vacuum is *not* a Cartan pure spinor, proved.
  Genuine Cartan purity belongs to the top wedge `ιMulti R 5 (basis of W)`, whose
  annihilator is `W`; that is the honest successor of the deleted axiom and needs
  interior contraction, which this Mathlib version does not supply.
* `sheet_anticommutes`, `sheet_nilsquare` — the Clifford relations of the Witt
  action, i.e. the nilpotent creation operators.  These are the genuine
  algebraic content that the deleted axioms were gesturing at.

## Scope boundaries

* **Only the split (isotropic) form is used.**  Every Clifford relation proved
  here is a relation for `Q ↾ W = 0`, i.e. `ι w * ι v = -ι v * ι w` and
  `ι w * ι w = 0`.  These are the relations Mathlib's `ExteriorAlgebra`
  (= `CliffordAlgebra 0`) actually supports.  No non-degenerate Clifford algebra
  appears, and nothing is claimed about one.
* **No spin-statistics, no `π₁(SO(3))`, no belt trick.**  Connecting a double
  cover to a spinor's `−1` phase would require an explicit covering homomorphism
  and an explicit `SU(2)` action on `ℂ²`.  Neither is present, and no such claim is
  made.
* **No ribbon or framing invariant.**  Linking number, twist and writhe live on
  `C²(S¹, ℝ³)` with a non-vanishing normal field and are stated via contour
  integrals.  They are absent here and deferred.
* **`IsPureSpinor` is a restatement, not a criterion.**  It encodes Cartan's
  rank-and-isotropy condition on the annihilator, which is the honest content of
  the deleted axiom.  Proving it *holds* for a genuine pure spinor requires the
  top wedge `ιMulti R 5 (basis of W)` together with interior contraction, which
  this Mathlib version does not supply.  `vacuum_is_not_pure` therefore refutes
  the old axiom rather than replacing it with a positive purity theorem.
-/

/--
The Witt decomposition of the spacetime manifold: `V` is the direct sum of the
Creation sheet `W` and the Annihilation sheet `W*`, both maximal totally isotropic.
-/
structure WittDecomposition (Q : QuadraticForm R V) where
  W : Submodule R V
  W_star : Submodule R V
  /-- The space is the direct sum of the two sheets. -/
  is_direct_sum : IsCompl W W_star
  /-- The creation sheet is totally isotropic. -/
  W_isotropic : ∀ w ∈ W, Q w = 0
  /-- The annihilation sheet is totally isotropic. -/
  W_star_isotropic : ∀ w_star ∈ W_star, Q w_star = 0
  /-- The metric provides a perfect duality pairing between the sheets. -/
  is_dual_pairing : ∀ w ∈ W, ∀ w_star ∈ W_star,
    Q.polarBilin w w_star ≠ 0 ∨ (w = 0 ∧ w_star = 0)
  /-- Each sheet has dimension `5`, i.e. half of the `10`-dimensional `V`. -/
  W_dim : Module.finrank R W = 5
  W_star_dim : Module.finrank R W_star = 5

variable (witt : WittDecomposition Q)

/--
The spinor module: the fermionic state space.  Because `W` is isotropic, the
restricted Clifford algebra collapses to its exterior algebra, so the spinors are
the differential forms on the creation sheet.
-/
abbrev SpinorModule := ExteriorAlgebra R witt.W

/-- The Fock vacuum `|0⟩`, the unit scalar: the empty universe. -/
def fockVacuum : SpinorModule Q witt := (1 : ExteriorAlgebra R witt.W)

/--
The Clifford action of the creation sheet on a spinor: `w` acts by exterior
multiplication.  This is the `W`-action on `⋀W` that Mathlib's `ExteriorAlgebra`
supports, and it is the correct one, since `⋀W` is the spinor module for the
restricted form `Q ↾ W = 0`.
-/
def wittAct (witt : WittDecomposition Q) (w : witt.W) (ψ : SpinorModule Q witt) :
    SpinorModule Q witt :=
  (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * ψ

/-- The action is zero on the zero spinor. -/
theorem wittAct_zero (witt : WittDecomposition Q) (w : witt.W) :
    wittAct Q witt w (0 : SpinorModule Q witt) = 0 := by
  simp [wittAct]

/-- The action is additive in the spinor. -/
theorem wittAct_add (witt : WittDecomposition Q) (w : witt.W)
    (ψ₁ ψ₂ : SpinorModule Q witt) :
    wittAct Q witt w (ψ₁ + ψ₂) = wittAct Q witt w ψ₁ + wittAct Q witt w ψ₂ := by
  simp only [wittAct]
  exact mul_add (ExteriorAlgebra.ι (R := R) (M := witt.W) w) ψ₁ ψ₂

/-- The action is compatible with the scalar structure. -/
theorem wittAct_smul (witt : WittDecomposition Q) (a : R) (w : witt.W)
    (ψ : SpinorModule Q witt) :
    wittAct Q witt w (a • ψ) = a • wittAct Q witt w ψ := by
  simp only [wittAct, Algebra.mul_smul_comm]

/-- The action is linear in the creation vector. -/
theorem wittAct_smul_w (witt : WittDecomposition Q) (c : R) (w : witt.W)
    (ψ : SpinorModule Q witt) :
    wittAct Q witt (c • w) ψ = c • wittAct Q witt w ψ := by
  rw [wittAct, (ExteriorAlgebra.ι (R := R) (M := witt.W)).map_smul, wittAct,
    Algebra.smul_mul_assoc]

/--
The annihilator of `ψ` inside the creation sheet, i.e. the subspace of `W` acting
trivially on `ψ`.  Cartan's purity test is a condition on this subspace.
-/
def sheetAnnihilator (witt : WittDecomposition Q) (ψ : SpinorModule Q witt) :
    Submodule R witt.W :=
  LinearMap.ker (show witt.W →ₗ[R] SpinorModule Q witt from
    { toFun := fun w => (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * ψ
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun c w => by
        rw [(ExteriorAlgebra.ι (R := R) (M := witt.W)).map_smul]
        exact (Algebra.smul_mul_assoc c
          (ExteriorAlgebra.ι (R := R) (M := witt.W) w) ψ) })

@[simp]
theorem mem_sheetAnnihilator (witt : WittDecomposition Q) (ψ : SpinorModule Q witt)
    (w : witt.W) :
    w ∈ sheetAnnihilator Q witt ψ ↔
      (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * ψ = 0 := by
  simp only [sheetAnnihilator, LinearMap.mem_ker]
  rfl

/-! ## The vacuum is a genuine element -/

/-- The Fock vacuum is **not** the zero spinor. -/
theorem fockVacuum_ne_zero : fockVacuum Q witt ≠ 0 := by
  rw [fockVacuum]
  exact one_ne_zero

/-! ## The vacuum is annihilated by nothing

This replaces the deleted axiom `W_star_annihilates_vacuum`.  The exterior action
of a nonzero creation vector on the degree-`0` vacuum is that vector, so the
annihilator collapses. -/

/-- A nonzero creation vector does **not** kill the vacuum. -/
theorem vacuum_not_annihilated (w : witt.W) (hw : w ≠ 0) :
    (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * fockVacuum Q witt ≠ 0 := by
  rw [fockVacuum, mul_one]
  intro hcontra
  exact hw ((ExteriorAlgebra.ι_eq_zero_iff (R := R) (M := witt.W) w).mp hcontra)

/-- **The annihilator of the vacuum is `{0}`.**  No nonzero creation vector acts
trivially on `|0⟩`. -/
theorem vacuum_annihilator_eq_bot :
    sheetAnnihilator Q witt (fockVacuum Q witt) = ⊥ := by
  ext w
  rw [mem_sheetAnnihilator, fockVacuum, mul_one]
  exact (ExteriorAlgebra.ι_eq_zero_iff (R := R) (M := witt.W) w)

/-! ## The vacuum is *not* a pure spinor -/

/--
Cartan's purity condition, taken where it is meaningful: the annihilator inside
the creation sheet must have full sheet dimension and be totally isotropic.
-/
def IsPureSpinor (witt : WittDecomposition Q) (ψ : SpinorModule Q witt) : Prop :=
  let annihilator := sheetAnnihilator Q witt ψ
  Module.finrank R annihilator = Module.finrank R witt.W ∧
    (∀ v ∈ annihilator, Q v = 0)

/--
**The vacuum is not a pure spinor.**  This is the honest content of the deleted
axiom `fockVacuum_is_pure_spinor`, which was false: the annihilator of `|0⟩` has
dimension `0`, not `5`.  Cartan purity belongs to the top wedge
`ιMulti R 5 (basis of W)`, whose annihilator *is* `W`.
-/
theorem vacuum_is_not_pure : ¬ IsPureSpinor Q witt (fockVacuum Q witt) := by
  intro h
  have hfrank : Module.finrank R (sheetAnnihilator Q witt (fockVacuum Q witt))
      = Module.finrank R witt.W := h.1
  rw [vacuum_annihilator_eq_bot, witt.W_dim] at hfrank
  simp at hfrank

/-- The pure-spinor condition of the vacuum fails already on rank, not on
isotropy: its annihilator is trivial. -/
theorem vacuum_annihilator_rank_lt :
    Module.finrank R (sheetAnnihilator Q witt (fockVacuum Q witt))
      < Module.finrank R witt.W := by
  rw [vacuum_annihilator_eq_bot, witt.W_dim]
  norm_num

/-! ## The genuine Clifford content of the Witt action

These are the theorems the deleted axioms were gesturing at.  For the restricted
form `Q ↾ W = 0` the generators anticommute, and each squares to zero: the
creation sheet acts by nilpotent operators on the spinor module. -/

theorem sheet_isOrtho (witt : WittDecomposition Q) (w v : witt.W) :
    QuadraticMap.IsOrtho (0 : QuadraticForm R witt.W) w v := by
  simp [QuadraticMap.IsOrtho]

/-- **The Clifford anticommutation relation** for the creation sheet. -/
theorem sheet_anticommutes (witt : WittDecomposition Q) (w v : witt.W) :
    (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * (ExteriorAlgebra.ι (R := R) (M := witt.W) v)
      = -((ExteriorAlgebra.ι (R := R) (M := witt.W) v)
          * (ExteriorAlgebra.ι (R := R) (M := witt.W) w)) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (sheet_isOrtho Q witt w v)

/-- **Each creation operator is nilpotent of order two** — the Fierz identity for
the split form. -/
theorem sheet_nilsquare (witt : WittDecomposition Q) (w : witt.W) :
    (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * (ExteriorAlgebra.ι (R := R) (M := witt.W) w)
      = 0 :=
  ExteriorAlgebra.ι_sq_zero (R := R) (M := witt.W) w

/-- The `2`-grading consequence: anticommutation is exactly anti-symmetry of the
exterior product. -/
theorem sheet_sum_swap (witt : WittDecomposition Q) (w v : witt.W) :
    (ExteriorAlgebra.ι (R := R) (M := witt.W) w) * (ExteriorAlgebra.ι (R := R) (M := witt.W) v)
      + (ExteriorAlgebra.ι (R := R) (M := witt.W) v)
          * (ExteriorAlgebra.ι (R := R) (M := witt.W) w) = 0 :=
  CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (sheet_isOrtho Q witt w v)

/-- The creation action is faithful on the vacuum: the annihilator computation is
exact, not merely an inclusion. -/
theorem wittAction_faithful (w : witt.W) :
    w ∈ sheetAnnihilator Q witt (fockVacuum Q witt) ↔ w = 0 := by
  rw [mem_sheetAnnihilator, fockVacuum, mul_one]
  exact (ExteriorAlgebra.ι_eq_zero_iff (R := R) (M := witt.W) w)

end InfoGeometry.Canonical.PureSpinor
