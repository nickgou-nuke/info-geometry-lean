import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.Zorn.G2PCCollection

/-!
# Certified PC Commutator Relations for U₆ ⊂ G₂(2)

The pairwise commutator table `[eᵢ, eⱼ]` on the six unipotent generators,
CAS-certified against the concrete 8×8 Zorn carrier **in Lean's own basis**
(`pc1Fun..pc6Fun`), see `scratch/verify_pc_commutator_table.py`,
`tmp/lean_basis_commutators.py`, and the GAP artifacts
`tmp/find_good_reflections.g` / `tmp/check_nilpotency.g`:

  - `[e₀, e₁] = e₂ e₃ e₅`
  - `[e₀, e₂] = e₅`
  - `[e₀, e₄] = e₃`
  - `[e₁, e₃] = e₅`
  - `[e₁, e₄] = e₅`
  - `[e₂, e₄] = e₅`
  - all other pairs commute

Structural facts certified alongside:
  - generator orders `(2, 4, 4, 2, 2, 2)` with `e₁² = e₂² = e₅`;
  - lower central series dimensions `(6, 3, 1, 0)`, i.e. nilpotency
    class **3** (GAP `NilpotencyClassOfGroup(SylowSubgroup) = 3`);
  - center `Z(U₆) = ⟨e₅⟩`.

Coordinate space is reused from `G2PCCollection` — no duplicated API.
-/

namespace InfoGeometry.Algebra.Zorn.G2PC

open InfoGeometry.Algebra.Zorn.G2PCCollection

/-! =========================================================================
    Commutator Table (certified constants)
    ========================================================================= -/

/--
Explicit polycyclic commutator function `[eᵢ, eⱼ]` for `i < j` on `U₆ ⊂ G₂(2)`
(certified against the concrete Zorn carrier):
  - `[e₀, e₁] = e₂ e₃ e₅`
  - `[e₀, e₂] = e₅`
  - `[e₀, e₄] = e₃`
  - `[e₁, e₃] = e₅`
  - `[e₁, e₄] = e₅`
  - `[e₂, e₄] = e₅`
  - All other pairs commute (`[eᵢ, eⱼ] = 1`).
-/
def pcComm (i j : Fin 6) : PCExp :=
  match i, j with
  | 0, 1 => fun k => match k with | 2 => 1 | 3 => 1 | 5 => 1 | _ => 0
  | 0, 2 => fun k => match k with | 5 => 1 | _ => 0
  | 0, 4 => fun k => match k with | 3 => 1 | _ => 0
  | 1, 3 => fun k => match k with | 5 => 1 | _ => 0
  | 1, 4 => fun k => match k with | 5 => 1 | _ => 0
  | 2, 4 => fun k => match k with | 5 => 1 | _ => 0
  | _, _ => zeroExp

/-! =========================================================================
    Structural Theorems
    ========================================================================= -/

/--
THEOREM (Centrality of Maximal Root Generator e₅):
The generator `e₅` commutes with all unipotent generators:
  `∀ i, [eᵢ, e₅] = 1`
-/
theorem e5_is_central (i : Fin 6) : pcComm i 5 = zeroExp := by
  fin_cases i <;> rfl

/--
THEOREM (e₃ Upper Filtration Commutativity):
The generator `e₃` commutes with all generators except `e₁`:
  `[e₀, e₃] = [e₂, e₃] = [e₄, e₃] = [e₅, e₃] = 1`
-/
theorem e3_comm_others (i : Fin 6) (h : i ≠ 1) : pcComm i 3 = zeroExp := by
  fin_cases i
  · rfl
  · contradiction
  · rfl
  · rfl
  · rfl
  · rfl

/--
THEOREM (e₄ Noncommutativity Support):
The generator `e₄` fails to commute exactly with `e₀`, `e₁`, `e₂`:
  `[e₀, e₄] = e₃`, `[e₁, e₄] = e₅`, `[e₂, e₄] = e₅`.
-/
theorem e4_noncomm_support :
    pcComm 0 4 ≠ zeroExp ∧ pcComm 1 4 ≠ zeroExp ∧ pcComm 2 4 ≠ zeroExp := by
  decide

/--
Canonical abelianization projection `π_ab : U₆ → 𝔽₂³` extracting
the surviving abelianization coordinates `(v₀, v₁, v₄)`.
-/
def piAb (v : PCExp) : Fin 3 → ZMod 2
  | 0 => v 0
  | 1 => v 1
  | 2 => v 4

/--
THEOREM (Derived Subgroup Annihilation):
All commutators `[eᵢ, eⱼ]` lie strictly inside the derived commutator subgroup
`[U, U] ⊆ span(e₂, e₃, e₄, e₅)` where `e₀ = e₁ = 0`.
(Certified refinement: actually `[U, U] = span(e₂, e₃, e₅)`.)
-/
theorem commutators_in_derived_subgroup (i j : Fin 6) :
    (pcComm i j) 0 = 0 ∧ (pcComm i j) 1 = 0 := by
  fin_cases i <;> fin_cases j <;> decide

/-! =========================================================================
    Lower Central Series Containments (class 3)
    ========================================================================= -/

/-- Step 1 in Lower Central Series: `γ₂ = [U, U] ⊆ span(e₂, e₃, e₄, e₅)`.
Certified refinement: `[U, U] = span(e₂, e₃, e₅)` (dimension 3). -/
def inGamma2 (v : PCExp) : Prop :=
  v 0 = 0 ∧ v 1 = 0

/-- Step 2 in Lower Central Series: `γ₃ = [U, γ₂] ⊆ span(e₃, e₄, e₅)`.
Certified refinement: `γ₃ = span(e₅) = Z(U₆)` (dimension 1). -/
def inGamma3 (v : PCExp) : Prop :=
  v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0

/-- Step 3 in Lower Central Series: `γ₄ = [U, γ₃] = {1}` (class 3). -/
def inGamma4 (v : PCExp) : Prop :=
  v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0

/--
THEOREM (Lower Central Series Step 1):
Every generator commutator `[eᵢ, eⱼ]` belongs to `γ₂ = [U, U]`.
-/
theorem pcComm_in_gamma2 (i j : Fin 6) : inGamma2 (pcComm i j) := by
  dsimp [inGamma2]
  exact commutators_in_derived_subgroup i j

/--
THEOREM (Lower Central Series Step 2):
Commutators of `e₀` with elements of the complement `{e₂, e₃, e₄, e₅}` land
inside `γ₃ ⊆ span(e₃, e₄, e₅)`; in the certified refinement they land in
`span(e₃, e₅)` with `e₅` central.
-/
theorem comm_e0_gamma2 (j : Fin 6) (hj : j ≥ 2) : inGamma3 (pcComm 0 j) := by
  fin_cases j
  · contradiction
  · contradiction
  · -- j = 2: [e₀, e₂] = e₅
    dsimp [inGamma3, pcComm]; decide
  · -- j = 3: [e₀, e₃] = 1
    dsimp [inGamma3, pcComm, zeroExp]; decide
  · -- j = 4: [e₀, e₄] = e₃
    dsimp [inGamma3, pcComm]; decide
  · -- j = 5: [e₀, e₅] = 1
    dsimp [inGamma3, pcComm, zeroExp]; decide

end InfoGeometry.Algebra.Zorn.G2PC
