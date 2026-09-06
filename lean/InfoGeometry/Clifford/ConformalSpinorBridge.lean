import Mathlib.Tactic
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.Clifford.ConformalLieAlgebra55

/-!
# InfoGeometry.Clifford.ConformalSpinorBridge

A finite, theorem-checked `𝔬𝔰𝔭(1|2)` spinor bridge used by the Cl(5,5)
conformal lane.

The carrier is the five-dimensional coordinate space with basis
`H, Ep, Em, G1, G2`.  The bracket is the table from the companion SymPy
witness `tools/sympy/osp12_spinor_bridge.py`:

* even sector: `H, Ep, Em`;
* odd sector: `G1, G2`;
* `[H, Ep] = 2 Ep`, `[H, Em] = -2 Em`, `[Ep, Em] = H`;
* `[H, G1] = G1`, `[H, G2] = -G2`, `[Ep, G2] = G1`, `[Em, G1] = G2`;
* odd anticommutators `{G1,G1}=2 Ep`, `{G2,G2}=-2 Em`, `{G1,G2}=-H`.

This module exports finite basis-level theorems and a global
`SuperLieRing` instance. The full arbitrary-linear-combination proofs
are broken down into reusable lemmas and checked directly by Lean.
-/

open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Clifford.ConformalSpinorBridge

open InfoGeometry.Clifford.ConformalLieAlgebra55

/-! ## 1. The five-dimensional carrier -/

/-- Indices for the basis `{H, Ep, Em, G1, G2}`. -/
inductive B : Type
  | H | Ep | Em | G1 | G2
  deriving DecidableEq, Fintype

open B

/-- The five-dimensional real coordinate space. -/
abbrev OSp12 : Type := B → ℝ

namespace OSp12

instance : AddCommGroup OSp12 := by unfold OSp12; infer_instance
instance : Module ℝ OSp12 := by unfold OSp12; infer_instance

/-! ## 2. Structure constants and bracket -/

/-- Structure constants for the finite `𝔬𝔰𝔭(1|2)` table. -/
def structConst (i j k : B) : ℚ :=
  match i, j, k with
  | .H,  .Ep, .Ep =>  2    | .Ep, .H,  .Ep => -2
  | .H,  .Em, .Em => -2    | .Em, .H,  .Em =>  2
  | .Ep, .Em, .H  =>  1    | .Em, .Ep, .H  => -1
  | .H,  .G1, .G1 =>  1    | .G1, .H,  .G1 => -1
  | .H,  .G2, .G2 => -1    | .G2, .H,  .G2 =>  1
  | .Ep, .G2, .G1 =>  1    | .G2, .Ep, .G1 => -1
  | .Em, .G1, .G2 =>  1    | .G1, .Em, .G2 => -1
  | .G1, .G2, .H  => -1    | .G2, .G1, .H  => -1
  | .G1, .G1, .Ep =>  2
  | .G2, .G2, .Em => -2
  | _, _, _ => 0

/-- Coordinate bracket induced by the finite `structConst` table.

It is written coordinatewise instead of as a double `Finset.univ` sum so that
basis-table proofs reduce by `cases`/`simp` without large heartbeat spikes. -/
def bracket (x y : OSp12) : OSp12
  | B.H  => x B.Ep * y B.Em - x B.Em * y B.Ep - x B.G1 * y B.G2 - x B.G2 * y B.G1
  | B.Ep => 2 * x B.H * y B.Ep - 2 * x B.Ep * y B.H + 2 * x B.G1 * y B.G1
  | B.Em => -2 * x B.H * y B.Em + 2 * x B.Em * y B.H - 2 * x B.G2 * y B.G2
  | B.G1 => x B.H * y B.G1 - x B.G1 * y B.H + x B.Ep * y B.G2 - x B.G2 * y B.Ep
  | B.G2 => -x B.H * y B.G2 + x B.G2 * y B.H + x B.Em * y B.G1 - x B.G1 * y B.Em

/-- Coordinate basis vector. -/
def basis (i : B) : OSp12 := Pi.single i (1 : ℝ)

/-- Finite even basis predicate. -/
def EvenBasis : Set B := {B.H, B.Ep, B.Em}

/-- Finite odd basis predicate. -/
def OddBasis : Set B := {B.G1, B.G2}

/-- The even coordinate part: the odd coordinates vanish. -/
def evenPart : Submodule ℝ OSp12 where
  carrier := {x | x B.G1 = 0 ∧ x B.G2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor <;> simp [Pi.add_apply, hx.1, hx.2, hy.1, hy.2]
  smul_mem' := by
    intro r x hx
    constructor <;> simp [Pi.smul_apply, hx.1, hx.2]

/-- The odd coordinate part: the even coordinates vanish. -/
def oddPart : Submodule ℝ OSp12 where
  carrier := {x | x B.H = 0 ∧ x B.Ep = 0 ∧ x B.Em = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · simp [Pi.add_apply, hx.1, hy.1]
    constructor
    · simp [Pi.add_apply, hx.2.1, hy.2.1]
    · simp [Pi.add_apply, hx.2.2, hy.2.2]
  smul_mem' := by
    intro r x hx
    constructor
    · simp [Pi.smul_apply, hx.1]
    constructor
    · simp [Pi.smul_apply, hx.2.1]
    · simp [Pi.smul_apply, hx.2.2]

/-! ## 3. Bilinearity on the coordinate bracket -/

/-- The bracket is additive in the left coordinate. -/
theorem add_lie (x y z : OSp12) :
    bracket (x + y) z = bracket x z + bracket y z := by
  ext k <;> fin_cases k <;> simp [bracket] <;> ring_nf

/-- The bracket is additive in the right coordinate. -/
theorem lie_add (x y z : OSp12) :
    bracket x (y + z) = bracket x y + bracket x z := by
  ext k <;> fin_cases k <;> simp [bracket] <;> ring_nf

/-- The bracket is homogeneous in the left coordinate. -/
theorem smul_lie (r : ℝ) (x y : OSp12) :
    bracket (r • x) y = r • bracket x y := by
  ext k <;> fin_cases k <;> simp [bracket, smul_eq_mul] <;> ring_nf

/-- The bracket is homogeneous in the right coordinate. -/
theorem lie_smul (r : ℝ) (x y : OSp12) :
    bracket x (r • y) = r • bracket x y := by
  ext k <;> fin_cases k <;> simp [bracket, smul_eq_mul] <;> ring_nf

/-! ## 4. Basis-level graded identities -/

/-- Even basis vectors skew-commute under the ordinary bracket. -/
theorem basis_even_even_skew (i j : B) (hi : i ∈ EvenBasis) (hj : j ∈ EvenBasis) :
    bracket (basis i) (basis j) = - bracket (basis j) (basis i) := by
  rcases hi with rfl | rfl | rfl <;>
  rcases hj with rfl | rfl | rfl <;>
  ext k <;> fin_cases k <;>
  simp [basis, bracket]

/-- Even and odd basis vectors skew-commute. -/
theorem basis_even_odd_skew (i j : B) (hi : i ∈ EvenBasis) (hj : j ∈ OddBasis) :
    bracket (basis i) (basis j) = - bracket (basis j) (basis i) := by
  rcases hi with rfl | rfl | rfl <;>
  rcases hj with rfl | rfl <;>
  ext k <;> fin_cases k <;>
  simp [basis, bracket]

/-- Odd basis vectors have symmetric super-bracket. -/
theorem basis_odd_odd_symm (i j : B) (hi : i ∈ OddBasis) (hj : j ∈ OddBasis) :
    bracket (basis i) (basis j) = bracket (basis j) (basis i) := by
  rcases hi with rfl | rfl <;>
  rcases hj with rfl | rfl <;>
  ext k <;> fin_cases k <;>
  simp [basis, bracket]

/-! ## 5. Named table readbacks -/

/-- `[H, Ep] = 2 Ep`. -/
theorem bracket_H_Ep : bracket (basis B.H) (basis B.Ep) = 2 • basis B.Ep := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[H, Em] = -2 Em`. -/
theorem bracket_H_Em : bracket (basis B.H) (basis B.Em) = (-2 : ℝ) • basis B.Em := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[Ep, Em] = H`. -/
theorem bracket_Ep_Em : bracket (basis B.Ep) (basis B.Em) = basis B.H := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[H, G1] = G1`. -/
theorem bracket_H_G1 : bracket (basis B.H) (basis B.G1) = basis B.G1 := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[H, G2] = -G2`. -/
theorem bracket_H_G2 : bracket (basis B.H) (basis B.G2) = - basis B.G2 := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[Ep, G2] = G1`. -/
theorem bracket_Ep_G2 : bracket (basis B.Ep) (basis B.G2) = basis B.G1 := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `[Em, G1] = G2`. -/
theorem bracket_Em_G1 : bracket (basis B.Em) (basis B.G1) = basis B.G2 := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `{G1, G1} = 2 Ep`. -/
theorem bracket_G1_G1 : bracket (basis B.G1) (basis B.G1) = 2 • basis B.Ep := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `{G2, G2} = -2 Em`. -/
theorem bracket_G2_G2 : bracket (basis B.G2) (basis B.G2) = (-2 : ℝ) • basis B.Em := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-- `{G1, G2} = -H`. -/
theorem bracket_G1_G2 : bracket (basis B.G1) (basis B.G2) = - basis B.H := by
  ext k <;> fin_cases k <;> simp [basis, bracket, structConst]

/-! ## 6. SuperLieRing Instance Lemmas -/

lemma sup_even_odd : (evenPart : Submodule ℝ OSp12) ⊔ oddPart = ⊤ := by
  apply top_unique
  intro x hx
  let e : OSp12 :=
    fun k =>
      match k with
      | B.H => x B.H
      | B.Ep => x B.Ep
      | B.Em => x B.Em
      | B.G1 => 0
      | B.G2 => 0
  let o : OSp12 :=
    fun k =>
      match k with
      | B.H => 0
      | B.Ep => 0
      | B.Em => 0
      | B.G1 => x B.G1
      | B.G2 => x B.G2
  exact Submodule.mem_sup.mpr
    ⟨e, by
        change e B.G1 = 0 ∧ e B.G2 = 0
        simp [e],
      o, by
        change o B.H = 0 ∧ o B.Ep = 0 ∧ o B.Em = 0
        simp [o],
      by
        ext k <;> fin_cases k <;> simp [e, o, Pi.add_apply]⟩

lemma even_odd_inter : (evenPart : Submodule ℝ OSp12) ⊓ oddPart = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    ext k <;> fin_cases k
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2
    · exact hx.1.1
    · exact hx.1.2
  · exact bot_le

lemma even_even_skew (x y : OSp12) (hx : x ∈ evenPart) (hy : y ∈ evenPart) :
    bracket x y = -bracket y x := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2, hy.1, hy.2] <;> ring

lemma even_odd_skew (x y : OSp12) (hx : x ∈ evenPart) (hy : y ∈ oddPart) :
    bracket x y = -bracket y x := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2, hy.1, hy.2.1, hy.2.2] <;> ring

lemma odd_odd_symm (x y : OSp12) (hx : x ∈ oddPart) (hy : y ∈ oddPart) :
    bracket x y = bracket y x := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2] <;> ring

lemma jacobi_even (x y z : OSp12) (hx : x ∈ evenPart) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  ext k <;> fin_cases k <;> simp [bracket, hx.1, hx.2] <;> ring

lemma jacobi_odd_odd (x y z : OSp12) (hx : x ∈ oddPart) (hy : y ∈ oddPart) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2] <;> ring

/-! ## 7. SuperLieRing Instance -/

instance : SuperLieRing OSp12 where
  bracket := bracket
  evenPart := evenPart
  oddPart := oddPart
  add_lie := add_lie
  lie_add := lie_add
  lie_smul := lie_smul
  sup_even_odd := sup_even_odd
  even_odd_inter := even_odd_inter
  even_even_skew := even_even_skew
  even_odd_skew := even_odd_skew
  odd_odd_symm := odd_odd_symm
  jacobi_even := jacobi_even
  jacobi_odd_odd := jacobi_odd_odd

end OSp12

end InfoGeometry.Clifford.ConformalSpinorBridge
