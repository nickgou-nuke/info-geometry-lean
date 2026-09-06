import Mathlib
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

This module deliberately exports finite basis-level theorems rather than a global
`SuperLieRing` instance: the full submodule-level instance is stronger API and
should only be restored once the arbitrary-linear-combination proof is kept small
enough for `lake build -R`.
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

/-- The even coordinate span, kept as data for downstream readers. -/
def evenPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {basis B.H, basis B.Ep, basis B.Em}

/-- The odd coordinate span, kept as data for downstream readers. -/
def oddPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {basis B.G1, basis B.G2}

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
  simp [basis, bracket] <;> ring_nf

/-- Even and odd basis vectors skew-commute. -/
theorem basis_even_odd_skew (i j : B) (hi : i ∈ EvenBasis) (hj : j ∈ OddBasis) :
    bracket (basis i) (basis j) = - bracket (basis j) (basis i) := by
  rcases hi with rfl | rfl | rfl <;>
  rcases hj with rfl | rfl <;>
  ext k <;> fin_cases k <;>
  simp [basis, bracket] <;> ring_nf

/-- Odd basis vectors have symmetric super-bracket. -/
theorem basis_odd_odd_symm (i j : B) (hi : i ∈ OddBasis) (hj : j ∈ OddBasis) :
    bracket (basis i) (basis j) = bracket (basis j) (basis i) := by
  rcases hi with rfl | rfl <;>
  rcases hj with rfl | rfl <;>
  ext k <;> fin_cases k <;>
  simp [basis, bracket] <;> ring_nf

/-! The full Jacobi lift over arbitrary linear combinations is intentionally not
re-exported here.  The companion SymPy witness checks the full finite table; this
Lean module keeps the small kernel-facing table readbacks and bilinearity laws. -/

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

end OSp12

end InfoGeometry.Clifford.ConformalSpinorBridge
