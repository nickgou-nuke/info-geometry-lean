/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Core.TensorPeirceDecomposition
import InfoGeometry.Algebra.ZornVectorMatrix
import Omega.POM.CatalanMoments

/-!
# Finite S₄ Dimension Arithmetic, Matrix Channels & Peirce Projector Poset (𝔎𝔅₁ ≺ ⋯ ≺ 𝔎𝔅₇)

## i. Overview

This owner proves finite arithmetic identities, a scaled coordinate decomposition of `3 × 3`
matrices, a Zorn cross-product coordinate identity, and conditional Peirce projector laws. It
does not construct an `S₄` representation or group-algebra decomposition, Bott periodicity,
Adams' `J`-homomorphism, a `KO₀` class, or a categorical colimit. The stage graph below is an
explicit ordering of declarations, not a dependency theorem deriving one mathematical lane from
another.

1. **Directive 1 — Wigner–Eckart / Clebsch–Gordan $S_4 = V_4 \rtimes S_3$ Decomposition (`𝔎𝔅₁, 𝔎𝔅₄, 𝔎𝔅₅`):**
   - `s4_wedderburn_artin_trees_and_adams_j_mod24_lock` proves the displayed dimension sums,
     tree-count arithmetic, Catalan values, a gcd calculation, and a power identity. It does not
     construct `S₄`, its normal subgroup `V₄`, irreducible representations, or a Wedderburn map.
   - `wigner_clebsch_gordan_s4_four_channel_decomposition` proves a coordinate identity over any
     commutative ring `K` for `M : Matrix (Fin 3) (Fin 3) K`:
     `smul 6 M = cgChan1_Triv M + cgChan2_Quadrupole M + cgChan3_SymOff M + cgChan3_AntisymVort M`,
     with the stated trace and transpose identities. No `S₄` action or equivariance is defined;
     over an arbitrary ring the factor `6` is not assumed invertible, so this is a scaled identity,
     not an unscaled direct-sum decomposition.
   - `kb5_antisym_channel_zorn_cross_product_bridge`:
     Proves that for any rank-1 tensor product `Matrix.vecMulVec u v` of two 3-vectors `u, v : Fin 3 → K`,
     the scalar trace is the Euclidean dot product `u · v` while the antisymmetric channel
     `cgChan3_AntisymVort (Matrix.vecMulVec u v)` is `3` times the 3D Zorn cross product `zornCross3D u v`.
2. **Directive 2 — Conditional Peirce Projector Laws & Finite Index Cardinality (`𝔎𝔅₆, 𝔎𝔅₇`):**
   - `ko_theory_pmi_bruhat_projector_colimit_stability`:
     Using canonical `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic` (`dressedPeirceProjector`,
     `genPhi`, `genV`, `genSig`, `evenGrade`, `comm`) and `InfoGeometry.Core.TensorPeirceDecomposition`
     (`PeirceIndex`, `peirceIndex_card`), proves the dressed element is idempotent, its even-grade
     difference has the displayed commutator form, its image under a unital ring homomorphism is
     idempotent, and the finite index cardinality scales by 16 after four binary levels. These are
     not a `KO₀` class, trace/index theorem, completed colimit, or classical Bott-periodicity result.
3. **Directive 3 — Modulo-24 Arithmetic & 4-Token Tree Counts (`𝔎𝔅₂, 𝔎𝔅₃`):**
   - `adams_j_homomorphism_all_z24_units_divisibility`:
     proves that `k² ≡ 1 (mod 24)` for residues coprime to 24, alongside the totient value. This is
     modular arithmetic only; it does not define or prove a statement about Adams' `J`-homomorphism
     or `π₃ˢ`.

## ii. Key results

- `CliffordBottWignerS4Stage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `s4_wedderburn_artin_trees_and_adams_j_mod24_lock`
- `adams_j_homomorphism_all_z24_units_divisibility`
- `Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition`
- `Mat3.kb5_antisym_channel_zorn_cross_product_bridge`
- `ko_theory_pmi_bruhat_projector_colimit_stability`
- `kb7_master_clifford_bott_wigner_s4_synthesis`

## iii. Table of contents

- Section 0: A seven-node declaration-order graph (`𝔎𝔅₁ ≺ ⋯ ≺ 𝔎𝔅₇`)
- Section 1 (`𝔎𝔅₁–𝔎𝔅₃`): Dimension, tree, gcd, and modulo-24 arithmetic
- Section 2 (`𝔎𝔅₄–𝔎𝔅₅`): Scaled coordinate channels and a Zorn cross-product identity
- Section 3 (`𝔎𝔅₆–𝔎𝔅₇`): Conditional Peirce projector laws and finite index cardinality

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content (finite algebra/arithmetic only):**
  - `CliffordBottWignerS4Stage` ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_7$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `s4_wedderburn_artin_trees_and_adams_j_mod24_lock`, `adams_j_homomorphism_all_z24_units_divisibility`,
  - `Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition`, `Mat3.kb5_antisym_channel_zorn_cross_product_bridge`,
  - `ko_theory_pmi_bruhat_projector_colimit_stability`, `kb7_master_clifford_bott_wigner_s4_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Idempotence (`hP : P * P = P`) and unital ring homomorphisms (`ι : B →+* B'`) are explicit theorem parameters.
* **BUCKET 3 — Open mathematical bridges:**
  - An actual `S₄` action and equivariance proof for the four channels; the `S₄` group-algebra decomposition;
    a topological model of Adams' `J` and `π₃ˢ`; a `KO₀` construction and index theorem; and a compatible
    tensor-tower colimit map remain open. Numerical coincidences in this owner do not discharge them.

## iv. References

- Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*, arXiv:2602.15029 (2026).
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic` (`dressedPeirceProjector`, `genPhi`, `genV`, `genSig`, `evenGrade`, `comm`).
- `InfoGeometry.Core.TensorPeirceDecomposition` (`PeirceIndex`, `peirceIndex_card`).
- `Omega.POM.CatalanMoments` (`catalanNumber`, `paper_pom_catalan_moments`).
-/

namespace CliffordBottKTheoryWignerS4Poset

universe u v

-- ============================================================================
-- SECTION 0: The 7-Stage Clifford–Bott–Wigner–S₄ Poset (𝔎𝔅₁ ≺ ⋯ ≺ 𝔎𝔅₇)
-- ============================================================================

/-- The seven named stages used to order declarations in this file. The associated cover graph is
acyclic by rank; this does not prove mathematical dependency edges between the listed topics. -/
inductive CliffordBottWignerS4Stage : Type
  | kb1S4WedderburnArtinAndV4Quotient
  | kb2SyntacticTreePermutohedronCayleyCatalan
  | kb3AdamsJHomomorphismPi3SpheresMod24
  | kb4WignerClebschGordanFourChannelSplit
  | kb5AntisymmetricChannelZornCrossProductBridge
  | kb6KO0BruhatProjectorIdempotenceAndIndex
  | kb7ColimitStabilizationAndMasterSynthesis
  deriving DecidableEq, Repr

namespace CliffordBottWignerS4Stage

/-- Numerical stage index `0 .. 6` for `CliffordBottWignerS4Stage`. -/
def rank : CliffordBottWignerS4Stage → ℕ
  | .kb1S4WedderburnArtinAndV4Quotient => 0
  | .kb2SyntacticTreePermutohedronCayleyCatalan => 1
  | .kb3AdamsJHomomorphismPi3SpheresMod24 => 2
  | .kb4WignerClebschGordanFourChannelSplit => 3
  | .kb5AntisymmetricChannelZornCrossProductBridge => 4
  | .kb6KO0BruhatProjectorIdempotenceAndIndex => 5
  | .kb7ColimitStabilizationAndMasterSynthesis => 6

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder CliffordBottWignerS4Stage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype CliffordBottWignerS4Stage where
  elems := {
    .kb1S4WedderburnArtinAndV4Quotient,
    .kb2SyntacticTreePermutohedronCayleyCatalan,
    .kb3AdamsJHomomorphismPi3SpheresMod24,
    .kb4WignerClebschGordanFourChannelSplit,
    .kb5AntisymmetricChannelZornCrossProductBridge,
    .kb6KO0BruhatProjectorIdempotenceAndIndex,
    .kb7ColimitStabilizationAndMasterSynthesis
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{KB}_k \prec \mathfrak{KB}_{k+1}$ of the 7-stage spine. -/
inductive coverEdge : CliffordBottWignerS4Stage → CliffordBottWignerS4Stage → Prop
  | kb1_to_kb2 : coverEdge .kb1S4WedderburnArtinAndV4Quotient .kb2SyntacticTreePermutohedronCayleyCatalan
  | kb2_to_kb3 : coverEdge .kb2SyntacticTreePermutohedronCayleyCatalan .kb3AdamsJHomomorphismPi3SpheresMod24
  | kb3_to_kb4 : coverEdge .kb3AdamsJHomomorphismPi3SpheresMod24 .kb4WignerClebschGordanFourChannelSplit
  | kb4_to_kb5 : coverEdge .kb4WignerClebschGordanFourChannelSplit .kb5AntisymmetricChannelZornCrossProductBridge
  | kb5_to_kb6 : coverEdge .kb5AntisymmetricChannelZornCrossProductBridge .kb6KO0BruhatProjectorIdempotenceAndIndex
  | kb6_to_kb7 : coverEdge .kb6KO0BruhatProjectorIdempotenceAndIndex .kb7ColimitStabilizationAndMasterSynthesis

/-- Every Hasse cover edge strictly increases the stage rank. -/
theorem coverEdge_strictMono {a b : CliffordBottWignerS4Stage} (h : coverEdge a b) :
    a.rank < b.rank := by
  cases h <;> decide

/-- No stage has a cover edge to itself. -/
theorem coverEdge_acyclic (a : CliffordBottWignerS4Stage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (coverEdge_strictMono h)

end CliffordBottWignerS4Stage

-- ============================================================================
-- SECTION 1 (𝔎𝔅₁–𝔎𝔅₃): Finite Dimension, Tree, Catalan, and Modulo-24 Arithmetic
-- ============================================================================

/-- `n`-th Catalan number `C_n = (2n choose n) / (n + 1)` re-exported from canonical
`Omega.POM.CatalanMoments.catalanNumber`. -/
abbrev catalanNum (n : ℕ) : ℕ :=
  Omega.POM.CatalanMoments.catalanNumber n

/--
**Theorem 1 (𝔎𝔅₁–𝔎𝔅₃ — Finite Dimension and Tree-Count Arithmetic):**
This theorem verifies numerical identities: the displayed sums of squares total 24 and 6,
`1 + 2 + 3 + 3 = 3 * 3`, the values `4^(4-2) = 16` and `24 - 16 = φ(24)`, two Catalan
values, a gcd calculation, and `4^4 = 16 * 16`. These equalities alone do not construct group
representations, a group-algebra decomposition, a Bott-periodicity map, or an Adams `J` map.
-/
theorem s4_wedderburn_artin_trees_and_adams_j_mod24_lock :
    (1 ^ 2 + 1 ^ 2 + 2 ^ 2) + (3 ^ 2 + 3 ^ 2) = 24 ∧
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 6 ∧
    1 + 2 + 3 + 3 = 3 * 3 ∧
    4 ^ (4 - 2) = 16 ∧
    24 - 4 ^ (4 - 2) = Nat.totient 24 ∧
    catalanNum 3 = 5 ∧
    catalanNum 4 = 14 ∧
    Nat.gcd (5 ^ 2 - 1) (7 ^ 2 - 1) = 24 ∧
    4 ^ 4 = 16 * 16 := by
  decide

/--
**Theorem 1b (𝔎𝔅₃ — Modulo-24 Unit Arithmetic):**
The proposition gives `φ(24) = 8` and proves that every `k : Fin 24` coprime to 24 has
`k.val * k.val ≡ 1 (mod 24)`. It does not identify this fact with a Bernoulli denominator
or prove an Adams `J`-homomorphism statement.
-/
theorem adams_j_homomorphism_all_z24_units_divisibility :
    Nat.totient 24 = 8 ∧
    (∀ k : Fin 24, Nat.Coprime k.val 24 → (k.val * k.val - 1) % 24 = 0) := by
  decide

-- ============================================================================
-- SECTION 2 (𝔎𝔅₄–𝔎𝔅₅): Scaled Matrix Coordinate Channels and the Zorn Cross-Product Identity
-- ============================================================================

/-- Canonical `3 × 3` matrix carrier `Matrix (Fin 3) (Fin 3) K` over `K`. -/
abbrev Mat3 (K : Type u) : Type u :=
  Matrix (Fin 3) (Fin 3) K

namespace Mat3
variable {K : Type u} [CommRing K]

/-- Scalar multiplication `c • A` on `Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
def smul (c : K) (A : Mat3 K) : Mat3 K :=
  c • A

/-- Matrix trace `A 0 0 + A 1 1 + A 2 2` on `Mat3 K`, equal to `Matrix.trace A`. -/
def tr (A : Mat3 K) : K :=
  A 0 0 + A 1 1 + A 2 2

/-- Matrix transpose `Aᵀ` on `Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
def transpose (A : Mat3 K) : Mat3 K :=
  Matrix.transpose A

-- The 4 Division-Free Wigner–Clebsch–Gordan Projection Channels of 6 • M ∈ 3 ⊗ 3:

/-- Channel `1_triv` (Isotropic Scalar Trace `2 Tr(M) I₃`, dim = 1): -/
def cgChan1_Triv (M : Mat3 K) : Mat3 K :=
  Matrix.of fun i j => if i = j then 2 * tr M else 0

/-- Channel `2_S3` (Traceless Diagonal Quadrupole factoring through `S₄ / V₄ ≅ S₃`, dim = 2): -/
def cgChan2_Quadrupole (M : Mat3 K) : Mat3 K :=
  Matrix.of fun i j => if i = j then 6 * M i i - 2 * tr M else 0

/-- Channel `3_+` (Symmetric Off-Diagonal Strain `3(M + Mᵀ)_off`, dim = 3): -/
def cgChan3_SymOff (M : Mat3 K) : Mat3 K :=
  Matrix.of fun i j => if i = j then 0 else 3 * (M i j + M j i)

/-- Channel `3_-` (Antisymmetric Zorn Cross-Product Vorticity `3(M - Mᵀ)_off`, dim = 3): -/
def cgChan3_AntisymVort (M : Mat3 K) : Mat3 K :=
  Matrix.of fun i j => if i = j then 0 else 3 * (M i j - M j i)

/-- 3D Zorn exterior cross product `u × v` on `Fin 3 → K`. -/
def zornCross3D (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/--
**Theorem 2 (𝔎𝔅₄ & 𝔎𝔅₅ — Scaled Coordinate Decomposition and Zorn Identity):**
For `M : Matrix (Fin 3) (Fin 3) K` over a commutative ring `K`, this theorem proves the exact
scaled reconstruction `6 • M` from four explicitly defined coordinate maps, together with
trace and transpose identities. Since 6 is not assumed invertible, it does not assert an
unscaled direct-sum decomposition. No `S₄` action or Clebsch–Gordan equivariance is defined.
-/
theorem wigner_clebsch_gordan_s4_four_channel_decomposition (M : Mat3 K) :
    smul 6 M =
      cgChan1_Triv M + cgChan2_Quadrupole M +
      cgChan3_SymOff M + cgChan3_AntisymVort M ∧
    tr (cgChan2_Quadrupole M) = 0 ∧
    tr (cgChan3_SymOff M) = 0 ∧
    tr (cgChan3_AntisymVort M) = 0 ∧
    transpose (cgChan3_SymOff M) = cgChan3_SymOff M ∧
    transpose (cgChan3_AntisymVort M) = smul (-1) (cgChan3_AntisymVort M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [smul, Matrix.smul_apply, cgChan1_Triv, cgChan2_Quadrupole, cgChan3_SymOff, cgChan3_AntisymVort, tr] <;>
      ring_nf
  · simp [tr, cgChan2_Quadrupole]
    ring
  · simp [tr, cgChan3_SymOff]
  · simp [tr, cgChan3_AntisymVort]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transpose, Matrix.transpose, cgChan3_SymOff] <;>
      ring_nf
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transpose, Matrix.transpose, smul, Matrix.smul_apply, cgChan3_AntisymVort] <;>
      ring_nf

/-- The four scaled channel maps are pairwise orthogonal projectors on `Mat3 K`.

The factor `6` records that the displayed channel maps are six times the
corresponding rational projections; all identities remain division-free over
an arbitrary commutative ring. -/
theorem wigner_clebsch_gordan_scaled_projector_laws (M : Mat3 K) :
    cgChan1_Triv (cgChan1_Triv M) = smul 6 (cgChan1_Triv M) ∧
    cgChan2_Quadrupole (cgChan2_Quadrupole M) = smul 6 (cgChan2_Quadrupole M) ∧
    cgChan3_SymOff (cgChan3_SymOff M) = smul 6 (cgChan3_SymOff M) ∧
    cgChan3_AntisymVort (cgChan3_AntisymVort M) = smul 6 (cgChan3_AntisymVort M) ∧
    cgChan1_Triv (cgChan2_Quadrupole M) = 0 ∧
    cgChan2_Quadrupole (cgChan1_Triv M) = 0 ∧
    cgChan1_Triv (cgChan3_SymOff M) = 0 ∧
    cgChan3_SymOff (cgChan1_Triv M) = 0 ∧
    cgChan1_Triv (cgChan3_AntisymVort M) = 0 ∧
    cgChan3_AntisymVort (cgChan1_Triv M) = 0 ∧
    cgChan2_Quadrupole (cgChan3_SymOff M) = 0 ∧
    cgChan3_SymOff (cgChan2_Quadrupole M) = 0 ∧
    cgChan2_Quadrupole (cgChan3_AntisymVort M) = 0 ∧
    cgChan3_AntisymVort (cgChan2_Quadrupole M) = 0 ∧
    cgChan3_SymOff (cgChan3_AntisymVort M) = 0 ∧
    cgChan3_AntisymVort (cgChan3_SymOff M) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [cgChan1_Triv, cgChan2_Quadrupole, cgChan3_SymOff,
        cgChan3_AntisymVort, smul, Matrix.smul_apply, tr] <;>
      ring_nf

/-- The Frobenius bilinear form on `3 × 3` matrices, written without division. -/
def frobInner (A B : Mat3 K) : K :=
  A 0 0 * B 0 0 + A 0 1 * B 0 1 + A 0 2 * B 0 2 +
  A 1 0 * B 1 0 + A 1 1 * B 1 1 + A 1 2 * B 1 2 +
  A 2 0 * B 2 0 + A 2 1 * B 2 1 + A 2 2 * B 2 2

/-- Algebraic Frobenius orthogonality and Pythagorean identity for the four
scaled channels. The form is bilinear over any commutative ring; no positivity
or real inner-product structure is assumed. -/
theorem wigner_clebsch_gordan_frobenius_orthogonality (M N : Mat3 K) :
    frobInner (cgChan1_Triv M) (cgChan2_Quadrupole N) = 0 ∧
    frobInner (cgChan2_Quadrupole M) (cgChan1_Triv N) = 0 ∧
    frobInner (cgChan1_Triv M) (cgChan3_SymOff N) = 0 ∧
    frobInner (cgChan3_SymOff M) (cgChan1_Triv N) = 0 ∧
    frobInner (cgChan1_Triv M) (cgChan3_AntisymVort N) = 0 ∧
    frobInner (cgChan3_AntisymVort M) (cgChan1_Triv N) = 0 ∧
    frobInner (cgChan2_Quadrupole M) (cgChan3_SymOff N) = 0 ∧
    frobInner (cgChan3_SymOff M) (cgChan2_Quadrupole N) = 0 ∧
    frobInner (cgChan2_Quadrupole M) (cgChan3_AntisymVort N) = 0 ∧
    frobInner (cgChan3_AntisymVort M) (cgChan2_Quadrupole N) = 0 ∧
    frobInner (cgChan3_SymOff M) (cgChan3_AntisymVort N) = 0 ∧
    frobInner (cgChan3_AntisymVort M) (cgChan3_SymOff N) = 0 ∧
    36 * frobInner M N =
      frobInner (cgChan1_Triv M) (cgChan1_Triv N) +
      frobInner (cgChan2_Quadrupole M) (cgChan2_Quadrupole N) +
      frobInner (cgChan3_SymOff M) (cgChan3_SymOff N) +
      frobInner (cgChan3_AntisymVort M) (cgChan3_AntisymVort N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [frobInner, cgChan1_Triv, cgChan2_Quadrupole,
      cgChan3_SymOff, cgChan3_AntisymVort, tr] <;>
    ring_nf

/--
**Theorem 2b (𝔎𝔅₅ — Antisymmetric Channel `3_-` Realizes the 3D Zorn Cross Product `u × v`):**
For any two 3-vectors `u, v : Fin 3 → K`, let `M = Matrix.vecMulVec u v` (`M i j = u i * v j`)
be their bilinear outer product in `3 ⊗ 3`:
1. The scalar trace `tr (Matrix.vecMulVec u v)` is the Euclidean dot product
   `u 0 * v 0 + u 1 * v 1 + u 2 * v 2` (Channel `1_triv`).
2. The three cyclic off-diagonal components `(1, 2)`, `(2, 0)`, `(0, 1)` of the antisymmetric
   Wigner–Clebsch–Gordan channel `cgChan3_AntisymVort (Matrix.vecMulVec u v)` equal `3` times
   the three components of the 3D Zorn cross product `zornCross3D u v`!
-/
theorem kb5_antisym_channel_zorn_cross_product_bridge (u v : Fin 3 → K) :
    tr (Matrix.vecMulVec u v) = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 ∧
    cgChan3_AntisymVort (Matrix.vecMulVec u v) 1 2 = 3 * zornCross3D u v 0 ∧
    cgChan3_AntisymVort (Matrix.vecMulVec u v) 2 0 = 3 * zornCross3D u v 1 ∧
    cgChan3_AntisymVort (Matrix.vecMulVec u v) 0 1 = 3 * zornCross3D u v 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tr, Matrix.vecMulVec_apply]
  · simp [cgChan3_AntisymVort, zornCross3D, Matrix.vecMulVec_apply]
  · simp [cgChan3_AntisymVort, zornCross3D, Matrix.vecMulVec_apply]
  · simp [cgChan3_AntisymVort, zornCross3D, Matrix.vecMulVec_apply]

/--
**Theorem 2c (𝔎𝔅₅ — Canonical Bridge to `InfoGeometry.Algebra.ZornVectorMatrix`):**
Connects `Mat3.tr (Matrix.vecMulVec u v)` and `Mat3.zornCross3D u v` directly to the canonical
Zorn vector-matrix operations `InfoGeometry.Algebra.ZornVec3.dot`, `InfoGeometry.Algebra.ZornVec3.cross`,
and upper-corner Zorn multiplication `InfoGeometry.Algebra.ZornVectorMatrix.mul`:
1. `tr (Matrix.vecMulVec u v) = InfoGeometry.Algebra.ZornVec3.dot u v`,
2. `zornCross3D u v = InfoGeometry.Algebra.ZornVec3.cross u v`,
3. `(InfoGeometry.Algebra.ZornVectorMatrix.mul ⟨0, u, fun _ => 0, 0⟩ ⟨0, v, fun _ => 0, 0⟩).w = InfoGeometry.Algebra.ZornVec3.cross u v`.
-/
theorem kb5_zorn_vector_matrix_cross_and_dot_bridge (u v : Fin 3 → K) :
    tr (Matrix.vecMulVec u v) = InfoGeometry.Algebra.ZornVec3.dot u v ∧
    zornCross3D u v = InfoGeometry.Algebra.ZornVec3.cross u v ∧
    (InfoGeometry.Algebra.ZornVectorMatrix.mul
      (⟨0, u, fun _ => 0, 0⟩ : InfoGeometry.Algebra.ZornVectorMatrix K)
      (⟨0, v, fun _ => 0, 0⟩ : InfoGeometry.Algebra.ZornVectorMatrix K)).w =
      InfoGeometry.Algebra.ZornVec3.cross u v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
    simp [tr, Matrix.vecMulVec_apply]
  · ext i
    fin_cases i <;> simp [zornCross3D, InfoGeometry.Algebra.ZornVec3.cross]
  · ext i
    simp [InfoGeometry.Algebra.ZornVectorMatrix.mul]

end Mat3

-- ============================================================================
-- SECTION 3 (𝔎𝔅₆–𝔎𝔅₇): Conditional Peirce Projector Laws and Finite Index Cardinality
-- ============================================================================

section KOTheoryColimitStabilization
variable {B : Type u} {B' : Type v} [Ring B] [Ring B']

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.TensorPeirceDecomposition

/-- Legacy name for the Peirce-dressed element `P + genPhi - genSig - genV * conePlus`.
This definition alone does not construct a `KO₀` class or index. -/
def P_hat_KO (P M : B) : B :=
  P + genPhi P M M - genSig P M M - genV P M M * conePlus P M

/-- Diagonal Peirce compression `K_diag P X = P X P + (1 - P) X (1 - P)`, coinciding with
canonical `InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade`. -/
abbrev K_diag (P X : B) : B :=
  evenGrade P X

/--
**Theorem 3 (𝔎𝔅₆ & 𝔎𝔅₇ — Conditional Peirce Identities and Finite Cardinality):**
Under the explicit idempotence hypothesis `hP` and for a unital ring homomorphism `ι`, this
proves equality with the canonical dressed Peirce element, idempotence, the even-grade
commutator identity, preservation of idempotence under `ι`, and a cardinality formula for
`PeirceIndex`. It does not define a trace, `KO₀` class, index, completed colimit, or Bott map.
-/
theorem ko_theory_pmi_bruhat_projector_colimit_stability
    (P M : B) (hP : P * P = P) (ι : B →+* B') (n : ℕ) :
    P_hat_KO P M = dressedPeirceProjector P M M ∧
    P_hat_KO P M * P_hat_KO P M = P_hat_KO P M ∧
    K_diag P (P_hat_KO P M - P) = - comm (conePlus P M) (coneMinus P M) ∧
    ι (P_hat_KO P M) * ι (P_hat_KO P M) = ι (P_hat_KO P M) ∧
    Fintype.card (PeirceIndex (n + 4)) = 16 * Fintype.card (PeirceIndex n) := by
  have h_eq : P_hat_KO P M = dressedPeirceProjector P M M :=
    (dressedPeirceProjector_eq hP M M).symm
  have h_idem : P_hat_KO P M * P_hat_KO P M = P_hat_KO P M := by
    rw [h_eq]
    exact dressedPeirceProjector_idempotent hP M M
  have h_diag : K_diag P (P_hat_KO P M - P) = - comm (conePlus P M) (coneMinus P M) := by
    dsimp [K_diag, P_hat_KO]
    peirce_nf hP
  have h_colim : ι (P_hat_KO P M) * ι (P_hat_KO P M) = ι (P_hat_KO P M) := by
    rw [← map_mul, h_idem]
  have h_bott : Fintype.card (PeirceIndex (n + 4)) = 16 * Fintype.card (PeirceIndex n) := by
    rw [peirceIndex_card (n + 4), peirceIndex_card n, Nat.pow_add]
    ring
  exact ⟨h_eq, h_idem, h_diag, h_colim, h_bott⟩

/--
**Theorem 4 (𝔎𝔅₇ — Master Conjunction of Finite Arithmetic and Conditional Algebraic Identities):**
This conjunction collects the declaration-order graph acyclicity, selected finite arithmetic
equalities, the scaled matrix coordinate and Zorn identities, and the conditional Peirce
identities from Theorem 3. It proves the listed propositions together; it does not construct
maps connecting them into a mathematical synthesis, nor a representation, `KO₀` index, Bott
periodicity, or categorical colimit.
-/
theorem kb7_master_clifford_bott_wigner_s4_synthesis
    {K : Type u} [CommRing K] (M : Mat3 K) (u v : Fin 3 → K)
    (P X : B) (hP : P * P = P) (ι : B →+* B') (n : ℕ) :
    (∀ a : CliffordBottWignerS4Stage, ¬ CliffordBottWignerS4Stage.coverEdge a a) ∧
    ((1 ^ 2 + 1 ^ 2 + 2 ^ 2) + (3 ^ 2 + 3 ^ 2) = 24 ∧
     catalanNum 3 = 5 ∧ catalanNum 4 = 14 ∧
     Nat.gcd (5 ^ 2 - 1) (7 ^ 2 - 1) = 24) ∧
    (Mat3.smul 6 M =
       Mat3.cgChan1_Triv M + Mat3.cgChan2_Quadrupole M +
       Mat3.cgChan3_SymOff M + Mat3.cgChan3_AntisymVort M ∧
     Mat3.cgChan3_AntisymVort (Matrix.vecMulVec u v) 1 2 = 3 * Mat3.zornCross3D u v 0) ∧
    (P_hat_KO P X * P_hat_KO P X = P_hat_KO P X ∧
     K_diag P (P_hat_KO P X - P) = - comm (conePlus P X) (coneMinus P X) ∧
     ι (P_hat_KO P X) * ι (P_hat_KO P X) = ι (P_hat_KO P X) ∧
     Fintype.card (PeirceIndex (n + 4)) = 16 * Fintype.card (PeirceIndex n)) := by
  have hS4 := s4_wedderburn_artin_trees_and_adams_j_mod24_lock
  have hCG := Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition M
  have hZorn := Mat3.kb5_antisym_channel_zorn_cross_product_bridge u v
  have hKO := ko_theory_pmi_bruhat_projector_colimit_stability P X hP ι n
  exact ⟨CliffordBottWignerS4Stage.coverEdge_acyclic,
    ⟨hS4.1, hS4.2.2.2.2.2.1, hS4.2.2.2.2.2.2.1, hS4.2.2.2.2.2.2.2.1⟩,
    ⟨hCG.1, hZorn.2.1⟩,
    ⟨hKO.2.1, hKO.2.2.1, hKO.2.2.2.1, hKO.2.2.2.2⟩⟩

end KOTheoryColimitStabilization

end CliffordBottKTheoryWignerS4Poset
