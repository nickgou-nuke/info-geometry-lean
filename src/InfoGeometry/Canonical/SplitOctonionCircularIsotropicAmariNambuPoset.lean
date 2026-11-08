/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.Canonical.SplitOctonionCircularChiralClosure
import InfoGeometry.Canonical.SplitOctonionPaperBasisBridge
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
import InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset

/-!
# Split-Octonion Circularly Polarized Isotropic Basis, Chiral DeWitt Sum/Difference, Amari–Chentsov Baryon Cubic Tensor, and Non-Commutative Nambu Associator Poset (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`)

This canonical module formalizes the 7-stage Acyclic Causal Poset
$$\mathfrak{O}_1 \prec \mathfrak{O}_2 \prec \mathfrak{O}_3 \prec \{\mathfrak{O}_4, \mathfrak{O}_5\} \prec \mathfrak{O}_6 \prec \mathfrak{O}_7$$
unifying the **Circularly Polarized Witt / Catto–Gürsey Split-Octonion Basis** of `ZornMatrix`,
the **Chiral DeWitt Vacuum Split** $(u_0, u_0^*) \leftrightarrow (I = u_0 + u_0^*, S_P = u_0 - u_0^*)$,
the **Maximally Isotropic (Null) Affine Coordinate Subspaces** $(\mathfrak{n}_+, \mathfrak{n}_-)$
of Amari Information Geometry, the **Amari–Chentsov Cubic Skewness Tensor = 3-Quark Baryon Singlet**,
and the **Non-Commutative Nambu 3-Bracket Associator** on the DeWitt Difference $S_P$:

1. **Rung 0 & Rung 1 Socratic Aporia (`socratic_aporia_isotropic_null_subspaces_and_split_metric_det`,
   `rung1_circular_polarization_converts_opposite_squares_to_isotropic_pair`)**:
   - Why two 3D subspaces $\mathfrak{n}_+$ and $\mathfrak{n}_-$ with **zero internal metric**
     ($\{u_i, u_j\} = 0$ and $\{u_i^*, u_j^*\} = 0$) form a **non-degenerate** 6D manifold:
     in the split basis $(u_1, u_2, u_3; u_1^*, u_2^*, u_3^*)$, the $6 \times 6$ metric matrix
     $G_{\text{split}} = \begin{pmatrix} 0_3 & I_3 \\ I_3 & 0_3 \end{pmatrix}$ satisfies
     $G_{\text{split}}^2 = I_6$.
   - Why circular polarization is required: in any associative ring $B$, if a compact generator
     $e^2 = -1$ and a hyperbolic boost generator $\tilde{e}^2 = +1$ anticommute ($e \tilde{e} + \tilde{e} e = 0$),
     neither is nilpotent, but their circularly polarized combinations $e + \tilde{e}$ and
     $-e + \tilde{e}$ are **square-zero nilpotent** ($(e + \tilde{e})^2 = 0$, $(-e + \tilde{e})^2 = 0$)
     with non-degenerate cross-anticommutator $\{e + \tilde{e}, -e + \tilde{e}\} = 4 \cdot 1$.

2. **Stage `𝔒₁` (`o1_chiral_dewitt_vacuum_idempotents_and_sum_diff_basis`)**:
   The Chiral DeWitt Vacuum Idempotents $u_0 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
   $u_0^* = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ in `ZornMat R` over any `[Ring R]`
   satisfy $u_0^2 = u_0$, $(u_0^*)^2 = u_0^*$, $u_0 u_0^* = u_0^* u_0 = 0$, and their sum and
   difference form the **Chiral DeWitt Split Basis**:
   $$I = u_0 + u_0^* = 1, \qquad S_P = u_0 - u_0^* = \gamma_5, \qquad S_P^2 = I$$
   bridged directly to `SplitOctonionQuaternionCircularBasis` (`rootPlus`, `rootMinus`, `diagEll`)
   and `SplitOctonionPaperBasisBridge` (`paperOne`, `paperI`).

3. **Stage `𝔒₂` (`o2_circular_polarized_isotropic_spaces_and_ray_exponentials`)**:
   - **Chiral Bimodule Absorption** over `[Ring R]`:
     $u_0 N_+(x) = N_+(x) u_0^* = N_+(x)$, $u_0^* N_+(x) = N_+(x) u_0 = 0$,
     $u_0^* N_-(y) = N_-(y) u_0 = N_-(y)$, and $u_0 N_-(y) = N_-(y) u_0^* = 0$.
   - **Maximal Isotropy** over `[CommRing K]`:
     $\{N_+(x), N_+(y)\} = 0$, $\{N_-(x), N_-(y)\} = 0$, $N_+(x)^2 = 0$, and $N_-(y)^2 = 0$.
   - **Exact Ray Exponential Flatness vs. Non-Collinear Diquark Defect**:
     Along any ray, $\mathcal{E}_+(t_1 x) \mathcal{E}_+(t_2 x) = \mathcal{E}_+((t_1 + t_2) x)$ and
     $\mathcal{E}_-(t_1 y) \mathcal{E}_-(t_2 y) = \mathcal{E}_-((t_1 + t_2) y)$, while for general
     $x_1, x_2 \in K^3$ the non-collinear defect is the Zorn diquark cross term
     $(1 + N_+(x_1))(1 + N_+(x_2)) - (1 + N_+(x_1 + x_2)) = N_-(x_1 \times x_2)$.

4. **Stages `𝔒₃, 𝔒₄, 𝔒₅` (`o3_o4_o5_dewitt_sum_fisher_metric_and_dewitt_diff_berry_curvature`)**:
   - **Opposite-Chirality Collision onto $(u_0, u_0^*)$** (`𝔒₃`):
     $N_+(x) N_-(y) = (x \cdot y) u_0$ and $N_-(y) N_+(x) = (y \cdot x) u_0^*$.
   - **DeWitt Sum = Operator Fisher Metric $V(x, y)$** (`𝔒₄`):
     $V(x, y) := \{N_+(x), N_-(y)\} = (x \cdot y) u_0 + (y \cdot x) u_0^*$, which over `[CommRing K]`
     equals $(x \cdot y)(u_0 + u_0^*) = (x \cdot y) I$.
   - **DeWitt Difference = Operator Berry Curvature / Skewness $\Sigma(x, y)$** (`𝔒₅`):
     $\Sigma(x, y) := [N_+(x), N_-(y)] = (x \cdot y) u_0 - (y \cdot x) u_0^*$, which over `[CommRing K]`
     equals $(x \cdot y)(u_0 - u_0^*) = (x \cdot y) S_P$.
   - **Chiral DeWitt Duality**: $S_P V(x, y) = \Sigma(x, y)$ and $S_P \Sigma(x, y) = V(x, y)$.

5. **Stage `𝔒₆` (`o6_split_octonion_diquark_hodge_dual_and_amari_chentsov_baryon_cubic`)**:
   - **Diquark Hodge Dual Map ($\mathfrak{n}_+ \times \mathfrak{n}_+ \to \mathfrak{n}_-$)**:
     $N_+(x) N_+(y) = N_-(x \times y)$ and $N_-(x) N_-(y) = -N_+(x \times y)$.
   - **Amari–Chentsov Cubic Skewness Tensor = 3-Quark Baryon Singlet**:
     $T(x, y, z) := \{N_+(x) N_+(y), N_+(z)\} = (z \cdot (x \times y)) u_0 + ((x \times y) \cdot z) u_0^*$,
     which over `[CommRing K]` equals $\det(x, y, z)(u_0 + u_0^*) = \det(x, y, z) I$.

6. **Stage `𝔒₇` (`o7_noncommutative_nambu_associator_on_dewitt_difference`)**:
   Over any non-commutative ring `[Ring R]`, for $u, v \in R^3$, the self-associators of
   $N_+(u)$ and $N_-(v)$ land strictly on the **DeWitt Difference $S_P = u_0 - u_0^*$**:
   $$[N_+(u), N_+(u), N_+(u)]_{\text{assoc}} = -\llbracket u \rrbracket (u_0 - u_0^*) = -\llbracket u \rrbracket S_P$$
   $$[N_-(v), N_-(v), N_-(v)]_{\text{assoc}} = -\llbracket v \rrbracket (u_0 - u_0^*) = -\llbracket v \rrbracket S_P$$
   where $\llbracket u \rrbracket = u \cdot (u \times u) = (u \times u) \cdot u$ is the Nambu 3-bracket.

## i. Overview

Formalizes the 7-stage `SplitOctonionAmariNambuStage` poset (`𝔒₁ ≺ … ≺ 𝔒₇`) uniting chiral
DeWitt vacuum idempotents, circularly polarized isotropic Witt bases, bi-Lagrangian split metrics,
Fisher/Berry DeWitt sum/difference pairings, diquark Hodge duality, and Nambu 3-bracket associators.

## ii. Key results

- `SplitOctonionAmariNambuStage.causalEdge_acyclic`
- `SplitOctonionAmariNambuStage.card_eq_seven`
- `o7_noncommutative_nambu_associator_on_dewitt_difference`

## iii. Table of contents

- Part I: The 7-Stage Causal Poset (`𝔒₁ ≺ … ≺ 𝔒₇`)
- Parts II–IV: Bi-Lagrangian Split Metric, Fisher/Berry DeWitt Duality, and Nambu Associator

## iv. References

- M. Zorn, *Alternativkörper und quadratische Systeme* (1933).
- Y. Nambu, *Generalized Hamiltonian Dynamics* (1973).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `SplitOctonionAmariNambuStage.causalEdge_acyclic`, `SplitOctonionAmariNambuStage.card_eq_seven`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- Stages `𝔒₁`–`𝔒₇` over `[Ring R]` and `[CommRing K]`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Continuum octonionic gauge field integration beyond algebraic Zorn vector-matrices.
-/

namespace InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset

open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

/-- Unambiguous alias for the ring-polymorphic `ZornMatrix R` over `[Ring R]`. -/
abbrev ZornMat (R : Type*) := InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix R

/-- Unambiguous alias for left scalar multiplication on `ZornMat R`. -/
@[simp] def zornSmul {R : Type*} [Ring R] (c : R) (X : ZornMat R) : ZornMat R :=
  InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul c X

/-- Unambiguous alias for the Zorn associator `(X * Y) * Z - X * (Y * Z)` on `ZornMat R`. -/
@[simp] def zornAssociator {R : Type*} [Ring R] (X Y Z : ZornMat R) : ZornMat R :=
  InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator X Y Z

/-- Unambiguous alias for `zornConePlus` in `ZornMat R`. -/
@[simp] def zornPlusVec {R : Type*} [Ring R] (u : Vec3 R) : ZornMat R :=
  InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u

/-- Unambiguous alias for `zornConeMinus` in `ZornMat R`. -/
@[simp] def zornMinusVec {R : Type*} [Ring R] (v : Vec3 R) : ZornMat R :=
  InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConeMinus v

/-- Unambiguous alias for `gamma5` in `ZornMat R`. -/
@[simp] def zornGamma5 {R : Type*} [Ring R] : ZornMat R :=
  InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.gamma5

@[simp] lemma zornMat_neg_a {R : Type*} [Ring R] (X : ZornMat R) : (-X).a = -X.a := rfl
@[simp] lemma zornMat_neg_u {R : Type*} [Ring R] (X : ZornMat R) : (-X).u = -X.u := rfl
@[simp] lemma zornMat_neg_v {R : Type*} [Ring R] (X : ZornMat R) : (-X).v = -X.v := rfl
@[simp] lemma zornMat_neg_d {R : Type*} [Ring R] (X : ZornMat R) : (-X).d = -X.d := rfl

/-!
## Part I: The 7-Stage Acyclic Causal Poset (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`)
-/

/-- The 7 stages of the Split-Octonion Circularly Polarized Isotropic Amari & Nambu Poset
(`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`). -/
inductive SplitOctonionAmariNambuStage : Type
  | O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis
  | O2_CircularPolarizedIsotropicWittBasesAndRayFlatness
  | O3_BiLagrangianSplitMetricNondegeneracy
  | O4_DeWittSumFisherMetricAnticommutator
  | O5_DeWittDiffBerryCurvatureCommutator
  | O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor
  | O7_NonCommutativeNambuAssociatorOnDeWittDifference
  deriving DecidableEq, Repr, Inhabited

namespace SplitOctonionAmariNambuStage

/-- Topological rank of each stage in `0..6`. -/
def rank : SplitOctonionAmariNambuStage → ℕ
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis => 0
  | .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness => 1
  | .O3_BiLagrangianSplitMetricNondegeneracy => 2
  | .O4_DeWittSumFisherMetricAnticommutator => 3
  | .O5_DeWittDiffBerryCurvatureCommutator => 4
  | .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor => 5
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => 6

/-- `rank` is injective on `SplitOctonionAmariNambuStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LE SplitOctonionAmariNambuStage where
  le a b := rank a ≤ rank b

instance : LT SplitOctonionAmariNambuStage where
  lt a b := rank a < rank b

instance : PartialOrder SplitOctonionAmariNambuStage where
  le_refl a := Nat.le_refl (rank a)
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm _ _ hab hba := rank_injective (Nat.le_antisymm hab hba)

instance instDecidableRelLE : DecidableRel (· ≤ · : SplitOctonionAmariNambuStage → SplitOctonionAmariNambuStage → Prop) :=
  fun a b => Nat.decLe (rank a) (rank b)

instance instDecidableRelLT : DecidableRel (· < · : SplitOctonionAmariNambuStage → SplitOctonionAmariNambuStage → Prop) :=
  fun a b => Nat.decLt (rank a) (rank b)

instance : Fintype SplitOctonionAmariNambuStage where
  elems := {
    .O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis,
    .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness,
    .O3_BiLagrangianSplitMetricNondegeneracy,
    .O4_DeWittSumFisherMetricAnticommutator,
    .O5_DeWittDiffBerryCurvatureCommutator,
    .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor,
    .O7_NonCommutativeNambuAssociatorOnDeWittDifference
  }
  complete x := by cases x <;> simp

/-- `SplitOctonionAmariNambuStage` has exactly 7 elements. -/
theorem card_eq_seven : Fintype.card SplitOctonionAmariNambuStage = 7 := by
  decide

/-- Direct causal edge relation in the diamond poset `𝔒₁ ≺ 𝔒₂ ≺ 𝔒₃ ≺ {𝔒₄, 𝔒₅} ≺ 𝔒₆ ≺ 𝔒₇`. -/
def causalEdge : SplitOctonionAmariNambuStage → SplitOctonionAmariNambuStage → Prop
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis,
    .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness => True
  | .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness,
    .O3_BiLagrangianSplitMetricNondegeneracy => True
  | .O3_BiLagrangianSplitMetricNondegeneracy,
    .O4_DeWittSumFisherMetricAnticommutator => True
  | .O3_BiLagrangianSplitMetricNondegeneracy,
    .O5_DeWittDiffBerryCurvatureCommutator => True
  | .O4_DeWittSumFisherMetricAnticommutator,
    .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor => True
  | .O5_DeWittDiffBerryCurvatureCommutator,
    .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor => True
  | .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor,
    .O7_NonCommutativeNambuAssociatorOnDeWittDifference => True
  | _, _ => False

instance instDecidableCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every causal edge strictly increases topological rank. -/
theorem causalEdge_strictMono {a b : SplitOctonionAmariNambuStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;>
    revert h <;>
    unfold causalEdge rank <;>
    decide

/-- Transitive closure of `causalEdge` strictly increases topological rank. -/
theorem transGen_causalEdge_strictMono {a b : SplitOctonionAmariNambuStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strictMono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strictMono hbc)

/-- **DAG Acyclicity Theorem (`causalEdge_acyclic`)**:
No stage in `𝔒₁..𝔒₇` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (s : SplitOctonionAmariNambuStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (transGen_causalEdge_strictMono h)

/-- Monotone representation-depth assignment across `𝔒₁..𝔒₇`. -/
def toRepDepth : SplitOctonionAmariNambuStage → RepDepth
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis => .operator
  | .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness => .operator
  | .O3_BiLagrangianSplitMetricNondegeneracy => .operator
  | .O4_DeWittSumFisherMetricAnticommutator => .transport
  | .O5_DeWittDiffBerryCurvatureCommutator => .transport
  | .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor => .thermo
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => .thermo

/-- Monotone ontology meta-level assignment across `𝔒₁..𝔒₇`. -/
def toOntologyMetaLevel : SplitOctonionAmariNambuStage → OntologyMetaLevel
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDiffBasis => .M1_ProjectorClabject
  | .O2_CircularPolarizedIsotropicWittBasesAndRayFlatness => .M1_ProjectorClabject
  | .O3_BiLagrangianSplitMetricNondegeneracy => .M2_GrassmannianPowertypeOrbit
  | .O4_DeWittSumFisherMetricAnticommutator => .M2_GrassmannianPowertypeOrbit
  | .O5_DeWittDiffBerryCurvatureCommutator => .M2_GrassmannianPowertypeOrbit
  | .O6_SplitOctonionDiquarkDualAndAmariChentsovBaryonCubicTensor => .M3_ErlangenCasimirMetaLaw
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => .M3_ErlangenCasimirMetaLaw

/-- `toRepDepth` is monotone with respect to the stage order on `SplitOctonionAmariNambuStage`. -/
theorem toRepDepth_monotone {a b : SplitOctonionAmariNambuStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth RepDepth.toNat <;>
    decide

/-- `toOntologyMetaLevel` is monotone with respect to the stage order on `SplitOctonionAmariNambuStage`. -/
theorem toOntologyMetaLevel_monotone {a b : SplitOctonionAmariNambuStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel OntologyMetaLevel.rank <;>
    decide

end SplitOctonionAmariNambuStage

/-!
## Part II: Rung 0 & Rung 1 Socratic Aporia — Bi-Lagrangian Isotropic Split Metric & Circular Polarization
-/

section SocraticAporiaAndCircularPolarization

/-- The $6 \times 6$ bi-Lagrangian split metric matrix
$G_{\text{split}} = \begin{pmatrix} 0_3 & I_3 \\ I_3 & 0_3 \end{pmatrix}$
on $\mathfrak{n}_+ \oplus \mathfrak{n}_-$ indexed by `Fin 3 ⊕ Fin 3`. -/
def splitMetric6 (R : Type*) [CommRing R] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R :=
  Matrix.fromBlocks 0 1 1 0

/-- **Rung 0 Socratic Aporia Theorem
(`socratic_aporia_isotropic_null_subspaces_and_split_metric_det`)**:
Why two 3D subspaces $\mathfrak{n}_+$ and $\mathfrak{n}_-$ with **zero internal metric**
($\{u_i, u_j\} = 0$ and $\{u_i^*, u_j^*\} = 0$) form a **strictly non-degenerate** 6D manifold:
1. The upper-left $3 \times 3$ block of `splitMetric6 R` (the metric on $\mathfrak{n}_+ \times \mathfrak{n}_+$)
   is identically `0` (`toBlocks₁₁ (splitMetric6 R) = 0`),
2. The lower-right $3 \times 3$ block of `splitMetric6 R` (the metric on $\mathfrak{n}_- \times \mathfrak{n}_-$)
   is identically `0` (`toBlocks₂₂ (splitMetric6 R) = 0`),
3. The off-diagonal cross-blocks on $\mathfrak{n}_+ \times \mathfrak{n}_-$ are `1 : Matrix (Fin 3) (Fin 3) R`,
4. `splitMetric6 R * splitMetric6 R = 1` (so `splitMetric6 R` is an exact involution, hence invertible!),
5. In `InfoGeometry.Algebra.ZornMatrix R`, the circular Witt basis elements `U i` and `V j` realize
   this exact bi-Lagrangian table:
   `U i * U j + U j * U i = 0`, `V i * V j + V j * V i = 0`, and
   `U i * V j + V j * U i = if i = j then I else 0`. -/
theorem socratic_aporia_isotropic_null_subspaces_and_split_metric_det
    {R : Type*} [CommRing R] (i j : Fin 3) :
    Matrix.toBlocks₁₁ (splitMetric6 R) = 0 ∧
    Matrix.toBlocks₂₂ (splitMetric6 R) = 0 ∧
    Matrix.toBlocks₁₂ (splitMetric6 R) = 1 ∧
    Matrix.toBlocks₂₁ (splitMetric6 R) = 1 ∧
    splitMetric6 R * splitMetric6 R = 1 ∧
    (InfoGeometry.Algebra.ZornMatrix.U i : InfoGeometry.Algebra.ZornMatrix R) *
        InfoGeometry.Algebra.ZornMatrix.U j +
      InfoGeometry.Algebra.ZornMatrix.U j * InfoGeometry.Algebra.ZornMatrix.U i = 0 ∧
    (InfoGeometry.Algebra.ZornMatrix.V i : InfoGeometry.Algebra.ZornMatrix R) *
        InfoGeometry.Algebra.ZornMatrix.V j +
      InfoGeometry.Algebra.ZornMatrix.V j * InfoGeometry.Algebra.ZornMatrix.V i = 0 ∧
    (InfoGeometry.Algebra.ZornMatrix.U i : InfoGeometry.Algebra.ZornMatrix R) *
        InfoGeometry.Algebra.ZornMatrix.V j +
      InfoGeometry.Algebra.ZornMatrix.V j * InfoGeometry.Algebra.ZornMatrix.U i =
        if i = j then InfoGeometry.Algebra.ZornMatrix.I else 0 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_,
    InfoGeometry.Algebra.ZornMatrix.U_anticommute i j,
    InfoGeometry.Algebra.ZornMatrix.V_anticommute i j,
    InfoGeometry.Algebra.ZornMatrix.U_V_anticommutator i j⟩
  unfold splitMetric6
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-- **Rung 1 Theorem (`rung1_circular_polarization_converts_opposite_squares_to_isotropic_pair`)**:
In any associative ring `B`, let `e` be a compact spin generator (`e * e = -1`) and `et` be an
anticommuting hyperbolic boost generator (`et * et = 1` and `e * et + et * e = 0`):
1. Neither `e` nor `et` is square-zero (`e² = -1`, `et² = +1`),
2. Their circularly polarized combinations `u_scaled := e + et` and `uStar_scaled := -e + et`
   are **strictly square-zero nilpotent**:
   `(e + et) * (e + et) = 0` and `(-e + et) * (-e + et) = 0`,
3. Their cross-anticommutator is strictly non-degenerate:
   `(e + et) * (-e + et) + (-e + et) * (e + et) = (4 : ℤ) • (1 : B)`. -/
theorem rung1_circular_polarization_converts_opposite_squares_to_isotropic_pair
    {B : Type*} [Ring B] (e et : B)
    (he : e * e = -1) (het : et * et = 1) (hanti : e * et + et * e = 0) :
    (e + et) * (e + et) = 0 ∧
    (-e + et) * (-e + et) = 0 ∧
    (e + et) * (-e + et) + (-e + et) * (e + et) = (4 : ℤ) • (1 : B) := by
  refine ⟨?_, ?_, ?_⟩
  · calc (e + et) * (e + et)
      _ = e * e + (e * et + et * e) + et * et := by noncomm_ring
      _ = -1 + 0 + 1 := by rw [he, hanti, het]
      _ = 0 := by abel
  · calc (-e + et) * (-e + et)
      _ = e * e - (e * et + et * e) + et * et := by noncomm_ring
      _ = -1 - 0 + 1 := by rw [he, hanti, het]
      _ = 0 := by abel
  · calc (e + et) * (-e + et) + (-e + et) * (e + et)
      _ = -(e * e) - (e * e) + et * et + et * et := by noncomm_ring
      _ = -(-1) - (-1) + 1 + 1 := by rw [he, het]
      _ = (4 : ℤ) • (1 : B) := by noncomm_ring

end SocraticAporiaAndCircularPolarization

/-!
## Part III: Stages `𝔒₁` & `𝔒₂` — Chiral DeWitt Vacuum Split Basis, Circularly Polarized Isotropic Subspaces $\mathfrak{n}_+, \mathfrak{n}_-$, and Affine Ray Exponentials
-/

section StageO1AndO2

variable {R : Type*} [Ring R]

/-- The upper-left Chiral DeWitt Vacuum Idempotent $u_0 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$
in `ZornMat R`. -/
@[simp] def zornU0 : ZornMat R := ⟨1, 0, 0, 0⟩

/-- The lower-right Chiral DeWitt Vacuum Idempotent $u_0^* = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$
in `ZornMat R`. -/
@[simp] def zornU0Star : ZornMat R := ⟨0, 0, 0, 1⟩

/-- The Chiral DeWitt Sum $I = u_0 + u_0^* = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$. -/
@[simp] def zornDeWittSum : ZornMat R := zornU0 + zornU0Star

/-- The Chiral DeWitt Difference $S_P = u_0 - u_0^* = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
@[simp] def zornDeWittDiff : ZornMat R := zornU0 - zornU0Star

/-- Primal $e$-isotropic ray exponential $\mathcal{E}_+(t, x) = 1 + N_+(t x)$ in `ZornMat R`. -/
@[simp] def zornRayExpPlus (t : R) (x : Vec3 R) : ZornMat R :=
  (1 : ZornMat R) + zornPlusVec (Vec3.smulLeft t x)

/-- Dual $m$-isotropic ray exponential $\mathcal{E}_-(t, y) = 1 + N_-(t y)$ in `ZornMat R`. -/
@[simp] def zornRayExpMinus (t : R) (y : Vec3 R) : ZornMat R :=
  (1 : ZornMat R) + zornMinusVec (Vec3.smulLeft t y)

/-- **Stage `𝔒₁` Theorem (`o1_chiral_dewitt_vacuum_idempotents_and_sum_diff_basis`)**:
In `ZornMat R` over any noncommutative ring `[Ring R]`:
1. $u_0$ and $u_0^*$ are complementary orthogonal idempotents:
   `zornU0 * zornU0 = zornU0`, `zornU0Star * zornU0Star = zornU0Star`,
   `zornU0 * zornU0Star = 0`, and `zornU0Star * zornU0 = 0`,
2. Their sum and difference form the **Chiral DeWitt Split Basis**:
   `zornDeWittSum = (1 : ZornMat R)`, `zornDeWittDiff = zornGamma5`, and
   `zornDeWittDiff * zornDeWittDiff = (1 : ZornMat R)`,
3. In the repository's split-octonion circular basis (`CircularChiralCausalConeBasis`,
   `SplitOctonionPaperBasisBridge`, and `SplitOctonionQuaternionCircularBasis`),
   `Fintype.card ChiralBasis = 8`, `paperOne = paperUPlus + paperUMinus`,
   `paperI = paperUPlus - paperUMinus`, and for every `i : Fin 3`,
   `{rootPlus i, rootMinus i} = 1` and `[rootPlus i, rootMinus i] = diagEll`. -/
theorem o1_chiral_dewitt_vacuum_idempotents_and_sum_diff_basis (i : Fin 3) :
    (zornU0 : ZornMat R) * zornU0 = zornU0 ∧
    (zornU0Star : ZornMat R) * zornU0Star = zornU0Star ∧
    (zornU0 : ZornMat R) * zornU0Star = 0 ∧
    (zornU0Star : ZornMat R) * zornU0 = 0 ∧
    (zornDeWittSum : ZornMat R) = 1 ∧
    (zornDeWittDiff : ZornMat R) = zornGamma5 ∧
    (zornDeWittDiff : ZornMat R) * zornDeWittDiff = 1 ∧
    Fintype.card InfoGeometry.Algebra.CircularChiralCausalConeBasis.ChiralBasis = 8 ∧
    InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperOne =
      InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperUPlus +
        InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperUMinus ∧
    InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperI =
      InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperUPlus -
        InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paperUMinus ∧
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) *
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i) +
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i) *
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) = 1 ∧
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) *
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i) -
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i) *
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) =
      InfoGeometry.Lie.SplitOctonionEllFlowOperator.diagEll := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    InfoGeometry.Algebra.CircularChiralCausalConeBasis.chiral_basis_card,
    InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paper_one_eq_uPlus_add_uMinus,
    InfoGeometry.Canonical.SplitOctonionPaperBasisBridge.paper_I_eq_uPlus_sub_uMinus,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_root_anticommutator i,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_root_commutator i⟩
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]

/-- **Stage `𝔒₂` Theorem (`o2_circular_polarized_isotropic_spaces_and_ray_exponentials`)**:
1. **Chiral Bimodule Absorption & DeWitt Grading** over any `[Ring R]`:
   For all `x y : Vec3 R`:
   - `zornU0 * zornPlusVec x = zornPlusVec x`, `zornPlusVec x * zornU0Star = zornPlusVec x`,
     `zornU0Star * zornPlusVec x = 0`, `zornPlusVec x * zornU0 = 0`,
   - `zornU0Star * zornMinusVec y = zornMinusVec y`, `zornMinusVec y * zornU0 = zornMinusVec y`,
     `zornU0 * zornMinusVec y = 0`, `zornMinusVec y * zornU0Star = 0`,
   - `zornDeWittDiff * zornPlusVec x = zornPlusVec x` and `zornPlusVec x * zornDeWittDiff = -zornPlusVec x`,
   - `zornDeWittDiff * zornMinusVec y = -zornMinusVec y` and `zornMinusVec y * zornDeWittDiff = zornMinusVec y`.
2. **Maximal Isotropy (Vanishing of Self-Anticommutators)** over any `[CommRing K]`:
   For all `x₁ x₂ y₁ y₂ : Vec3 K`:
   - `zornPlusVec x₁ * zornPlusVec x₂ + zornPlusVec x₂ * zornPlusVec x₁ = 0`,
   - `zornMinusVec y₁ * zornMinusVec y₂ + zornMinusVec y₂ * zornMinusVec y₁ = 0`,
   - `zornPlusVec x₁ * zornPlusVec x₁ = 0` and `zornMinusVec y₁ * zornMinusVec y₁ = 0`.
3. **Exact Ray Exponential Flatness vs. Non-Collinear Diquark Defect** over `[CommRing K]`:
   - Along any ray: `zornRayExpPlus t₁ x₁ * zornRayExpPlus t₂ x₁ = zornRayExpPlus (t₁ + t₂) x₁`
     and `zornRayExpMinus t₁ y₁ * zornRayExpMinus t₂ y₁ = zornRayExpMinus (t₁ + t₂) y₁`,
   - For general `x₁, x₂ : Vec3 K`, the non-collinear unipotent product defect is the Zorn diquark
     cross product:
     `((1 : ZornMat K) + zornPlusVec x₁) * ((1 : ZornMat K) + zornPlusVec x₂) - ((1 : ZornMat K) + zornPlusVec (x₁ + x₂)) = zornMinusVec (Vec3.cross x₁ x₂)`. -/
theorem o2_circular_polarized_isotropic_spaces_and_ray_exponentials
    (x y : Vec3 R)
    {K : Type*} [CommRing K] (t₁ t₂ : K) (x₁ x₂ y₁ y₂ : Vec3 K) :
    (zornU0 * zornPlusVec x = zornPlusVec x ∧
     zornPlusVec x * zornU0Star = zornPlusVec x ∧
     zornU0Star * zornPlusVec x = 0 ∧
     zornPlusVec x * zornU0 = 0 ∧
     zornU0Star * zornMinusVec y = zornMinusVec y ∧
     zornMinusVec y * zornU0 = zornMinusVec y ∧
     zornU0 * zornMinusVec y = 0 ∧
     zornMinusVec y * zornU0Star = 0 ∧
     zornDeWittDiff * zornPlusVec x = zornPlusVec x ∧
     zornPlusVec x * zornDeWittDiff = -zornPlusVec x ∧
     zornDeWittDiff * zornMinusVec y = -zornMinusVec y ∧
     zornMinusVec y * zornDeWittDiff = zornMinusVec y) ∧
    (zornPlusVec x₁ * zornPlusVec x₂ + zornPlusVec x₂ * zornPlusVec x₁ = 0 ∧
     zornMinusVec y₁ * zornMinusVec y₂ + zornMinusVec y₂ * zornMinusVec y₁ = 0 ∧
     zornPlusVec x₁ * zornPlusVec x₁ = 0 ∧
     zornMinusVec y₁ * zornMinusVec y₁ = 0) ∧
    (zornRayExpPlus t₁ x₁ * zornRayExpPlus t₂ x₁ = zornRayExpPlus (t₁ + t₂) x₁ ∧
     zornRayExpMinus t₁ y₁ * zornRayExpMinus t₂ y₁ = zornRayExpMinus (t₁ + t₂) y₁ ∧
     ((1 : ZornMat K) + zornPlusVec x₁) * ((1 : ZornMat K) + zornPlusVec x₂) -
       ((1 : ZornMat K) + zornPlusVec (x₁ + x₂)) =
       zornMinusVec (Vec3.cross x₁ x₂)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨?_, ?_, ?_, ?_⟩,
          ⟨?_, ?_, ?_⟩⟩
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornRayExpPlus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornRayExpMinus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)

end StageO1AndO2

/-! ### Isotropy does not imply a globally additive chart law

The Zorn carrier has square-zero rays, but its primal off-diagonal space is not
closed under multiplication: non-collinear products produce a dual cross term.
This explicit witness prevents the isotropy statement from being read as global
abelian flatness. -/

/-- The standard first and second coordinate directions multiply to a nonzero
dual vector in `ZornMatrix ℚ`; hence isotropy of the primal space alone does not
make its unipotent chart additive across distinct directions. -/
theorem zorn_primal_noncollinear_product_ne_zero :
    zornPlusVec (⟨1, 0, 0⟩ : Vec3 ℚ) * zornPlusVec ⟨0, 1, 0⟩ ≠
      (0 : ZornMat ℚ) := by
  intro h
  have hz := congrArg (fun M : ZornMat ℚ => M.v.z) h
  norm_num [zornPlusVec, ZornMatrix.zornConePlus,
    ZornMatrix.mul_v, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] at hz

/-!
## Part IV: Stages `𝔒₃`, `𝔒₄`, & `𝔒₅` — Opposite-Chirality Collision onto $(u_0, u_0^*)$, DeWitt Sum = Operator Fisher Metric $V$, and DeWitt Difference = Operator Berry Curvature $\Sigma$
-/

section StageO3ToO5

variable {R : Type*} [Ring R]

/-- The Operator Fisher Metric anticommutator
$V(x, y) := \{N_+(x), N_-(y)\} = N_+(x) N_-(y) + N_-(y) N_+(x)$ in `ZornMat R`. -/
@[simp] def zornFisherV (x y : Vec3 R) : ZornMat R :=
  zornPlusVec x * zornMinusVec y + zornMinusVec y * zornPlusVec x

/-- The Operator Berry Curvature / Skewness commutator
$\Sigma(x, y) := [N_+(x), N_-(y)] = N_+(x) N_-(y) - N_-(y) N_+(x)$ in `ZornMat R`. -/
@[simp] def zornBerrySig (x y : Vec3 R) : ZornMat R :=
  zornPlusVec x * zornMinusVec y - zornMinusVec y * zornPlusVec x

/-- **Stages `𝔒₃, 𝔒₄, 𝔒₅` Theorem
(`o3_o4_o5_dewitt_sum_fisher_metric_and_dewitt_diff_berry_curvature`)**:
1. **Stage `𝔒₃` — Opposite-Chirality Collision onto $(u_0, u_0^*)$** over `[Ring R]`:
   - `zornPlusVec x * zornMinusVec y = zornSmul (Vec3.dot x y) zornU0`,
   - `zornMinusVec y * zornPlusVec x = zornSmul (Vec3.dot y x) zornU0Star`.
2. **Stage `𝔒₄` — DeWitt Sum = Operator Fisher Metric $V(x, y)$**:
   - Over `[Ring R]`:
     `zornFisherV x y = zornSmul (Vec3.dot x y) zornU0 + zornSmul (Vec3.dot y x) zornU0Star`,
   - Over `[CommRing K]`:
     `zornFisherV xK yK = zornSmul (Vec3.dot xK yK) zornDeWittSum` and
     `zornFisherV xK yK = zornSmul (Vec3.dot xK yK) (1 : ZornMat K)`.
3. **Stage `𝔒₅` — DeWitt Difference = Operator Berry Curvature $\Sigma(x, y)$**:
   - Over `[Ring R]`:
     `zornBerrySig x y = zornSmul (Vec3.dot x y) zornU0 - zornSmul (Vec3.dot y x) zornU0Star`,
   - Over `[CommRing K]`:
     `zornBerrySig xK yK = zornSmul (Vec3.dot xK yK) zornDeWittDiff` and
     `zornBerrySig xK yK = zornSmul (Vec3.dot xK yK) zornGamma5`.
4. **Chiral DeWitt Duality (`S_P V = Σ` and `S_P Σ = V`)** over `[Ring R]`:
   - `zornDeWittDiff * zornFisherV x y = zornBerrySig x y`,
   - `zornDeWittDiff * zornBerrySig x y = zornFisherV x y`.
5. **Basis Specialization (`SplitOctonionCircularChiralClosure`)**:
   For all `i j : Fin 3`,
   `anticommutator (sigmaPlus i) (sigmaMinus j) = if i = j then I else 0` and
   `commutator (sigmaPlus i) (sigmaMinus j) = if i = j then chirality else 0`. -/
theorem o3_o4_o5_dewitt_sum_fisher_metric_and_dewitt_diff_berry_curvature
    (x y : Vec3 R)
    {K : Type*} [CommRing K] (xK yK : Vec3 K) (i j : Fin 3) :
    (zornPlusVec x * zornMinusVec y = zornSmul (Vec3.dot x y) zornU0 ∧
     zornMinusVec y * zornPlusVec x = zornSmul (Vec3.dot y x) zornU0Star) ∧
    (zornFisherV x y =
       zornSmul (Vec3.dot x y) zornU0 + zornSmul (Vec3.dot y x) zornU0Star ∧
     zornFisherV xK yK = zornSmul (Vec3.dot xK yK) zornDeWittSum ∧
     zornFisherV xK yK = zornSmul (Vec3.dot xK yK) (1 : ZornMat K)) ∧
    (zornBerrySig x y =
       zornSmul (Vec3.dot x y) zornU0 - zornSmul (Vec3.dot y x) zornU0Star ∧
     zornBerrySig xK yK = zornSmul (Vec3.dot xK yK) zornDeWittDiff ∧
     zornBerrySig xK yK = zornSmul (Vec3.dot xK yK) zornGamma5) ∧
    (zornDeWittDiff * zornFisherV x y = zornBerrySig x y ∧
     zornDeWittDiff * zornBerrySig x y = zornFisherV x y) ∧
    (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.anticommutator
       (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaPlus i)
       (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaMinus j) =
       if i = j then InfoGeometry.Algebra.ZornMatrix.I else 0) ∧
    (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.commutator
       (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaPlus i)
       (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaMinus j) =
       if i = j then InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.chirality else 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaPlus_sigmaMinus_anticommutator i j,
    InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.commutator_sigmaPlus_sigmaMinus i j⟩
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try noncomm_ring)
  · ext <;> (simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try noncomm_ring)

end StageO3ToO5

/-!
## Part V: Stage `𝔒₆` — Split-Octonion Diquark Hodge Dual (`u_i u_j = ε_{ijk} u_k*`) and the Amari–Chentsov Cubic Skewness / 3-Quark Baryon Singlet Tensor
-/

section StageO6_DiquarkAndAmariChentsovCubic

variable {R : Type*} [Ring R]

/-- The trilinear Amari–Chentsov / 3-Quark Baryon Cubic Skewness Tensor in `ZornMat R`:
$$T(x, y, z) := \{N_+(x) N_+(y), \, N_+(z)\} = (N_+(x) N_+(y)) N_+(z) + N_+(z) (N_+(x) N_+(y))$$ -/
@[simp] def zornAmariChentsovCubic (x y z : Vec3 R) : ZornMat R :=
  (zornPlusVec x * zornPlusVec y) * zornPlusVec z +
    zornPlusVec z * (zornPlusVec x * zornPlusVec y)

/-- **Stage `𝔒₆` Theorem
(`o6_split_octonion_diquark_hodge_dual_and_amari_chentsov_baryon_cubic`)**:
1. **Diquark Hodge Dual Map ($\mathfrak{n}_+ \times \mathfrak{n}_+ \to \mathfrak{n}_-$ and
   $\mathfrak{n}_- \times \mathfrak{n}_- \to \mathfrak{n}_+$)** over any `[Ring R]`:
   - `zornPlusVec x * zornPlusVec y = zornMinusVec (Vec3.cross x y)`,
   - `zornMinusVec x * zornMinusVec y = -zornPlusVec (Vec3.cross x y)`,
   - On the circular basis (`ZornMatrix`), `U 0 * U 1 = V 2`, `U 1 * U 2 = V 0`, and `U 2 * U 0 = V 1`.
2. **Trilinear Amari–Chentsov Cubic Skewness Tensor = 3-Quark Baryon Singlet**:
   - Over `[Ring R]`:
     `zornAmariChentsovCubic x y z = zornFisherV z (Vec3.cross x y)` and
     `zornAmariChentsovCubic x y z = zornSmul (Vec3.dot z (Vec3.cross x y)) zornU0 + zornSmul (Vec3.baryonDet3 x y z) zornU0Star`,
   - Over `[CommRing K]`:
     `zornAmariChentsovCubic xK yK zK = zornSmul (Vec3.baryonDet3 xK yK zK) zornDeWittSum` and
     `zornAmariChentsovCubic xK yK zK = zornSmul (Vec3.baryonDet3 xK yK zK) (1 : ZornMat K)`. -/
theorem o6_split_octonion_diquark_hodge_dual_and_amari_chentsov_baryon_cubic
    (x y z : Vec3 R)
    {K : Type*} [CommRing K] (xK yK zK : Vec3 K) :
    (zornPlusVec x * zornPlusVec y = zornMinusVec (Vec3.cross x y) ∧
     zornMinusVec x * zornMinusVec y = -zornPlusVec (Vec3.cross x y) ∧
     (InfoGeometry.Algebra.ZornMatrix.U 0 : InfoGeometry.Algebra.ZornMatrix K) *
       InfoGeometry.Algebra.ZornMatrix.U 1 = InfoGeometry.Algebra.ZornMatrix.V 2 ∧
     (InfoGeometry.Algebra.ZornMatrix.U 1 : InfoGeometry.Algebra.ZornMatrix K) *
       InfoGeometry.Algebra.ZornMatrix.U 2 = InfoGeometry.Algebra.ZornMatrix.V 0 ∧
     (InfoGeometry.Algebra.ZornMatrix.U 2 : InfoGeometry.Algebra.ZornMatrix K) *
       InfoGeometry.Algebra.ZornMatrix.U 0 = InfoGeometry.Algebra.ZornMatrix.V 1) ∧
    (zornAmariChentsovCubic x y z = zornFisherV z (Vec3.cross x y) ∧
     zornAmariChentsovCubic x y z =
       zornSmul (Vec3.dot z (Vec3.cross x y)) zornU0 +
         zornSmul (Vec3.baryonDet3 x y z) zornU0Star ∧
     zornAmariChentsovCubic xK yK zK =
       zornSmul (Vec3.baryonDet3 xK yK zK) zornDeWittSum ∧
     zornAmariChentsovCubic xK yK zK =
       zornSmul (Vec3.baryonDet3 xK yK zK) (1 : ZornMat K)) := by
  refine ⟨⟨?_, ?_,
    InfoGeometry.Algebra.ZornMatrix.U_zero_mul_U_one,
    InfoGeometry.Algebra.ZornMatrix.U_one_mul_U_two,
    InfoGeometry.Algebra.ZornMatrix.U_two_mul_U_zero⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> (simp [zornAmariChentsovCubic, zornFisherV, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]; try noncomm_ring)
  · ext <;> (simp [zornAmariChentsovCubic, Vec3.baryonDet3, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]; try noncomm_ring)
  · ext <;> (simp [zornAmariChentsovCubic, Vec3.baryonDet3, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornAmariChentsovCubic, Vec3.baryonDet3, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]; try ring)

end StageO6_DiquarkAndAmariChentsovCubic

/-!
## Part VI: Stage `𝔒₇` — Non-Commutative Nambu Associator Lands Strictly on the DeWitt Difference $S_P = u_0 - u_0^*$
-/

section StageO7_NonCommutativeNambuAssociator

variable {R : Type*} [Ring R]

/-- **Stage `𝔒₇` Theorem (`o7_noncommutative_nambu_associator_on_dewitt_difference`)**:
Over any non-commutative associative ring `[Ring R]`, for any quark vector `u : Vec3 R` and
antiquark vector `v : Vec3 R`:
1. **Chromomagnetic Self-Wedge (`N_+(u)² = N_-(u × u)`)**:
   `zornPlusVec u * zornPlusVec u = zornMinusVec (Vec3.cross u u)` and
   `zornMinusVec v * zornMinusVec v = -zornPlusVec (Vec3.cross v v)`.
2. **Equality of Left and Right Nambu 3-Bracket Contractions**:
   `Vec3.dot u (Vec3.cross u u) = Vec3.nambu3 u` and
   `Vec3.dot (Vec3.cross u u) u = Vec3.nambu3 u`.
3. **Primal Self-Associator Lands Strictly on the DeWitt Difference $S_P = u_0 - u_0^*$**:
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = -zornBerrySig u (Vec3.cross u u)`,
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = zornSmul (Vec3.nambu3 u) zornU0Star - zornSmul (Vec3.nambu3 u) zornU0`,
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = zornSmul (-Vec3.nambu3 u) zornDeWittDiff`,
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = zornSmul (-Vec3.nambu3 u) zornGamma5`,
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩`.
4. **Dual Lower-Sector Self-Associator Also Lands on the DeWitt Difference $S_P = u_0 - u_0^*$**:
   `zornAssociator (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) = zornSmul (-Vec3.nambu3 v) zornDeWittDiff`. -/
theorem o7_noncommutative_nambu_associator_on_dewitt_difference (u v : Vec3 R) :
    (zornPlusVec u * zornPlusVec u = zornMinusVec (Vec3.cross u u) ∧
     zornMinusVec v * zornMinusVec v = -zornPlusVec (Vec3.cross v v)) ∧
    (Vec3.dot u (Vec3.cross u u) = Vec3.nambu3 u ∧
     Vec3.dot (Vec3.cross u u) u = Vec3.nambu3 u) ∧
    (zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
       -zornBerrySig u (Vec3.cross u u) ∧
     zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
       zornSmul (Vec3.nambu3 u) zornU0Star - zornSmul (Vec3.nambu3 u) zornU0 ∧
     zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
       zornSmul (-Vec3.nambu3 u) zornDeWittDiff ∧
     zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
       zornSmul (-Vec3.nambu3 u) zornGamma5 ∧
     zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
       ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩) ∧
    zornAssociator (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) =
      zornSmul (-Vec3.nambu3 v) zornDeWittDiff := by
  have hAnom := (noncommutative_mat4_plucker_hodge_and_nambu_klein_anomaly u u).2.2.2.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hAnom⟩, ?_⟩
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp only [Vec3.dot, Vec3.cross, Vec3.nambu3]; noncomm_ring
  · simp only [Vec3.dot, Vec3.cross, Vec3.nambu3]; noncomm_ring
  · ext <;> (simp [zornAssociator, zornBerrySig, zornPlusVec, zornMinusVec,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConeMinus,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try noncomm_ring)
  · change InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u) = _
    rw [hAnom]
    ext <;> simp [zornSmul, zornU0, zornU0Star,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul,
      Vec3.smulLeft]
  · change InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u) = _
    rw [hAnom]
    ext <;> simp [zornSmul, zornDeWittDiff, zornU0, zornU0Star,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul,
      Vec3.smulLeft]
  · change InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u)
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConePlus u) = _
    rw [hAnom]
    ext <;> simp [zornSmul, zornGamma5,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.gamma5,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul,
      Vec3.smulLeft]
  · ext <;> (simp [zornAssociator, zornMinusVec, zornDeWittDiff, zornU0, zornU0Star, zornSmul,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.associator,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornConeMinus,
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight, Vec3.nambu3]; try noncomm_ring)

end StageO7_NonCommutativeNambuAssociator

/-!
## Part VII: Master Synthesis Theorem (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`)
-/

/-- **Master Synthesis Theorem (`split_octonion_circular_isotropic_amari_nambu_master_synthesis`)**:
Unifies the 7-stage Acyclic Causal Poset (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`), the $6 \times 6$ bi-Lagrangian
split metric involution `splitMetric6 K * splitMetric6 K = 1`, circular polarization nilpotency,
the Chiral DeWitt Vacuum Split $(u_0, u_0^*) \leftrightarrow (I = u_0 + u_0^*, S_P = u_0 - u_0^*)$,
maximal isotropy of $\mathfrak{n}_+$ and $\mathfrak{n}_-$ (`{N_+(x), N_+(y)} = 0`), exact ray
exponential flatness (`ℰ_+(t₁ x) ℰ_+(t₂ x) = ℰ_+((t₁ + t₂) x)`), DeWitt Sum = Operator Fisher
Metric (`{N_+(x), N_-(y)} = (x · y)(u_0 + u_0*)`), DeWitt Difference = Operator Berry Curvature
(`[N_+(x), N_-(y)] = (x · y)(u_0 - u_0*)`), the diquark Hodge dual `N_+(x) N_+(y) = N_-(x × y)`
and Amari–Chentsov / 3-quark baryon cubic tensor `{N_+(x) N_+(y), N_+(z)} = det(x, y, z) I`,
and the non-commutative Nambu associator `[N_+(u), N_+(u), N_+(u)]_assoc = -⟦u⟧ S_P`. -/
theorem split_octonion_circular_isotropic_amari_nambu_master_synthesis
    {R : Type*} [Ring R] (u v : Vec3 R)
    {K : Type*} [CommRing K] (t₁ t₂ : K) (xK yK zK : Vec3 K) :
    -- 1. 7-Stage Poset Acyclicity & Cardinality:
    (∀ st : SplitOctonionAmariNambuStage,
      ¬ Relation.TransGen SplitOctonionAmariNambuStage.causalEdge st st) ∧
    Fintype.card SplitOctonionAmariNambuStage = 7 ∧
    -- 2. Rung 0 Bi-Lagrangian Split Metric Involution:
    splitMetric6 K * splitMetric6 K = 1 ∧
    -- 3. Stage O1 (Chiral DeWitt Vacuum Idempotents & Sum/Difference Basis):
    (zornU0 : ZornMat R) * zornU0 = zornU0 ∧
    (zornU0Star : ZornMat R) * zornU0Star = zornU0Star ∧
    (zornU0 : ZornMat R) * zornU0Star = 0 ∧
    (zornDeWittSum : ZornMat R) = 1 ∧
    (zornDeWittDiff : ZornMat R) = zornGamma5 ∧
    (zornDeWittDiff : ZornMat R) * zornDeWittDiff = 1 ∧
    -- 4. Stage O2 (Maximal Isotropy & Affine Ray Exponential Homomorphism):
    zornPlusVec xK * zornPlusVec yK + zornPlusVec yK * zornPlusVec xK = 0 ∧
    zornMinusVec xK * zornMinusVec yK + zornMinusVec yK * zornMinusVec xK = 0 ∧
    zornRayExpPlus t₁ xK * zornRayExpPlus t₂ xK = zornRayExpPlus (t₁ + t₂) xK ∧
    zornRayExpMinus t₁ yK * zornRayExpMinus t₂ yK = zornRayExpMinus (t₁ + t₂) yK ∧
    -- 5. Stages O3, O4, O5 (DeWitt Sum Fisher Metric V & DeWitt Difference Berry Curvature Σ):
    zornPlusVec u * zornMinusVec v = zornSmul (Vec3.dot u v) zornU0 ∧
    zornMinusVec v * zornPlusVec u = zornSmul (Vec3.dot v u) zornU0Star ∧
    zornFisherV xK yK = zornSmul (Vec3.dot xK yK) zornDeWittSum ∧
    zornBerrySig xK yK = zornSmul (Vec3.dot xK yK) zornDeWittDiff ∧
    zornDeWittDiff * zornFisherV u v = zornBerrySig u v ∧
    -- 6. Stage O6 (Split-Octonion Diquark Dual & Amari–Chentsov Baryon Cubic Tensor):
    zornPlusVec u * zornPlusVec v = zornMinusVec (Vec3.cross u v) ∧
    zornAmariChentsovCubic xK yK zK =
      zornSmul (Vec3.baryonDet3 xK yK zK) zornDeWittSum ∧
    -- 7. Stage O7 (Non-Commutative Nambu Associator on the DeWitt Difference S_P):
    zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
      zornSmul (-Vec3.nambu3 u) zornDeWittDiff ∧
    zornAssociator (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) =
      zornSmul (-Vec3.nambu3 v) zornDeWittDiff := by
  have hR0 := socratic_aporia_isotropic_null_subspaces_and_split_metric_det (R := K) 0 0
  have hO1 := o1_chiral_dewitt_vacuum_idempotents_and_sum_diff_basis (R := R) 0
  have hO2 := o2_circular_polarized_isotropic_spaces_and_ray_exponentials u v t₁ t₂ xK yK xK yK
  have hO2' := o2_circular_polarized_isotropic_spaces_and_ray_exponentials u v t₁ t₂ xK yK yK yK
  have hO345 := o3_o4_o5_dewitt_sum_fisher_metric_and_dewitt_diff_berry_curvature u v xK yK 0 0
  have hO6 := o6_split_octonion_diquark_hodge_dual_and_amari_chentsov_baryon_cubic u v u xK yK zK
  have hO7 := o7_noncommutative_nambu_associator_on_dewitt_difference u v
  exact ⟨SplitOctonionAmariNambuStage.causalEdge_acyclic,
    SplitOctonionAmariNambuStage.card_eq_seven,
    hR0.2.2.2.2.1,
    hO1.1, hO1.2.1, hO1.2.2.1, hO1.2.2.2.2.1, hO1.2.2.2.2.2.1, hO1.2.2.2.2.2.2.1,
    hO2.2.1.1, hO2.2.1.2.1, hO2.2.2.1, hO2'.2.2.2.1,
    hO345.1.1, hO345.1.2, hO345.2.1.2.1, hO345.2.2.1.2.1, hO345.2.2.2.1.1,
    hO6.1.1, hO6.2.2.2.1,
    hO7.2.2.1.2.2.1, hO7.2.2.2⟩

end InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
