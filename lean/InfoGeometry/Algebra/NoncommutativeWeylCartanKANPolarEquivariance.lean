/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.IwasawaKANTriad
import InfoGeometry.Optimization.PolarDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-!
# Weyl Gauge Scale, Noncommutative Trace-to-Determinant, Cartan Split, and $G(\cdot)G^{-1}$ Equivariance of the Iwasawa $K A N$ & Polar Decompositions ($\mathcal{K}\mathcal{P}_1$–$\mathcal{K}\mathcal{P}_4$)

This owner formalizes the acyclic dependency poset $(\mathcal{K}\mathcal{P}, \preceq)$
linking the Weyl diagonal scalar-matrix trace component, the noncommutative Plemelj–Newton
trace-to-determinant formula, the Cartan decomposition $2 \bullet M = M_{\mathrm{diag\text{-}tr}}(M) +
M_{\mathrm{sym}}^0(M) + M_{\mathrm{antisym}}^0(M)$ (together with the exact centrality
equivalence for scalar diagonal embeddings), the Iwasawa $K A N$ subgroups and their Borel–Cholesky /
Schur-complement Polar Gram reduction, and unitary/symmetry equivariance under $G(\cdot)G^{-1}$
conjugation over arbitrary noncommutative rings `[Ring B]` and $\star$-rings `[Ring B] [StarRing B]`:

* $\mathcal{K}\mathcal{P}_1$: **Weyl Diagonal Scalar-Matrix Trace Component, Cartan Split & Noncommutative Trace-to-Determinant**:
  Decomposes $2 \bullet M = M_{\mathrm{Weyl}}(M) + M_{\mathrm{sym}}^0(M) + M_{\mathrm{antisym}}^0(M)$,
  proves the traceless symmetric/antisymmetric transpose laws and $\mathfrak{gl}_2$ Cartan brackets,
  establishes $(\mathrm{Tr}_2 M)^2 - \mathrm{Tr}_2(M^2) = \{M_{00}, M_{11}\} - \{M_{01}, M_{10}\}$,
  characterizes central scalar diagonal embeddings and gives an explicit non-central Weyl-scale
  witness over $B = M_2(\mathbb{Z})$,
  and bridges to `InfoGeometry.Canonical.IwasawaKANTriad` (`e1`, `e2`, `eps`).
* $\mathcal{K}\mathcal{P}_2$: **Iwasawa $K A N$ Subgroups & Polar Gram Bridge**:
  Proves the Iwasawa $K, A, N$ subgroup composition laws (bridging to `K_grp`, `A_grp`, `N_grp`),
  the elimination of unitary $K$ in $M^\dagger M = (A N)^\dagger (A N)$, and the noncommutative
  Schur complement recovery $S_{11} - n^\star S_{00} n = a_-^\star a_-$.
* $\mathcal{K}\mathcal{P}_3$: **Unitary Symmetry Equivariance of Polar Decomposition**:
  Over any $\star$-ring `R`, proves $G M G^{-1} = U_G P_G$ preserves $U_G^\star U_G = 1$, $P_G^\star = P_G$,
  and $(G M G^{-1})^\star (G M G^{-1}) = G(M^\star M)G^{-1} = P_G^2$, specialized to $M_2(B)$ and
  bridged to `InfoGeometry.Optimization.PolarDecomposition`.
* $\mathcal{K}\mathcal{P}_4$: **Symmetry Equivariance of Iwasawa $K A N$ under $G(\cdot)G^{-1}$**:
  Establishes diagonal Borelian $A(g_+, g_-)$, non-abelian fiber gauge $\iota(g)$, chirality parity
  $\Gamma_1$, and Weyl group reflection $\Sigma$ (opposite Bruhat $N_-(n)$) conjugation laws, plus
  the diamond synthesis `kan_polar_gram_fiber_unitary_equivariance`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
## Theorem-Dependency Poset $(\mathcal{K}\mathcal{P}, \preceq)$

The nodes name proved theorem packages, and an edge means a theorem-level
dependency. `KP1` is the arbitrary-ring Cartan package. `KP2` is the
star-ring KAN/Gram package. `KP3` contains unitary polar covariance and the
real polar-factor transport theorem for the explicitly pushed metric
`Hᵀ * H`. The capstone `KP4` uses `KP2` and `KP3`. The real
positive-definite constructions are a separate carrier and are not inferred
from `KP1`; hence this dependency order is not the previously claimed bounded
diamond.
-/

section CausalPoset

/-- Nodes of the theorem-dependency poset for the Weyl–Cartan, Iwasawa $K A N$,
and Polar packages. -/
inductive WeylCartanKANPolarArchetype
  | KP1
  | KP2
  | KP3
  | KP4
  | KP5
  deriving DecidableEq, Repr, Inhabited

/-- The actual theorem dependencies: `KP1 ≤ KP5`, `KP2 ≤ KP4`, and
`KP3 ≤ KP4`. `KP5` is the real normalization of `KP1`; the KAN and polar
factorization branch remains independent of the Cartan split. -/
def kpPosetLE : WeylCartanKANPolarArchetype → WeylCartanKANPolarArchetype → Prop
  | .KP1, .KP1 => True
  | .KP1, .KP5 => True
  | .KP2, .KP2 => True
  | .KP2, .KP4 => True
  | .KP3, .KP3 => True
  | .KP3, .KP4 => True
  | .KP4, .KP4 => True
  | .KP5, .KP5 => True
  | _, _ => False

instance : DecidableRel kpPosetLE := fun a b => by
  cases a <;> cases b <;> simp only [kpPosetLE] <;> infer_instance

instance : PartialOrder WeylCartanKANPolarArchetype where
  le := kpPosetLE
  le_refl a := by cases a <;> simp [kpPosetLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [kpPosetLE]
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all [kpPosetLE]

-- theorem-class: bridge
/-- The proved order has the Cartan-normalization edge `KP1 ≤ KP5` and the two
independent factorization inputs `KP2, KP3 ≤ KP4`. There are no other cross
edges among these nodes. -/
@[rep_depth operator]
theorem kpPoset_actual_dependencies :
    WeylCartanKANPolarArchetype.KP1 ≤ .KP5 ∧
    WeylCartanKANPolarArchetype.KP2 ≤ .KP4 ∧
    WeylCartanKANPolarArchetype.KP3 ≤ .KP4 ∧
    ¬(WeylCartanKANPolarArchetype.KP2 ≤ .KP3) ∧
    ¬(WeylCartanKANPolarArchetype.KP3 ≤ .KP2) ∧
    ¬(WeylCartanKANPolarArchetype.KP1 ≤ .KP2) ∧
    ¬(WeylCartanKANPolarArchetype.KP1 ≤ .KP3) ∧
    ¬(WeylCartanKANPolarArchetype.KP1 ≤ .KP4) ∧
    ¬(WeylCartanKANPolarArchetype.KP4 ≤ .KP1) ∧
    ¬(WeylCartanKANPolarArchetype.KP5 ≤ .KP4) := by
  simp [LE.le, kpPosetLE]

/-- Exhaustive description of the order: apart from reflexivity, its only
covering edges are `KP1 < KP5`, `KP2 < KP4`, and `KP3 < KP4`. -/
theorem kpPosetLE_iff (a b : WeylCartanKANPolarArchetype) :
    kpPosetLE a b ↔
      a = b ∨
      (a = .KP1 ∧ b = .KP5) ∨
      (a = .KP2 ∧ b = .KP4) ∨
      (a = .KP3 ∧ b = .KP4) := by
  cases a <;> cases b <;> simp [kpPosetLE]

end CausalPoset

/-!
## Foundational Infrastructure: `mat2` Constructor, Simp Lemmas & Noncommutativity Witnesses
-/

def mat2 {B : Type*} (a b c d : B) : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {B : Type*} {M N : Matrix (Fin 2) (Fin 2) B}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

@[simp] private lemma mat2_00 {B : Type*} (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] private lemma mat2_01 {B : Type*} (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] private lemma mat2_10 {B : Type*} (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] private lemma mat2_11 {B : Type*} (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] private lemma tr2_00 {B : Type*} (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] private lemma tr2_01 {B : Type*} (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] private lemma tr2_10 {B : Type*} (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] private lemma tr2_11 {B : Type*} (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 1 1 = M 1 1 := rfl

@[simp] private lemma ct2_00 {B : Type*} [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] private lemma ct2_01 {B : Type*} [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] private lemma ct2_10 {B : Type*} [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] private lemma ct2_11 {B : Type*} [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 1 = star (M 1 1) := rfl

section RingOps

variable {B : Type*} [Ring B]

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] private lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] private lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] private lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] private lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 a

end RingOps

-- theorem-class: witness
/-- Canonical existential noncommutativity witness on `Matrix (Fin 2) (Fin 2) B` for any
nontrivial ring `B`. -/
@[rep_depth operator]
theorem matrix_fin2_noncommutative_witness {B : Type*} [Ring B] [Nontrivial B] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) B, X * Y ≠ Y * X := by
  refine ⟨mat2 1 0 0 0, mat2 0 1 0 0, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp at h01

-- theorem-class: witness
/-- Concrete noncommutativity witnesses for the carrier $M_2(B)$:
1. Over any nontrivial ring $B$, $E_{00} E_{01} \ne E_{01} E_{00}$.
2. Over the noncommutative fiber ring $B = M_2(\mathbb{Z})$, the diagonal fiber embedding
   $\iota(B) \subset M_2(B)$ preserves noncommutativity. -/
@[rep_depth operator]
theorem weyl_cartan_matrix_noncommutative :
    (∀ (B : Type*) [Ring B] [Nontrivial B],
      mat2 (1 : B) 0 0 0 * mat2 0 1 0 0 ≠ mat2 0 1 0 0 * mat2 1 0 0 0) ∧
    (fiberEmbed (mat2 (0 : ℤ) 1 0 0) * fiberEmbed (mat2 (0 : ℤ) 0 1 0) ≠
      fiberEmbed (mat2 (0 : ℤ) 0 1 0) * fiberEmbed (mat2 (0 : ℤ) 1 0 0)) := by
  constructor
  · intro B _ _ h
    have h01 := congrFun (congrFun h 0) 1
    simp at h01
  · intro h
    have h00 := congrFun (congrFun (congrFun (congrFun h 0) 0) 0) 0
    simp [fiberEmbed] at h00

end Matrix2Simp

/-!
## Archetype $\mathcal{K}\mathcal{P}_1$: Weyl Gauge Scale, Noncommutative Trace-to-Determinant & Cartan Split ($\mathfrak{gl}_2 = \mathfrak{z} \oplus \mathfrak{p} \oplus \mathfrak{k}$)
-/

section ArchetypeKP1_WeylCartanAndTraceToDet

variable {B : Type*} [Ring B]

/-- Diagonal scalar-matrix trace component $M_{\mathrm{Weyl}}(M) = \iota(\mathrm{Tr}_2(M)) = \mathrm{diag}(\mathrm{Tr}_2 M, \mathrm{Tr}_2 M)$,
which is central in $M_2(B)$ iff $\mathrm{Tr}_2(M)$ lies in the center of $B$. -/
def weylScalePart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed (Matrix.trace M)

/-- Traceless symmetric part (non-compact Cartan strain $\mathfrak{p} = \mathrm{span}_B\{\Gamma_1, \Sigma\}$). -/
def tracelessSymPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 (M 0 0 - M 1 1) (M 0 1 + M 1 0) (M 1 0 + M 0 1) (M 1 1 - M 0 0)

/-- Traceless antisymmetric part (compact rotation $\mathfrak{k} = \mathrm{span}_B\{\Omega\}$). -/
def tracelessAntisymPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 0 (M 0 1 - M 1 0) (M 1 0 - M 0 1) 0

/-- Symmetrized noncommutative determinant $\det_{\mathrm{sym}}(M) = \{M_{00}, M_{11}\} - \{M_{01}, M_{10}\}$. -/
def symDet (M : Matrix (Fin 2) (Fin 2) B) : B :=
  (M 0 0 * M 1 1 + M 1 1 * M 0 0) - (M 0 1 * M 1 0 + M 1 0 * M 0 1)

-- theorem-class: bridge
/-- Exact owner identification between `(sigmaOp, omegaOp, gamma1Op)` and the triad generators
`(e1, e2, eps)` in `InfoGeometry.Canonical.IwasawaKANTriad`. -/
@[rep_depth operator]
theorem cartan_generators_eq_iwasawaKANTriad :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) = InfoGeometry.Canonical.IwasawaKANTriad.e1 B ∧
    (omegaOp : Matrix (Fin 2) (Fin 2) B) = -InfoGeometry.Canonical.IwasawaKANTriad.e2 B ∧
    (gamma1Op : Matrix (Fin 2) (Fin 2) B) = InfoGeometry.Canonical.IwasawaKANTriad.eps B := by
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2
    · rfl
    · rfl
    · rfl
    · rfl
  · apply ext_fin2
    · simp [omegaOp, InfoGeometry.Canonical.IwasawaKANTriad.e2]
    · simp [omegaOp, InfoGeometry.Canonical.IwasawaKANTriad.e2]
    · simp [omegaOp, InfoGeometry.Canonical.IwasawaKANTriad.e2]
    · simp [omegaOp, InfoGeometry.Canonical.IwasawaKANTriad.e2]
  · rw [InfoGeometry.Canonical.IwasawaKANTriad.eps_eq]
    apply ext_fin2
    · rfl
    · rfl
    · rfl
    · rfl

-- theorem-class: symmetry
/-- **Weyl–Cartan Split & Noncommutative Trace-to-Determinant Theorem ($\mathcal{K}\mathcal{P}_1$)**:
For any operator matrix $M \in M_2(B)$ over a noncommutative ring $B$:
1. $2 \bullet M = M_{\mathrm{Weyl}}(M) + M_{\mathrm{sym}}^0(M) + M_{\mathrm{antisym}}^0(M)$;
2. $\mathrm{Tr}_2(M_{\mathrm{sym}}^0(M)) = 0$ and $\mathrm{Tr}_2(M_{\mathrm{antisym}}^0(M)) = 0$;
3. $(M_{\mathrm{sym}}^0(M))^\top = M_{\mathrm{sym}}^0(M)$ and $(M_{\mathrm{antisym}}^0(M))^\top = -M_{\mathrm{antisym}}^0(M)$;
4. *Noncommutative Plemelj–Newton Trace-to-Determinant*: $(\mathrm{Tr}_2 M)^2 - \mathrm{Tr}_2(M^2) = \det_{\mathrm{sym}}(M)$;
5. *Cartan Lie Brackets*: $\⁅\Gamma_1, \Sigma⁆ = -(2\bullet \Omega)$, $\⁅\Omega, \Gamma_1⁆ = 2\bullet \Sigma$,
   $\⁅\Omega, \Sigma⁆ = -(2\bullet \Gamma_1)$. -/
@[rep_depth operator]
theorem weyl_cartan_split_and_noncommutative_trace_to_det (M : Matrix (Fin 2) (Fin 2) B) :
    weylScalePart M + tracelessSymPart M + tracelessAntisymPart M = 2 • M ∧
    Matrix.trace (tracelessSymPart M) = 0 ∧
    Matrix.trace (tracelessAntisymPart M) = 0 ∧
    (tracelessSymPart M)ᵀ = tracelessSymPart M ∧
    (tracelessAntisymPart M)ᵀ = -tracelessAntisymPart M ∧
    (Matrix.trace M) ^ 2 - Matrix.trace (M * M) = symDet M ∧
    ⁅(gamma1Op : Matrix (Fin 2) (Fin 2) B), (sigmaOp : Matrix (Fin 2) (Fin 2) B)⁆ =
      -(2 • (omegaOp : Matrix (Fin 2) (Fin 2) B)) ∧
    ⁅(omegaOp : Matrix (Fin 2) (Fin 2) B), (gamma1Op : Matrix (Fin 2) (Fin 2) B)⁆ =
      2 • (sigmaOp : Matrix (Fin 2) (Fin 2) B) ∧
    ⁅(omegaOp : Matrix (Fin 2) (Fin 2) B), (sigmaOp : Matrix (Fin 2) (Fin 2) B)⁆ =
      -(2 • (gamma1Op : Matrix (Fin 2) (Fin 2) B)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2
    · simp [weylScalePart, tracelessSymPart, tracelessAntisymPart, fiberEmbed, two_smul]
    · simp [weylScalePart, tracelessSymPart, tracelessAntisymPart, fiberEmbed, two_smul]
    · simp [weylScalePart, tracelessSymPart, tracelessAntisymPart, fiberEmbed, two_smul]
    · simp [weylScalePart, tracelessSymPart, tracelessAntisymPart, fiberEmbed, two_smul]; abel
  · simp [tracelessSymPart]
  · simp [tracelessAntisymPart]
  · apply ext_fin2
    · simp [tracelessSymPart]
    · simp [tracelessSymPart, add_comm]
    · simp [tracelessSymPart, add_comm]
    · simp [tracelessSymPart]
  · apply ext_fin2
    · simp [tracelessAntisymPart]
    · simp [tracelessAntisymPart]
    · simp [tracelessAntisymPart]
    · simp [tracelessAntisymPart]
  · dsimp [symDet]; simp; noncomm_ring
  · rw [Ring.lie_def]
    apply ext_fin2
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]; abel
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
  · rw [Ring.lie_def]
    apply ext_fin2
    · simp [gamma1Op, sigmaOp, omegaOp]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp]
  · rw [Ring.lie_def]
    apply ext_fin2
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]; abel
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]
    · simp [gamma1Op, sigmaOp, omegaOp, two_smul]

-- theorem-class: bridge
/-- When `B` is commutative (`CommRing B`), the symmetrized noncommutative determinant reduces to
the classical doubled determinant `symDet M = 2 • M.det`. -/
@[rep_depth operator]
theorem symDet_eq_two_smul_det_of_commRing {C : Type*} [CommRing C]
    (M : Matrix (Fin 2) (Fin 2) C) :
    symDet M = 2 • M.det := by
  dsimp [symDet]
  rw [Matrix.det_fin_two, two_smul, mul_comm (M 1 1) (M 0 0), mul_comm (M 1 0) (M 0 1)]
  abel

/-- The noncommutative Cartan decomposition is natural under every unital ring
homomorphism. `Matrix.map f` is the induced map on the matrix carrier; the
statement makes explicit which parts of the `M₂(B)` construction can be
transported to a scalar or other coefficient ring. -/
theorem weyl_cartan_data_natural {C : Type*} [Ring C] (f : B →+* C)
    (M : Matrix (Fin 2) (Fin 2) B) :
    f.mapMatrix (weylScalePart M) = weylScalePart (f.mapMatrix M) ∧
    f.mapMatrix (tracelessSymPart M) = tracelessSymPart (f.mapMatrix M) ∧
    f.mapMatrix (tracelessAntisymPart M) = tracelessAntisymPart (f.mapMatrix M) ∧
    f (symDet M) = symDet (f.mapMatrix M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ext_fin2
    all_goals simp [weylScalePart, fiberEmbed, RingHom.mapMatrix_apply, mat2, Matrix.trace,
      Matrix.diag, Fin.sum_univ_two]
  · apply ext_fin2
    all_goals simp [tracelessSymPart, RingHom.mapMatrix_apply, mat2]
  · apply ext_fin2
    all_goals simp [tracelessAntisymPart, RingHom.mapMatrix_apply, mat2]
  · simp [symDet, RingHom.mapMatrix_apply]

-- theorem-class: symmetry
/-- A diagonal scalar-matrix embedding `fiberEmbed a = diag(a, a)` is central in $M_2(B)$
if and only if `a` lies in the center of the base ring `B`. -/
@[rep_depth operator]
theorem fiberEmbed_central_iff (a : B) :
    (∀ N : Matrix (Fin 2) (Fin 2) B, fiberEmbed a * N = N * fiberEmbed a) ↔
    (∀ b : B, a * b = b * a) := by
  constructor
  · intro h b
    have h00 := congrFun (congrFun (h (fiberEmbed b)) 0) 0
    simpa [fiberEmbed] using h00
  · intro hc N
    apply ext_fin2 <;> simp [fiberEmbed, hc]

-- theorem-class: witness
/-- Explicit witness over $B = M_2(\mathbb{Z})$ showing that `weylScalePart M = diag(Tr₂ M, Tr₂ M)`
is NOT central in general when $B$ is noncommutative. -/
@[rep_depth operator]
theorem weylScalePart_noncentral_witness :
    ∃ M N : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ),
      weylScalePart M * N ≠ N * weylScalePart M := by
  refine ⟨mat2 (mat2 (0 : ℤ) 1 0 0) (0 : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
    fiberEmbed (mat2 (0 : ℤ) 0 1 0), ?_⟩
  intro h
  have h00 := congrFun (congrFun (congrFun (congrFun h 0) 0) 0) 0
  simp [weylScalePart, fiberEmbed] at h00

end ArchetypeKP1_WeylCartanAndTraceToDet

/-!
## Archetype $\mathcal{K}\mathcal{P}_2$: Iwasawa $K A N$ Subgroup Structure & Bridge to the Polar Gram Square $M^\dagger M$
-/

section ArchetypeKP2_IwasawaKANAndPolarBridge

variable {B : Type*} [Ring B]

/-- Compact rotor subgroup element $K(c, s) = \bigl(\begin{smallmatrix} c & -s \\ s & c \end{smallmatrix}\bigr) \in M_2(B)$. -/
def iwasawaK (c s : B) : Matrix (Fin 2) (Fin 2) B := mat2 c (-s) s c

/-- Hyperbolic diagonal dilation subgroup element $A(a_+, a_-) = \mathrm{diag}(a_+, a_-) \in M_2(B)$. -/
def iwasawaA (a_plus a_minus : B) : Matrix (Fin 2) (Fin 2) B := mat2 a_plus 0 0 a_minus

/-- Upper-triangular nilpotent Witt subgroup element $N(n) = \bigl(\begin{smallmatrix} 1 & n \\ 0 & 1 \end{smallmatrix}\bigr) \in M_2(B)$. -/
def iwasawaN (n : B) : Matrix (Fin 2) (Fin 2) B := mat2 1 n 0 1

/-- Opposite lower-triangular nilpotent Witt subgroup element $N_-(n) = \bigl(\begin{smallmatrix} 1 & 0 \\ n & 1 \end{smallmatrix}\bigr) \in M_2(B)$. -/
def iwasawaNMinus (n : B) : Matrix (Fin 2) (Fin 2) B := mat2 1 0 n 1

-- theorem-class: bridge
/-- Exact owner identification of `iwasawaK`, `iwasawaA`, `iwasawaN` with `K_grp`, `A_grp`, `N_grp`
from `InfoGeometry.Canonical.IwasawaKANTriad`. -/
@[rep_depth operator]
theorem iwasawa_subgroups_eq_iwasawaKANTriad (c s a_plus a_minus n : B) :
    iwasawaK c s = InfoGeometry.Canonical.IwasawaKANTriad.K_grp B c s ∧
    iwasawaA a_plus a_minus = InfoGeometry.Canonical.IwasawaKANTriad.A_grp B a_plus a_minus ∧
    iwasawaN n = InfoGeometry.Canonical.IwasawaKANTriad.N_grp B n := by
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2
    · rfl
    · rfl
    · rfl
    · rfl
  · apply ext_fin2
    · rfl
    · rfl
    · rfl
    · rfl
  · apply ext_fin2
    · rfl
    · rfl
    · rfl
    · rfl

-- theorem-class: bridge
/-- **Iwasawa $K A N$ Subgroup Laws & Polar Gram Reduction Theorem ($\mathcal{K}\mathcal{P}_2$)**:
1. $N(n_1) N(n_2) = N(n_1 + n_2)$ and $N(n) N(-n) = 1$;
2. $A(a_1, b_1) A(a_2, b_2) = A(a_1 a_2, b_1 b_2)$ and $A(a_+, a_-) N(n) = \bigl(\begin{smallmatrix} a_+ & a_+ n \\ 0 & a_- \end{smallmatrix}\bigr)$;
3. *Polar Gram Reduction*: Over `[StarRing B]`, for any $M = K A(a_+, a_-) N(n)$ with $K^\dagger K = 1$,
   the Polar square $M^\dagger M$ eliminates $K$ and equals the Borel–Cholesky metric:
   $M^\dagger M = (A N)^\dagger (A N) = \bigl(\begin{smallmatrix} a_+^\star a_+ & a_+^\star a_+ n \\ n^\star a_+^\star a_+ & n^\star a_+^\star a_+ n + a_-^\star a_- \end{smallmatrix}\bigr)$;
4. *Schur Complement Recovery*: $(M^\dagger M)_{11} - n^\star (M^\dagger M)_{00} n = a_-^\star a_-$. -/
@[rep_depth operator]
theorem iwasawa_kan_subgroups_and_polar_gram_reduction [StarRing B]
    (a₁ b₁ a₂ b₂ a_plus a_minus n₁ n₂ n : B)
    {K : Matrix (Fin 2) (Fin 2) B} (hK : Kᴴ * K = 1) :
    let M := K * iwasawaA a_plus a_minus * iwasawaN n
    iwasawaN n₁ * iwasawaN n₂ = iwasawaN (n₁ + n₂) ∧
    iwasawaN n * iwasawaN (-n) = 1 ∧
    iwasawaA a₁ b₁ * iwasawaA a₂ b₂ = iwasawaA (a₁ * a₂) (b₁ * b₂) ∧
    iwasawaA a_plus a_minus * iwasawaN n = mat2 a_plus (a_plus * n) 0 a_minus ∧
    Mᴴ * M =
      mat2 (star a_plus * a_plus) (star a_plus * a_plus * n)
           (star n * (star a_plus * a_plus))
           (star n * (star a_plus * a_plus) * n + star a_minus * a_minus) ∧
    (Mᴴ * M) 1 1 - star n * (Mᴴ * M) 0 0 * n = star a_minus * a_minus := by
  intro M
  have h_gram : Mᴴ * M =
      mat2 (star a_plus * a_plus) (star a_plus * a_plus * n)
           (star n * (star a_plus * a_plus))
           (star n * (star a_plus * a_plus) * n + star a_minus * a_minus) := by
    have h_elim : Mᴴ * M =
        (iwasawaA a_plus a_minus * iwasawaN n)ᴴ *
        (iwasawaA a_plus a_minus * iwasawaN n) := by
      dsimp [M]
      calc (K * iwasawaA a_plus a_minus * iwasawaN n)ᴴ *
           (K * iwasawaA a_plus a_minus * iwasawaN n)
        _ = (iwasawaN n)ᴴ * (iwasawaA a_plus a_minus)ᴴ * (Kᴴ * K) *
            iwasawaA a_plus a_minus * iwasawaN n := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = (iwasawaN n)ᴴ * (iwasawaA a_plus a_minus)ᴴ * 1 *
            iwasawaA a_plus a_minus * iwasawaN n := by rw [hK]
        _ = (iwasawaA a_plus a_minus * iwasawaN n)ᴴ *
            (iwasawaA a_plus a_minus * iwasawaN n) := by
            simp only [conjTranspose_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [h_elim]
    apply ext_fin2
    · simp [iwasawaA, iwasawaN]
    · simp [iwasawaA, iwasawaN]; noncomm_ring
    · simp [iwasawaA, iwasawaN]; noncomm_ring
    · simp [iwasawaA, iwasawaN]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, h_gram, ?_⟩
  · apply ext_fin2
    · simp [iwasawaN]
    · simp [iwasawaN, add_comm]
    · simp [iwasawaN]
    · simp [iwasawaN]
  · apply ext_fin2
    · simp [iwasawaN]
    · simp [iwasawaN, add_comm]
    · simp [iwasawaN]
    · simp [iwasawaN]
  · apply ext_fin2
    · simp [iwasawaA]
    · simp [iwasawaA]
    · simp [iwasawaA]
    · simp [iwasawaA]
  · apply ext_fin2
    · simp [iwasawaA, iwasawaN]
    · simp [iwasawaA, iwasawaN]
    · simp [iwasawaA, iwasawaN]
    · simp [iwasawaA, iwasawaN]
  · rw [h_gram]
    simp [mul_assoc]

end ArchetypeKP2_IwasawaKANAndPolarBridge

/-!
## Archetype $\mathcal{K}\mathcal{P}_3$: Polar Decomposition Equivariance under Unitary Symmetry Conjugation $G(\cdot)G^{-1}$
-/

section ArchetypeKP3_PolarDecompositionEquivariance

-- theorem-class: symmetry
/-- **Polar Decomposition Unitary Equivariance Theorem ($\mathcal{K}\mathcal{P}_3$)**:
In any noncommutative $\star$-ring $R$, if $M = U P$ with $U^\star U = 1$ and $P^\star = P$, and
$G \in R^\times$ is a unitary symmetry ($G^{-1} = G^\star$), then $M_G = G M G^{-1}$, $U_G = G U G^{-1}$,
and $P_G = G P G^{-1}$ satisfy:
1. $M_G = U_G P_G$;
2. $U_G^\star U_G = 1$;
3. $P_G^\star = P_G$;
4. $M_G^\star M_G = G (M^\star M) G^{-1} = P_G^2$. -/
@[rep_depth operator]
theorem polar_decomposition_unitary_equivariance {R : Type*} [Ring R] [StarRing R]
    {U P : R} (hU : star U * U = 1) (hP : star P = P)
    (G : Rˣ) (hG_unit : (↑G⁻¹ : R) = star (G : R)) :
    let M := U * P
    let M_G := (G : R) * M * (↑G⁻¹ : R)
    let U_G := (G : R) * U * (↑G⁻¹ : R)
    let P_G := (G : R) * P * (↑G⁻¹ : R)
    M_G = U_G * P_G ∧
    star U_G * U_G = 1 ∧
    star P_G = P_G ∧
    star M_G * M_G = (G : R) * (star M * M) * (↑G⁻¹ : R) ∧
    star M_G * M_G = P_G * P_G := by
  intro M M_G U_G P_G
  have hG1 : (↑G⁻¹ : R) * (G : R) = 1 := Units.inv_mul G
  have hG2 : (G : R) * (↑G⁻¹ : R) = 1 := Units.mul_inv G
  have h_star_inv : star (↑G⁻¹ : R) = (G : R) := by rw [hG_unit, star_star]
  have h_prod : M_G = U_G * P_G := by
    dsimp [M_G, U_G, P_G, M]
    calc (G : R) * (U * P) * (↑G⁻¹ : R)
      _ = (G : R) * U * ((↑G⁻¹ : R) * (G : R)) * P * (↑G⁻¹ : R) := by rw [hG1]; noncomm_ring
      _ = ((G : R) * U * (↑G⁻¹ : R)) * ((G : R) * P * (↑G⁻¹ : R)) := by noncomm_ring
  have h_UG : star U_G * U_G = 1 := by
    dsimp [U_G]
    simp only [star_mul, h_star_inv, ← hG_unit]
    calc (G : R) * (star U * (↑G⁻¹ : R)) * ((G : R) * U * (↑G⁻¹ : R))
      _ = (G : R) * star U * ((↑G⁻¹ : R) * (G : R)) * U * (↑G⁻¹ : R) := by noncomm_ring
      _ = (G : R) * (star U * U) * (↑G⁻¹ : R) := by rw [hG1]; noncomm_ring
      _ = 1 := by rw [hU, mul_one, hG2]
  have h_PG : star P_G = P_G := by
    dsimp [P_G]
    simp only [star_mul, h_star_inv, ← hG_unit, hP, mul_assoc]
  have h_MG1 : star M_G * M_G = (G : R) * (star M * M) * (↑G⁻¹ : R) := by
    dsimp [M_G]
    simp only [star_mul, h_star_inv, ← hG_unit]
    calc (G : R) * (star M * (↑G⁻¹ : R)) * ((G : R) * M * (↑G⁻¹ : R))
      _ = (G : R) * star M * ((↑G⁻¹ : R) * (G : R)) * M * (↑G⁻¹ : R) := by noncomm_ring
      _ = (G : R) * (star M * M) * (↑G⁻¹ : R) := by rw [hG1]; noncomm_ring
  refine ⟨h_prod, h_UG, h_PG, h_MG1, ?_⟩
  rw [h_prod]
  calc star (U_G * P_G) * (U_G * P_G)
    _ = P_G * (star U_G * U_G) * P_G := by simp only [star_mul, h_PG]; noncomm_ring
    _ = P_G * P_G := by rw [h_UG]; noncomm_ring

-- theorem-class: bridge
/-- Matrix specialization of `polar_decomposition_unitary_equivariance` on $M_2(B)$ for any
noncommutative $\star$-ring `[Ring B] [StarRing B]`. -/
@[rep_depth operator]
theorem polar_matrix_unitary_equivariance {B : Type*} [Ring B] [StarRing B]
    {U P : Matrix (Fin 2) (Fin 2) B} (hU : Uᴴ * U = 1) (hP : Pᴴ = P)
    (G : (Matrix (Fin 2) (Fin 2) B)ˣ)
    (hG_unit : (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B) = (G : Matrix (Fin 2) (Fin 2) B)ᴴ) :
    let M := U * P
    let M_G := (G : Matrix (Fin 2) (Fin 2) B) * M * (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B)
    let U_G := (G : Matrix (Fin 2) (Fin 2) B) * U * (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B)
    let P_G := (G : Matrix (Fin 2) (Fin 2) B) * P * (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B)
    M_G = U_G * P_G ∧
    U_Gᴴ * U_G = 1 ∧
    P_Gᴴ = P_G ∧
    M_Gᴴ * M_G = (G : Matrix (Fin 2) (Fin 2) B) * (Mᴴ * M) * (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B) ∧
    M_Gᴴ * M_G = P_G * P_G :=
  polar_decomposition_unitary_equivariance hU hP G hG_unit

-- theorem-class: bridge
/-- Bridge to `InfoGeometry.Optimization.PolarDecomposition`: given a right-polar decomposition
$A = P U$ in `Matrix n n ℝ`, its transpose $A^\top = U^\top P$ satisfies the left-polar hypotheses
of `polar_decomposition_unitary_equivariance` and is therefore equivariant under any orthogonal
unit $G \in \mathrm{GL}_n(\mathbb{R})$ with $G^{-1} = G^\top$. -/
@[rep_depth operator]
theorem polar_right_transpose_unitary_equivariance
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (D : InfoGeometry.Optimization.PolarDecomposition A)
    (G : (Matrix n n ℝ)ˣ)
    (hG_orth : (↑G⁻¹ : Matrix n n ℝ) = (G : Matrix n n ℝ)ᵀ) :
    let U := D.Uᵀ
    let P := D.P
    let A_G := (G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ)
    let U_G := (G : Matrix n n ℝ) * U * (↑G⁻¹ : Matrix n n ℝ)
    let P_G := (G : Matrix n n ℝ) * P * (↑G⁻¹ : Matrix n n ℝ)
    A_G = U_G * P_G ∧
    U_Gᴴ * U_G = 1 ∧
    P_Gᴴ = P_G ∧
    A_Gᴴ * A_G = (G : Matrix n n ℝ) * (A * Aᵀ) * (↑G⁻¹ : Matrix n n ℝ) ∧
    A_Gᴴ * A_G = P_G * P_G := by
  have hA_tr : Aᵀ = D.Uᵀ * D.P := by
    calc Aᵀ = (D.P * D.U)ᵀ := congrArg Matrix.transpose D.decomp
      _ = D.Uᵀ * D.Pᵀ := Matrix.transpose_mul D.P D.U
      _ = D.Uᵀ * D.P := by rw [D.self_adjoint]
  have hU_star : (D.Uᵀ)ᴴ * D.Uᵀ = 1 := by
    have htr : (D.Uᵀ)ᴴ = D.U := by ext i j; simp
    rw [htr]
    exact D.unitary
  have hP_star : D.Pᴴ = D.P := by
    have htr : D.Pᴴ = D.Pᵀ := by ext i j; simp
    rw [htr, D.self_adjoint]
  have hG_star : (↑G⁻¹ : Matrix n n ℝ) = star (G : Matrix n n ℝ) := by
    rw [hG_orth]
    ext i j; simp
  rcases polar_decomposition_unitary_equivariance hU_star hP_star G hG_star with
    ⟨h1, h2, h3, h4, h5⟩
  have hAAt : star (D.Uᵀ * D.P) * (D.Uᵀ * D.P) = A * Aᵀ := by
    rw [← hA_tr]
    have htr : star Aᵀ = A := by ext i j; simp
    rw [htr]
  refine ⟨?_, h2, h3, ?_, ?_⟩
  · show (G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ) =
      ((G : Matrix n n ℝ) * D.Uᵀ * (↑G⁻¹ : Matrix n n ℝ)) *
      ((G : Matrix n n ℝ) * D.P * (↑G⁻¹ : Matrix n n ℝ))
    rw [hA_tr]
    exact h1
  · show ((G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ))ᴴ *
        ((G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ)) =
      (G : Matrix n n ℝ) * (A * Aᵀ) * (↑G⁻¹ : Matrix n n ℝ)
    rw [← hAAt, hA_tr]
    exact h4
  · show ((G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ))ᴴ *
        ((G : Matrix n n ℝ) * Aᵀ * (↑G⁻¹ : Matrix n n ℝ)) =
      ((G : Matrix n n ℝ) * D.P * (↑G⁻¹ : Matrix n n ℝ)) *
      ((G : Matrix n n ℝ) * D.P * (↑G⁻¹ : Matrix n n ℝ))
    rw [hA_tr]
    exact h5

-- theorem-class: bridge
/-- A change of frame transports a polar factorization to the pushed-forward
metric.  Here `H` is the inverse frame and the metric matrix in the new frame
is `Hᵀ * H` (the coordinate form of `G⁻ᵀ G⁻¹`).  Thus arbitrary similarity
preserves the factorization when orthogonality and self-adjointness are read
relative to that metric; Euclidean equivariance is the special case where
`Hᵀ * H = 1`. -/
@[rep_depth operator]
theorem polar_factorization_pushed_metric_naturality
    {n : Type*} [Fintype n] [DecidableEq n]
    (G H U P : Matrix n n ℝ)
    (hGH : G * H = 1) (hHG : H * G = 1)
    (hU : Uᵀ * U = 1) (hP : Pᵀ = P) :
    G * (U * P) * H = (G * U * H) * (G * P * H) ∧
    ((Hᵀ * H) * (G * Gᵀ) = 1 ∧ (G * Gᵀ) * (Hᵀ * H) = 1) ∧
    (G * U * H)ᵀ * (Hᵀ * H) * (G * U * H) = Hᵀ * H ∧
    (G * P * H)ᵀ * (Hᵀ * H) = (Hᵀ * H) * (G * P * H) := by
  have hGtrHtr : Gᵀ * Hᵀ = 1 := by
    calc Gᵀ * Hᵀ = (H * G)ᵀ := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hHG, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc G * (U * P) * H = G * U * P * H := by noncomm_ring
      _ = G * U * (H * G) * P * H := by rw [hHG]; noncomm_ring
      _ = (G * U * H) * (G * P * H) := by noncomm_ring
  · constructor
    · calc Hᵀ * H * (G * Gᵀ) = Hᵀ * (H * G) * Gᵀ := by noncomm_ring
        _ = Hᵀ * Gᵀ := by rw [hHG]; noncomm_ring
        _ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
    · calc G * Gᵀ * (Hᵀ * H) = G * (Gᵀ * Hᵀ) * H := by noncomm_ring
        _ = G * H := by rw [hGtrHtr]; noncomm_ring
        _ = 1 := hGH
  · calc (G * U * H)ᵀ * (Hᵀ * H) * (G * U * H)
        = Hᵀ * Uᵀ * ((Gᵀ * Hᵀ) * (H * G)) * U * H := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul]
            noncomm_ring
      _ = Hᵀ * Uᵀ * U * H := by rw [hGtrHtr, hHG]; noncomm_ring
      _ = Hᵀ * (Uᵀ * U) * H := by noncomm_ring
      _ = Hᵀ * H := by rw [hU]; simp
  · calc (G * P * H)ᵀ * (Hᵀ * H)
        = Hᵀ * Pᵀ * (Gᵀ * Hᵀ) * H := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul]
            noncomm_ring
      _ = Hᵀ * P * H := by rw [hGtrHtr, hP]; noncomm_ring
      _ = Hᵀ * (H * G) * P * H := by rw [hHG]; noncomm_ring
      _ = (Hᵀ * H) * (G * P * H) := by noncomm_ring

end ArchetypeKP3_PolarDecompositionEquivariance

/-!
## Archetype $\mathcal{K}\mathcal{P}_4$: Symmetry Equivariance of the Iwasawa $K A N$ Decomposition under $G(\cdot)G^{-1}$
-/

section ArchetypeKP4_IwasawaKANEquivariance

variable {B : Type*} [Ring B]

-- theorem-class: symmetry
/-- **Iwasawa $K A N$ Symmetry Equivariance Theorem ($\mathcal{K}\mathcal{P}_4$)**:
Under conjugation $M \mapsto G M G^{-1}$ in $M_2(B)$:
1. *Diagonal Borelian Symmetry $G = A(g_+, g_-)$ ($g_+, g_- \in B^\times$)*:
   $A(g_+, g_-)(A(a_+, a_-) N(n))A(g_+^{-1}, g_-^{-1}) = A(g_+ a_+ g_+^{-1}, g_- a_- g_-^{-1}) N(g_+ n g_-^{-1})$.
2. *Non-Abelian Fiber Gauge Symmetry $G = \iota(g)$ ($g \in B^\times$)*:
   $\iota(g)(K(c, s) A(a_+, a_-) N(n))\iota(g^{-1}) = K(g c g^{-1}, g s g^{-1}) A(g a_+ g^{-1}, g a_- g^{-1}) N(g n g^{-1})$.
3. *Chirality Parity Symmetry $G = \Gamma_1$ ($G^{-1} = \Gamma_1$)*:
   $\Gamma_1 (K(c, s) A(a_+, a_-) N(n)) \Gamma_1 = K(c, -s) A(a_+, a_-) N(-n)$.
4. *Weyl Reflection Symmetry $G = \Sigma$ ($G^{-1} = \Sigma$, Opposite Iwasawa / Bruhat Duality)*:
   $\Sigma (K(c, s) A(a_+, a_-) N(n)) \Sigma = K(c, -s) A(a_-, a_+) N_-(n)$. -/
@[rep_depth operator, capstone]
theorem iwasawa_kan_symmetry_equivariance
    (g_plus g_minus g : Bˣ) (c s a_plus a_minus n : B) :
    let K_cs := iwasawaK c s
    let A_pm := iwasawaA a_plus a_minus
    let N_n := iwasawaN n
    iwasawaA (g_plus : B) (g_minus : B) * (A_pm * N_n) *
      iwasawaA (↑g_plus⁻¹ : B) (↑g_minus⁻¹ : B) =
      iwasawaA ((g_plus : B) * a_plus * (↑g_plus⁻¹ : B))
               ((g_minus : B) * a_minus * (↑g_minus⁻¹ : B)) *
      iwasawaN ((g_plus : B) * n * (↑g_minus⁻¹ : B)) ∧
    fiberEmbed (g : B) * (K_cs * A_pm * N_n) * fiberEmbed (↑g⁻¹ : B) =
      iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) *
      iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) *
      iwasawaN ((g : B) * n * (↑g⁻¹ : B)) ∧
    gamma1Op * (K_cs * A_pm * N_n) * gamma1Op =
      iwasawaK c (-s) * A_pm * iwasawaN (-n) ∧
    sigmaOp * (K_cs * A_pm * N_n) * sigmaOp =
      iwasawaK c (-s) * iwasawaA a_minus a_plus * iwasawaNMinus n := by
  intro K_cs A_pm N_n
  have hgp : (↑g_plus⁻¹ : B) * (g_plus : B) = 1 := Units.inv_mul g_plus
  have hg : (↑g⁻¹ : B) * (g : B) = 1 := Units.inv_mul g
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ext_fin2
    · simp [A_pm, N_n, iwasawaA, iwasawaN]
    · simp [A_pm, N_n, iwasawaA, iwasawaN]
      calc (g_plus : B) * (a_plus * n) * (↑g_minus⁻¹ : B)
        _ = (g_plus : B) * a_plus * ((↑g_plus⁻¹ : B) * (g_plus : B)) * n * (↑g_minus⁻¹ : B) := by
            rw [hgp]; noncomm_ring
        _ = ((g_plus : B) * a_plus * (↑g_plus⁻¹ : B)) *
            ((g_plus : B) * n * (↑g_minus⁻¹ : B)) := by noncomm_ring
    · simp [A_pm, N_n, iwasawaA, iwasawaN]
    · simp [A_pm, N_n, iwasawaA, iwasawaN]
  · apply ext_fin2
    · simp [K_cs, A_pm, N_n, fiberEmbed, iwasawaK, iwasawaA, iwasawaN]
      calc (g : B) * (c * a_plus) * (↑g⁻¹ : B)
        _ = (g : B) * c * ((↑g⁻¹ : B) * (g : B)) * a_plus * (↑g⁻¹ : B) := by
            rw [hg]; noncomm_ring
        _ = ((g : B) * c * (↑g⁻¹ : B)) * ((g : B) * a_plus * (↑g⁻¹ : B)) := by noncomm_ring
    · simp [K_cs, A_pm, N_n, fiberEmbed, iwasawaK, iwasawaA, iwasawaN]
      calc (g : B) * (c * a_plus * n + -(s * a_minus)) * (↑g⁻¹ : B)
        _ = (g : B) * c * ((↑g⁻¹ : B) * (g : B)) * a_plus *
            ((↑g⁻¹ : B) * (g : B)) * n * (↑g⁻¹ : B) -
            (g : B) * s * ((↑g⁻¹ : B) * (g : B)) * a_minus * (↑g⁻¹ : B) := by
            rw [hg]; noncomm_ring
        _ = ((g : B) * c * (↑g⁻¹ : B)) * ((g : B) * a_plus * (↑g⁻¹ : B)) *
            ((g : B) * n * (↑g⁻¹ : B)) +
            -(((g : B) * s * (↑g⁻¹ : B)) * ((g : B) * a_minus * (↑g⁻¹ : B))) := by
            noncomm_ring
    · simp [K_cs, A_pm, N_n, fiberEmbed, iwasawaK, iwasawaA, iwasawaN]
      calc (g : B) * (s * a_plus) * (↑g⁻¹ : B)
        _ = (g : B) * s * ((↑g⁻¹ : B) * (g : B)) * a_plus * (↑g⁻¹ : B) := by
            rw [hg]; noncomm_ring
        _ = ((g : B) * s * (↑g⁻¹ : B)) * ((g : B) * a_plus * (↑g⁻¹ : B)) := by noncomm_ring
    · simp [K_cs, A_pm, N_n, fiberEmbed, iwasawaK, iwasawaA, iwasawaN]
      calc (g : B) * (s * a_plus * n + c * a_minus) * (↑g⁻¹ : B)
        _ = (g : B) * s * ((↑g⁻¹ : B) * (g : B)) * a_plus *
            ((↑g⁻¹ : B) * (g : B)) * n * (↑g⁻¹ : B) +
            (g : B) * c * ((↑g⁻¹ : B) * (g : B)) * a_minus * (↑g⁻¹ : B) := by
            rw [hg]; noncomm_ring
        _ = ((g : B) * s * (↑g⁻¹ : B)) * ((g : B) * a_plus * (↑g⁻¹ : B)) *
            ((g : B) * n * (↑g⁻¹ : B)) +
            ((g : B) * c * (↑g⁻¹ : B)) * ((g : B) * a_minus * (↑g⁻¹ : B)) := by
            noncomm_ring
  · apply ext_fin2
    · simp [K_cs, A_pm, N_n, gamma1Op, iwasawaK, iwasawaA, iwasawaN]
    · simp [K_cs, A_pm, N_n, gamma1Op, iwasawaK, iwasawaA, iwasawaN]; noncomm_ring
    · simp [K_cs, A_pm, N_n, gamma1Op, iwasawaK, iwasawaA, iwasawaN]
    · simp [K_cs, A_pm, N_n, gamma1Op, iwasawaK, iwasawaA, iwasawaN]
  · apply ext_fin2
    · simp [K_cs, A_pm, N_n, sigmaOp, iwasawaK, iwasawaA, iwasawaN, iwasawaNMinus]; noncomm_ring
    · simp [K_cs, A_pm, N_n, sigmaOp, iwasawaK, iwasawaA, iwasawaN, iwasawaNMinus]
    · simp [K_cs, A_pm, N_n, sigmaOp, iwasawaK, iwasawaA, iwasawaN, iwasawaNMinus]; noncomm_ring
    · simp [K_cs, A_pm, N_n, sigmaOp, iwasawaK, iwasawaA, iwasawaN, iwasawaNMinus]

-- theorem-class: conservation
/-- **Diamond Synthesis ($\mathcal{K}\mathcal{P}_2 \wedge \mathcal{K}\mathcal{P}_3 \wedge \mathcal{K}\mathcal{P}_4$)**:
Under a unitary non-abelian fiber gauge transformation $G = \iota(g)$ ($g \in B^\times$, $g^{-1} = g^\star$)
on $M = K(c,s) A(a_+, a_-) N(n)$ with $K(c,s)^\dagger K(c,s) = 1$:
1. The conjugated operator $M_g = \iota(g) M \iota(g^{-1})$ keeps its Iwasawa $K A N$ form with
   adjoint-rotated parameters $(g c g^{-1}, g s g^{-1}, g a_+ g^{-1}, g a_- g^{-1}, g n g^{-1})$;
2. The Polar Gram square transforms covariantly as $M_g^\dagger M_g = \iota(g)(M^\dagger M)\iota(g^{-1})$
   with unitary elimination preserved;
3. The Cholesky pivot $(M_g^\dagger M_g)_{00}$ and noncommutative Schur complement
   $(M_g^\dagger M_g)_{11} - n_g^\star (M_g^\dagger M_g)_{00} n_g$ transform covariantly in the
   adjoint representation $x \mapsto g x g^{-1}$. -/
@[rep_depth operator, capstone]
theorem kan_polar_gram_fiber_unitary_equivariance [StarRing B]
    (g : Bˣ) (hg : (↑g⁻¹ : B) = star (g : B)) (c s a_plus a_minus n : B)
    (hK : (iwasawaK c s)ᴴ * iwasawaK c s = 1) :
    let K_g := iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B))
    let A_g := iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B))
    let N_g := iwasawaN ((g : B) * n * (↑g⁻¹ : B))
    let n_g := (g : B) * n * (↑g⁻¹ : B)
    let M := iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n
    let M_g := fiberEmbed (g : B) * M * fiberEmbed (↑g⁻¹ : B)
    M_g = K_g * A_g * N_g ∧
    M_gᴴ * M_g = fiberEmbed (g : B) * (Mᴴ * M) * fiberEmbed (↑g⁻¹ : B) ∧
    (M_gᴴ * M_g) 0 0 = (g : B) * (star a_plus * a_plus) * (↑g⁻¹ : B) ∧
    (M_gᴴ * M_g) 1 1 - star n_g * (M_gᴴ * M_g) 0 0 * n_g =
      (g : B) * (star a_minus * a_minus) * (↑g⁻¹ : B) := by
  intro K_g A_g N_g n_g M M_g
  have hM_g : M_g = K_g * A_g * N_g :=
    (iwasawa_kan_symmetry_equivariance g g g c s a_plus a_minus n).2.1
  have hK_unit : K_gᴴ * K_g = 1 := by
    have hK_conj : K_g = fiberEmbed (g : B) * iwasawaK c s * fiberEmbed (↑g⁻¹ : B) := by
      have h_eq := (iwasawa_kan_symmetry_equivariance g g g c s 1 1 0).2.1
      have hA1 : iwasawaA (1 : B) 1 = (1 : Matrix (Fin 2) (Fin 2) B) := by
        apply ext_fin2 <;> rfl
      have hN0 : iwasawaN (0 : B) = (1 : Matrix (Fin 2) (Fin 2) B) := by
        apply ext_fin2 <;> rfl
      have hAg : iwasawaA ((g : B) * 1 * (↑g⁻¹ : B)) ((g : B) * 1 * (↑g⁻¹ : B)) = 1 := by
        simp only [mul_one, Units.mul_inv]
        apply ext_fin2 <;> rfl
      have hNg : iwasawaN ((g : B) * 0 * (↑g⁻¹ : B)) = 1 := by
        simp only [mul_zero, zero_mul]
        exact hN0
      simpa only [hA1, hN0, hAg, hNg, Matrix.mul_one] using h_eq.symm
    let G : (Matrix (Fin 2) (Fin 2) B)ˣ :=
      { val := fiberEmbed (g : B)
        inv := fiberEmbed (↑g⁻¹ : B)
        val_inv := by
          apply ext_fin2
          · simp [fiberEmbed]
          · simp [fiberEmbed]
          · simp [fiberEmbed]
          · simp [fiberEmbed]
        inv_val := by
          apply ext_fin2
          · simp [fiberEmbed]
          · simp [fiberEmbed]
          · simp [fiberEmbed]
          · simp [fiberEmbed] }
    have hG_unit : (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B) = (G : Matrix (Fin 2) (Fin 2) B)ᴴ := by
      apply ext_fin2
      · simp [G, fiberEmbed, hg]
      · simp [G, fiberEmbed]
      · simp [G, fiberEmbed]
      · simp [G, fiberEmbed, hg]
    have h_pol := polar_decomposition_unitary_equivariance (P := (1 : Matrix (Fin 2) (Fin 2) B))
      hK conjTranspose_one G hG_unit
    dsimp only at h_pol
    have h_conjK : (G : Matrix (Fin 2) (Fin 2) B) * iwasawaK c s *
        (↑G⁻¹ : Matrix (Fin 2) (Fin 2) B) = K_g := hK_conj.symm
    rw [← h_conjK]
    exact h_pol.2.1
  have h_gram_orig := (iwasawa_kan_subgroups_and_polar_gram_reduction
    (1 : B) 1 1 1 a_plus a_minus 0 0 n hK).2.2.2.2.1
  have h_gram_conj := iwasawa_kan_subgroups_and_polar_gram_reduction
    (1 : B) 1 1 1 ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) 0 0 n_g hK_unit
  have hM_gram : M_gᴴ * M_g = fiberEmbed (g : B) * (Mᴴ * M) * fiberEmbed (↑g⁻¹ : B) := by
    have h_inv_g : (↑g⁻¹ : B) * (g : B) = 1 := Units.inv_mul g
    have h_Ginv : (fiberEmbed (↑g⁻¹ : B))ᴴ = fiberEmbed (g : B) := by
      apply ext_fin2
      · simp [fiberEmbed, hg]
      · simp [fiberEmbed]
      · simp [fiberEmbed]
      · simp [fiberEmbed, hg]
    have h_G : (fiberEmbed (g : B))ᴴ = fiberEmbed (↑g⁻¹ : B) := by
      apply ext_fin2
      · simp [fiberEmbed, hg]
      · simp [fiberEmbed]
      · simp [fiberEmbed]
      · simp [fiberEmbed, hg]
    have h_GGinv : fiberEmbed (↑g⁻¹ : B) * fiberEmbed (g : B) = (1 : Matrix (Fin 2) (Fin 2) B) := by
      apply ext_fin2
      · simp [fiberEmbed]
      · simp [fiberEmbed]
      · simp [fiberEmbed]
      · simp [fiberEmbed]
    dsimp [M_g]
    calc (fiberEmbed (g : B) * M * fiberEmbed (↑g⁻¹ : B))ᴴ *
         (fiberEmbed (g : B) * M * fiberEmbed (↑g⁻¹ : B))
      _ = (fiberEmbed (↑g⁻¹ : B))ᴴ * Mᴴ * (fiberEmbed (g : B))ᴴ *
          (fiberEmbed (g : B) * M * fiberEmbed (↑g⁻¹ : B)) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = fiberEmbed (g : B) * Mᴴ * (fiberEmbed (↑g⁻¹ : B) * fiberEmbed (g : B)) *
          M * fiberEmbed (↑g⁻¹ : B) := by
          rw [h_Ginv, h_G]; simp only [Matrix.mul_assoc]
      _ = fiberEmbed (g : B) * (Mᴴ * M) * fiberEmbed (↑g⁻¹ : B) := by
          rw [h_GGinv, Matrix.mul_one]; noncomm_ring
  have h_star_g : star (g : B) = (↑g⁻¹ : B) := hg.symm
  have h_star_ginv : star (↑g⁻¹ : B) = (g : B) := by rw [hg, star_star]
  have h_00 : (M_gᴴ * M_g) 0 0 = (g : B) * (star a_plus * a_plus) * (↑g⁻¹ : B) := by
    rw [hM_gram]
    dsimp only [M]
    rw [h_gram_orig]
    simp [fiberEmbed]
  have h_schur : (M_gᴴ * M_g) 1 1 - star n_g * (M_gᴴ * M_g) 0 0 * n_g =
      (g : B) * (star a_minus * a_minus) * (↑g⁻¹ : B) := by
    dsimp only at h_gram_conj
    have h_schur_raw := h_gram_conj.2.2.2.2.2
    rw [← hM_g] at h_schur_raw
    rw [h_schur_raw]
    simp only [star_mul, h_star_ginv, h_star_g]
    calc (g : B) * (star a_minus * (↑g⁻¹ : B)) * ((g : B) * a_minus * (↑g⁻¹ : B))
      _ = (g : B) * star a_minus * ((↑g⁻¹ : B) * (g : B)) * a_minus * (↑g⁻¹ : B) := by noncomm_ring
      _ = (g : B) * (star a_minus * a_minus) * (↑g⁻¹ : B) := by
          rw [Units.inv_mul g]; noncomm_ring
  exact ⟨hM_g, hM_gram, h_00, h_schur⟩

end ArchetypeKP4_IwasawaKANEquivariance

/-!
## Typed Archetype Registrations & Audit Checks
-/

section TypedArchetypeRegistrations

open InfoGeometry.MetaCompiler

/-- Parametric Typed Archetype $\mathcal{K}\mathcal{P}_1$: Weyl gauge scale, Cartan split, and
noncommutative trace-to-determinant formula over any ring `B`. -/
def weylCartanTraceToDetArchetype (B : Type) [Ring B] : TypedArchetype Unit .proved where
  name := `weylCartanTraceToDetArchetype
  phase := 1
  claim := fun _ =>
    ∀ M : Matrix (Fin 2) (Fin 2) B,
      weylScalePart M + tracelessSymPart M + tracelessAntisymPart M = 2 • M ∧
      Matrix.trace (tracelessSymPart M) = 0 ∧
      Matrix.trace (tracelessAntisymPart M) = 0 ∧
      (tracelessSymPart M)ᵀ = tracelessSymPart M ∧
      (tracelessAntisymPart M)ᵀ = -tracelessAntisymPart M ∧
      (Matrix.trace M) ^ 2 - Matrix.trace (M * M) = symDet M ∧
      ⁅(gamma1Op : Matrix (Fin 2) (Fin 2) B), (sigmaOp : Matrix (Fin 2) (Fin 2) B)⁆ =
        -(2 • (omegaOp : Matrix (Fin 2) (Fin 2) B)) ∧
      ⁅(omegaOp : Matrix (Fin 2) (Fin 2) B), (gamma1Op : Matrix (Fin 2) (Fin 2) B)⁆ =
        2 • (sigmaOp : Matrix (Fin 2) (Fin 2) B) ∧
      ⁅(omegaOp : Matrix (Fin 2) (Fin 2) B), (sigmaOp : Matrix (Fin 2) (Fin 2) B)⁆ =
        -(2 • (gamma1Op : Matrix (Fin 2) (Fin 2) B))
  evidence := fun _ M => weyl_cartan_split_and_noncommutative_trace_to_det M

/-- Concrete noncommutative-fiber `Mat2C := Matrix (Fin 2) (Fin 2) ℂ` instance of $\mathcal{K}\mathcal{P}_1$. -/
def weylCartanTraceToDetMat2CArchetype : TypedArchetype Unit .proved :=
  weylCartanTraceToDetArchetype InfoGeometry.Algebra.FiniteSpin.Mat2C

#register_archetype weylCartanTraceToDetMat2CArchetype
#audit_archetype weylCartanTraceToDetMat2CArchetype

/-- Parametric Typed Archetype $\mathcal{K}\mathcal{P}_2$: Iwasawa $K A N$ subgroups, Polar Gram
reduction, and noncommutative Schur complement recovery over any $\star$-ring `B`. -/
def iwasawaKANPolarGramArchetype (B : Type) [Ring B] [StarRing B] : TypedArchetype Unit .proved where
  name := `iwasawaKANPolarGramArchetype
  phase := 2
  claim := fun _ =>
    ∀ (a₁ b₁ a₂ b₂ a_plus a_minus n₁ n₂ n : B)
      (K : Matrix (Fin 2) (Fin 2) B), Kᴴ * K = 1 →
      let M := K * iwasawaA a_plus a_minus * iwasawaN n
      iwasawaN n₁ * iwasawaN n₂ = iwasawaN (n₁ + n₂) ∧
      iwasawaN n * iwasawaN (-n) = 1 ∧
      iwasawaA a₁ b₁ * iwasawaA a₂ b₂ = iwasawaA (a₁ * a₂) (b₁ * b₂) ∧
      iwasawaA a_plus a_minus * iwasawaN n = mat2 a_plus (a_plus * n) 0 a_minus ∧
      Mᴴ * M =
        mat2 (star a_plus * a_plus) (star a_plus * a_plus * n)
             (star n * (star a_plus * a_plus))
             (star n * (star a_plus * a_plus) * n + star a_minus * a_minus) ∧
      (Mᴴ * M) 1 1 - star n * (Mᴴ * M) 0 0 * n = star a_minus * a_minus
  evidence := fun _ a₁ b₁ a₂ b₂ a_plus a_minus n₁ n₂ n _ hK =>
    iwasawa_kan_subgroups_and_polar_gram_reduction a₁ b₁ a₂ b₂ a_plus a_minus n₁ n₂ n hK

/-- Concrete noncommutative-fiber `Mat2C` instance of $\mathcal{K}\mathcal{P}_2$. -/
def iwasawaKANPolarGramMat2CArchetype : TypedArchetype Unit .proved :=
  iwasawaKANPolarGramArchetype InfoGeometry.Algebra.FiniteSpin.Mat2C

#register_archetype iwasawaKANPolarGramMat2CArchetype
#audit_archetype iwasawaKANPolarGramMat2CArchetype

/-- Parametric Typed Archetype $\mathcal{K}\mathcal{P}_3$: Unitary symmetry equivariance
$G M G^{-1} = U_G P_G$ of the Polar decomposition over any $\star$-ring `R`. -/
def polarUnitaryEquivarianceArchetype (R : Type) [Ring R] [StarRing R] : TypedArchetype Unit .proved where
  name := `polarUnitaryEquivarianceArchetype
  phase := 2
  claim := fun _ =>
    ∀ (U P : R), star U * U = 1 → star P = P →
      ∀ (G : Rˣ), (↑G⁻¹ : R) = star (G : R) →
        let M := U * P
        let M_G := (G : R) * M * (↑G⁻¹ : R)
        let U_G := (G : R) * U * (↑G⁻¹ : R)
        let P_G := (G : R) * P * (↑G⁻¹ : R)
        M_G = U_G * P_G ∧
        star U_G * U_G = 1 ∧
        star P_G = P_G ∧
        star M_G * M_G = (G : R) * (star M * M) * (↑G⁻¹ : R) ∧
        star M_G * M_G = P_G * P_G
  evidence := fun _ _ _ hU hP G hG => polar_decomposition_unitary_equivariance hU hP G hG

/-- Concrete noncommutative `Mat2C` instance of $\mathcal{K}\mathcal{P}_3$. -/
def polarUnitaryEquivarianceMat2CArchetype : TypedArchetype Unit .proved :=
  polarUnitaryEquivarianceArchetype InfoGeometry.Algebra.FiniteSpin.Mat2C

#register_archetype polarUnitaryEquivarianceMat2CArchetype
#audit_archetype polarUnitaryEquivarianceMat2CArchetype

/-- Parametric Typed Archetype $\mathcal{K}\mathcal{P}_4$: Symmetry equivariance of Iwasawa $K A N$
and diamond unification with the Polar Gram square & Schur complement over any $\star$-ring `B`. -/
def iwasawaKANSymmetryEquivarianceArchetype (B : Type) [Ring B] [StarRing B] :
    TypedArchetype Unit .proved where
  name := `iwasawaKANSymmetryEquivarianceArchetype
  phase := 3
  claim := fun _ =>
    (∀ (g_plus g_minus g : Bˣ) (c s a_plus a_minus n : B),
      let K_cs := iwasawaK c s
      let A_pm := iwasawaA a_plus a_minus
      let N_n := iwasawaN n
      iwasawaA (g_plus : B) (g_minus : B) * (A_pm * N_n) *
        iwasawaA (↑g_plus⁻¹ : B) (↑g_minus⁻¹ : B) =
        iwasawaA ((g_plus : B) * a_plus * (↑g_plus⁻¹ : B))
                 ((g_minus : B) * a_minus * (↑g_minus⁻¹ : B)) *
        iwasawaN ((g_plus : B) * n * (↑g_minus⁻¹ : B)) ∧
      fiberEmbed (g : B) * (K_cs * A_pm * N_n) * fiberEmbed (↑g⁻¹ : B) =
        iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) *
        iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) *
        iwasawaN ((g : B) * n * (↑g⁻¹ : B)) ∧
      gamma1Op * (K_cs * A_pm * N_n) * gamma1Op =
        iwasawaK c (-s) * A_pm * iwasawaN (-n) ∧
      sigmaOp * (K_cs * A_pm * N_n) * sigmaOp =
        iwasawaK c (-s) * iwasawaA a_minus a_plus * iwasawaNMinus n) ∧
    (∀ (g : Bˣ), (↑g⁻¹ : B) = star (g : B) → ∀ (c s a_plus a_minus n : B),
      (iwasawaK c s)ᴴ * iwasawaK c s = 1 →
        let K_g := iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B))
        let A_g := iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B))
        let N_g := iwasawaN ((g : B) * n * (↑g⁻¹ : B))
        let n_g := (g : B) * n * (↑g⁻¹ : B)
        let M := iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n
        let M_g := fiberEmbed (g : B) * M * fiberEmbed (↑g⁻¹ : B)
        M_g = K_g * A_g * N_g ∧
        M_gᴴ * M_g = fiberEmbed (g : B) * (Mᴴ * M) * fiberEmbed (↑g⁻¹ : B) ∧
        (M_gᴴ * M_g) 0 0 = (g : B) * (star a_plus * a_plus) * (↑g⁻¹ : B) ∧
        (M_gᴴ * M_g) 1 1 - star n_g * (M_gᴴ * M_g) 0 0 * n_g =
          (g : B) * (star a_minus * a_minus) * (↑g⁻¹ : B))
  evidence := fun _ =>
    ⟨fun g_plus g_minus g c s a_plus a_minus n =>
      iwasawa_kan_symmetry_equivariance g_plus g_minus g c s a_plus a_minus n,
     fun g hg c s a_plus a_minus n hK =>
      kan_polar_gram_fiber_unitary_equivariance g hg c s a_plus a_minus n hK⟩

/-- Concrete noncommutative-fiber `Mat2C` instance of $\mathcal{K}\mathcal{P}_4$. -/
def iwasawaKANSymmetryEquivarianceMat2CArchetype : TypedArchetype Unit .proved :=
  iwasawaKANSymmetryEquivarianceArchetype InfoGeometry.Algebra.FiniteSpin.Mat2C

#register_archetype iwasawaKANSymmetryEquivarianceMat2CArchetype
#audit_archetype iwasawaKANSymmetryEquivarianceMat2CArchetype

end TypedArchetypeRegistrations

end InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
