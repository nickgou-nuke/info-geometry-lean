import InfoGeometry.Quiver.BetheAnsatzXXZ
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quiver.HbarOper
import InfoGeometry.Physics.LogCFT
import Mathlib.LinearAlgebra.Matrix.Block
/-
Copyright (c) 2024 InfoGeometry Contributors.
All rights reserved.
Released under Apache 2.0 license as described in
the file LICENSE.

Koroteev–Zeitlin, "3D Mirror Symmetry for Instanton
Moduli Spaces", Comm. Math. Phys. 403(2), 2023.

This file contains finite data models and algebraic fragments related to:
1. Nakajima quiver variety dimension data for type-A quivers
2. The parameter profiles used to name the family X_{k,l}
3. QQ-system (Baxter Q-operators)
4. Z-twisted Miura (G,ℏ)-opers
5. XXZ Bethe Ansatz equations
6. Hilb^k[ℂ²] dimension data
7. Quantum K-theory parameter data (without a ring carrier)
8. Trigonometric Ruijsenaars–Schneider Lax matrix
9. Instanton moduli dimension symmetry

These declarations do not construct the hyperkähler quotients, mirror maps,
quantum K-theory rings, or geometric limits named in the motivating literature.
-/

import Mathlib.Tactic

open Matrix Finset BigOperators

noncomputable section

namespace KoroteevZeitlin

/-! ## §1. Nakajima quiver variety for A_r quiver -/

/-- Dimension vector: gauge-group ranks at each
vertex of a type-A_r quiver. -/
abbrev DimVec (r : ℕ) := Fin r → ℕ

/-- Framing vector: flavor-symmetry ranks at each
vertex of a type-A_r quiver. -/
abbrev FrameVec (r : ℕ) := Fin r → ℕ

/-- Complex dimension formula used throughout this file for type-A Nakajima varieties. -/
def quiverDim (r : ℕ) (v : DimVec r) (w : FrameVec r) : ℕ :=
  2 * (∑ i : Fin r,
      (v i * w i + if h : (i : ℕ) + 1 < r then v i * v ⟨(i : ℕ) + 1, h⟩ else 0))
    - 2 * ∑ i : Fin r, v i * v i

/-- Finite dimension, framing, stability, and dimension data for a type-A
quiver. This structure does not construct a representation space, a group
action, or a hyperkähler quotient. -/
structure NakajimaQuiverVariety (r : ℕ) where
  /-- Gauge-group rank at each vertex. -/
  v : DimVec r
  /-- Flavor-symmetry rank at each vertex. -/
  w : FrameVec r
  /-- Stability parameter (real FI). -/
  ζ : Fin r → ℝ
  /-- Complex dimension
    2(∑_{i→i+1} v_i v_{i+1} + ∑_i v_i w_i - ∑_i v_i²).
    -/
  dimℂ : ℕ

/-- Construct A_r quiver variety from vectors. -/
def mkQuiver (r : ℕ) (v : DimVec r)
    (w : FrameVec r) (ζ : Fin r → ℝ) :
    NakajimaQuiverVariety r :=
  { v := v, w := w, ζ := ζ, dimℂ := quiverDim r v w }

/-! ## §2. Self-mirror family X_{k,l} -/

/-- The family X_{k,l}: type-A_{k-1} quiver variety
with uniform dimension l and framing concentrated
at vertex 0.

  v = (l, l, …, l) ∈ ℕ^k
  w = (l, 0, …, 0)
  (called "cotangent type" in Koroteev–Zeitlin)

This definition records only the dimension/framing/stability data; it does not
construct a variety or a mirror equivalence. -/
def X_kl (k l : ℕ) (hk : 0 < k) :
    NakajimaQuiverVariety k where
  v := fun _ => l
  w := fun i => if i = ⟨0, hk⟩ then l else 0
  ζ := fun _ => 0
  dimℂ := 0

/-- The self-parameter member has constant gauge profile and framing supported
at the distinguished initial vertex. This is a statement about the encoded
quiver data, not a self-mirror equivalence. -/
theorem X_kk_data_profile (k : ℕ) (hk : 0 < k) :
    (∀ i : Fin k, (X_kl k k hk).v i = k) ∧
    (∀ i : Fin k, (X_kl k k hk).w i = if i = ⟨0, hk⟩ then k else 0) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## §3. Mirror equivalence: open debt

The source definitions in this file do not supply a mirror functor, parameter
exchange maps, or an isomorphism of the represented varieties. Consequently no
`MirrorPair` witness is defined here. The verified statements in §2 concern
only the explicit finite profiles. -/

/-- Exact gauge and framing profiles encoded by the two parameter orders.
The theorem makes no claim that these data are related by a geometric mirror
map; that map is not defined in this finite data model. -/
theorem X_kl_data_profiles (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (∀ i : Fin k, (X_kl k l hk).v i = l) ∧
    (∀ i : Fin k, (X_kl k l hk).w i = if i = ⟨0, hk⟩ then l else 0) ∧
    (∀ j : Fin l, (X_kl l k hl).v j = k) ∧
    (∀ j : Fin l, (X_kl l k hl).w j = if j = ⟨0, hl⟩ then k else 0) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## §4. QQ-system (Baxter Q-operators) -/

/-- A QQ-system consists of two families of
polynomials (Q_i, Q̃_i) satisfying the
nonlinear q-difference functional relation:

  Q_i(qz) Q̃_i(z) - Q_i(z) Q̃_i(qz)
    = ∏_{j∼i} Q_j(z)

for each vertex i of the Dynkin diagram,
where j ∼ i means j is adjacent to i.
This encodes the Baxter TQ-relation for the
XXZ spin chain. -/
structure QQSystem (r : ℕ) where
  /-- The Q-polynomial at each vertex. -/
  Q : Fin r → Polynomial ℂ
  /-- The Q̃-polynomial at each vertex. -/
  Q_tilde : Fin r → Polynomial ℂ
  /-- The q-shift parameter (|q| ≠ 1). -/
  q : ℂ
  /-- q is not a root of unity. -/
  q_not_root : ∀ n : ℕ, 0 < n → q ^ n ≠ 1

namespace QQSystem

/-- Polynomial degrees encode the dimension vector of the quiver system. -/
def dim_vec {r : ℕ} (S : QQSystem r) : Fin r → ℕ := fun i =>
  (S.Q i).natDegree

/-- Every polynomial degree is zero or strictly positive. -/
theorem deg_Q {r : ℕ} (S : QQSystem r) (i : Fin r) :
    (S.Q i).natDegree = 0 ∨ 0 < (S.Q i).natDegree := by
  exact Nat.eq_zero_or_pos (S.Q i).natDegree

end QQSystem

/-- Substitution `z ↦ q * z` on a polynomial, represented by composition. -/
def qShiftPolynomial (q : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (Polynomial.C q * Polynomial.X)

/-- The QQ-system functional equation as an identity of polynomials:
  `Q_i(qz) Q̃_i(z) - Q_i(z) Q̃_i(qz) = ∏_{j adj i} Q_j(z)`. -/
def QQRelation (S : QQSystem r)
    (adj : Fin r → Fin r → Prop) : Prop :=
  ∀ i : Fin r,
    letI : DecidablePred (adj i) := Classical.decPred (adj i)
    qShiftPolynomial S.q (S.Q i) * S.Q_tilde i -
      S.Q i * qShiftPolynomial S.q (S.Q_tilde i) =
      ∏ j ∈ Finset.univ.filter (adj i), S.Q j

/-- Evaluating the polynomial QQ identity at `z` gives its pointwise
q-difference equation. This is the polynomial consequence proved here; it does
not assert a correspondence with Miura opers or Bethe states. -/
theorem qqRelation_eval_at (S : QQSystem r) (adj : Fin r → Fin r → Prop)
    (hS : QQRelation S adj) (i : Fin r) (z : ℂ) :
    letI : DecidablePred (adj i) := Classical.decPred (adj i)
    (S.Q i).eval (S.q * z) * (S.Q_tilde i).eval z -
        (S.Q i).eval z * (S.Q_tilde i).eval (S.q * z) =
      ∏ j ∈ Finset.univ.filter (adj i), (S.Q j).eval z := by
  classical
  have hPoly := hS i
  have hEval := congrArg (fun P : Polynomial ℂ => P.eval z) hPoly
  simpa [QQRelation, qShiftPolynomial, Polynomial.eval_comp,
    Polynomial.eval_prod] using hEval

/-! ## §5. Z-twisted Miura (G,ℏ)-opers -/

/-- A Z-twisted Miura (G,ℏ)-oper on ℂ× is a
connection on a G-bundle over the punctured
plane that is in Miura (Borel-reduced) position.

For G = GL_N, this is an ℏ-difference connection
  Φ(z) = A_1(z) · A_2(z) ··· A_r(z)
where each A_i is upper-triangular with prescribed
singularities determined by Z (the "twist"). -/
structure MiuraHbarOper (N : ℕ) where
  /-- ℏ-parameter (q-shift for difference
  connection). -/
  hbar : ℂ
  /-- Twist parameter Z ∈ T (maximal torus). -/
  Z : Fin N → ℂ
  /-- Ordered Miura factors, each in upper-triangular position. -/
  factor : Fin N → ℂ → Matrix (Fin N) (Fin N) ℂ
  factor_upper : ∀ i z, (factor i z).IsUpperTriangular

namespace MiuraHbarOper

/-- The defining representation rank is the index of the Miura oper. -/
def rank {N : ℕ} (_ : MiuraHbarOper N) : ℕ := N

/-- The connection is the ordered product of the Miura factors.

`List.finRange` fixes the factor order; no commutation of matrix factors is
assumed. -/
def connection {N : ℕ} (M : MiuraHbarOper N) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((List.finRange N).map fun i => M.factor i z).prod

theorem upperTriangular_one (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℂ).IsUpperTriangular := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl _) hij
  simp [hne]

private theorem upperTriangular_mul {N : ℕ}
    (A C : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) :
    (A * C).IsUpperTriangular := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k < i
  · simp [hA hki]
  · have hik : i ≤ k := le_of_not_gt hki
    have hjk : j < k := lt_of_lt_of_le hij hik
    simp [hC hjk]

private theorem list_prod_upperTriangular {N : ℕ}
    (xs : List (Matrix (Fin N) (Fin N) ℂ))
    (hxs : ∀ A ∈ xs, A.IsUpperTriangular) :
    xs.prod.IsUpperTriangular := by
  induction xs with
  | nil =>
      simpa using upperTriangular_one N
  | cons A xs ih =>
      simp only [List.prod_cons]
      apply upperTriangular_mul
      · exact hxs A (by simp)
      · apply ih
        intro C hC
        exact hxs C (by simp [hC])

/-- A Miura connection is upper triangular because it is an ordered product
of upper-triangular factors. The conclusion follows from matrix multiplication,
not from reflexivity of a stored connection field. -/
theorem is_miura {N : ℕ} (M : MiuraHbarOper N) (z : ℂ) :
    (M.connection z).IsUpperTriangular := by
  unfold connection
  apply list_prod_upperTriangular
  intro A hA
  rcases List.mem_map.mp hA with ⟨i, hi, hEq⟩
  subst A
  exact M.factor_upper i z

end MiuraHbarOper

/-- Space of Z-twisted Miura ℏ-opers for G = GL_N
with given singularity data. Denoted OpG,ℏ^Z
in Koroteev–Zeitlin. -/
structure MiuraOperSpace (N : ℕ) where
  /-- Collection of opers. -/
  opers : Set (MiuraHbarOper N)
  /-- The twist. -/
  twist : Fin N → ℂ
  /-- ℏ-parameter shared by all opers. -/
  hbar : ℂ

/-! The QQ-to-oper correspondence is not derived from the structures in this
file. The previous placeholder merely constructed unit Miura factors and did
not use the QQ relation, so that correspondence is not asserted here. The
kernel-checked result available from this owner is `qqRelation_eval_at`. -/

/-! ## §6. XXZ Bethe Ansatz equations -/

/-- XXZ Bethe Ansatz equations for type-A_r.
At each vertex i with k_i Bethe roots
{σ_{i,a}}_{a=1}^{k_i}, the BAE read:

  ∏_b ((σ_{i,a} - q σ_{i,b}) /
       (q σ_{i,a} - σ_{i,b}))
  · ∏_{j∼i} ∏_b ((q σ_{i,a} - σ_{j,b}) /
                  (σ_{i,a} - q σ_{j,b}))
  = z_i

for each a = 1,…,k_i and each vertex i.
Here z_i are the Kähler parameters and q = e^ℏ.
-/
structure XXZBetheData (r : ℕ) where
  /-- Number of Bethe roots at vertex i. -/
  numRoots : Fin r → ℕ
  /-- Bethe roots σ_{i,a}. -/
  roots : (i : Fin r) → Fin (numRoots i) → ℂ
  /-- q-parameter. -/
  q : ℂ
  /-- Kähler parameters z_i. -/
  z : Fin r → ℂ
  /-- Equivariant (mass) parameters a_j. -/
  a : Fin r → ℂ

/-- The numerator of the XXZ Bethe equation at a root. -/
def BAE_numerator (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop)
    (i : Fin r) (ai : Fin (B.numRoots i)) :
    ℂ := by
  classical
  let σ := B.roots i ai
  let self_part := ∏ b : Fin (B.numRoots i),
    if b = ai then 1 else (σ - B.q * B.roots i b) / (B.q * σ - B.roots i b)
  let nbr_part := ∏ j ∈ Finset.univ.filter (adj i),
    ∏ b : Fin (B.numRoots j), (B.q * σ - B.roots j b) / (σ - B.q * B.roots j b)
  exact self_part * nbr_part

/-- The XXZ Bethe equation ratio, defined as its numerator divided by the
Kähler parameter at the chosen vertex. -/
def BAE_ratio (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop)
    (i : Fin r) (ai : Fin (B.numRoots i)) : ℂ :=
  BAE_numerator B adj i ai / B.z i

/-- A Bethe state is a solution: all BAE ratios
equal 1. -/
def IsBetheState (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop) : Prop :=
  ∀ (i : Fin r) (a : Fin (B.numRoots i)),
    BAE_ratio B adj i a = 1

/-- When every Kähler parameter is nonzero, the ratio form of the Bethe
equations is equivalent to the corresponding cross-multiplied numerator
equations. -/
theorem isBetheState_iff_crossMultiplied (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop) (hz : ∀ i, B.z i ≠ 0) :
    IsBetheState B adj ↔
      ∀ (i : Fin r) (a : Fin (B.numRoots i)),
        BAE_numerator B adj i a = B.z i := by
  constructor
  · intro h i a
    have hratio := h i a
    rw [BAE_ratio, div_eq_iff_mul_eq (hz i)] at hratio
    simpa [mul_comm] using hratio.symm
  · intro h i a
    rw [BAE_ratio, div_eq_iff_mul_eq (hz i)]
    simpa [mul_comm] using (h i a).symm

/-! ## §7. Hilb^k[ℂ²] dimension data -/

/-- Finite Jordan-quiver data commonly used for the Hilbert-scheme model, with
gauge coordinate `k`, framing coordinate `1`, and stability coordinate `1`.
No Hilbert scheme or limiting construction is represented by this record. -/
def HilbK (k : ℕ) : NakajimaQuiverVariety 1 where
  v := ![k]
  w := ![1]
  ζ := ![1]
  dimℂ := 2 * k

/-! The `HilbK` record is finite dimension-vector data. This file does not
construct a Hilbert scheme or an `l → ∞` limit. -/

/-- Exact profile encoded by `HilbK`: one gauge coordinate `k`, one framing
coordinate, stability parameter `1`, and the declared dimension `2k`. -/
theorem HilbK_data_profile (k : ℕ) :
    (HilbK k).v = ![k] ∧ (HilbK k).w = ![1] ∧
    (HilbK k).ζ = ![1] ∧ (HilbK k).dimℂ = 2 * k := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §8. Quantum K-theory parameters: open algebraic structure -/

/-- Parameters associated with a quiver datum. This record is not a quantum
K-theory ring: no carrier or multiplication is defined in this owner. -/
structure QKParameterData (r : ℕ) where
  /-- Underlying quiver variety. -/
  base : NakajimaQuiverVariety r
  /-- Quantum parameter. -/
  q : ℂ
  /-- Equivariant parameters (torus). -/
  equiv_params : Fin r → ℂ

/-! These fields record parameters only. No quantum K-theory carrier, ring
operations, curve-counting product, or mirror isomorphism is defined here. -/

/-! ## §9. Trigonometric Ruijsenaars–Schneider
   Lax matrix -/

/-- The trigonometric Ruijsenaars–Schneider (tRS)
Lax matrix L(z) ∈ Mat_{N×N}(ℂ(z)).

  L_{ij}(z) = ∏_{k≠i}
    θ(q a_i/a_k; p)
    / θ(a_i/a_k; p)
    · θ(z/a_j; p)
    / θ(q z/a_j; p)
    · δ_{ij}  + (off-diagonal terms)

The eigenvalues of L(z) generate quantum
integrals of motion for the tRS system. -/
structure TRSLaxMatrix (N : ℕ) where
  /-- Spectral parameter. -/
  z : ℂ
  /-- Particle positions. -/
  a : Fin N → ℂ
  /-- Coupling constant q = e^{β γ}. -/
  q : ℂ
  /-- Elliptic nome p (p = 0 for trig case). -/
  p : ℂ
  /-- The Lax matrix. -/
  L : Matrix (Fin N) (Fin N) ℂ

namespace TRSLaxMatrix

/-- The particle rank is the matrix index of the Lax datum. -/
def rank {N : ℕ} (_ : TRSLaxMatrix N) : ℕ := N

end TRSLaxMatrix

/-- Build the trigonometric (p = 0) Lax matrix.
In the trigonometric limit the theta function
reduces to (1 - x), so:

  L_{ij} = δ_{ij} · ∏_{k≠j}
    (1 - q · a_i / a_k) / (1 - a_i / a_k)
-/
def trsLaxMatrix (N : ℕ) (z : ℂ)
    (a : Fin N → ℂ) (q : ℂ) :
    TRSLaxMatrix N := by
  classical
  refine
    { z := z
      a := a
      q := q
      p := 0
      L := Matrix.of fun i j =>
        if i = j then
          ∏ k ∈ Finset.univ.filter (· ≠ j), (1 - q * a i / a k) / (1 - a i / a k)
        else
          (1 - q) * (a i / (a i - a j))
            * ∏ k ∈ Finset.univ.filter (fun m => m ≠ i ∧ m ≠ j),
                (1 - q * a i / a k) / (1 - a i / a k) }

/-! The explicit finite matrix above is a data definition. An R-matrix and a
nondegenerate RLL/Yang–Baxter relation are not constructed or proved here; the
former existential with `R = 0` was an annihilating witness and established no
intertwining information. -/

/-! ## §10. Instanton moduli finite dimension data -/

/-- Finite Jordan-quiver data indexed by rank `N` and charge `k`. This record
does not construct the sheaf moduli space. -/
def instantonModuli (N k : ℕ) :
    NakajimaQuiverVariety 1 where
  v := ![k]
  w := ![N]
  ζ := ![1]
  dimℂ := 2 * N * k

/-- Exact finite data stored for the Jordan-quiver instanton model. -/
theorem instantonModuli_data_profile (N k : ℕ) :
    (instantonModuli N k).v = ![k] ∧
    (instantonModuli N k).w = ![N] ∧
    (instantonModuli N k).ζ = ![1] ∧
    (instantonModuli N k).dimℂ = 2 * N * k := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The two declared dimension fields are equal under swapping their indices. -/
theorem instantonModuli_dim_sym (N k : ℕ) :
    (instantonModuli N k).dimℂ =
    (instantonModuli k N).dimℂ := by
  have h := congrArg (fun t : ℕ => 2 * t) (Nat.mul_comm N k)
  simpa [instantonModuli, Nat.mul_assoc] using h

/-! The dimension symmetry theorem above is arithmetic about the declared
natural-number fields. It does not establish an isomorphism of moduli spaces or
a quantum K-theory mirror theorem. -/

/-! ## §11. Vertex functions and qKZ -/

/-- Finite parameter and coefficient data for a candidate vertex series. The
coefficient sequence is not constructed from quasimap moduli in this file. -/
structure VertexFunction (r : ℕ) where
  /-- Underlying quiver variety. -/
  base : NakajimaQuiverVariety r
  /-- q-parameter. -/
  q : ℂ
  /-- Kähler parameters z_i. -/
  z : Fin r → ℂ
  /-- Equivariant parameters a_j. -/
  a : Fin r → ℂ
  /-- Degree-d coefficient (K-theory class). -/
  coeff : ℕ → ℂ

/-- A recurrence predicate on the stored coefficient sequence. This finite
type uses existential 1-by-1 complex matrices; it does not encode the general
operator-valued quantum difference connection. -/
def SatisfiesQKZ {r : ℕ}
    (V : VertexFunction r) : Prop :=
  ∃ M : (i : Fin r) → Matrix (Fin 1) (Fin 1) ℂ, ∀ (i : Fin r) (d : ℕ), V.coeff (d + 1) = (M i 0 0) * V.coeff d

/-! `SatisfiesQKZ` is an explicit recurrence predicate on the coefficient
sequence. The vertex-function record does not assume this recurrence, and this
file proves no theorem asserting it for all or for `X_kl` vertex functions. -/

/-! ## §12. QQ and Bethe relations

The QQ-to-Bethe correspondence is not established by the structures in this
file. `isBetheState_iff_crossMultiplied` records the precise algebraic form of
the Bethe equations when the vertex parameters are nonzero. -/

/-! ## §13. Parameter-profile data

The profile theorem above records the actual fields of `X_kl` and its parameter
reversal. It does not establish an isomorphism or mirror equivalence. -/

end KoroteevZeitlin

end
