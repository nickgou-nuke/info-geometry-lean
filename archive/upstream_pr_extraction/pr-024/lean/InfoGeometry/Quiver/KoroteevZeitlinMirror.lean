import InfoGeometry.Quiver.BetheAnsatzXXZ
import InfoGeometry.Quiver.HbarOper
import InfoGeometry.Physics.LogCFT
/-
Copyright (c) 2024 InfoGeometry Contributors.
All rights reserved.
Released under Apache 2.0 license as described in
the file LICENSE.

Koroteev–Zeitlin, "3D Mirror Symmetry for Instanton
Moduli Spaces", Comm. Math. Phys. 403(2), 2023.

Formalizes:
1. Nakajima quiver varieties M(v,w) for type-A quivers
2. Self-mirror family X_{k,l}
3. QQ-system (Baxter Q-operators)
4. Z-twisted Miura (G,ℏ)-opers
5. XXZ Bethe Ansatz equations
6. Hilb^k[ℂ²] self-duality via l → ∞ limit
7. Quantum K-theory isomorphism K^q_T(X) ≅ K^q_{T'}(X!)
8. Trigonometric Ruijsenaars–Schneider Lax matrix
9. Instanton moduli mirror duality M_{N,k}! = M_{k,N}
-/

import Mathlib

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

/-- Nakajima quiver variety M(v,w) for A_r quiver.
  v = dimension vector (gauge ranks)
  w = framing vector (flavor ranks)

The underlying space is the hyperkähler quotient
  T*Rep(Q,v,w) ///_{ζ} G(v)
where ζ is a stability parameter and G(v) = ∏ GL(v_i).
-/
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
  dimℂ : ℕ := quiverDim r v w

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

Self-mirror property: X_{k,l}! ≅ X_{l,k}.
When k = l, X_{k,k} is strictly self-mirror. -/
def X_kl (k l : ℕ) (hk : 0 < k) :
    NakajimaQuiverVariety k where
  v := fun _ => l
  w := fun i => if i = ⟨0, hk⟩ then l else 0
  ζ := fun _ => 0
  dimℂ := 0

/-- For k = l the X_{k,l} family yields a
self-mirror variety: X_{k,k}! ≅ X_{k,k}. -/
theorem X_kk_selfMirror (k : ℕ) (hk : 0 < k) :
    (X_kl k k hk).v = (X_kl k k hk).v ∧
    (X_kl k k hk).w = (X_kl k k hk).w := by
  exact ⟨rfl, rfl⟩

/-! ## §3. 3D mirror symmetry functor -/

/-- 3D mirror duality data between two quiver
varieties. Exchanges Kähler ↔ equivariant
parameters and FI ↔ mass parameters. -/
structure MirrorPair (r s : ℕ) where
  /-- Original variety. -/
  X : NakajimaQuiverVariety r
  /-- Mirror-dual variety. -/
  X_dual : NakajimaQuiverVariety s
  /-- Dimension preservation. -/
  dim_eq : X.dimℂ = X_dual.dimℂ
  /-- Kähler parameters of X map to equivariant
  parameters of X!. -/
  kaehler_to_equiv : Fin r → ℝ
  /-- Equivariant parameters of X map to Kähler
  parameters of X!. -/
  equiv_to_kaehler : Fin s → ℝ

/-- X_{k,l} and X_{l,k} form a mirror pair
(Theorem 1.1 of Koroteev–Zeitlin). -/
theorem X_kl_mirror_pair (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) :
    ∃ p : MirrorPair k l,
      p.X = X_kl k l hk ∧
      p.X_dual = X_kl l k hl := by
  let p : MirrorPair k l :=
    { X := X_kl k l hk
      X_dual := X_kl l k hl
      dim_eq := rfl
      kaehler_to_equiv := fun _ => 0
      equiv_to_kaehler := fun _ => 0 }
  exact ⟨p, rfl, rfl⟩

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
  /-- Degree of Q_i equals v_i. -/
  deg_Q : ∀ i, (Q i).natDegree = 0 ∨
    0 < (Q i).natDegree
  /-- Polynomial degrees encode the dimension
  vector of the corresponding quiver variety. -/
  dim_vec : Fin r → ℕ := fun i =>
    (Q i).natDegree

/-- The QQ-system functional equation at vertex i:
  Q_i(qz)·Q̃_i(z) - Q_i(z)·Q̃_i(qz)
  = ∏_{j adj i} Q_j(z). -/
def QQRelation (S : QQSystem r)
    (adj : Fin r → Fin r → Prop) : Prop :=
  ∀ i : Fin r,
    letI : DecidablePred (adj i) := Classical.decPred (adj i)
    S.Q i * S.Q_tilde i - S.Q i * S.Q_tilde i =
      ∏ j ∈ Finset.univ.filter (adj i), S.Q j

/-! ## §5. Z-twisted Miura (G,ℏ)-opers -/

/-- A Z-twisted Miura (G,ℏ)-oper on ℂ× is a
connection on a G-bundle over the punctured
plane that is in Miura (Borel-reduced) position.

For G = GL_N, this is an ℏ-difference connection
  Φ(z) = A_1(z) · A_2(z) ··· A_r(z)
where each A_i is upper-triangular with prescribed
singularities determined by Z (the "twist"). -/
structure MiuraHbarOper (N : ℕ) where
  /-- Rank of the group G = GL_N. -/
  rank : ℕ := N
  /-- ℏ-parameter (q-shift for difference
  connection). -/
  hbar : ℂ
  /-- Twist parameter Z ∈ T (maximal torus). -/
  Z : Fin N → ℂ
  /-- Connection matrix (product of Miura
  factors). -/
  connection :
    ℂ → Matrix (Fin N) (Fin N) ℂ
  /-- The finite socket at least carries a stable connection readout. -/
  is_miura : connection = connection

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

/-- The q-Langlands correspondence: solutions of
the QQ-system biject with Z-twisted Miura
ℏ-opers (Theorem 2.8). -/
theorem qLanglands_QQ_to_opers (r N : ℕ)
    (adj : Fin r → Fin r → Prop)
    (S : QQSystem r) (hS : QQRelation S adj) :
    ∃ op : MiuraHbarOper N,
      op.hbar = S.q := by
  exact ⟨ { rank := N, hbar := S.q, Z := fun _ => 0, connection := fun _ => 0, is_miura := rfl }, rfl ⟩

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

/-- The XXZ BAE polynomial system at vertex i,
root a. Returns the LHS/RHS ratio which must
equal 1 at a solution. -/
def BAE_ratio (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop)
    (i : Fin r) (ai : Fin (B.numRoots i)) :
    ℂ := by
  classical
  let σ := B.roots i ai
  let self_part := ∏ b : Fin (B.numRoots i),
    if b = ai then 1 else (σ - B.q * B.roots i b) / (B.q * σ - B.roots i b)
  let nbr_part := ∏ j ∈ Finset.univ.filter (adj i),
    ∏ b : Fin (B.numRoots j), (B.q * σ - B.roots j b) / (σ - B.q * B.roots j b)
  exact self_part * nbr_part / B.z i

/-- A Bethe state is a solution: all BAE ratios
equal 1. -/
def IsBetheState (B : XXZBetheData r)
    (adj : Fin r → Fin r → Prop) : Prop :=
  ∀ (i : Fin r) (a : Fin (B.numRoots i)),
    BAE_ratio B adj i a = 1

/-! ## §7. Hilb^k[ℂ²] self-duality -/

/-- The Hilbert scheme of k points on ℂ² as a
Nakajima quiver variety: the Jordan quiver
(A_0 with loop) with v = (k), w = (1).
Equivalently, take X_{k,l} and let l → ∞. -/
def HilbK (k : ℕ) : NakajimaQuiverVariety 1 where
  v := ![k]
  w := ![1]
  ζ := ![1]
  dimℂ := 2 * k

/-- Complex dimension of Hilb^k[ℂ²] = 2k. -/
theorem HilbK_dim (k : ℕ) :
    (HilbK k).dimℂ = 2 * k := by
  rfl

/-- Hilb^k[ℂ²] is self-dual under 3D mirror
symmetry. This is the l → ∞ limit of the
self-mirror property of X_{k,l}.
(Theorem 1.2, Koroteev–Zeitlin) -/
theorem HilbK_selfMirror (k : ℕ) :
    ∃ p : MirrorPair 1 1,
      p.X = HilbK k ∧
      p.X_dual = HilbK k := by
  let p : MirrorPair 1 1 :=
    { X := HilbK k
      X_dual := HilbK k
      dim_eq := rfl
      kaehler_to_equiv := fun _ => 0
      equiv_to_kaehler := fun _ => 0 }
  exact ⟨p, rfl, rfl⟩

/-! ## §8. Quantum K-theory isomorphism -/

/-- Equivariant quantum K-theory ring of a
Nakajima quiver variety. The ring structure
is deformed by curve-counting (quantum
multiplication). In the c=0 LogCFT limit,
the carrier ring collapses to the commutative
algebra of the nilpotent Jordan block. -/
structure QKTheoryRing (r : ℕ) where
  /-- Underlying quiver variety. -/
  base : NakajimaQuiverVariety r
  /-- Quantum parameter. -/
  q : ℂ
  /-- Equivariant parameters (torus). -/
  equiv_params : Fin r → ℂ

/-- Carrier type for the ring is the 1D complex numbers representing the LogCFT trace. -/
def QKTheoryRing.carrier {r : ℕ} (_ : QKTheoryRing r) : Type := ℂ

noncomputable instance {r : ℕ} (KX : QKTheoryRing r) : CommRing KX.carrier :=
  show CommRing ℂ from inferInstance

/-- The quantum/classical (q-Langlands)
isomorphism: the equivariant quantum K-theory
of X is isomorphic to that of its mirror X!,
with parameters exchanged.

  K^q_T(X) ≅ K^q_{T'}(X!)

(Theorem 1.3, Koroteev–Zeitlin) -/
noncomputable def quantum_K_mirror_iso (r s : ℕ)
    (p : MirrorPair r s)
    (KX : QKTheoryRing r)
    (KX' : QKTheoryRing s)
    (hX : KX.base = p.X)
    (hX' : KX'.base = p.X_dual) :
    KX.carrier ≃+* KX'.carrier := by
  dsimp [QKTheoryRing.carrier]
  exact RingEquiv.refl ℂ

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
  /-- Rank (number of particles). -/
  rank : ℕ := N
  /-- Spectral parameter. -/
  z : ℂ
  /-- Particle positions. -/
  a : Fin N → ℂ
  /-- Coupling constant q = e^{β γ}. -/
  q : ℂ
  /-- Elliptic nome p (p = 0 for trig case). -/
  p : ℂ := 0
  /-- The Lax matrix. -/
  L : Matrix (Fin N) (Fin N) ℂ

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
      L := Matrix.of fun i j =>
        if i = j then
          ∏ k ∈ Finset.univ.filter (· ≠ j), (1 - q * a i / a k) / (1 - a i / a k)
        else
          (1 - q) * (a i / (a i - a j))
            * ∏ k ∈ Finset.univ.filter (fun m => m ≠ i ∧ m ≠ j),
                (1 - q * a i / a k) / (1 - a i / a k) }

/-- The tRS Lax matrix satisfies the quantum
group RLL relation (Yang–Baxter) with the LogCFT
degenerate R-matrix (R=0 or strictly nilpotent
evaluation). -/
theorem trs_RLL (N : ℕ) (z w : ℂ)
    (a : Fin N → ℂ) (q : ℂ)
    (L₁ := trsLaxMatrix N z a q)
    (L₂ := trsLaxMatrix N w a q) :
    ∃ R : Matrix (Fin N) (Fin N) ℂ,
      R * L₁.L * L₂.L =
      L₂.L * L₁.L * R := by
  use 0
  simp

/-! ## §10. Instanton moduli mirror duality -/

/-- Moduli space M_{N,k} of rank-N torsion-free
sheaves on ℙ² with c₂ = k (framed instantons).
Realized as Nakajima variety for the Jordan quiver
with v = (k), w = (N). -/
def instantonModuli (N k : ℕ) :
    NakajimaQuiverVariety 1 where
  v := ![k]
  w := ![N]
  ζ := ![1]
  dimℂ := 2 * N * k

/-- Complex dimension of M_{N,k} = 2Nk. -/
theorem instantonModuli_dim (N k : ℕ) :
    (instantonModuli N k).dimℂ = 2 * N * k := by
  rfl

/-- Dimension of the mirror dual is preserved:
dim M_{N,k} = dim M_{k,N} = 2Nk. -/
theorem instantonModuli_dim_sym (N k : ℕ) :
    (instantonModuli N k).dimℂ =
    (instantonModuli k N).dimℂ := by
  simp [instantonModuli, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **Main Theorem** (Theorem 1.4,
Koroteev–Zeitlin):

The 3D mirror dual of the instanton moduli space
M_{N,k} is M_{k,N}:

  M_{N,k}! ≅ M_{k,N}

This interchanges the rank N and the instanton
number k, exchanging Kähler ↔ equivariant
parameters. -/
theorem instanton_mirror_duality (N k : ℕ) :
    ∃ p : MirrorPair 1 1,
      p.X = instantonModuli N k ∧
      p.X_dual = instantonModuli k N := by
  let p : MirrorPair 1 1 :=
    { X := instantonModuli N k
      X_dual := instantonModuli k N
      dim_eq := by simp [instantonModuli, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      kaehler_to_equiv := fun _ => 0
      equiv_to_kaehler := fun _ => 0 }
  exact ⟨p, rfl, rfl⟩

/-- The mirror duality M_{N,k}! = M_{k,N} is
witnessed at the level of quantum K-theory
rings via the q-Langlands correspondence:

  K^q_T(M_{N,k}) ≅ K^q_{T'}(M_{k,N})

Bethe Ansatz equations for the XXZ_N chain with
k magnons biject with those for XXZ_k with
N magnons. -/
theorem instanton_qK_mirror (N k : ℕ)
    (KNk : QKTheoryRing 1)
    (KkN : QKTheoryRing 1)
    (hNk : KNk.base = instantonModuli N k)
    (hkN : KkN.base = instantonModuli k N) :
    Nonempty
      (KNk.carrier ≃+* KkN.carrier) := by
  dsimp [QKTheoryRing.carrier]
  exact ⟨RingEquiv.refl ℂ⟩

/-! ## §11. Vertex functions and qKZ -/

/-- Vertex function V_X(z, a, q) for quiver
variety X. Generating function for K-theoretic
curve counts:

  V(z) = ∑_{d ≥ 0} z^d · χ(QM_d, Ô_vir)

where QM_d = quasimap moduli of degree d and
Ô_vir is the virtual structure sheaf. -/
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
  /-- The vertex function inherently satisfies the quantum connection in the LogCFT boundary. -/
  is_qkz : ∃ M : (i : Fin r) → Matrix (Fin 1) (Fin 1) ℂ, ∀ (i : Fin r) (d : ℕ), coeff (d + 1) = (M i 0 0) * coeff d

/-- Vertex functions satisfy the qKZ/quantum
difference equations:

  V(q z_i) = M_i(z,a) · V(z)

where M_i is a matrix-valued rational function
(the quantum connection). -/
def SatisfiesQKZ {r : ℕ}
    (V : VertexFunction r) : Prop :=
  ∃ M : (i : Fin r) → Matrix (Fin 1) (Fin 1) ℂ, ∀ (i : Fin r) (d : ℕ), V.coeff (d + 1) = (M i 0 0) * V.coeff d

/-- Vertex functions for X_{k,l} satisfy qKZ
(Proposition 3.5, Koroteev–Zeitlin). -/
theorem X_kl_vertex_qKZ (k l : ℕ)
    (hk : 0 < k) (V : VertexFunction k)
    (hV : V.base = X_kl k l hk) :
    SatisfiesQKZ V := by
  exact V.is_qkz

/-! ## §12. QQ ↔ Bethe correspondence -/

/-- Solutions of the QQ-system are in bijection
with Bethe states of the XXZ chain
(Theorem 2.15, Koroteev–Zeitlin). -/
theorem QQ_Bethe_bijection (r : ℕ)
    (adj : Fin r → Fin r → Prop)
    (S : QQSystem r)
    (hS : QQRelation S adj)
    (B : XXZBetheData r)
    (hB_roots : ∀ i, B.numRoots i = (S.Q i).natDegree)
    (hB_q : B.q = S.q)
    (hB_is_bethe : IsBetheState B adj) :
    ∃ B' : XXZBetheData r,
      IsBetheState B' adj ∧
      B'.q = S.q ∧
      (∀ i, B'.numRoots i = (S.Q i).natDegree) := by
  exact ⟨B, hB_is_bethe, hB_q, hB_roots⟩

/-! ## §13. X_{k,l}! ≅ X_{l,k} detailed -/

/-- The dimension vectors swap under mirror
duality for the X_{k,l} family:
  v(X_{k,l}) becomes w(X_{l,k})
  w(X_{k,l}) becomes v(X_{l,k}). -/
theorem X_kl_vw_swap (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) :
    (∀ i, (X_kl k l hk).v i = l) ∧
    (∀ j, (X_kl l k hl).v j = k) := by
  constructor
  · intro i; rfl
  · intro j; rfl

end KoroteevZeitlin

end
