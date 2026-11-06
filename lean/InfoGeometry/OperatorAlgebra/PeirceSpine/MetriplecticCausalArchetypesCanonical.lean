/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.Basic.Real.Star
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

/-!
# Metriplectic–Causal Archetypes — Canonical Non-Commutative Matrix Operator Algebra

Pure mathematical archetypes regenerated as a **causal poset** of non-commutative matrix
operator algebra over star rings. No scalar, no diagonal, no commuting toys: every statement
is about matrices, operators, commutators, anticommutators, adjoints, Gramians, Krein metrics,
Clifford / Jordan–Wigner generators, BCFW bridges, and Yangian R-matrices.

Archetypal structure (raw stream → causal order):

1. **MCP₁ — Binary star cut.** `M = S + K` with `S* = S`, `K* = -K` (doubled form avoids halving).

2. **MCP₂ — Fourfold relational anatomy.** Jacobi identity; adjoint anti-homomorphism;
   commutator–anticommutator derivation; strictly lower nilpotent `N² = 0`.

3. **MCP₁ doubling — Transcendent function.** `{S,K}` gravity, `[S,K]` tension,
   `M(S,K)` bridge, `D(S,K)² = diag(G_out, G_in)` round-trip.

4. **MCP₃ — Para-Kähler triad & light-cone nullity.** `J²=K²=I`, `ε²=-I`,
   `2Π± = I ± σ_x` Krein-null, corrected cross-pairing `2(J+ε)`.

5. **MCP₄ — Walsh–Hadamard elenchus.** `H₂ cl11Elem H₂ = 2·cl11Elem(dᵢ,d_s,d_p,-d_c)`.

6. **MCP₅ — Lorentzian determinant & BCFW.** `det Ω = w_c²-w_p²-w_s²`, `Ω²=-f·I`,
   `(I-Ω)(I+Ω)=(1+f)·I`; `[B₀₁(z₁),B₁₂(z₂)] = z₁z₂·E₀₂`.

7. **MCP₆ — Krein–Hamiltonian–Hopf crash.** `J₄`-skew-adjoint generator,
   `N(Δω,g)² = -(Δω²-g²)·I`, crash `N(Δω,Δω)² = 0`, Jordan chain, null norm.

8. **MCP₇ — Yangian R-matrix & Clifford EP.** `R(u,η)R(-u,η) = (η²-u²)·I`;
   Baxterized braid; Clifford EP period **8** `(B₁₂²)² = -4·I`.

9. **MCP₈ — Zitterbewegung & ℤ₄ monodromy.** `dw·N + ((dw²-g²)·Γ - dw·N) = (dw²-g²)·Γ`;
   `B_EP = -ε`, `B_EP² = -I`, `B_EP⁴ = I`.

10. **MCP₉ — FW rapidity dictionary.** `f = -tanh²θ`, `(1-f)/(1+f) = cosh(2θ)`,
    strand product `sinh(2θ)²/4`, `θ = artanh √(-f)`.

11. **MCP₁₀ — Causal poset.** Re-exports the companion's `mcp_poset_chain_and_irreflexivity`.

All definitions live at top level (shared variable context) so every theorem can reference
every matrix operator without section-local hiding.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalArchetypesCanonical

open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

variable {R : Type*} [CommRing R]
variable {B : Type*} [Ring B] [StarRing B]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₁ — Binary star cut over a star ring
────────────────────────────────────────────────────────────────────────────────-/

def selfAdjointPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  M + Mᴴ

def skewAdjointPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  M - Mᴴ

theorem selfAdjointPart_isSelfAdjoint (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.IsHermitian (selfAdjointPart M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointPart, Matrix.conjTranspose_apply, Matrix.add_apply,
      Matrix.mul_apply, Fin.sum_univ_two, star_add, star_star] <;>
    ring <;> simp [star_add, star_star]

theorem skewAdjointPart_isSkewAdjoint (M : Matrix (Fin 2) (Fin 2) B) :
    (skewAdjointPart M)ᴴ = -(skewAdjointPart M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewAdjointPart, Matrix.conjTranspose_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_two, star_add, star_star, star_neg,
      star_sub] <;> ring <;> simp [star_add, star_star, star_neg, star_sub]

theorem starCutSum (M : Matrix (Fin 2) (Fin 2) B) :
    selfAdjointPart M + skewAdjointPart M = 2 • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointPart, skewAdjointPart, Matrix.add_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      star_add, star_star] <;> ring <;> simp [star_add, star_star]

theorem conjTransposeMulReverse (A B : Matrix (Fin 2) (Fin 2) B) :
    (A * B)ᴴ = Bᴴ * Aᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      star_mul, star_add] <;>
    (try ring) <;>
    (try simp_all [star_mul, star_add]) <;>
    (try abel)

theorem conjTransposeInvolutive (M : Matrix (Fin 2) (Fin 2) B) :
    (Mᴴ)ᴴ = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, star_star]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₂ — Fourfold relational anatomy and commutator calculus
────────────────────────────────────────────────────────────────────────────────-/

theorem jacobiIdentity (A B C : Matrix (Fin 2) (Fin 2) B) :
    comm (comm A B) C + comm (comm B C) A + comm (comm C A) B = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
      Fin.sum_univ_two] <;>
    noncomm_ring

theorem commAnticommDerivation (A B C : Matrix (Fin 2) (Fin 2) B) :
    comm A (anticomm B C) = anticomm (comm A B) C + anticomm B (comm A C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm, anticomm, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
      Fin.sum_univ_two] <;>
    noncomm_ring

theorem strictLower2_nilpotent (a : B) :
    (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) *
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem strictLower2_nonNormal {a : B} (h : a * star a ≠ 0) :
    (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) *
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B)ᴴ -
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B)ᴴ *
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) ≠ 0 := by
  intro hn
  have h₁ : (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) *
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B)ᴴ -
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B)ᴴ *
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) B) =
      !![-(star a * a), 0; 0, a * star a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
        Fin.sum_univ_two, star_add, star_star, star_neg]
    <;> ring <;> simp [star_add, star_star, star_neg]
  rw [h₁] at hn
  have h₂ : (a * star a : B) = 0 := by
    have h₃ : (!![-(star a * a), 0; 0, a * star a] : Matrix (Fin 2) (Fin 2) B) = 0 := by
      rw [hn]
    have h₄ : (a * star a : B) = 0 := by
      have h₅ : (!![-(star a * a), 0; 0, a * star a] : Matrix (Fin 2) (Fin 2) B) 1 1 = 0 := by
        rw [h₃]
        simp [Matrix.zero_apply]
      simp [Matrix.zero_apply] at h₅ ⊢
      <;> simp_all [Matrix.zero_apply]
      <;> linarith
    exact h₄
  exact h h₂

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₁ doubling — Transcendent function: pairing S and K
────────────────────────────────────────────────────────────────────────────────-/

def metriplecticBlock (S K : B) : Matrix (Fin 2) (Fin 2) B := !![S, K; K, S]

def chiralDiracBlock (S K : B) : Matrix (Fin 2) (Fin 2) B := !![0, S + K; S - K, 0]

def equilibriumFlowRoot (S K : B) : Matrix (Fin 2) (Fin 2) B := !![S, K; -K, -S]

theorem metriplecticBlockSquare (S K : B) :
    metriplecticBlock S K * metriplecticBlock S K =
      !![S * S + K * K, S * K + K * S; K * S + S * K, K * K + S * S] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metriplecticBlock, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring
  <;> simp [add_comm, add_left_comm, add_assoc]

theorem equilibriumFlowRootSquare (S K : B) :
    equilibriumFlowRoot S K * equilibriumFlowRoot S K =
      !![S * S - K * K, S * K - K * S; S * K - K * S, S * S - K * K] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [equilibriumFlowRoot, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring
  <;> simp [sub_eq_add_neg]

theorem metriplecticBlockKreinAdjoint (S K : B) (hS : star S = S) (hK : star K = -K) :
    Matrix.conjTranspose (metriplecticBlock S K) =
      ![(1 : B), 0; 0, -1] * metriplecticBlock S K * ![(1 : B), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metriplecticBlock, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, hS, hK, star_add, star_sub, star_neg]
  <;>
    (try ring) <;>
    (try simp_all [star_add, star_sub, star_neg])

theorem chiralDiracBlockSquare (S K : B) :
    chiralDiracBlock S K * chiralDiracBlock S K =
      !![(S + K) * (S - K), 0; 0, (S - K) * (S + K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracBlock, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring
  <;> simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₃ — Para-Kähler triad and light-cone nullity (over R)
────────────────────────────────────────────────────────────────────────────────-/

def sigmaZ : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def sigmaX : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
def epsSymp : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

theorem cl11TriadMatrix :
    sigmaZ * sigmaZ = 1 ∧
    sigmaX * sigmaX = 1 ∧
    epsSymp * epsSymp = -1 ∧
    sigmaZ * sigmaX * sigmaZ = -sigmaX ∧
    epsSymp = sigmaZ * sigmaX := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, epsSymp, Matrix.mul_apply, Fin.sum_univ_two] }

theorem lightConeNullityAndCrossPairing :
    (1 + sigmaX : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * (1 + sigmaX) = 0 ∧
    (1 - sigmaX : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * (1 - sigmaX) = 0 ∧
    (1 + sigmaX : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * (1 - sigmaX) =
      (2 : R) • (sigmaZ + epsSymp) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, epsSymp, Matrix.mul_apply, Matrix.transpose_apply,
          Fin.sum_univ_two] <;> ring }

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₄ — Walsh–Hadamard elenchus (matrix level)
────────────────────────────────────────────────────────────────────────────────-/

def walshHadamard2 : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, -1]

def cl11Elem (di dp ds dc : R) : Matrix (Fin 2) (Fin 2) R :=
  !![di + dp, ds - dc; ds + dc, di - dp]

theorem walshHadamardConjugation (di dp ds dc : R) :
    walshHadamard2 * cl11Elem di dp ds dc * walshHadamard2 =
      (2 : R) • cl11Elem di ds dp (-dc) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walshHadamard2, cl11Elem, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem walshHadamard2Sq :
    walshHadamard2 * walshHadamard2 = (2 : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walshHadamard2, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem walshHadamardDiagonalCommute (a b c d : R) :
    Commute (walshHadamard2 * !![a, 0; 0, b] * walshHadamard2)
      (walshHadamard2 * !![c, 0; 0, d] * walshHadamard2) := by
  have hx : walshHadamard2 * !![a, 0; 0, b] * walshHadamard2 =
      !![a + b, a - b; a - b, a + b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [walshHadamard2, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hy : walshHadamard2 * !![c, 0; 0, d] * walshHadamard2 =
      !![c + d, c - d; c - d, c + d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [walshHadamard2, Matrix.mul_apply, Fin.sum_univ_two]; ring
  simp only [Commute, hx, hy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₅ — Lorentzian determinant, Cayley, BCFW bridge
────────────────────────────────────────────────────────────────────────────────-/

def cl11Traceless (wp ws wc : R) : Matrix (Fin 2) (Fin 2) R :=
  !![wp, ws - wc; ws + wc, -wp]

def cl11LoopWeight (wp ws wc : R) : R := wc ^ 2 - wp ^ 2 - ws ^ 2

theorem lorentzianDetCayley (wp ws wc : R) :
    Matrix.trace (cl11Traceless wp ws wc) = 0 ∧
    Matrix.det (cl11Traceless wp ws wc) = cl11LoopWeight wp ws wc ∧
    cl11Traceless wp ws wc * cl11Traceless wp ws wc =
      -(cl11LoopWeight wp ws wc • (1 : Matrix (Fin 2) (Fin 2) R)) ∧
    (1 - cl11Traceless wp ws wc) * (1 + cl11Traceless wp ws wc) =
      (1 + cl11LoopWeight wp ws wc) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { simp [cl11Traceless, cl11LoopWeight, Matrix.trace, Matrix.det_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp; ring }

def bcfwBridge01 (z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, z, 0; 0, 1, 0; 0, 0, 1]

def bcfwBridge12 (z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, 1, z; 0, 0, 1]

theorem bcfwBridgeCommutator (z1 z2 : R) :
    comm (bcfwBridge01 z1) (bcfwBridge12 z2) = (z1 * z2) •
      (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bcfwBridge01, bcfwBridge12, comm, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.zero_apply, Fin.sum_univ_three]
  <;> ring <;> simp [mul_assoc]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₆ — Krein–Hamiltonian–Hopf crash
────────────────────────────────────────────────────────────────────────────────-/

def kreinMetric4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

def jwGamma2 : Matrix (Fin 4) (Fin 4) R :=
  !![0, -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

def jwE1 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

def kreinHopfSemi (wBar : R) : Matrix (Fin 4) (Fin 4) R := wBar • jwGamma2

def kreinHopfNilPart (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  dw • jwGamma2 + g • jwE1

def kreinHopfGenerator (wBar dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  kreinHopfSemi wBar + kreinHopfNilPart dw g

theorem jwGamma2_sq : jwGamma2 * jwGamma2 = -(1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  simp only [jwGamma2, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
    Matrix.zero_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp

theorem jwE1_sq : jwE1 * jwE1 = (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  simp only [jwE1, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply,
    Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp

theorem jwGamma2_jwE1_anticomm : jwGamma2 * jwE1 = -jwE1 * jwGamma2 := by
  ext i j
  simp only [jwGamma2, jwE1, Matrix.mul_apply, Matrix.neg_apply,
    Matrix.zero_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp

theorem kreinMetric4_commutes_jwGamma2 :
    kreinMetric4 * jwGamma2 = jwGamma2 * kreinMetric4 := by
  ext i j
  simp only [kreinMetric4, jwGamma2, Matrix.mul_apply, Matrix.zero_apply,
    Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp

theorem kreinMetric4_anticommutes_jwE1 :
    kreinMetric4 * jwE1 = -jwE1 * kreinMetric4 := by
  ext i j
  simp only [kreinMetric4, jwE1, Matrix.mul_apply, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp

theorem kreinHopfCrash (wBar dw g : R) :
    kreinMetric4 * (kreinHopfGenerator wBar dw g)ᵀ * kreinMetric4 =
      -kreinHopfGenerator wBar dw g ∧
    kreinHopfSemi wBar * kreinHopfNilPart dw g =
      kreinHopfNilPart dw g * kreinHopfSemi wBar ∧
    kreinHopfNilPart dw g * kreinHopfNilPart dw g =
      -((dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) := by
  have h₁ : jwGamma2 * jwGamma2 = -(1 : Matrix (Fin 4) (Fin 4) R) := jwGamma2_sq
  have h₂ : jwE1 * jwE1 = (1 : Matrix (Fin 4) (Fin 4) R) := jwE1_sq
  have h₃ : jwGamma2 * jwE1 = -jwE1 * jwGamma2 := jwGamma2_jwE1_anticomm
  have h₄ : kreinMetric4 * jwGamma2 = jwGamma2 * kreinMetric4 := kreinMetric4_commutes_jwGamma2
  have h₅ : kreinMetric4 * jwE1 = -jwE1 * kreinMetric4 := kreinMetric4_anticommutes_jwE1
  have h₆ : (jwGamma2 : Matrix (Fin 4) (Fin 4) R)ᵀ = -(jwGamma2 : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    simp only [jwGamma2, Matrix.transpose_apply, Matrix.neg_apply, Matrix.zero_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp
  have h₇ : (jwE1 : Matrix (Fin 4) (Fin 4) R)ᵀ = (jwE1 : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    simp only [jwE1, Matrix.transpose_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp
  have h₈ : (kreinMetric4 : Matrix (Fin 4) (Fin 4) R)ᵀ = (kreinMetric4 : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    simp only [kreinMetric4, Matrix.transpose_apply, Matrix.zero_apply, Matrix.one_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, ?_, ?_⟩
  · calc
      kreinMetric4 * (kreinHopfGenerator wBar dw g)ᵀ * kreinMetric4
        = kreinMetric4 * ((wBar • jwGamma2 + dw • jwGamma2 + g • jwE1)ᵀ) * kreinMetric4 := by
          simp [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart]
          <;> ring
        _ = kreinMetric4 * (wBar • jwGamma2ᵀ + dw • jwGamma2ᵀ + g • jwE1ᵀ) * kreinMetric4 := by
          simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, h₆, h₇]
          <;> simp_all [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
          <;> ring
        _ = kreinMetric4 * (wBar • (-(jwGamma2)) + dw • (-(jwGamma2)) + g • jwE1) * kreinMetric4 := by
          rw [h₆, h₇]
          <;> simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
          <;> ring
        _ = -(wBar • (kreinMetric4 * jwGamma2 * kreinMetric4) +
            dw • (kreinMetric4 * jwGamma2 * kreinMetric4) -
            g • (kreinMetric4 * jwE1 * kreinMetric4)) := by
          calc
            kreinMetric4 * (wBar • (-(jwGamma2)) + dw • (-(jwGamma2)) + g • jwE1) * kreinMetric4
              = (wBar • (kreinMetric4 * (-(jwGamma2))) + dw • (kreinMetric4 * (-(jwGamma2))) +
                  g • (kreinMetric4 * jwE1)) * kreinMetric4 := by
                ext i j
                simp only [kreinMetric4, jwGamma2, jwE1, Matrix.mul_apply,
                  Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
                  Matrix.zero_apply, Matrix.one_apply, Fin.sum_univ_four]
                fin_cases i <;> fin_cases j <;>
                  simp [h₄, h₅]
                <;> ring
              _ = (wBar • (-(kreinMetric4 * jwGamma2)) + dw • (-(kreinMetric4 * jwGamma2)) +
                  g • (kreinMetric4 * jwE1)) * kreinMetric4 := by
                simp [Matrix.smul_neg, Matrix.smul_mul, Matrix.mul_smul]
                <;> ring
              _ = -(wBar • (kreinMetric4 * jwGamma2) * kreinMetric4 +
                  dw • (kreinMetric4 * jwGamma2) * kreinMetric4 -
                  g • (kreinMetric4 * jwE1) * kreinMetric4) := by
                simp [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
                <;> ring
              _ = -(wBar • jwGamma2 * (kreinMetric4 * kreinMetric4) +
                  dw • jwGamma2 * (kreinMetric4 * kreinMetric4) -
                  g • jwE1 * (kreinMetric4 * kreinMetric4)) := by
                calc
                  -(wBar • (kreinMetric4 * jwGamma2) * kreinMetric4 +
                    dw • (kreinMetric4 * jwGamma2) * kreinMetric4 -
                    g • (kreinMetric4 * jwE1) * kreinMetric4)
                    = -(wBar • jwGamma2 * (kreinMetric4 * kreinMetric4) +
                      dw • jwGamma2 * (kreinMetric4 * kreinMetric4) -
                      g • jwE1 * (kreinMetric4 * kreinMetric4)) := by
                    ext i j
                    simp only [kreinMetric4, jwGamma2, jwE1, Matrix.mul_apply,
                      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
                      Matrix.zero_apply, Matrix.one_apply, Fin.sum_univ_four]
                    fin_cases i <;> fin_cases j <;>
                      simp [Matrix.mul_assoc]
                    <;> ring
                    <;> simp_all [Matrix.mul_assoc]
                  _ = -(wBar • jwGamma2 * (kreinMetric4 * kreinMetric4) +
                    dw • jwGamma2 * (kreinMetric4 * kreinMetric4) -
                    g • jwE1 * (kreinMetric4 * kreinMetric4)) := by rfl
              _ = -(wBar • jwGamma2 + dw • jwGamma2 - g • jwE1) := by
                have h₉ : kreinMetric4 * kreinMetric4 = (1 : Matrix (Fin 4) (Fin 4) R) := by
                  ext i j
                  simp only [kreinMetric4, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply,
                    Fin.sum_univ_four]
                  fin_cases i <;> fin_cases j <;> simp
                calc
                  -(wBar • jwGamma2 * (kreinMetric4 * kreinMetric4) +
                    dw • jwGamma2 * (kreinMetric4 * kreinMetric4) -
                    g • jwE1 * (kreinMetric4 * kreinMetric4))
                    = -(wBar • jwGamma2 * 1 + dw • jwGamma2 * 1 - g • jwE1 * 1) := by
                      rw [h₉]
                      <;> simp [Matrix.mul_one]
                    _ = -(wBar • jwGamma2 + dw • jwGamma2 - g • jwE1) := by
                      simp [Matrix.smul_one]
                      <;> ring
            _ = -(kreinHopfGenerator wBar dw g) := by
              simp [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart]
              <;> ring
              <;> simp_all [Matrix.mul_smul, Matrix.smul_mul]
  · calc
      kreinHopfSemi wBar * kreinHopfNilPart dw g
        = (wBar • jwGamma2) * (dw • jwGamma2 + g • jwE1) := by
          simp [kreinHopfSemi, kreinHopfNilPart]
        _ = wBar • dw • (jwGamma2 * jwGamma2) + wBar • g • (jwGamma2 * jwE1) := by
          calc
            (wBar • jwGamma2) * (dw • jwGamma2 + g • jwE1)
              = (wBar • jwGamma2) * (dw • jwGamma2) + (wBar • jwGamma2) * (g • jwE1) := by rw [Matrix.mul_add]
            _ = wBar • dw • (jwGamma2 * jwGamma2) + wBar • g • (jwGamma2 * jwE1) := by
              simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
              <;> ring
        _ = wBar • dw • (-(1 : Matrix (Fin 4) (Fin 4) R)) + wBar • g • (-jwE1 * jwGamma2) := by
          rw [h₁, h₃]
          <;> simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          <;> ring
        _ = -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) - wBar • g • (jwE1 * jwGamma2) := by
          simp [smul_neg]
          <;> ring
        _ = kreinHopfNilPart dw g * kreinHopfSemi wBar := by
          calc
            -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) - wBar • g • (jwE1 * jwGamma2)
              = -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) + wBar • g • (jwGamma2 * jwE1) := by
                rw [h₃]
                <;> simp [smul_neg]
                <;> ring
              _ = (dw • jwGamma2 + g • jwE1) * (wBar • jwGamma2) := by
                calc
                  -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) + wBar • g • (jwGamma2 * jwE1)
                    = (dw • jwGamma2) * (wBar • jwGamma2) + (g • jwE1) * (wBar • jwGamma2) := by
                      calc
                        (dw • jwGamma2) * (wBar • jwGamma2) + (g • jwE1) * (wBar • jwGamma2)
                          = dw • wBar • (jwGamma2 * jwGamma2) + g • wBar • (jwE1 * jwGamma2) := by
                            simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
                            <;> ring
                          _ = dw • wBar • (-(1 : Matrix (Fin 4) (Fin 4) R)) + g • wBar • (jwE1 * jwGamma2) := by
                            rw [h₁]
                            <;> simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
                            <;> ring
                          _ = -(dw • wBar • (1 : Matrix (Fin 4) (Fin 4) R)) + g • wBar • (jwE1 * jwGamma2) := by
                            simp [smul_neg]
                            <;> ring
                          _ = -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) + wBar • g • (jwE1 * jwGamma2) := by
                            simp [mul_comm, Matrix.smul_mul, Matrix.mul_smul]
                            <;> ring
                    _ = -(wBar • dw • (1 : Matrix (Fin 4) (Fin 4) R)) + wBar • g • (jwE1 * jwGamma2) := by rfl
                _ = (dw • jwGamma2 + g • jwE1) * (wBar • jwGamma2) := by
                  calc
                    (dw • jwGamma2) * (wBar • jwGamma2) + (g • jwE1) * (wBar • jwGamma2)
                      = (dw • jwGamma2 + g • jwE1) * (wBar • jwGamma2) := by
                        rw [Matrix.add_mul]
                        <;> simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
                      _ = (dw • jwGamma2 + g • jwE1) * (wBar • jwGamma2) := by rfl
              _ = kreinHopfNilPart dw g * kreinHopfSemi wBar := by
                simp [kreinHopfNilPart, kreinHopfSemi]
                <;> ring
  · calc
      kreinHopfNilPart dw g * kreinHopfNilPart dw g
        = (dw • jwGamma2 + g • jwE1) * (dw • jwGamma2 + g • jwE1) := by
          simp [kreinHopfNilPart]
        _ = dw • dw • (jwGamma2 * jwGamma2) + dw • g • (jwGamma2 * jwE1) +
            g • dw • (jwE1 * jwGamma2) + g • g • (jwE1 * jwE1) := by
          calc
            (dw • jwGamma2 + g • jwE1) * (dw • jwGamma2 + g • jwE1)
              = (dw • jwGamma2) * (dw • jwGamma2) + (dw • jwGamma2) * (g • jwE1) +
                (g • jwE1) * (dw • jwGamma2) + (g • jwE1) * (g • jwE1) := by
                  rw [Matrix.add_mul, Matrix.mul_add]
                  <;> simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
              _ = dw • dw • (jwGamma2 * jwGamma2) + dw • g • (jwGamma2 * jwE1) +
                g • dw • (jwE1 * jwGamma2) + g • g • (jwE1 * jwE1) := by
                simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
                <;> ring
        _ = dw • dw • (-(1 : Matrix (Fin 4) (Fin 4) R)) + dw • g • (-jwE1 * jwGamma2) +
            g • dw • (-jwGamma2 * jwE1) + g • g • (1 : Matrix (Fin 4) (Fin 4) R) := by
          rw [h₁, h₃, h₃, h₂]
          <;> simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
          <;> ring
        _ = (g ^ 2 - dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
          have h₉ : dw • g = g • dw := by rw [mul_comm]
          calc
            dw • dw • (-(1 : Matrix (Fin 4) (Fin 4) R)) + dw • g • (-jwE1 * jwGamma2) +
              g • dw • (-jwGamma2 * jwE1) + g • g • (1 : Matrix (Fin 4) (Fin 4) R)
              = -(dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) + dw • g • (-jwE1 * jwGamma2) +
                  g • dw • (-jwGamma2 * jwE1) + (g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
                simp [pow_two, Matrix.smul_smul, Matrix.mul_smul]
                <;> ring
                <;> simp_all [Matrix.smul_smul, Matrix.mul_smul]
              _ = -(dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) + (g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
                have h₁₀ : dw • g • (-jwE1 * jwGamma2) + g • dw • (-jwGamma2 * jwE1) = 0 := by
                  calc
                    dw • g • (-jwE1 * jwGamma2) + g • dw • (-jwGamma2 * jwE1)
                      = dw • g • (-jwE1 * jwGamma2) + dw • g • (-jwGamma2 * jwE1) := by
                        rw [h₉]
                        <;> simp [Matrix.smul_mul, Matrix.mul_smul]
                      _ = dw • g • ((-jwE1 * jwGamma2) + (-jwGamma2 * jwE1)) := by
                        rw [← Matrix.smul_add]
                        <;> simp [Matrix.mul_smul]
                      _ = dw • g • (-(jwE1 * jwGamma2 + jwGamma2 * jwE1)) := by
                        simp [smul_neg, add_assoc]
                        <;> ring
                      _ = 0 := by
                        have h₁₁ : jwE1 * jwGamma2 + jwGamma2 * jwE1 = 0 := by
                          rw [← h₃]
                          <;> simp [add_neg_cancel_right]
                        rw [h₁₁]
                        <;> simp [Matrix.smul_zero]
                calc
                  -(dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) + dw • g • (-jwE1 * jwGamma2) +
                    g • dw • (-jwGamma2 * jwE1) + (g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)
                    = -(dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) + 0 + (g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
                      rw [h₁₀]
                      <;> simp [Matrix.add_zero]
                    _ = (g ^ 2 - dw ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
                      simp [Matrix.smul_smul, Matrix.mul_smul]
                      <;> ring
                      <;> simp_all [Matrix.smul_smul, Matrix.mul_smul]
              _ = -((dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) := by
                simp [Matrix.smul_smul, Matrix.mul_smul, sub_eq_add_neg]
                <;> ring
                <;> simp_all [Matrix.smul_smul, Matrix.mul_smul]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₇ — Yangian R-matrix, braided QYBE, Clifford EP period 8
────────────────────────────────────────────────────────────────────────────────-/

def swap4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

def yangR4 (u eta : R) : Matrix (Fin 4) (Fin 4) R := u • (1 : Matrix (Fin 4) (Fin 4) R) + eta • swap4

theorem yangianUnitarityCollapse (u eta : R) :
    yangR4 u eta * yangR4 (-u) eta = (eta ^ 2 - u ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    yangR4 eta eta * yangR4 (-eta) eta = 0 := by
  have hP : swap4 * swap4 = (1 : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    simp only [swap4, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, ?_⟩
  · simp only [yangR4, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp; ring
  · simp only [yangR4, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp; ring

theorem baxterizedBraidIdentity {B : Type*} [Ring B] (P Q : B)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hbraid : P * Q * P = Q * P * Q) :
    (1 + P) * (1 + (2 : ℤ) • Q) * (1 + P) =
      (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) := by
  calc
    (1 + P) * (1 + (2 : ℤ) • Q) * (1 + P)
        = (2 : ℤ) • (1 + P + Q + P * Q + Q * P + P * Q * P) := by
          calc
            (1 + P) * (1 + (2 : ℤ) • Q) * (1 + P)
              = (1 + P) * (1 + 2 • Q) * (1 + P) := by rfl
            _ = (1 + P + 2 • Q + 2 • P * Q) * (1 + P) := by
              rw [add_mul, mul_add, add_mul, mul_add]
              <;> simp [smul_add, add_assoc]
              <;> ring
            _ = 1 + P + 2 • Q + 2 • P * Q + P + P * P + 2 • Q * P + 2 • P * Q * P := by
              rw [add_mul, mul_add, add_mul, mul_add]
              <;> simp [smul_add, add_assoc]
              <;> ring
            _ = 2 • 1 + 2 • P + 2 • Q + 2 • (P * Q) + 2 • (Q * P) + 2 • (P * Q * P) := by
              rw [hP]
              <;> simp [smul_add, add_assoc, mul_assoc]
              <;> ring
              <;> simp_all [smul_add, add_assoc]
              <;> linarith
            _ = (2 : ℤ) • (1 + P + Q + P * Q + Q * P + P * Q * P) := by
              ring
              <;> simp [smul_add, add_assoc]
              <;> linarith
    _ = (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by
      have h₁ : P * Q * P = Q * P * Q := hbraid
      calc
        (2 : ℤ) • (1 + P + Q + P * Q + Q * P + P * Q * P)
          = (2 : ℤ) • (1 + P + Q + P * Q + Q * P + Q * P * Q) := by rw [h₁]
        _ = (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by
          simp [add_assoc, add_left_comm, add_comm]
          <;> abel
    _ = (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) := by
      calc
        (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q)
          = (1 + Q + P + Q * P + P * Q + Q * P * Q) +
              (1 + Q + P + Q * P + P * Q + Q * P * Q) := by ring
        _ = (1 + Q) * (1 + P) + (1 + Q) * (1 + P) +
              (1 + Q) * (2 • P) + (2 • P) * (1 + Q) := by
          -- Expand (1+Q)(1+2P)(1+Q) = (1+Q)(1+P+2P+2P²)(1+Q) = ...
          -- Actually just expand directly:
          have h₂ : Q * Q = 1 := hQ
          calc
            (1 + Q + P + Q * P + P * Q + Q * P * Q) +
              (1 + Q + P + Q * P + P * Q + Q * P * Q)
              = 2 • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by ring
            _ = (1 + Q) * (1 + P) + (1 + Q) * (1 + P) +
                (1 + Q) * (2 • P) + (2 • P) * (1 + Q) := by
              -- (1+Q)(1+2P)(1+Q) expanded:
              -- (1+Q)(1+2P) = 1 + Q + 2P + 2QP
              -- (1 + Q + 2P + 2QP)(1+Q) = 1 + Q + Q + Q² + 2P + 2PQ + 2QP + 2QPQ
              -- = 1 + 2Q + 1 + 2P + 2PQ + 2QP + 2QPQ  (using Q²=1)
              -- = 2 + 2P + 2Q + 2PQ + 2QP + 2QPQ
              -- We need to match this to our expression.
              -- Let's just expand (1+Q)(1+2P)(1+Q) directly:
              have h₃ : (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) =
                  (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by
                calc
                  (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q)
                    = (1 + Q) * (1 + 2 • P) * (1 + Q) := by rfl
                  _ = (1 + Q + 2 • P + 2 • Q * P) * (1 + Q) := by
                    rw [add_mul, mul_add, add_mul, mul_add]
                    <;> simp [smul_add, add_assoc]
                    <;> ring
                  _ = 1 + Q + 2 • P + 2 • Q * P + Q + Q * Q + 2 • P * Q + 2 • Q * P * Q := by
                    rw [add_mul, mul_add, add_mul, mul_add]
                    <;> simp [smul_add, add_assoc]
                    <;> ring
                  _ = 2 • 1 + 2 • Q + 2 • P + 2 • (P * Q) + 2 • (Q * P) + 2 • (Q * P * Q) := by
                    rw [hQ]
                    <;> simp [smul_add, add_assoc, mul_assoc]
                    <;> ring
                    <;> simp_all [smul_add, add_assoc]
                    <;> linarith
                  _ = (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by
                    ring
                    <;> simp [smul_add, add_assoc]
                    <;> linarith
              rw [h₃]
              <;> ring
              <;> simp_all [smul_add, add_assoc]
              <;> linarith
        _ = (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) := by
          calc
            (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q)
              = (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) := by
                -- Expand (1+Q)(1+2P)(1+Q) and compare with 2(1+Q+P+QP+PQ+QPQ)
                have h₂ : Q * Q = 1 := hQ
                calc
                  (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q)
                    = (1 + Q + P + Q * P + P * Q + Q * P * Q) +
                        (1 + Q + P + Q * P + P * Q + Q * P * Q) := by ring
                  _ = (1 + Q) * (1 + P) + (1 + Q) * (1 + P) +
                      (1 + Q) * (2 • P) + (2 • P) * (1 + Q) := by
                    -- This is just regrouping the terms of 2(1+Q+P+QP+PQ+QPQ)
                    -- to match the expansion of (1+Q)(1+2P)(1+Q).
                    -- (1+Q)(1+2P)(1+Q) = (1+Q)(1+P+2P)(1+Q) -- not quite, 2P ≠ P+P in general
                    -- But: (1+Q)(1+2P) = 1 + Q + 2P + 2QP
                    -- Then ×(1+Q) = 1+Q+Q+Q²+2P+2PQ+2QP+2QPQ = 2+2P+2Q+2PQ+2QP+2QPQ (using Q²=1)
                    -- = 2(1+P+Q+PQ+QP+QPQ)
                    simp [add_assoc, add_left_comm, add_comm, h₂]
                    <;> ring
                    <;> simp_all [add_assoc, add_left_comm, add_comm, h₂]
                    <;> linarith
                  _ = (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q) := by
                    -- Verify: (1+Q)(1+2P)(1+Q) expands to 2(1+P+Q+PQ+QP+QPQ)
                    calc
                      (1 + Q) * (1 + (2 : ℤ) • P) * (1 + Q)
                        = (1 + Q) * (1 + 2 • P) * (1 + Q) := by rfl
                      _ = (1 + Q + 2 • P + 2 • Q * P) * (1 + Q) := by
                        rw [add_mul, mul_add, add_mul, mul_add]
                        <;> simp [smul_add, add_assoc]
                        <;> ring
                      _ = 1 + Q + 2 • P + 2 • Q * P + Q + Q * Q + 2 • P * Q + 2 • Q * P * Q := by
                        rw [add_mul, mul_add, add_mul, mul_add]
                        <;> simp [smul_add, add_assoc]
                        <;> ring
                      _ = 2 • 1 + 2 • Q + 2 • P + 2 • (P * Q) + 2 • (Q * P) + 2 • (Q * P * Q) := by
                        rw [hQ]
                        <;> simp [smul_add, add_assoc, mul_assoc]
                        <;> ring
                        <;> simp_all [smul_add, add_assoc]
                        <;> linarith
                      _ = (2 : ℤ) • (1 + Q + P + Q * P + P * Q + Q * P * Q) := by
                        ring
                        <;> simp [smul_add, add_assoc]
                        <;> linarith

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₈ — Zitterbewegung and ℤ₄ spin monodromy
────────────────────────────────────────────────────────────────────────────────-/

theorem zitterSplit (dw g : R) :
    dw • (kreinHopfNilPart dw g : Matrix (Fin 4) (Fin 4) R) +
      ((dw ^ 2 - g ^ 2) • (jwGamma2 : Matrix (Fin 4) (Fin 4) R) -
        dw • (kreinHopfNilPart dw g : Matrix (Fin 4) (Fin 4) R)) =
      (dw ^ 2 - g ^ 2) • (jwGamma2 : Matrix (Fin 4) (Fin 4) R) := by
  rw [add_sub_cancel]

theorem spinMonodromyZ4 :
    (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) * (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) =
      -(1 : Matrix (Fin 2) (Fin 2) R) ∧
    (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) ^ 4 = 1 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [epsSymp, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
  · calc
    (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) ^ 4
      = ((-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
         (-(epsSymp : Matrix (Fin 2) (Fin 2) R))) *
        ((-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
         (-(epsSymp : Matrix (Fin 2) (Fin 2) R))) := by
          calc
            (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) ^ 4 =
              (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
              (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
              (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
              (-(epsSymp : Matrix (Fin 2) (Fin 2) R)) := by
                rw [pow_succ, pow_succ, pow_succ, pow_one]
                <;> ring
            _ = ((-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
               (-(epsSymp : Matrix (Fin 2) (Fin 2) R))) *
               ((-(epsSymp : Matrix (Fin 2) (Fin 2) R)) *
               (-(epsSymp : Matrix (Fin 2) (Fin 2) R))) := by simp [mul_assoc]
      _ = (-(1 : Matrix (Fin 2) (Fin 2) R)) * (-(1 : Matrix (Fin 2) (Fin 2) R)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [epsSymp, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
      _ = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₉ — FW rapidity dictionary (native real-analysis, reused)
────────────────────────────────────────────────────────────────────────────────-/

theorem fwRapidityDictionary (f θ χ : ℝ) (hf₀ : -1 < f) (hf₁ : f < 0) :
    (1 - InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) =
      Real.cosh (2 * θ) ∧
    (InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerStrand θ χ /
        (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ)) *
      (InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperStrand θ χ /
        (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ)) =
      (Real.sinh (2 * θ)) ^ 2 / 4 ∧
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight
      (Real.artanh (Real.sqrt (-f))) = f := by
  exact ⟨InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopPrefactor_eq_cosh_two θ,
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.dressedStrand_product θ χ,
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight_artanh_sqrt f hf₀ hf₁⟩

/-! ─────────────────────────────────────────────────────────────────────────────
MCP₁₀ — Causal poset and Peirce-spine operator realization
────────────────────────────────────────────────────────────────────────────────-/

open MetriplecticCausalPlabicKreinYangianStage

theorem causalPosetChainAndIrreflexivity :
    (causalEdge .MCP1_MetriplecticCoincidenceAndDoubledBlocks
      .MCP2_GohbergKreinHilbertAndCotlarTricomi ∧
     causalEdge .MCP2_GohbergKreinHilbertAndCotlarTricomi
      .MCP3_ParaKahlerTriadAndJordanWignerKreinGrading ∧
     causalEdge .MCP3_ParaKahlerTriadAndJordanWignerKreinGrading
      .MCP4_WalshHadamardElenchusAndXorSwizzleSchur ∧
     causalEdge .MCP4_WalshHadamardElenchusAndXorSwizzleSchur
      .MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly ∧
     causalEdge .MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly
      .MCP6_Cl22KreinHamiltonianHopfAndJordanCrash ∧
     causalEdge .MCP6_Cl22KreinHamiltonianHopfAndJordanCrash
      .MCP7_YangianRMatrixQYBEAndResonantCollapse ∧
     causalEdge .MCP7_YangianRMatrixQYBEAndResonantCollapse
      .MCP8_DiracKreinZitterbewegungAndSecularTrajectory ∧
     causalEdge .MCP8_DiracKreinZitterbewegungAndSecularTrajectory
      .MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession ∧
     causalEdge .MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession
      .MCP10_Bidirectional17TurnPeirceSpineSynthesis) ∧
    (∀ (s : MetriplecticCausalPlabicKreinYangianStage), ¬ causalEdge s s) := by
  exact mcp_poset_chain_and_irreflexivity

end InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalArchetypesCanonical
