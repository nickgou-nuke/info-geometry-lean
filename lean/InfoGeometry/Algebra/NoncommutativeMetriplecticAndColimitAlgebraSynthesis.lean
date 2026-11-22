/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.MatrixNoncommutativity

/-!
# Noncommutative Metriplectic Dynamics & The Quotient ★-Algebra Cl_∞(A)

Formalizes four causally ordered archetypes (MA₁–MA₄) over an arbitrary
noncommutative ring `[Ring A]` and ★-ring `[Ring A] [StarRing A]`:
- `MA₁`: Universal noncommutative metriplectic dynamics & positive-cone entropy production
- `MA₂`: All-scales metriplectic eigenmode law & Bott colimit stability on `ClTower A n`
- `MA₃`: Quotient ★-involution, negation & ★-covariant trace/supertrace on `ClInf A`
- `MA₄`: Cross-scale binary alignment (`alignL`, `alignR`) & quotient compatibility
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive ★-Tower `ClTower A n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Archetype MA₁: Universal Noncommutative Metriplectic Dynamics & Positive-Cone Entropy Production
-/

section ArchetypeMA1_UniversalMetriplecticDynamics

variable {R : Type*} [Ring R]

/-- Reversible Hamiltonian commutator flow `J_H(ρ) = ⁅H, ρ⁆`. -/
def hamFlow (H ρ : R) : R := ⁅H, ρ⁆

/-- Irreversible Lindblad double-commutator dissipator `D_L(ρ) = -⁅L, ⁅L, ρ⁆⁆`. -/
def lindbladFlow (L ρ : R) : R := -⁅L, ⁅L, ρ⁆⁆

/-- Full noncommutative metriplectic evolution operator `M_{H, L}(ρ) = ⁅H, ρ⁆ - ⁅L, ⁅L, ρ⁆⁆`. -/
def metriplecticFlow (H L ρ : R) : R :=
  hamFlow H ρ + lindbladFlow L ρ

/-- **Universal Noncommutative Metriplectic Conservation & Positive-Cone Entropy Production (MA₁)**:
1. *Reversible Conservation*: `ρ * J_H(ρ) + J_H(ρ) * ρ = ⁅H, ρ * ρ⁆`,
2. *Irreversible Positive-Cone Entropy Production*: For `star L = L` and `star ρ = ρ`,
   `-(ρ * D_L(ρ)) = star ⁅L, ρ⁆ * ⁅L, ρ⁆ + ⁅L, ρ * ⁅L, ρ⁆⁆`,
3. *Casimir Stationarity*: If `⁅H, C⁆ = 0` and `⁅L, C⁆ = 0`, then `M_{H, L}(C) = 0`. -/
theorem universal_metriplectic_conservation_and_entropy_production [StarRing R]
    (H L ρ C : R) (hL_sa : star L = L) (hρ_sa : star ρ = ρ)
    (hHC : ⁅H, C⁆ = 0) (hLC : ⁅L, C⁆ = 0) :
    ρ * hamFlow H ρ + hamFlow H ρ * ρ = ⁅H, ρ * ρ⁆ ∧
    -(ρ * lindbladFlow L ρ) = star ⁅L, ρ⁆ * ⁅L, ρ⁆ + ⁅L, ρ * ⁅L, ρ⁆⁆ ∧
    metriplecticFlow H L C = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [hamFlow]; simp only [Ring.lie_def]; noncomm_ring
  · dsimp [lindbladFlow]
    simp only [Ring.lie_def, star_sub, star_mul, hL_sa, hρ_sa]
    noncomm_ring
  · dsimp [metriplecticFlow, hamFlow, lindbladFlow]
    rw [hHC, hLC, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero, add_zero]

end ArchetypeMA1_UniversalMetriplecticDynamics

/-!
## Inductive ★-Tower `ClTower A n` & Core Operators
-/

universe u

abbrev ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => mat2 (towerScalar n a) 0 0 (towerScalar n a)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      change towerTrace (0 : ClTower A n) + towerTrace (0 : ClTower A n) = 0
      rw [towerTrace_zero n, add_zero]

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      change towerTrace (-(X 0 0)) + towerTrace (-(X 1 1)) =
        -(towerTrace (X 0 0) + towerTrace (X 1 1))
      rw [towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_star [StarRing A] : ∀ {n : ℕ} (M : ClTower A n),
    towerTrace (star M) = star (towerTrace M)
  | 0,     _ => rfl
  | _ + 1, M => by
      change towerTrace (star (M 0 0)) + towerTrace (star (M 1 1)) =
        star (towerTrace (M 0 0) + towerTrace (M 1 1))
      rw [towerTrace_star, towerTrace_star, star_add]

lemma chiralityOp_selfAdjoint [StarRing A] : ∀ (n : ℕ),
    star (chiralityOp n : ClTower A n) = chiralityOp n
  | 0     => star_one A
  | n + 1 => by
      apply ext_fin2 <;> simp [chiralityOp, star_neg, chiralityOp_selfAdjoint n]

lemma towerTrace_chirality_mul_comm : ∀ {n : ℕ} (X : ClTower A n),
    towerTrace (X * chiralityOp n) = towerTrace (chiralityOp n * X)
  | 0,     X => by
      change X * (1 : A) = (1 : A) * X
      rw [mul_one, one_mul]
  | n + 1, X => by
      dsimp [towerTrace, chiralityOp]
      simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, towerTrace_neg]
      rw [towerTrace_chirality_mul_comm (X 0 0), towerTrace_chirality_mul_comm (X 1 1)]

lemma superTrace_star [StarRing A] {n : ℕ} (M : ClTower A n) :
    superTrace (star M) = star (superTrace M) := by
  dsimp [superTrace]
  rw [← towerTrace_star, star_mul, chiralityOp_selfAdjoint n, towerTrace_chirality_mul_comm]

/-!
## Archetype MA₂: All-Scales Metriplectic Eigenmode Law & Colimit Stability on `ClTower A n`
-/

section ArchetypeMA2_AllScalesMetriplecticEigenmodes

lemma bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma cantorProj_idem : ∀ (n : ℕ), cantorProj n * cantorProj n = (cantorProj n : ClTower A n)
  | 0     => mul_one 1
  | n + 1 => by dsimp [cantorProj]; rw [← bottEmbed_mul, cantorProj_idem n]

lemma towerScalar_add (n : ℕ) (a b : A) :
    towerScalar n (a + b) = towerScalar n a + towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, Matrix.add_apply, ih]

lemma towerScalar_sub (n : ℕ) (a b : A) :
    towerScalar n (a - b) = towerScalar n a - towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, Matrix.sub_apply, ih]

lemma towerScalar_mul (n : ℕ) (a b : A) :
    towerScalar n (a * b) = towerScalar n a * towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, Matrix.mul_apply, Fin.sum_univ_two, ih]

lemma towerScalar_comm_cantorProj (n : ℕ) (a : A) :
    towerScalar n a * cantorProj n = cantorProj n * towerScalar n a := by
  induction' n with m ih
  · change a * (1 : A) = (1 : A) * a
    rw [mul_one, one_mul]
  · apply ext_fin2 <;> simp [towerScalar, cantorProj, bottEmbed, Matrix.mul_apply, Fin.sum_univ_two, ih]

lemma towerScalar_bottEmbed (n : ℕ) (a : A) (X : ClTower A n) :
    towerScalar (n + 1) a * bottEmbed X = bottEmbed (towerScalar n a * X) := by
  apply ext_fin2 <;> simp [towerScalar, bottEmbed, Matrix.mul_apply, Fin.sum_univ_two]

def massGapOp (a : A) (n : ℕ) : ClTower A n :=
  towerScalar n a * (1 - cantorProj n)

def coherenceMode (n : ℕ) (X : ClTower A n) : ClTower A n :=
  (1 - cantorProj n) * X * cantorProj n

lemma massGapOp_comm_coherence (a : A) (n : ℕ) (Φ : ClTower A n)
    (hL : cantorProj n * Φ = 0) (hR : Φ * cantorProj n = Φ) :
    ⁅massGapOp a n, Φ⁆ = towerScalar n a * Φ := by
  have hP := cantorProj_idem (A := A) n
  have h_left : massGapOp a n * Φ = towerScalar n a * Φ := by
    dsimp [massGapOp]
    calc towerScalar n a * (1 - cantorProj n) * Φ
      _ = towerScalar n a * Φ - towerScalar n a * (cantorProj n * Φ) := by noncomm_ring
      _ = towerScalar n a * Φ := by rw [hL, mul_zero, sub_zero]
  have h_ann_L : cantorProj n * massGapOp a n = 0 := by
    dsimp [massGapOp]
    calc cantorProj n * (towerScalar n a * (1 - cantorProj n))
      _ = (cantorProj n * towerScalar n a) * (1 - cantorProj n) := by noncomm_ring
      _ = (towerScalar n a * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n a]
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  have h_right : Φ * massGapOp a n = 0 := by
    calc Φ * massGapOp a n = (Φ * cantorProj n) * massGapOp a n := by rw [hR]
      _ = Φ * (cantorProj n * massGapOp a n) := by noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  rw [Ring.lie_def, h_left, h_right, sub_zero]

/-- **All-Scales Metriplectic Eigenmode & Colimit Stability Theorem (MA₂)**:
For `H_n = massGapOp ω₀ n` and `L_n = massGapOp m₀ n` on `ClTower A n`:
1. `metriplecticFlow H_n L_n (cantorProj n) = 0` (vacuum Casimir stationarity),
2. `metriplecticFlow H_n L_n (coherenceMode n X) = towerScalar n (ω₀ - m₀ * m₀) * coherenceMode n X`,
3. `metriplecticFlow H_{n+1} L_{n+1} (bottEmbed (coherenceMode n X)) = bottEmbed (metriplecticFlow H_n L_n (coherenceMode n X))`. -/
theorem all_scales_metriplectic_eigenmode_and_colimit_stability
    (ω₀ m₀ : A) (n : ℕ) (X : ClTower A n) :
    let H_n   := massGapOp ω₀ n
    let L_n   := massGapOp m₀ n
    let H_n1  := massGapOp ω₀ (n + 1)
    let L_n1  := massGapOp m₀ (n + 1)
    let Ψ_coh := coherenceMode n X
    metriplecticFlow H_n L_n (cantorProj n) = 0 ∧
    metriplecticFlow H_n L_n Ψ_coh = towerScalar n (ω₀ - m₀ * m₀) * Ψ_coh ∧
    metriplecticFlow H_n1 L_n1 (bottEmbed Ψ_coh) =
      bottEmbed (metriplecticFlow H_n L_n Ψ_coh) := by
  intro H_n L_n H_n1 L_n1 Ψ_coh
  have hP := cantorProj_idem (A := A) n
  have h_vac_comm : ∀ (a : A), ⁅massGapOp a n, (cantorProj n : ClTower A n)⁆ = 0 := by
    intro a; rw [Ring.lie_def]; dsimp [massGapOp]
    calc towerScalar n a * (1 - cantorProj n) * cantorProj n -
         cantorProj n * (towerScalar n a * (1 - cantorProj n))
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) -
          (cantorProj n * towerScalar n a) * (1 - cantorProj n) := by noncomm_ring
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) -
          (towerScalar n a * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n a]
      _ = 0 := by
          rw [hP, sub_self, mul_zero, zero_sub, neg_eq_zero, mul_sub, mul_one, mul_assoc, hP, sub_self]
  have hL_Ψ : cantorProj n * Ψ_coh = 0 := by
    dsimp [Ψ_coh, coherenceMode]
    calc cantorProj n * ((1 - cantorProj n) * X * cantorProj n)
      _ = (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, zero_mul, zero_mul]
  have hR_Ψ : Ψ_coh * cantorProj n = Ψ_coh := by
    dsimp [Ψ_coh, coherenceMode]
    calc (1 - cantorProj n) * X * cantorProj n * cantorProj n
      _ = (1 - cantorProj n) * X * (cantorProj n * cantorProj n) := by noncomm_ring
      _ = Ψ_coh := by rw [hP]; rfl
  have hL_mΨ : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
    calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
      _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
      _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
          rw [← towerScalar_comm_cantorProj n m₀]
      _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
      _ = 0 := by rw [hL_Ψ, mul_zero]
  have hR_mΨ : (towerScalar n m₀ * Ψ_coh) * cantorProj n = towerScalar n m₀ * Ψ_coh := by
    rw [mul_assoc, hR_Ψ]
  have h_eig_n : metriplecticFlow H_n L_n Ψ_coh = towerScalar n (ω₀ - m₀ * m₀) * Ψ_coh := by
    dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n, L_n]
    rw [massGapOp_comm_coherence ω₀ n Ψ_coh hL_Ψ hR_Ψ,
        massGapOp_comm_coherence m₀ n Ψ_coh hL_Ψ hR_Ψ,
        massGapOp_comm_coherence m₀ n (towerScalar n m₀ * Ψ_coh) hL_mΨ hR_mΨ,
        ← mul_assoc, ← towerScalar_mul, towerScalar_sub, sub_mul]
    abel
  refine ⟨?_, h_eig_n, ?_⟩
  · dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n, L_n]
    rw [h_vac_comm ω₀, h_vac_comm m₀, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero, add_zero]
  · have hL_b : cantorProj (n + 1) * bottEmbed Ψ_coh = 0 := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, hL_Ψ]; apply ext_fin2 <;> rfl
    have hR_b : bottEmbed Ψ_coh * cantorProj (n + 1) = bottEmbed Ψ_coh := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, hR_Ψ]
    have hL_mb : cantorProj (n + 1) * (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) = 0 := by
      rw [towerScalar_bottEmbed]; dsimp [cantorProj]; rw [← bottEmbed_mul, hL_mΨ]
      apply ext_fin2 <;> rfl
    have hR_mb : (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) * cantorProj (n + 1) =
        towerScalar (n + 1) m₀ * bottEmbed Ψ_coh := by
      rw [mul_assoc, hR_b]
    rw [h_eig_n, ← towerScalar_bottEmbed]
    dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n1, L_n1]
    rw [massGapOp_comm_coherence ω₀ (n + 1) (bottEmbed Ψ_coh) hL_b hR_b,
        massGapOp_comm_coherence m₀ (n + 1) (bottEmbed Ψ_coh) hL_b hR_b,
        massGapOp_comm_coherence m₀ (n + 1) (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) hL_mb hR_mb,
        ← mul_assoc, ← towerScalar_mul, towerScalar_sub, sub_mul]
    abel

end ArchetypeMA2_AllScalesMetriplecticEigenmodes

/-!
## Archetype MA₃ & MA₄: Quotient ★-Algebra Operations & Cross-Scale Binary Alignment on `ClInf A`
-/

section ArchetypeMA3_MA4_ColimitQuotientStarAlgebra

def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

lemma bottEmbed_neg {n : ℕ} (X : ClTower A n) :
    bottEmbed (-X) = -bottEmbed X := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_neg {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (-X) = -bottEmbedIter k X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_neg]

lemma bottEmbed_star [StarRing A] {n : ℕ} (X : ClTower A n) :
    bottEmbed (star X) = star (bottEmbed X) := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_star [StarRing A] {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (star X) = star (bottEmbedIter k X) := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_star]

lemma colimit_towerTrace_invariant {n : ℕ} (X : ClTower A n) :
    towerTrace (bottEmbed X) = towerTrace X := by
  dsimp [towerTrace, bottEmbed]; rw [towerTrace_zero n, add_zero]

lemma colimit_towerTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    towerTrace (bottEmbedIter k X) = towerTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [colimit_towerTrace_invariant, ih]

lemma colimit_superTrace_invariant {n : ℕ} (X : ClTower A n) :
    superTrace (bottEmbed X) = superTrace X := by
  dsimp [superTrace, bottEmbed, chiralityOp, towerTrace]; simp [towerTrace_zero n]

lemma colimit_superTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    superTrace (bottEmbedIter k X) = superTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [colimit_superTrace_invariant, ih]

lemma bottEmbed_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbed X) (bottEmbed Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma bottEmbedIter_congr_heq {m₁ m₂ : ℕ} (d : ℕ) {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbedIter d X) (bottEmbedIter d Y) := by
  induction' d with d ih
  · exact h_heq
  · exact bottEmbed_congr_heq (congrArg (· + d) h_dim) ih

lemma bottEmbedIter_add_heq {n : ℕ} (k d : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (k + d) X) (bottEmbedIter d (bottEmbedIter k X)) := by
  induction' d with d ih
  · exact HEq.rfl
  · exact bottEmbed_congr_heq (Nat.add_assoc n k d).symm ih

lemma bottEmbedIter_comm_heq {n : ℕ} (a b : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (a + b) X) (bottEmbedIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

def ClInfRel (u v : Σ n : ℕ, ClTower A n) : Prop :=
  ∃ (k₁ k₂ : ℕ), u.1 + k₁ = v.1 + k₂ ∧
    HEq (bottEmbedIter k₁ u.2) (bottEmbedIter k₂ v.2)

theorem clInfRel_trans {u v w : Σ n : ℕ, ClTower A n}
    (huv : ClInfRel u v) (hvw : ClInfRel v w) : ClInfRel u w := by
  rcases huv with ⟨k₁, k₂, h12, heq12⟩
  rcases hvw with ⟨l₁, l₂, h23, heq23⟩
  refine ⟨k₁ + l₁, l₂ + k₂, by omega, ?_⟩
  exact (bottEmbedIter_add_heq k₁ l₁ u.2).trans <|
    (bottEmbedIter_congr_heq l₁ h12 heq12).trans <|
    (bottEmbedIter_add_heq k₂ l₁ v.2).symm.trans <|
    (bottEmbedIter_comm_heq k₂ l₁ v.2).trans <|
    (bottEmbedIter_add_heq l₁ k₂ v.2).trans <|
    (bottEmbedIter_congr_heq k₂ h23 heq23).trans <|
    (bottEmbedIter_add_heq l₂ k₂ w.2).symm

instance clInfSetoid (A : Type u) [Ring A] : Setoid (Σ n : ℕ, ClTower A n) where
  r := ClInfRel
  iseqv := {
    refl  := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm  := fun ⟨k₁, k₂, h, heq⟩ => ⟨k₂, k₁, h.symm, heq.symm⟩
    trans := clInfRel_trans
  }

abbrev ClInf (A : Type u) [Ring A] := Quotient (clInfSetoid A)

def toClInf (n : ℕ) (X : ClTower A n) : ClInf A :=
  Quotient.mk (clInfSetoid A) ⟨n, X⟩

lemma neg_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) : HEq (-X) (-Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma star_congr_heq [StarRing A] {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) : HEq (star X) (star Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

/-- Quotient-lifted negation on `ClInf A`. -/
def clInfNeg : ClInf A → ClInf A :=
  Quotient.map (fun u => ⟨u.1, -u.2⟩) (by
    rintro u v ⟨k₁, k₂, h_dim, h_heq⟩
    refine ⟨k₁, k₂, h_dim, ?_⟩
    dsimp
    rw [bottEmbedIter_neg, bottEmbedIter_neg]
    exact neg_congr_heq h_dim h_heq)

/-- Quotient-lifted ★-involution on `ClInf A`. -/
def clInfStar [StarRing A] : ClInf A → ClInf A :=
  Quotient.map (fun u => ⟨u.1, star u.2⟩) (by
    rintro u v ⟨k₁, k₂, h_dim, h_heq⟩
    refine ⟨k₁, k₂, h_dim, ?_⟩
    dsimp
    rw [bottEmbedIter_star, bottEmbedIter_star]
    exact star_congr_heq h_dim h_heq)

lemma trace_eq_of_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    towerTrace X = towerTrace Y ∧ superTrace X = superTrace Y := by
  subst h_dim; cases eq_of_heq h_heq; exact ⟨rfl, rfl⟩

/-- Quotient-lifted ungraded trace `Tr_∞ : ClInf A → A`. -/
def clInfTrace : ClInf A → A :=
  Quotient.lift (fun u => towerTrace u.2) (fun u v ⟨k₁, k₂, h_dim, h_heq⟩ => by
    calc towerTrace u.2
      _ = towerTrace (bottEmbedIter k₁ u.2) := (colimit_towerTrace_iter_invariant k₁ u.2).symm
      _ = towerTrace (bottEmbedIter k₂ v.2) := (trace_eq_of_heq h_dim h_heq).1
      _ = towerTrace v.2                    := colimit_towerTrace_iter_invariant k₂ v.2)

/-- Quotient-lifted Atiyah–Singer supertrace `Str_∞ : ClInf A → A`. -/
def clInfSuperTrace : ClInf A → A :=
  Quotient.lift (fun u => superTrace u.2) (fun u v ⟨k₁, k₂, h_dim, h_heq⟩ => by
    calc superTrace u.2
      _ = superTrace (bottEmbedIter k₁ u.2) := (colimit_superTrace_iter_invariant k₁ u.2).symm
      _ = superTrace (bottEmbedIter k₂ v.2) := (trace_eq_of_heq h_dim h_heq).2
      _ = superTrace v.2                    := colimit_superTrace_iter_invariant k₂ v.2)

/-- Canonical scale-aligned binary representatives in `ClTower A (n₁ + n₂)`. -/
def alignL (u v : Σ n : ℕ, ClTower A n) : ClTower A (u.1 + v.1) :=
  bottEmbedIter v.1 u.2

def alignR (u v : Σ n : ℕ, ClTower A n) : ClTower A (u.1 + v.1) :=
  Nat.add_comm v.1 u.1 ▸ bottEmbedIter u.1 v.2

/-- **Quotient ★-Algebra & Cross-Scale Binary Alignment Theorem (MA₃ & MA₄)**:
On `ClInf A = Quotient (clInfSetoid A)`:
1. `clInfNeg` and `clInfStar` are involutions,
2. `clInfSuperTrace (clInfNeg x) = -clInfSuperTrace x`,
   `clInfTrace (clInfStar x) = star (clInfTrace x)`, and
   `clInfSuperTrace (clInfStar x) = star (clInfSuperTrace x)`,
3. For any two elements `u = ⟨n₁, X₁⟩` and `v = ⟨n₂, X₂⟩`, the common-scale
   representatives `alignL u v`, `alignR u v` in `ClTower A (n₁ + n₂)`
   project in `ClInf A` to `toClInf u.1 u.2` and `toClInf v.1 v.2` respectively. -/
theorem clInf_star_algebra_and_binary_alignment_properties [StarRing A]
    (x : ClInf A) (u v : Σ n : ℕ, ClTower A n) :
    clInfNeg (clInfNeg x) = x ∧
    clInfStar (clInfStar x) = x ∧
    clInfSuperTrace (clInfNeg x) = -clInfSuperTrace x ∧
    clInfTrace (clInfStar x) = star (clInfTrace x) ∧
    clInfSuperTrace (clInfStar x) = star (clInfSuperTrace x) ∧
    toClInf (u.1 + v.1) (alignL u v) = toClInf u.1 u.2 ∧
    toClInf (u.1 + v.1) (alignR u v) = toClInf v.1 v.2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Quotient.inductionOn x (fun w => ?_)
    change Quotient.mk (clInfSetoid A) ⟨w.1, -(-w.2)⟩ = Quotient.mk (clInfSetoid A) w
    rw [neg_neg]
  · refine Quotient.inductionOn x (fun w => ?_)
    change Quotient.mk (clInfSetoid A) ⟨w.1, star (star w.2)⟩ = Quotient.mk (clInfSetoid A) w
    rw [star_star]
  · refine Quotient.inductionOn x (fun w => ?_)
    change superTrace (-w.2) = -superTrace w.2
    dsimp [superTrace]
    rw [mul_neg, towerTrace_neg]
  · refine Quotient.inductionOn x (fun w => ?_)
    dsimp [clInfTrace, clInfStar]
    exact towerTrace_star w.2
  · refine Quotient.inductionOn x (fun w => ?_)
    dsimp [clInfSuperTrace, clInfStar]
    exact superTrace_star w.2
  · apply Quotient.sound
    exact ⟨0, v.1, Nat.add_zero _, HEq.rfl⟩
  · apply Quotient.sound
    refine ⟨0, u.1, by simp [Nat.add_comm], ?_⟩
    dsimp [alignR, bottEmbedIter]
    exact eqRec_heq (Nat.add_comm v.1 u.1) (bottEmbedIter u.1 v.2)

end ArchetypeMA3_MA4_ColimitQuotientStarAlgebra

end InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis
