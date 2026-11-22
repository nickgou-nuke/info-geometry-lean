/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.DahmPluckerKleinCollineation

/-!
# `sl₄ ≅ so(Klein form)`: the full Lie algebra isomorphism on Plücker space

This module constructs, with all generators and the full bracket, the classical
isomorphism behind Dahm's projective unification:

* `lam2 X` is the derivation induced by a `4 × 4` matrix `X` on `Λ²R⁴`, written
  in the owner's Plücker order `(p01, p02, p03, p12, p13, p23)` with the owner's
  column convention.  `lam2_mulVec_wedge` ties it to `Vec4.wedge` and `act`:
  `Λ²X (u ∧ v) = Xu ∧ v + u ∧ Xv`.
* `lam2` is `R`-linear and a Lie homomorphism on **all** of `gl₄`
  (`lam2_lie`), and `(Λ²X)ᵀ G + G Λ²X = (tr X) • G` for the Klein polar Gram
  matrix `G = kleinGram` (`lam2_kleinGram`).
* Restricted to `sl₄` it lands in Mathlib's `skewAdjointMatricesLieSubalgebra G`
  (`lam2Hom`).  Over a field of characteristic zero an explicit inverse `psi`
  (CAS-derived) gives `psi ∘ lam2 = id` on `gl₄` and `lam2 ∘ psi = id` on
  `so(G)`, so `sl₄(K) ≃ₗ⁅K⁆ so(G)` (`sl4EquivSoKlein`).
* Signature: with the integer matrix `kleinCongruence`, `Sᵀ G S = 2 • D`,
  `D = diag(1,-1,1,-1,1,-1)`; hence `so(G) ≃ₗ⁅K⁆ so(D)` and
  `sl₄(K) ≃ₗ⁅K⁆ so(D)` (`sl4EquivSoSplit`).  For `K = ℝ` this is
  `sl(4,ℝ) ≅ so(3,3)`; the compact and other real forms are separate modules.

All certificates (`psi`, the constraint combinations, `kleinCongruence` and its
inverse) were computed and re-verified in Sage before translation; the CAS script
is recorded in the task artifacts.  Lean re-proves every identity from scratch.
-/

namespace InfoGeometry.Projective.DahmKleinLieIsomorphism

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
The `Λ²` action, its Lie-homomorphism law, Klein-form compatibility, and
characteristic-zero Lie equivalences are proved for the explicit carriers.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The inverse map uses a field of characteristic zero so division by two is
available; the split-signature equivalence uses the displayed congruence.

#### BUCKET 3: OPEN CLOSURE DEBT
Compact real-form identifications and physical interpretations are not
constructed by this module.
-/

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix LieAlgebra
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.DahmPluckerKleinCollineation

section CommRing

variable {R : Type*} [CommRing R]

/-- The off-diagonal matrix unit `E₀₁`. -/
def matrixUnit01 : Matrix (Fin 6) (Fin 6) R := Matrix.single 0 1 1

/-- The opposite off-diagonal matrix unit `E₁₀`. -/
def matrixUnit10 : Matrix (Fin 6) (Fin 6) R := Matrix.single 1 0 1

/-- The ambient endomorphism algebra is genuinely noncommutative whenever its
coefficient ring is nontrivial: `E₀₁E₁₀ = E₀₀` whereas `E₁₀E₀₁ = E₁₁`. -/
theorem matrix_endomorphism_noncommutative [Nontrivial R] :
    matrixUnit01 (R := R) * matrixUnit10 (R := R) ≠
      matrixUnit10 (R := R) * matrixUnit01 (R := R) := by
  have hAB : matrixUnit01 (R := R) * matrixUnit10 (R := R) =
      Matrix.single 0 0 (1 : R) := by
    simp [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same]
  have hBA : matrixUnit10 (R := R) * matrixUnit01 (R := R) =
      Matrix.single 1 1 (1 : R) := by
    simp [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same]
  rw [hAB, hBA]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hone : (1 : R) = 0 := by simpa using h00
  exact one_ne_zero hone

/-- Matrix unit `E₀₁` in the four-dimensional generator algebra. -/
def generatorMatrixUnit01 : Matrix (Fin 4) (Fin 4) R := Matrix.single 0 1 1

/-- Matrix unit `E₁₀` in the four-dimensional generator algebra. -/
def generatorMatrixUnit10 : Matrix (Fin 4) (Fin 4) R := Matrix.single 1 0 1

/-- The `4 × 4` generator algebra is noncommutative over nontrivial `R`. -/
theorem generator_endomorphism_noncommutative [Nontrivial R] :
    generatorMatrixUnit01 (R := R) * generatorMatrixUnit10 (R := R) ≠
      generatorMatrixUnit10 (R := R) * generatorMatrixUnit01 (R := R) := by
  have hAB : generatorMatrixUnit01 (R := R) * generatorMatrixUnit10 (R := R) =
      Matrix.single 0 0 (1 : R) := by
    simp [generatorMatrixUnit01, generatorMatrixUnit10, Matrix.single_mul_single_same]
  have hBA : generatorMatrixUnit10 (R := R) * generatorMatrixUnit01 (R := R) =
      Matrix.single 1 1 (1 : R) := by
    simp [generatorMatrixUnit01, generatorMatrixUnit10, Matrix.single_mul_single_same]
  rw [hAB, hBA]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hone : (1 : R) = 0 := by simpa using h00
  exact one_ne_zero hone

/-- Gram matrix of the Klein polar form `B(P,Q) = Q(P+Q) - Q(P) - Q(Q)` in the owner
Plücker order: `B(e01,e23) = 1`, `B(e02,e13) = -1`, `B(e03,e12) = 1`. -/
def kleinGram : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

/-- Plücker coordinates as a column vector in the owner order. -/
def toVec6 (P : Plucker6 R) : Fin 6 → R := ![P.p01, P.p02, P.p03, P.p12, P.p13, P.p23]

/-- The Gram matrix represents the owner's polar form. -/
theorem polar_eq_kleinGram (P Q : Plucker6 R) :
    Plucker6.polar P Q = toVec6 P ⬝ᵥ (kleinGram *ᵥ toVec6 Q) := by
  rw [Plucker6.polar_formula]
  simp [toVec6, kleinGram, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- The derivation `Λ²X` in the owner Plücker order (column convention). -/
def lam2 (X : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  !![(X 0 0) + (X 1 1), (X 1 2), (X 1 3), -(X 0 2), -(X 0 3), 0;
     (X 2 1), (X 0 0) + (X 2 2), (X 2 3), (X 0 1), 0, -(X 0 3);
     (X 3 1), (X 3 2), (X 0 0) + (X 3 3), 0, (X 0 1), (X 0 2);
     -(X 2 0), (X 1 0), 0, (X 1 1) + (X 2 2), (X 2 3), -(X 1 3);
     -(X 3 0), 0, (X 1 0), (X 3 2), (X 1 1) + (X 3 3), (X 1 2);
     0, -(X 3 0), (X 2 0), -(X 3 1), (X 2 1), (X 2 2) + (X 3 3)]

/-- Orientation check against the owner: `Λ²X (u ∧ v) = Xu ∧ v + u ∧ Xv`. -/
theorem lam2_mulVec_wedge (X : Matrix (Fin 4) (Fin 4) R) (u v : Vec4 R) :
    lam2 X *ᵥ toVec6 (Vec4.wedge u v) =
      toVec6 (Vec4.wedge (act X u) v) + toVec6 (Vec4.wedge u (act X v)) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  ext r
  fin_cases r <;> simp [lam2, toVec6, Vec4.wedge, act, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The induced exterior-square infinitesimal action is additive in its generator. -/
theorem lam2_add (X Y : Matrix (Fin 4) (Fin 4) R) : lam2 (X + Y) = lam2 X + lam2 Y := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lam2] <;> ring

/-- The induced exterior-square infinitesimal action is linear in its generator. -/
theorem lam2_smul (c : R) (X : Matrix (Fin 4) (Fin 4) R) : lam2 (c • X) = c • lam2 X := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lam2] <;> ring

set_option maxHeartbeats 2000000 in
/-- **Lie homomorphism on all of `gl₄`.** -/
theorem lam2_lie (X Y : Matrix (Fin 4) (Fin 4) R) :
    lam2 (X * Y - Y * X) = lam2 X * lam2 Y - lam2 Y * lam2 X := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lam2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 1000000 in
/-- **Klein compatibility:** `(Λ²X)ᵀ G + G Λ²X = (tr X) • G`. -/
theorem lam2_kleinGram (X : Matrix (Fin 4) (Fin 4) R) :
    (lam2 X)ᵀ * kleinGram + kleinGram * lam2 X = X.trace • kleinGram := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lam2, kleinGram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.trace] <;> ring

/-- Trace-free matrices act by Klein-skew-adjoint matrices (Mathlib's convention
`Aᵀ * J = J * (-A)`). -/
theorem lam2_isSkewAdjoint {X : Matrix (Fin 4) (Fin 4) R} (hX : X.trace = 0) :
    (kleinGram : Matrix (Fin 6) (Fin 6) R).IsSkewAdjoint (lam2 X) := by
  have h := lam2_kleinGram X
  rw [hX, zero_smul] at h
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero]
  exact h

/-- Trace-zero generators act by endomorphisms skew-adjoint for the Klein form. -/
theorem lam2_mem {X : Matrix (Fin 4) (Fin 4) R} (hX : X ∈ SpecialLinear.sl (Fin 4) R) :
    lam2 X ∈ skewAdjointMatricesLieSubalgebra (kleinGram : Matrix (Fin 6) (Fin 6) R) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact lam2_isSkewAdjoint (by simpa [SpecialLinear.sl] using hX)

/-- `lam2` as a Lie algebra homomorphism `gl₄ → gl₆`. -/
def lam2LieHom : Matrix (Fin 4) (Fin 4) R →ₗ⁅R⁆ Matrix (Fin 6) (Fin 6) R where
  toFun := lam2
  map_add' := lam2_add
  map_smul' := lam2_smul
  map_lie' {X Y} := by
    rw [Ring.lie_def, Ring.lie_def]
    exact lam2_lie X Y

/-- The Lie algebra homomorphism `sl₄ → so(G)`. -/
def lam2Hom : SpecialLinear.sl (Fin 4) R →ₗ⁅R⁆
    skewAdjointMatricesLieSubalgebra (kleinGram : Matrix (Fin 6) (Fin 6) R) :=
  { toLinearMap :=
      LinearMap.codRestrict
        (skewAdjointMatricesLieSubalgebra (kleinGram : Matrix (Fin 6) (Fin 6) R)).toSubmodule
        (lam2LieHom.toLinearMap.comp (SpecialLinear.sl (Fin 4) R).incl.toLinearMap)
        (fun X => lam2_mem X.2)
    map_lie' := fun {X Y} => Subtype.ext (lam2LieHom.map_lie (X : Matrix (Fin 4) (Fin 4) R) Y) }

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient-field instance of the matrix-unit witness used by the
Klein skew-adjoint endomorphism algebra. -/
theorem field_matrix_endomorphism_noncommutative :
    matrixUnit01 (R := K) * matrixUnit10 (R := K) ≠
      matrixUnit10 (R := K) * matrixUnit01 (R := K) := by
  have hAB : matrixUnit01 (R := K) * matrixUnit10 (R := K) =
      Matrix.single 0 0 (1 : K) := by
    simp [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same]
  have hBA : matrixUnit10 (R := K) * matrixUnit01 (R := K) =
      Matrix.single 1 1 (1 : K) := by
    simp [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same]
  rw [hAB, hBA]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hone : (1 : K) = 0 := by simpa using h00
  exact one_ne_zero hone

/-- Explicit inverse of `lam2` (reads `X` off `Λ²X`; needs `2⁻¹`). -/
def psi (M : Matrix (Fin 6) (Fin 6) K) : Matrix (Fin 4) (Fin 4) K :=
  !![(1/2 : K) * (M 0 0) + (1/2 : K) * (M 1 1) + (-1/2 : K) * (M 3 3), (M 1 3), -(M 0 3), -(M 0 4);
     (M 3 1), (1/2 : K) * (M 0 0) + (-1/2 : K) * (M 1 1) + (1/2 : K) * (M 3 3), (M 0 1), (M 0 2);
     -(M 3 0), (M 1 0), (-1/2 : K) * (M 0 0) + (1/2 : K) * (M 1 1) + (1/2 : K) * (M 3 3), (M 1 2);
     -(M 4 0), (M 2 0), (M 2 1), (-1/2 : K) * (M 0 0) + (1/2 : K) * (M 2 2) + (1/2 : K) * (M 4 4)]

/-- `psi` is a left inverse of `lam2` on all of `gl₄`. -/
theorem psi_lam2 (X : Matrix (Fin 4) (Fin 4) K) : psi (lam2 X) = X := by
  ext k i
  fin_cases k <;> fin_cases i <;> simp [psi, lam2] <;> ring

set_option maxHeartbeats 2000000 in
/-- `psi` is a right inverse of `lam2` on `so(G)`, and lands in `sl₄`. -/
theorem lam2_psi_of_skewAdjoint {M : Matrix (Fin 6) (Fin 6) K}
    (hM : Mᵀ * kleinGram = kleinGram * (-M)) :
    lam2 (psi M) = M ∧ (psi M).trace = 0 := by
  have c00 : (2 : K) * (M 5 0) = 0 := by
    have h00 := congrFun (congrFun hM 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h00
    first | linear_combination h00 | linear_combination -h00
  have c01 : -(M 4 0) + (M 5 1) = 0 := by
    have h01 := congrFun (congrFun hM 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h01
    first | linear_combination h01 | linear_combination -h01
  have c02 : (M 3 0) + (M 5 2) = 0 := by
    have h02 := congrFun (congrFun hM 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h02
    first | linear_combination h02 | linear_combination -h02
  have c03 : (M 2 0) + (M 5 3) = 0 := by
    have h03 := congrFun (congrFun hM 0) 3
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h03
    first | linear_combination h03 | linear_combination -h03
  have c04 : -(M 1 0) + (M 5 4) = 0 := by
    have h04 := congrFun (congrFun hM 0) 4
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h04
    first | linear_combination h04 | linear_combination -h04
  have c05 : (M 0 0) + (M 5 5) = 0 := by
    have h05 := congrFun (congrFun hM 0) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h05
    first | linear_combination h05 | linear_combination -h05
  have c11 : (-2 : K) * (M 4 1) = 0 := by
    have h11 := congrFun (congrFun hM 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h11
    first | linear_combination h11 | linear_combination -h11
  have c12 : (M 3 1) - (M 4 2) = 0 := by
    have h12 := congrFun (congrFun hM 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h12
    first | linear_combination h12 | linear_combination -h12
  have c13 : (M 2 1) - (M 4 3) = 0 := by
    have h13 := congrFun (congrFun hM 1) 3
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h13
    first | linear_combination h13 | linear_combination -h13
  have c14 : -(M 1 1) - (M 4 4) = 0 := by
    have h14 := congrFun (congrFun hM 1) 4
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h14
    first | linear_combination h14 | linear_combination -h14
  have c15 : (M 0 1) - (M 4 5) = 0 := by
    have h15 := congrFun (congrFun hM 1) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h15
    first | linear_combination h15 | linear_combination -h15
  have c22 : (2 : K) * (M 3 2) = 0 := by
    have h22 := congrFun (congrFun hM 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h22
    first | linear_combination h22 | linear_combination -h22
  have c23 : (M 2 2) + (M 3 3) = 0 := by
    have h23 := congrFun (congrFun hM 2) 3
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h23
    first | linear_combination h23 | linear_combination -h23
  have c24 : -(M 1 2) + (M 3 4) = 0 := by
    have h24 := congrFun (congrFun hM 2) 4
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h24
    first | linear_combination h24 | linear_combination -h24
  have c25 : (M 0 2) + (M 3 5) = 0 := by
    have h25 := congrFun (congrFun hM 2) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h25
    first | linear_combination h25 | linear_combination -h25
  have c33 : (2 : K) * (M 2 3) = 0 := by
    have h33 := congrFun (congrFun hM 3) 3
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h33
    first | linear_combination h33 | linear_combination -h33
  have c34 : -(M 1 3) + (M 2 4) = 0 := by
    have h34 := congrFun (congrFun hM 3) 4
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h34
    first | linear_combination h34 | linear_combination -h34
  have c35 : (M 0 3) + (M 2 5) = 0 := by
    have h35 := congrFun (congrFun hM 3) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h35
    first | linear_combination h35 | linear_combination -h35
  have c44 : (-2 : K) * (M 1 4) = 0 := by
    have h44 := congrFun (congrFun hM 4) 4
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h44
    first | linear_combination h44 | linear_combination -h44
  have c45 : (M 0 4) - (M 1 5) = 0 := by
    have h45 := congrFun (congrFun hM 4) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h45
    first | linear_combination h45 | linear_combination -h45
  have c55 : (2 : K) * (M 0 5) = 0 := by
    have h55 := congrFun (congrFun hM 5) 5
    simp [Matrix.mul_apply, Fin.sum_univ_succ, kleinGram] at h55
    first | linear_combination h55 | linear_combination -h55
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (-1/2 : K) * c55
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (1/2 : K) * c44
    · simp [lam2, psi] <;> linear_combination c45
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (-1/2 : K) * c14 + (-1/2 : K) * c23
    · simp [lam2, psi] <;> linear_combination (-1/2 : K) * c33
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c34
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c35
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (-1/2 : K) * c22
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c24
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c25
    · simp [lam2, psi] <;> ring
    · simp [lam2, psi] <;> linear_combination (1/2 : K) * c11
    · simp [lam2, psi] <;> linear_combination c12
    · simp [lam2, psi] <;> linear_combination c13
    · simp [lam2, psi] <;> linear_combination (1/2 : K) * c14 + (1/2 : K) * c23
    · simp [lam2, psi] <;> linear_combination c15
    · simp [lam2, psi] <;> linear_combination (-1/2 : K) * c00
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c01
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c02
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c03
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c04
    · simp [lam2, psi] <;> linear_combination (-1 : K) * c05 + (-1/2 : K) * c14 + (1/2 : K) * c23
  · simp [psi, Matrix.trace, Fin.sum_univ_succ] <;> linear_combination (-1/2 : K) * c14 + (1/2 : K) * c23

/-- The Klein action has zero kernel on trace-free generators. -/
theorem lam2Hom_injective : Function.Injective (lam2Hom (R := K)) := by
  intro X Y h
  have h' : lam2 X.val = lam2 Y.val := by
    have hv : (↑(lam2Hom X) : Matrix (Fin 6) (Fin 6) K) =
        ↑(lam2Hom Y) := congrArg Subtype.val h
    have hx : (lam2Hom X).val = lam2 X.val := rfl
    have hy : (lam2Hom Y).val = lam2 Y.val := rfl
    rw [hx, hy] at hv
    exact hv
  exact Subtype.ext (by rw [← psi_lam2 X.val, ← psi_lam2 Y.val, h'])

/-- Every Klein-skew-adjoint endomorphism comes from a unique trace-free
four-dimensional generator. -/
theorem lam2Hom_surjective : Function.Surjective (lam2Hom (R := K)) := by
  rintro ⟨M, hM⟩
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at hM
  obtain ⟨h1, h2⟩ := lam2_psi_of_skewAdjoint hM
  refine ⟨⟨psi M, by simpa [SpecialLinear.sl] using h2⟩, Subtype.ext ?_⟩
  change lam2 (psi M) = M
  exact h1

/-- **`sl₄(K) ≅ so(Klein form)`** as Lie algebras, with the explicit map `lam2`. -/
noncomputable def sl4EquivSoKlein :
    SpecialLinear.sl (Fin 4) K ≃ₗ⁅K⁆
      skewAdjointMatricesLieSubalgebra (kleinGram : Matrix (Fin 6) (Fin 6) K) :=
  LieEquiv.ofBijective lam2Hom ⟨lam2Hom_injective, lam2Hom_surjective⟩

/-! ### Signature `(3,3)` -/

/-- Split Klein substitution `p01 = x₁ + x₂, p23 = x₁ - x₂, …` as a matrix
(columns `x₁ … x₆`, rows in owner Plücker order; `p13 = -(x₃ - x₄)`). -/
def kleinCongruence : Matrix (Fin 6) (Fin 6) K :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, -1;
     0, 0, -1, 1, 0, 0;
     1, -1, 0, 0, 0, 0]

/-- CAS-computed inverse of `kleinCongruence`. -/
def kleinCongruenceInv : Matrix (Fin 6) (Fin 6) K :=
  !![1/2, 0, 0, 0, 0, 1/2;
     1/2, 0, 0, 0, 0, -1/2;
     0, 1/2, 0, 0, -1/2, 0;
     0, 1/2, 0, 0, 1/2, 0;
     0, 0, 1/2, 1/2, 0, 0;
     0, 0, 1/2, -1/2, 0, 0]

/-- The split diagonal form `diag(1,-1,1,-1,1,-1)`. -/
def splitDiag : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, -1, 1, -1, 1, -1]

/-- The displayed coordinate change is a left inverse to its proposed inverse. -/
theorem kleinCongruence_mul_inv : kleinCongruence * kleinCongruenceInv = (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [kleinCongruence, kleinCongruenceInv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- The displayed coordinate change is a right inverse to its proposed inverse. -/
theorem kleinCongruenceInv_mul : kleinCongruenceInv * kleinCongruence = (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [kleinCongruence, kleinCongruenceInv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- **Signature:** `Sᵀ G S = 2 • diag(1,-1,1,-1,1,-1)`. -/
theorem kleinCongruence_congr :
    kleinCongruenceᵀ * kleinGram * kleinCongruence = (2 : K) • (splitDiag : Matrix (Fin 6) (Fin 6) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [kleinCongruence, kleinGram, splitDiag, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal] <;> norm_num

instance kleinCongruenceInvertible : Invertible (kleinCongruence : Matrix (Fin 6) (Fin 6) K) :=
  ⟨kleinCongruenceInv, kleinCongruenceInv_mul, kleinCongruence_mul_inv⟩

/-- Rescaling the form by the unit `2` does not change its skew-adjoint algebra. -/
theorem skewAdjoint_two_smul_eq :
    skewAdjointMatricesLieSubalgebra ((2 : K) • (splitDiag : Matrix (Fin 6) (Fin 6) K)) =
      skewAdjointMatricesLieSubalgebra (splitDiag : Matrix (Fin 6) (Fin 6) K) := by
  refine LieSubalgebra.ext _ _ (fun A => ?_)
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  simpa using mem_skewAdjointMatricesLieSubalgebra_unit_smul h2.unit splitDiag A

/-- **`sl₄(K) ≅ so(D)`, `D = diag(1,-1,1,-1,1,-1)`**; for `K = ℝ`, `sl(4,ℝ) ≅ so(3,3)`. -/
noncomputable def sl4EquivSoSplit :
    SpecialLinear.sl (Fin 4) K ≃ₗ⁅K⁆
      skewAdjointMatricesLieSubalgebra (splitDiag : Matrix (Fin 6) (Fin 6) K) :=
  (sl4EquivSoKlein.trans
      (skewAdjointMatricesLieSubalgebraEquiv kleinGram kleinCongruence
        kleinCongruenceInvertible)).trans
    (LieEquiv.ofEq _ _ (by rw [kleinCongruence_congr, skewAdjoint_two_smul_eq]))

end Field

end InfoGeometry.Projective.DahmKleinLieIsomorphism
