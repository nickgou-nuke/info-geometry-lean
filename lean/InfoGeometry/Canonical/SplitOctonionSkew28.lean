import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Basis.Basic
import InfoGeometry.Canonical.SplitOctonionJordanForm

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitOctonionSkew28

open Matrix
open InfoGeometry.Canonical.SplitOctonionJordanForm

abbrev Index := {p : Fin 8 × Fin 8 // p.1 < p.2}
abbrev Matrix8 := Matrix (Fin 8) (Fin 8) ℝ
abbrev Skew8 := skewAdjointMatricesSubmodule (1 : Matrix8)

theorem index_card : Fintype.card Index = 28 := by
  native_decide

def skewMatrix (c : Index → ℝ) : Matrix8 := fun i j =>
  if h : i < j then c ⟨(i, j), h⟩
  else if h : j < i then -c ⟨(j, i), h⟩
  else 0

theorem skewMatrix_isSkew (c : Index → ℝ) :
    (skewMatrix c)ᵀ = -(skewMatrix c) := by
  ext i j
  by_cases hij : i < j
  · have hji : ¬ j < i := by omega
    simp [skewMatrix, hij, hji]
  · by_cases hji : j < i
    · have h' : ¬ i < j := by omega
      simp [skewMatrix, h', hji]
    · have heq : i = j := by omega
      subst heq
      simp [skewMatrix]

def skewCoordinateMap : (Index → ℝ) →ₗ[ℝ] Skew8 where
  toFun c := ⟨skewMatrix c, by
    rw [mem_skewAdjointMatricesSubmodule]
    change (skewMatrix c)ᵀ * 1 = 1 * -(skewMatrix c)
    simpa using skewMatrix_isSkew c
  ⟩
  map_add' c d := by
    apply Subtype.ext
    funext i j
    by_cases hij : i < j
    · simp [skewMatrix, hij]
    · by_cases hji : j < i
      · simp [skewMatrix, hij, hji, add_comm]
      · have : i = j := by omega
        subst this
        simp [skewMatrix]
  map_smul' r c := by
    apply Subtype.ext
    funext i j
    by_cases hij : i < j
    · simp [skewMatrix, hij]
    · by_cases hji : j < i
      · simp [skewMatrix, hij, hji]
      · have : i = j := by omega
        subst this
        simp [skewMatrix]

def skewCoordinates : Skew8 →ₗ[ℝ] (Index → ℝ) where
  toFun A p := A.1 p.1.1 p.1.2
  map_add' A B := by rfl
  map_smul' r A := by rfl

theorem skewCoordinates_skewCoordinateMap (c : Index → ℝ) :
    skewCoordinates (skewCoordinateMap c) = c := by
  funext p
  simp [skewCoordinates, skewCoordinateMap, skewMatrix, p.2]

theorem skewCoordinateMap_skewCoordinates (A : Skew8) :
    skewCoordinateMap (skewCoordinates A) = A := by
  apply Subtype.ext
  ext i j
  by_cases hij : i < j
  · have hji : ¬ j < i := by omega
    simp [skewCoordinateMap, skewCoordinates, skewMatrix, hij]
  · by_cases hji : j < i
    · have h' : ¬ i < j := by omega
      have hA := (mem_skewAdjointMatricesSubmodule (1 : Matrix8) A.1).mp A.2
      have hA' : A.1ᵀ = -A.1 := by
        simpa [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using hA
      have hs := congrFun (congrFun hA' i) j
      simp [skewCoordinateMap, skewCoordinates, skewMatrix, h', hji] at hs ⊢
      linarith
    · have heq : i = j := by omega
      subst heq
      have hA := (mem_skewAdjointMatricesSubmodule (1 : Matrix8) A.1).mp A.2
      have hA' : A.1ᵀ = -A.1 := by
        simpa [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using hA
      have hs := congrFun (congrFun hA' i) i
      simp [skewCoordinateMap, skewCoordinates, skewMatrix] at hs ⊢
      linarith

noncomputable def skewCoordinateEquiv : (Index → ℝ) ≃ₗ[ℝ] Skew8 :=
  LinearEquiv.ofBijective skewCoordinateMap
    ⟨(fun c d h => by
        have h' := congrArg skewCoordinates h
        exact (skewCoordinates_skewCoordinateMap c).symm.trans
          (h'.trans (skewCoordinates_skewCoordinateMap d))),
      (fun A => ⟨skewCoordinates A, skewCoordinateMap_skewCoordinates A⟩)⟩

/-! ### The explicit 28-coordinate skew basis -/

noncomputable def skewBasis : Module.Basis Index ℝ Skew8 :=
  (Pi.basisFun ℝ Index).map skewCoordinateEquiv

theorem skewBasis_span_top :
    Submodule.span ℝ (Set.range skewBasis) = ⊤ := by
  exact skewBasis.span_eq

theorem skewBasis_coordinate_decomposition (A : Skew8) :
    ∑ p : Index, (skewBasis.repr A p) • skewBasis p = A := by
  exact skewBasis.sum_repr A

theorem finrank_skew8 : Module.finrank ℝ Skew8 = 28 := by
  rw [← LinearEquiv.finrank_eq skewCoordinateEquiv]
  simp [index_card]

def eta44 : Matrix8 :=
  Matrix.diagonal (fun i => if i.val < 4 then 1 else -1)

theorem eta44_transpose : eta44ᵀ = eta44 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [eta44]
  · have h' : j ≠ i := Ne.symm h
    simp [eta44, h, h']

theorem eta44_mul_self : eta44 * eta44 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta44, Matrix.mul_apply, Fin.sum_univ_succ]

abbrev Orthogonal44 := skewAdjointMatricesSubmodule eta44

def orthogonal44Bracket (A B : Orthogonal44) : Orthogonal44 :=
  ⟨(A : Matrix8) * (B : Matrix8) -
      (B : Matrix8) * (A : Matrix8),
    Matrix.isSkewAdjoint_bracket eta44 A.property B.property⟩

noncomputable instance : LieRing Orthogonal44 where
  bracket := orthogonal44Bracket
  add_lie := by
    intro A B C
    apply Subtype.ext
    change ((A : Matrix8) + (B : Matrix8)) * (C : Matrix8) -
      (C : Matrix8) * ((A : Matrix8) + (B : Matrix8)) =
      ((A : Matrix8) * (C : Matrix8) -
        (C : Matrix8) * (A : Matrix8)) +
      ((B : Matrix8) * (C : Matrix8) -
        (C : Matrix8) * (B : Matrix8))
    rw [add_mul, mul_add]
    abel
  lie_add := by
    intro A B C
    apply Subtype.ext
    change (A : Matrix8) * ((B : Matrix8) + (C : Matrix8)) -
      ((B : Matrix8) + (C : Matrix8)) * (A : Matrix8) =
      ((A : Matrix8) * (B : Matrix8) -
        (B : Matrix8) * (A : Matrix8)) +
      ((A : Matrix8) * (C : Matrix8) -
        (C : Matrix8) * (A : Matrix8))
    rw [mul_add, add_mul]
    abel
  lie_self := by
    intro A
    apply Subtype.ext
    simp only [orthogonal44Bracket, Subtype.coe_mk]
    simp
  leibniz_lie := by
    intro A B C
    apply Subtype.ext
    simp [orthogonal44Bracket]
    noncomm_ring

noncomputable instance : LieAlgebra ℝ Orthogonal44 where
  lie_smul := by
    intro r A B
    apply Subtype.ext
    change (A : Matrix8) * (r • (B : Matrix8)) -
      (r • (B : Matrix8)) * (A : Matrix8) =
      r • ((A : Matrix8) * (B : Matrix8) -
        (B : Matrix8) * (A : Matrix8))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem orthogonal44_beta_skew (A : Orthogonal44) (x y : MiddleCarrier) :
    beta44 (A.1.mulVec x) y + beta44 x (A.1.mulVec y) = 0 := by
  have hA := (mem_skewAdjointMatricesSubmodule eta44 A.1).mp A.2
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hA
  have hbeta (u v : MiddleCarrier) :
      beta44 u v = eta44.mulVec u ⬝ᵥ v := by
    simp [beta44, eta44, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  have hskew : eta44 * A.1 = -(A.1ᵀ * eta44) := by
    have h := congrArg Neg.neg hA
    simpa [Matrix.mul_neg, neg_neg] using h.symm
  rw [hbeta, hbeta, Matrix.mulVec_mulVec, hskew]
  simp only [Matrix.neg_mulVec, neg_dotProduct]
  rw [← Matrix.mulVec_mulVec]
  have hdot :
      A.1ᵀ.mulVec (eta44.mulVec x) ⬝ᵥ y =
        eta44.mulVec x ⬝ᵥ A.1.mulVec y := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, dotProduct_comm]
  rw [hdot]
  ring

def etaTransport : Skew8 →ₗ[ℝ] Orthogonal44 where
  toFun A := ⟨eta44 * A.1, by
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    have hA := (mem_skewAdjointMatricesSubmodule (1 : Matrix8) A.1).mp A.2
    have hA' : A.1ᵀ = -A.1 := by
      simpa [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using hA
    calc
      (eta44 * A.1)ᵀ * eta44 = A.1ᵀ := by
        rw [Matrix.transpose_mul, eta44_transpose, Matrix.mul_assoc, eta44_mul_self, mul_one]
      _ = -A.1 := hA'
      _ = eta44 * -(eta44 * A.1) := by
        simp [← Matrix.mul_assoc, eta44_mul_self]
  ⟩
  map_add' A B := by
    apply Subtype.ext
    ext i j
    change (eta44 * (A.1 + B.1)) i j = (eta44 * A.1 + eta44 * B.1) i j
    simp only [Matrix.mul_apply, Matrix.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' r A := by
    apply Subtype.ext
    ext i j
    change (∑ x, eta44 i x * (r * A.1 x j)) =
      r * ∑ x, eta44 i x * A.1 x j
    calc
      (∑ x, eta44 i x * (r * A.1 x j)) =
          ∑ x, r * (eta44 i x * A.1 x j) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = r * ∑ x, eta44 i x * A.1 x j := by
        rw [Finset.mul_sum]

def etaTransportInverse : Orthogonal44 →ₗ[ℝ] Skew8 where
  toFun A := ⟨eta44 * A.1, by
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    have h := (mem_skewAdjointMatricesSubmodule eta44 A.1).mp A.2
    change A.1ᵀ * eta44 = eta44 * (-A.1) at h
    simp only [mul_one, one_mul]
    change (eta44 * A.1)ᵀ = -(eta44 * A.1)
    simpa [Matrix.transpose_mul, eta44_transpose, Matrix.mul_neg] using h
  ⟩
  map_add' A B := by
    apply Subtype.ext
    ext i j
    change (eta44 * (A.1 + B.1)) i j = (eta44 * A.1 + eta44 * B.1) i j
    simp only [Matrix.mul_apply, Matrix.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' r A := by
    apply Subtype.ext
    ext i j
    change (∑ x, eta44 i x * (r * A.1 x j)) =
      r * ∑ x, eta44 i x * A.1 x j
    calc
      (∑ x, eta44 i x * (r * A.1 x j)) =
          ∑ x, r * (eta44 i x * A.1 x j) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = r * ∑ x, eta44 i x * A.1 x j := by
        rw [Finset.mul_sum]

theorem etaTransportInverse_apply (A : Skew8) :
    etaTransportInverse (etaTransport A) = A := by
  apply Subtype.ext
  change eta44 * (eta44 * A.1) = A.1
  rw [← Matrix.mul_assoc, eta44_mul_self, one_mul]

theorem etaTransport_apply_inverse (A : Orthogonal44) :
    etaTransport (etaTransportInverse A) = A := by
  apply Subtype.ext
  change eta44 * (eta44 * A.1) = A.1
  rw [← Matrix.mul_assoc, eta44_mul_self, one_mul]

noncomputable def orthogonal44Equiv : Skew8 ≃ₗ[ℝ] Orthogonal44 :=
  LinearEquiv.ofBijective etaTransport ⟨
    (fun A B h => by
      have h' := congrArg etaTransportInverse h
      simpa [etaTransportInverse_apply] using h'),
    (fun A => ⟨etaTransportInverse A, etaTransport_apply_inverse A⟩)⟩

noncomputable def orthogonal44Basis : Module.Basis Index ℝ Orthogonal44 :=
  skewBasis.map orthogonal44Equiv

theorem orthogonal44Basis_span_top :
    Submodule.span ℝ (Set.range orthogonal44Basis) = ⊤ := by
  exact orthogonal44Basis.span_eq

theorem orthogonal44Basis_coordinate_decomposition (A : Orthogonal44) :
    ∑ p : Index, (orthogonal44Basis.repr A p) • orthogonal44Basis p = A := by
  exact orthogonal44Basis.sum_repr A

theorem finrank_orthogonal44 : Module.finrank ℝ Orthogonal44 = 28 := by
  exact (LinearEquiv.finrank_eq orthogonal44Equiv).symm.trans finrank_skew8

end InfoGeometry.Canonical.SplitOctonionSkew28
