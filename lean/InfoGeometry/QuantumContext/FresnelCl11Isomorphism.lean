/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.QuantumContext.AharonovBohmFresnelDivergenceResolution

/-!
# Section 124: Fresnel Quadrature Coordinates and the Native Real `Cl(1,1)` Model
Target: `InfoGeometry/QuantumContext/FresnelCl11Isomorphism.lean`

Formalizes the coordinate bijection of two pairs of Fresnel quadratures `(ψ_+, ψ_-)`
with a four-entry matrix record, and then connects its real specialization to
the repository's native `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)` model:
  `M(ψ_+, ψ_-) = [[C_+, S_+], [C_-, S_-]]`
and proves:
1. Explicit coordinate equivalence `fresnelPairCoordEquiv : (FresnelWave R × FresnelWave R) ≃ Cl11Op R`
   and coordinatewise addition/scalar compatibility of the embedding.
2. Determinant identity with the alternating quadrature pairing:
   `det(M(ψ_+, ψ_-)) = H_{(+,-)}(ψ_+, ψ_-) = C_+ S_- - S_+ C_-`.
3. Frobenius–Hilbert–Schmidt norm identity (total incoherent intensity):
   `frobeniusNormSq(M(ψ_+, ψ_-)) = I_+ + I_-`.
4. Structure of the Gram matrix `G_L = M · Mᵀ`:
   `M · Mᵀ = [[I_+, G_{(+,-)}], [G_{(+,-)}, I_-]]`,
   whence `det(M · Mᵀ) = (det M)²` recovers the Brahmagupta–Fibonacci identity:
   `I_+ · I_- - G_{(+,-)}² = H_{(+,-)}²`.
5. A finite identity for the defined transition expression; equality with the
   displayed matrix formula includes its general `(c²+s²)` coefficient, with
   a simplified specialization when `c²+s²=1`.
-/

namespace InfoGeometry.QuantumContext.FresnelCl11Isomorphism

variable {R : Type*} [CommRing R]

open InfoGeometry.QuantumContext.SorkinFluxQubit

/-! ### 1. Shared Fresnel Amplitudes and Their Matrix Coordinates -/

/-- Four-entry record used for `2 × 2` matrix coordinates. -/
@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace Cl11Op

variable {R : Type*} [CommRing R]

def zeroOp : Cl11Op R := ⟨0, 0, 0, 0⟩

def sampleCl11OpInt : Cl11Op ℤ := ⟨1, 0, 0, 1⟩

theorem sampleCl11OpInt_ne_zero :
    sampleCl11OpInt ≠ zeroOp := by
  decide

def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

def scale (c : R) (A : Cl11Op R) : Cl11Op R :=
  ⟨c * A.m11, c * A.m12, c * A.m21, c * A.m22⟩

def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21,
   A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21,
   A.m21 * B.m12 + A.m22 * B.m22⟩

/-- Non-commutativity of `Cl11Op.mul` over `ℤ`. -/
theorem cl11Op_mul_noncommutative :
    let A : Cl11Op ℤ := ⟨1, 1, 0, 1⟩
    let B : Cl11Op ℤ := ⟨1, 0, 1, 1⟩
    mul A B ≠ mul B A := by
  decide

def transpose (A : Cl11Op R) : Cl11Op R :=
  ⟨A.m11, A.m21, A.m12, A.m22⟩

def trace (A : Cl11Op R) : R :=
  A.m11 + A.m22

def det (A : Cl11Op R) : R :=
  A.m11 * A.m22 - A.m12 * A.m21

/-- Frobenius–Hilbert–Schmidt inner product: `⟨A, B⟩_HS = Tr(Aᵀ · B)`. -/
def frobeniusInner (A B : Cl11Op R) : R :=
  A.m11 * B.m11 + A.m12 * B.m12 + A.m21 * B.m21 + A.m22 * B.m22

/-- Squared Frobenius–Hilbert–Schmidt norm: `‖A‖²_HS = ⟨A, A⟩_HS`. -/
def frobeniusNormSq (A : Cl11Op R) : R :=
  frobeniusInner A A

/-! ### 2. Coordinate Equivalence and Real Clifford Specialization -/

/--
Embedding of the shared Fresnel quadrature pair `(ψ_+, ψ_-)` as rows of a four-entry matrix record:
`M(ψ_+, ψ_-) = [[C_+, S_+], [C_-, S_-]]`.
-/
def embedFresnelPair (ψ_pos ψ_neg : FresnelWave R) : Cl11Op R :=
  ⟨ψ_pos.cQuad, ψ_pos.sQuad, ψ_neg.cQuad, ψ_neg.sQuad⟩

/-- Projection of the first row to the upper slit `ψ_+`. -/
def projSlitPos (M : Cl11Op R) : FresnelWave R :=
  ⟨M.m11, M.m12⟩

/-- Projection of the second row to the lower slit `ψ_-`. -/
def projSlitNeg (M : Cl11Op R) : FresnelWave R :=
  ⟨M.m21, M.m22⟩

/--
Bijection (type equivalence) between the shared Fresnel quadrature pairs and
the four-entry matrix coordinate record. The separate real bridge below
identifies this record with the native `Cl(1,1)` matrix model.
-/
def fresnelPairCoordEquiv : (FresnelWave R × FresnelWave R) ≃ Cl11Op R where
  toFun p := embedFresnelPair p.1 p.2
  invFun M := (projSlitPos M, projSlitNeg M)
  left_inv := by
    rintro ⟨⟨c₁, s₁⟩, ⟨c₂, s₂⟩⟩
    rfl
  right_inv := by
    rintro ⟨m11, m12, m21, m22⟩
    rfl

/-- Coordinatewise addition compatibility of the embedding. -/
theorem embed_add (ψ_pos₁ ψ_neg₁ ψ_pos₂ ψ_neg₂ : FresnelWave R) :
    embedFresnelPair
        ⟨ψ_pos₁.cQuad + ψ_pos₂.cQuad, ψ_pos₁.sQuad + ψ_pos₂.sQuad⟩
        ⟨ψ_neg₁.cQuad + ψ_neg₂.cQuad, ψ_neg₁.sQuad + ψ_neg₂.sQuad⟩ =
      add (embedFresnelPair ψ_pos₁ ψ_neg₁) (embedFresnelPair ψ_pos₂ ψ_neg₂) := by
  dsimp [embedFresnelPair, add]

/-- Coordinatewise scalar compatibility of the embedding. -/
theorem embed_scale (c : R) (ψ_pos ψ_neg : FresnelWave R) :
    embedFresnelPair ⟨c * ψ_pos.cQuad, c * ψ_pos.sQuad⟩
        ⟨c * ψ_neg.cQuad, c * ψ_neg.sQuad⟩ =
      scale c (embedFresnelPair ψ_pos ψ_neg) := by
  dsimp [embedFresnelPair, scale]

/-! ### 3. Determinant and Frobenius Norm Identities: `det(M) = H_{(+,-)}` and `frobeniusNormSq(M) = I_+ + I_-` -/

/--
The determinant of `M` equals the alternating quadrature pairing `H_{(+,-)}`:
`det(M(ψ_+, ψ_-)) = C_+ S_- - S_+ C_- = H_{(+,-)}(ψ_+, ψ_-)`.
-/
@[simp]
theorem det_embed_eq_yin_symplectic_H (ψ_pos ψ_neg : FresnelWave R) :
    det (embedFresnelPair ψ_pos ψ_neg) = FresnelWave.yinH ψ_pos ψ_neg := by
  dsimp [det, embedFresnelPair, FresnelWave.yinH]

/--
The squared Frobenius norm of `M` equals the sum of the slit intensities `I_+ + I_-`:
`frobeniusNormSq(M(ψ_+, ψ_-)) = I_+ + I_-`.
-/
@[simp]
theorem frobenius_norm_sq_embed_eq_intensity_sum (ψ_pos ψ_neg : FresnelWave R) :
    frobeniusNormSq (embedFresnelPair ψ_pos ψ_neg) =
      FresnelWave.intensity ψ_pos + FresnelWave.intensity ψ_neg := by
  dsimp [frobeniusNormSq, frobeniusInner, embedFresnelPair, FresnelWave.intensity]
  ring

/-! ### 4. Gram Matrix `M · Mᵀ` and a Brahmagupta–Fibonacci Identity -/

/--
The Gram matrix `G_L = M · Mᵀ` packs `I_+`, `I_-`, and `G_{(+,-)}`:
`M · Mᵀ = [[I_+, G_{(+,-)}], [G_{(+,-)}, I_-]]`.
The diagonal entries are the two intensities, while the off-diagonal entries are
the symmetric pairing `G_{(+,-)}`.
-/
theorem gram_matrix_embed_explicit (ψ_pos ψ_neg : FresnelWave R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    mul M (transpose M) =
      ⟨FresnelWave.intensity ψ_pos,
       FresnelWave.yangG ψ_pos ψ_neg,
       FresnelWave.yangG ψ_pos ψ_neg,
       FresnelWave.intensity ψ_neg⟩ := by
  dsimp [embedFresnelPair, mul, transpose,
         FresnelWave.intensity, FresnelWave.yangG]
  ext <;> ring

/-- The trace of the Gram matrix `M · Mᵀ` equals the sum of the intensities `I_+ + I_-`. -/
theorem trace_gram_embed_eq_intensity_sum (ψ_pos ψ_neg : FresnelWave R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    trace (mul M (transpose M)) =
      FresnelWave.intensity ψ_pos + FresnelWave.intensity ψ_neg := by
  dsimp [embedFresnelPair, trace, mul, transpose, FresnelWave.intensity]

/--
Determinant of the Gram matrix `M · Mᵀ` as the Brahmagupta–Fibonacci–Fresnel identity:
`det(M · Mᵀ) = I_+ · I_- - G_{(+,-)}² = (det M)² = H_{(+,-)}²`.
-/
theorem det_gram_embed_eq_yin_sq (ψ_pos ψ_neg : FresnelWave R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    det (mul M (transpose M)) =
      FresnelWave.intensity ψ_pos * FresnelWave.intensity ψ_neg -
        FresnelWave.yangG ψ_pos ψ_neg * FresnelWave.yangG ψ_pos ψ_neg ∧
    det (mul M (transpose M)) = det M * det M := by
  constructor
  · dsimp [embedFresnelPair, det, mul, transpose,
           FresnelWave.intensity, FresnelWave.yangG]
    ring
  · dsimp [embedFresnelPair, det, mul, transpose]
    ring

/-! ### 5. Matrix Formula for the Defined Two-Slit Transition Expression -/

/-- A parameterized `2 × 2` matrix `U(c, s) = [[c, s], [-s, c]]`. -/
def parameterMatrix (c s : R) : Cl11Op R :=
  ⟨c, s, -s, c⟩

/--
For the supplied scalar parameters, the upper off-diagonal entry `m12` of
`M · U(c, s) · Mᵀ` equals `c · G_{(+,-)} + s · H_{(+,-)}`.
-/
theorem parameterized_gram_m12 (ψ_pos ψ_neg : FresnelWave R) (c s : R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    (mul (mul M (parameterMatrix c s)) (transpose M)).m12 =
      c * FresnelWave.yangG ψ_pos ψ_neg +
      s * FresnelWave.yinH ψ_pos ψ_neg := by
  dsimp [embedFresnelPair, parameterMatrix, mul, transpose,
         FresnelWave.yangG, FresnelWave.yinH]
  ring

/--
The defined two-slit transition expression, rewritten using the record's
invariants. The correction term retains the general coefficient `c²+s²`;
it vanishes under the additional unit-circle hypothesis.
-/
theorem ab_prob_from_cl11_invariants (ψ_pos ψ_neg : FresnelWave R) (c s : R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    FresnelWave.abProb ψ_pos ψ_neg c s =
      frobeniusNormSq M +
        ((c * c + s * s) - 1) * FresnelWave.intensity ψ_neg +
        2 * c * (mul M (transpose M)).m12 + 2 * s * det M := by
  dsimp [embedFresnelPair, frobeniusNormSq, frobeniusInner, mul, transpose, det,
         FresnelWave.abProb, FresnelWave.intensity,
         FresnelWave.yangG, FresnelWave.yinH]
  ring

/-- On the unit circle, the defined transition expression has the simplified
matrix formula without a correction term. -/
theorem ab_prob_from_cl11_invariants_of_unit_circle
    (ψ_pos ψ_neg : FresnelWave R) (c s : R)
    (hcs : c * c + s * s = 1) :
    let M := embedFresnelPair ψ_pos ψ_neg
    FresnelWave.abProb ψ_pos ψ_neg c s =
      frobeniusNormSq M + 2 * c * (mul M (transpose M)).m12 +
        2 * s * det M := by
  rw [ab_prob_from_cl11_invariants]
  rw [hcs]
  ring

end Cl11Op

/-! ### 6. Coordinate identification with the native `Cl(1,1)` matrix model

`Cl11Op` is a four-entry record.  At real scalars its coordinate map agrees
with the repository-owned algebra equivalence
`CliffordAlgebra q11 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`.  These lemmas connect
the record's operations to that existing model; they do not identify generic
`Cl11Op R` for arbitrary `R` with a Clifford algebra.
-/

namespace Cl11Op

open scoped Matrix

/-- The four record entries as an actual `2 × 2` real matrix. -/
def toNativeMatrix (A : Cl11Op ℝ) : InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  !![A.m11, A.m12; A.m21, A.m22]

/-- Read a record from the four entries of a native `2 × 2` real matrix. -/
def ofNativeMatrix (M : InfoGeometry.Clifford.Cl11Matrix.Mat2) : Cl11Op ℝ :=
  ⟨M 0 0, M 0 1, M 1 0, M 1 1⟩

theorem ofNativeMatrix_toNativeMatrix (A : Cl11Op ℝ) :
    ofNativeMatrix (toNativeMatrix A) = A := by
  ext <;> simp [ofNativeMatrix, toNativeMatrix]

theorem toNativeMatrix_ofNativeMatrix
    (M : InfoGeometry.Clifford.Cl11Matrix.Mat2) :
    toNativeMatrix (ofNativeMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toNativeMatrix, ofNativeMatrix]

theorem toNativeMatrix_mul (A B : Cl11Op ℝ) :
    toNativeMatrix (Cl11Op.mul A B) =
      toNativeMatrix A * toNativeMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toNativeMatrix, Cl11Op.mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_eq_nativeMatrix_det (A : Cl11Op ℝ) :
    Cl11Op.det A = (toNativeMatrix A).det := by
  simp [Cl11Op.det, toNativeMatrix, Matrix.det_fin_two]

/-- Real Clifford element represented by the record's native matrix. -/
noncomputable def toNativeClifford (A : Cl11Op ℝ) :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 :=
  InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (toNativeMatrix A)

theorem toNativeClifford_mul (A B : Cl11Op ℝ) :
    toNativeClifford (Cl11Op.mul A B) =
      toNativeClifford A * toNativeClifford B := by
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  simp only [toNativeClifford,
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.apply_symm_apply,
    map_mul]
  exact toNativeMatrix_mul A B

/-- Fresnel rows, viewed through the native real Clifford matrix model. -/
noncomputable def fresnelToNativeClifford
    (ψ_pos ψ_neg : FresnelWave ℝ) :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 :=
  toNativeClifford (Cl11Op.embedFresnelPair ψ_pos ψ_neg)

theorem nativeMatrix_fresnelToNativeClifford
    (ψ_pos ψ_neg : FresnelWave ℝ) :
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (fresnelToNativeClifford ψ_pos ψ_neg) =
      toNativeMatrix (Cl11Op.embedFresnelPair ψ_pos ψ_neg) := by
  simp [fresnelToNativeClifford, toNativeClifford]

theorem nativeCliffordDet_fresnel_eq_yin
    (ψ_pos ψ_neg : FresnelWave ℝ) :
    (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (fresnelToNativeClifford ψ_pos ψ_neg)).det =
      FresnelWave.yinH ψ_pos ψ_neg := by
  rw [nativeMatrix_fresnelToNativeClifford, ← det_eq_nativeMatrix_det]
  exact Cl11Op.det_embed_eq_yin_symplectic_H ψ_pos ψ_neg

end Cl11Op

end InfoGeometry.QuantumContext.FresnelCl11Isomorphism
