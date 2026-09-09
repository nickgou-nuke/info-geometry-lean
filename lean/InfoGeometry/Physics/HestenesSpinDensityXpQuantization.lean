import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

/-!
# Finite Hestenes--spin density and first-quantization core

This owner formalizes the finite, native part of the quantization chain:

`FourMomentum → Pauli soldering → Gram operator → trace-normalized density`

and the algebraic symmetric/antisymmetric lift of the classical `xp` product.
The Pauli carrier is a chiral `2 × 2` block; it is not asserted to be the
full split Clifford algebra.  Likewise, the symmetric product below is the
finite algebraic shadow of the unbounded dilation operator, not a claim of
self-adjointness on `L²`.
-/

noncomputable section

namespace InfoGeometry.Physics.HestenesSpinDensityXpQuantization

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
open scoped ComplexOrder MatrixOrder

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Rapidity and Pauli soldering -/

/-- A real rapidity-space four-vector. -/
structure RapidityFourVector where
  time : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- The complex four-vector used by the existing Pauli soldering owner. -/
def rapidityComplex (r : RapidityFourVector) : FourMomentum :=
  ⟨r.time, r.x, r.y, r.z⟩

/-- Solder a rapidity four-vector to its chiral `2 × 2` Pauli block. -/
def solderRapidity (r : RapidityFourVector) : M2C :=
  pauliMomentum (rapidityComplex r)

@[simp] theorem solderRapidity_apply (r : RapidityFourVector) :
    solderRapidity r =
      !![(r.time : ℂ) + r.z, (r.x : ℂ) - Complex.I * r.y;
         (r.x : ℂ) + Complex.I * r.y, (r.time : ℂ) - r.z] := by
  simp [solderRapidity, pauliMomentum, rapidityComplex]

theorem solderRapidity_det (r : RapidityFourVector) :
    (solderRapidity r).det =
      (r.time : ℂ) ^ 2 - r.x ^ 2 - r.y ^ 2 - r.z ^ 2 := by
  simpa [solderRapidity, rapidityComplex, minkowskiSq] using
    det_pauliMomentum (rapidityComplex r)

/-! ## Gram density and trace normalization -/

/-- The positive Gram operator associated with a chiral matrix amplitude. -/
def gram (A : M2C) : M2C := A * Aᴴ

/-- The right Gram operator records the column inner products of an amplitude. -/
def rightGram (A : M2C) : M2C := Aᴴ * A

theorem rightGram_isHermitian (A : M2C) : (rightGram A).IsHermitian := by
  exact isHermitian_conjTranspose_mul_self A

theorem rightGram_posSemidef (A : M2C) : (rightGram A).PosSemidef := by
  exact posSemidef_conjTranspose_mul_self A

/-! The Gram construction is the positive factor in the finite polar model. -/

theorem gram_conjTranspose (A : M2C) :
    gram Aᴴ = Aᴴ * A := by
  simp [gram, Matrix.conjTranspose_conjTranspose]

theorem gram_trace_cyclic (A : M2C) :
    Matrix.trace (gram A) = Matrix.trace (Aᴴ * A) := by
  unfold gram
  rw [Matrix.trace_mul_comm]

theorem gram_trace_eq_rightGram_trace (A : M2C) :
    Matrix.trace (gram A) = Matrix.trace (rightGram A) := by
  exact gram_trace_cyclic A

theorem rightGram_leftUnitary (U A : M2C) (hU : Uᴴ * U = 1) :
    rightGram (U * A) = rightGram A := by
  unfold rightGram
  rw [Matrix.conjTranspose_mul]
  calc
    Aᴴ * Uᴴ * (U * A) = Aᴴ * (Uᴴ * U) * A := by simp [mul_assoc]
    _ = Aᴴ * A := by rw [hU]; simp

theorem rightGram_rightConjugate (A U : M2C) :
    rightGram (A * U) = Uᴴ * rightGram A * U := by
  unfold rightGram
  rw [Matrix.conjTranspose_mul]
  calc
    Uᴴ * Aᴴ * (A * U) = Uᴴ * (Aᴴ * A) * U := by simp [mul_assoc]
    _ = Uᴴ * rightGram A * U := rfl

theorem gram_leftUnitary_conjugate (U A : M2C) :
    gram (U * A) = U * gram A * Uᴴ := by
  unfold gram
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- The real trace/volume scalar of the Gram operator. -/
def gramTrace (A : M2C) : ℝ := (Matrix.trace (gram A)).re

theorem gramTrace_conjTranspose (A : M2C) :
    gramTrace Aᴴ = gramTrace A := by
  unfold gramTrace
  rw [gram_conjTranspose]
  exact congrArg Complex.re (gram_trace_cyclic A).symm

/-- Algebraic positive cone: a matrix is Gram-positive when it is `B Bᴴ`. -/
def GramPositive (M : M2C) : Prop := ∃ B : M2C, M = gram B

/-- Positive Gram matrices after a strictly positive real volume rescaling. -/
def ProjectiveGramPositive (M : M2C) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ B : M2C, M = (c : ℂ)⁻¹ • gram B

/-- Trace-normalized density matrix, defined when the Gram trace is nonzero. -/
def densityMatrix (A : M2C) : M2C :=
  (gramTrace A : ℂ)⁻¹ • gram A

/-- The right density uses the same Frobenius/Gram trace as the left density. -/
def rightDensityMatrix (A : M2C) : M2C :=
  (gramTrace A : ℂ)⁻¹ • rightGram A

theorem gram_mul_affinity_eq_affinity_mul_rightGram (A : M2C) :
    gram A * A = A * rightGram A := by
  unfold gram rightGram
  noncomm_ring

theorem densityMatrix_mul_affinity_eq_affinity_mul_rightDensityMatrix
    (A : M2C) :
    densityMatrix A * A = A * rightDensityMatrix A := by
  unfold densityMatrix rightDensityMatrix
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [gram_mul_affinity_eq_affinity_mul_rightGram]

theorem gramTrace_leftUnitary (U A : M2C) (hU : Uᴴ * U = 1) :
    gramTrace (U * A) = gramTrace A := by
  unfold gramTrace
  rw [gram_leftUnitary_conjugate]
  have htrace : Matrix.trace (U * gram A * Uᴴ) = Matrix.trace (gram A) := by
    calc
      Matrix.trace (U * gram A * Uᴴ) =
          Matrix.trace (Uᴴ * (U * gram A)) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((Uᴴ * U) * gram A) := by rw [mul_assoc]
      _ = Matrix.trace (gram A) := by rw [hU]; simp
  rw [htrace]

theorem densityMatrix_leftUnitary_conjugate
    (U A : M2C) (hU : Uᴴ * U = 1) :
    densityMatrix (U * A) = U * densityMatrix A * Uᴴ := by
  unfold densityMatrix
  rw [gramTrace_leftUnitary U A hU, gram_leftUnitary_conjugate]
  simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]

theorem rightDensityMatrix_leftUnitary
    (U A : M2C) (hU : Uᴴ * U = 1) :
    rightDensityMatrix (U * A) = rightDensityMatrix A := by
  unfold rightDensityMatrix
  rw [gramTrace_leftUnitary U A hU, rightGram_leftUnitary U A hU]

/-! ## Real Cartan split of a finite complex generator -/

def cartanSkew (X : M2C) : M2C :=
  (1 / 2 : ℂ) • (X - Xᴴ)

def cartanHermitian (X : M2C) : M2C :=
  (1 / 2 : ℂ) • (X + Xᴴ)

theorem cartan_split (X : M2C) :
    X = cartanSkew X + cartanHermitian X := by
  simp [cartanSkew, cartanHermitian]
  module

theorem cartanSkew_isSkewAdjoint (X : M2C) :
    (cartanSkew X)ᴴ = -cartanSkew X := by
  simp [cartanSkew, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem cartanHermitian_isSelfAdjoint (X : M2C) :
    (cartanHermitian X)ᴴ = cartanHermitian X := by
  simp [cartanHermitian, add_comm]

theorem cartan_split_unique (X K H : M2C)
    (hK : Kᴴ = -K) (hH : Hᴴ = H) (h : X = K + H) :
    K = cartanSkew X ∧ H = cartanHermitian X := by
  constructor
  · unfold cartanSkew
    rw [h]
    simp [hK, hH]
    module
  · unfold cartanHermitian
    rw [h]
    simp [hK, hH]
    module

theorem cartanSkew_eq_zero_iff (X : M2C) :
    cartanSkew X = 0 ↔ Xᴴ = X := by
  unfold cartanSkew
  constructor
  · intro h
    have hsub : X - Xᴴ = 0 := by
      apply (smul_eq_zero.mp h).resolve_left
      norm_num
    exact (sub_eq_zero.mp hsub).symm
  · intro h
    simp [h]

theorem cartanHermitian_eq_zero_iff (X : M2C) :
    cartanHermitian X = 0 ↔ Xᴴ = -X := by
  unfold cartanHermitian
  constructor
  · intro h
    have hadd : X + Xᴴ = 0 := by
      apply (smul_eq_zero.mp h).resolve_left
      norm_num
    exact eq_neg_of_add_eq_zero_right hadd
  · intro h
    simp [h]

theorem gram_neg (A : M2C) :
    gram (-A) = gram A := by
  unfold gram
  simp

theorem gramTrace_neg (A : M2C) :
    gramTrace (-A) = gramTrace A := by
  unfold gramTrace
  rw [gram_neg]

theorem densityMatrix_neg (A : M2C) :
    densityMatrix (-A) = densityMatrix A := by
  unfold densityMatrix
  rw [gramTrace_neg, gram_neg]

theorem gram_positive (A : M2C) : GramPositive (gram A) :=
  ⟨A, rfl⟩

theorem gram_isHermitian (A : M2C) : (gram A).IsHermitian := by
  exact isHermitian_mul_conjTranspose_self A

theorem gram_posSemidef (A : M2C) : (gram A).PosSemidef := by
  exact posSemidef_self_mul_conjTranspose A

theorem gramTrace_formula (A : M2C) :
    gramTrace A = ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (A i j) := by
  classical
  simp [gramTrace, gram, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose, Fin.sum_univ_two, Complex.normSq_apply]

theorem gramTrace_nonneg (A : M2C) : 0 ≤ gramTrace A := by
  rw [gramTrace_formula]
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _

theorem gramTrace_eq_zero_iff (A : M2C) :
    gramTrace A = 0 ↔ A = 0 := by
  rw [gramTrace_formula]
  constructor
  · intro h
    have hrows' :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun i => Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _)).mp h
    funext i
    funext j
    have hrow : (∑ k : Fin 2, Complex.normSq (A i k)) = 0 := congrFun hrows' i
    exact Complex.normSq_eq_zero.mp
      (congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg
          (fun j => Complex.normSq_nonneg (A i j))).mp hrow) j)
  · intro h
    subst A
    simp

theorem gramTrace_pos_of_ne_zero {A : M2C} (hA : A ≠ 0) :
    0 < gramTrace A := by
  have hne : gramTrace A ≠ 0 := by
    intro h
    exact hA ((gramTrace_eq_zero_iff A).mp h)
  exact lt_of_le_of_ne (gramTrace_nonneg A) (Ne.symm hne)

theorem trace_rightDensityMatrix_of_ne_zero {A : M2C} (hA : A ≠ 0) :
    Matrix.trace (rightDensityMatrix A) = 1 := by
  unfold rightDensityMatrix gramTrace
  rw [Matrix.trace_smul]
  have htr : (Matrix.trace (gram A)).re ≠ 0 := by
    exact ne_of_gt (gramTrace_pos_of_ne_zero hA)
  have hright : Matrix.trace (rightGram A) = Matrix.trace (gram A) := by
    exact (gram_trace_eq_rightGram_trace A).symm
  rw [hright]
  have hreal : Matrix.trace (gram A) = ((Matrix.trace (gram A)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [gram, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose,
        Fin.sum_univ_two]
      ring
  rw [hreal]
  simp [htr]

theorem rightDensityMatrix_isHermitian_of_ne_zero {A : M2C} (_hA : A ≠ 0) :
    (rightDensityMatrix A).IsHermitian := by
  unfold rightDensityMatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hc : star ((gramTrace A : ℂ)⁻¹) = (gramTrace A : ℂ)⁻¹ := by
    simp
  rw [hc, rightGram_isHermitian]

theorem rightDensityMatrix_isHermitian (A : M2C) :
    (rightDensityMatrix A).IsHermitian := by
  unfold rightDensityMatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hc : star ((gramTrace A : ℂ)⁻¹) = (gramTrace A : ℂ)⁻¹ := by
    simp
  rw [hc, rightGram_isHermitian]

theorem rightDensityMatrix_posSemidef {A : M2C} (hA : A ≠ 0) :
    (rightDensityMatrix A).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨rightDensityMatrix_isHermitian_of_ne_zero hA, ?_⟩
  intro x
  have hraw := (rightGram_posSemidef A).dotProduct_mulVec_nonneg x
  have hcp : 0 < (gramTrace A : ℂ) := by
    exact_mod_cast gramTrace_pos_of_ne_zero hA
  have hc : 0 ≤ (gramTrace A : ℂ)⁻¹ :=
    (le_of_lt (RCLike.inv_pos.mpr hcp))
  simpa [rightDensityMatrix, Matrix.smul_mulVec] using mul_nonneg hc hraw

theorem densityMatrix_projectiveGramPositive {A : M2C} (hA : A ≠ 0) :
    ProjectiveGramPositive (densityMatrix A) := by
  refine ⟨gramTrace A, gramTrace_pos_of_ne_zero hA, A, ?_⟩
  rfl

theorem densityMatrix_isHermitian_of_ne_zero {A : M2C} (_hA : A ≠ 0) :
    (densityMatrix A).IsHermitian := by
  unfold densityMatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hc : star ((gramTrace A : ℂ)⁻¹) = (gramTrace A : ℂ)⁻¹ := by
    simp
  rw [hc, gram_isHermitian A]

theorem densityMatrix_isHermitian (A : M2C) :
    (densityMatrix A).IsHermitian := by
  unfold densityMatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hc : star ((gramTrace A : ℂ)⁻¹) = (gramTrace A : ℂ)⁻¹ := by
    simp
  rw [hc, gram_isHermitian A]

theorem densityMatrix_posSemidef {A : M2C} (hA : A ≠ 0) :
    (densityMatrix A).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨densityMatrix_isHermitian_of_ne_zero hA, ?_⟩
  intro x
  have hraw := (gram_posSemidef A).dotProduct_mulVec_nonneg x
  have hcp : 0 < (gramTrace A : ℂ) := by
    exact_mod_cast gramTrace_pos_of_ne_zero hA
  have hc : 0 ≤ (gramTrace A : ℂ)⁻¹ :=
    (le_of_lt (RCLike.inv_pos.mpr hcp))
  simpa [densityMatrix, Matrix.smul_mulVec] using mul_nonneg hc hraw

theorem trace_densityMatrix_of_ne_zero {A : M2C} (hA : A ≠ 0) :
    Matrix.trace (densityMatrix A) = 1 := by
  unfold densityMatrix gramTrace
  rw [Matrix.trace_smul]
  have htr : (Matrix.trace (gram A)).re ≠ 0 := by
    exact ne_of_gt (gramTrace_pos_of_ne_zero hA)
  have hreal : Matrix.trace (gram A) = ((Matrix.trace (gram A)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [gram, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose,
        Fin.sum_univ_two]
      ring
  rw [hreal]
  simp [htr]

theorem densityMatrix_ne_zero {A : M2C} (hA : A ≠ 0) :
    densityMatrix A ≠ 0 := by
  intro hzero
  have htrace := congrArg Matrix.trace hzero
  rw [trace_densityMatrix_of_ne_zero hA] at htrace
  simp at htrace

/-! ## Symmetric and antisymmetric first quantization -/

/-! ## Spin connection and first quantization -/

/-- Algebraic spin connection action in the chiral matrix block. -/
def spinConnection (Ω X : M2C) : M2C := Ω * X - X * Ω

theorem spinConnection_add (Ω₁ Ω₂ X : M2C) :
    spinConnection (Ω₁ + Ω₂) X =
      spinConnection Ω₁ X + spinConnection Ω₂ X := by
  simp [spinConnection, mul_add, add_mul]
  module

theorem spinConnection_add_right (Ω X₁ X₂ : M2C) :
    spinConnection Ω (X₁ + X₂) =
      spinConnection Ω X₁ + spinConnection Ω X₂ := by
  simp [spinConnection, mul_add, add_mul]
  module

theorem spinConnection_zero (Ω : M2C) :
    spinConnection Ω 0 = 0 := by
  simp [spinConnection]

theorem spinConnection_mul (Ω X Y : M2C) :
    spinConnection Ω (X * Y) =
      spinConnection Ω X * Y + X * spinConnection Ω Y := by
  unfold spinConnection
  noncomm_ring

/-! The following two maps are the finite matrix realization of the symmetric
and antisymmetric parts of the classical `xp` product. -/

/-- Symmetric lift of the classical product `xp`. -/
def symmetricXP (X P : M2C) : M2C :=
  (1 / 2 : ℂ) • (X * P + P * X)

/-- Antisymmetric lift of the classical product `xp`. -/
def antisymmetricXP (X P : M2C) : M2C :=
  (1 / 2 : ℂ) • (X * P - P * X)

theorem spinConnection_swap (X P : M2C) :
    spinConnection P X = -spinConnection X P := by
  unfold spinConnection
  noncomm_ring

theorem antisymmetricXP_eq_half_spinConnection (X P : M2C) :
    antisymmetricXP X P = (1 / 2 : ℂ) • spinConnection X P := by
  rfl

theorem spinConnection_eq_two_smul_antisymmetricXP (X P : M2C) :
    spinConnection X P = (2 : ℂ) • antisymmetricXP X P := by
  unfold spinConnection antisymmetricXP
  module

theorem xp_split (X P : M2C) :
    X * P = symmetricXP X P + antisymmetricXP X P := by
  simp [symmetricXP, antisymmetricXP]
  module

theorem symmetricXP_swap (X P : M2C) :
    symmetricXP P X = symmetricXP X P := by
  simp [symmetricXP, add_comm]

theorem antisymmetricXP_swap (X P : M2C) :
    antisymmetricXP P X = -antisymmetricXP X P := by
  simp [antisymmetricXP, sub_eq_add_neg]

/-! ## Consolidated finite quantization chain -/

theorem finite_hestenes_spin_density_xp_chain
    (r : RapidityFourVector) (A X P : M2C) (hA : A ≠ 0) :
      (solderRapidity r).det =
        (r.time : ℂ) ^ 2 - r.x ^ 2 - r.y ^ 2 - r.z ^ 2 ∧
      ProjectiveGramPositive (densityMatrix A) ∧
      (densityMatrix A).PosSemidef ∧
      (densityMatrix A).IsHermitian ∧
      Matrix.trace (densityMatrix A) = 1 ∧
      X * P = symmetricXP X P + antisymmetricXP X P ∧
      spinConnection X P = X * P - P * X := by
  exact ⟨solderRapidity_det r,
    densityMatrix_projectiveGramPositive hA,
    densityMatrix_posSemidef hA,
    densityMatrix_isHermitian_of_ne_zero hA,
    trace_densityMatrix_of_ne_zero hA,
    xp_split X P,
    rfl⟩

end InfoGeometry.Physics.HestenesSpinDensityXpQuantization

end noncomputable section
