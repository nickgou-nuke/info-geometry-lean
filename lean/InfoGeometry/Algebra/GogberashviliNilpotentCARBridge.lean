import Mathlib

/-!
# Chiral Zorn CAR, scalar Schur complement, and BdG Berezinian

This file closes two finite algebraic layers with native Mathlib structures.

* In an associative algebra over a field with `2 ≠ 0`, a split triad
  `I² = 1`, `j² = -1`, `jI = -Ij` produces complementary idempotents and a
  nilpotent CAR pair.
* For a scalar `2 × 2` block, its determinant/Zorn-norm shadow, Schur
  complement, and scalar Berezinian satisfy exact field identities.

The CAR result is deliberately modewise and associative. It does not install
an associative multiplication on the full split-octonion Zorn carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra

namespace GogberashviliNilpotentCARBridge

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Positive primitive idempotent associated with an involution `J`. -/
def DPlus (J : A) : A :=
  (2 : K)⁻¹ • (1 + J)

/-- Negative primitive idempotent associated with an involution `J`. -/
def DMinus (J : A) : A :=
  (2 : K)⁻¹ • (1 - J)

/-- Positive nilpotent mode. -/
def GPlus (I j : A) : A :=
  (2 : K)⁻¹ • (I + j)

/-- Negative nilpotent mode. -/
def GMinus (I j : A) : A :=
  (2 : K)⁻¹ • (I - j)

private theorem smul_mul_smul
    (r s : K) (x y : A) :
    (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

private theorem inv_two_sq_mul_two
    (h2 : (2 : K) ≠ 0) :
    (2 : K)⁻¹ * (2 : K)⁻¹ * 2 = (2 : K)⁻¹ := by
  calc
    (2 : K)⁻¹ * (2 : K)⁻¹ * 2
        = (2 : K)⁻¹ * ((2 : K)⁻¹ * 2) := by
            rw [mul_assoc]
    _ = (2 : K)⁻¹ * 1 := by
          rw [inv_mul_cancel₀ h2]
    _ = (2 : K)⁻¹ := by
          rw [mul_one]

/-- The split triad determines an involutive projector axis `J² = 1`. -/
theorem J_square_one
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    J * J = 1 := by
  rw [hJ]
  calc
    (I * j) * (I * j) = I * (j * I) * j := by
      simp only [mul_assoc]
    _ = I * (-(I * j)) * j := by
      rw [hcross]
    _ = -((I * I) * (j * j)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = 1 := by
      rw [hI, hj]
      simp

/-- The two primitive idempotents resolve the unit. -/
@[simp]
theorem DPlus_add_DMinus
    (h2 : (2 : K) ≠ 0)
    (J : A) :
    DPlus (K := K) J + DMinus (K := K) J = 1 := by
  unfold DPlus DMinus
  rw [← smul_add]
  have hsum :
      (1 + J) + (1 - J) = (2 : K) • (1 : A) := by
    calc
      (1 + J) + (1 - J) = (1 : A) + 1 := by
        abel
      _ = ((1 : K) + 1) • (1 : A) := by
        rw [add_smul, one_smul]
      _ = (2 : K) • (1 : A) := by
        norm_num
  rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- `DPlus` is idempotent when `J² = 1`. -/
@[simp]
theorem DPlus_idempotent
    (h2 : (2 : K) ≠ 0)
    (J : A)
    (hJ : J * J = 1) :
    DPlus (K := K) J * DPlus (K := K) J =
      DPlus (K := K) J := by
  unfold DPlus
  rw [smul_mul_smul]
  have hsq :
      (1 + J) * (1 + J) = (2 : K) • (1 + J) := by
    calc
      (1 + J) * (1 + J) = 1 + J + J + J * J := by
        noncomm_ring
      _ = 1 + J + J + 1 := by
        rw [hJ]
      _ = (2 : K) • (1 + J) := by
        rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
        abel
  rw [hsq, smul_smul, inv_two_sq_mul_two h2]

/-- `DMinus` is idempotent when `J² = 1`. -/
@[simp]
theorem DMinus_idempotent
    (h2 : (2 : K) ≠ 0)
    (J : A)
    (hJ : J * J = 1) :
    DMinus (K := K) J * DMinus (K := K) J =
      DMinus (K := K) J := by
  unfold DMinus
  rw [smul_mul_smul]
  have hsq :
      (1 - J) * (1 - J) = (2 : K) • (1 - J) := by
    calc
      (1 - J) * (1 - J) = 1 - J - J + J * J := by
        noncomm_ring
      _ = 1 - J - J + 1 := by
        rw [hJ]
      _ = (2 : K) • (1 - J) := by
        rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
        abel
  rw [hsq, smul_smul, inv_two_sq_mul_two h2]

/-- The complementary projectors are orthogonal in this order. -/
@[simp]
theorem DPlus_mul_DMinus
    (J : A)
    (hJ : J * J = 1) :
    DPlus (K := K) J * DMinus (K := K) J = 0 := by
  unfold DPlus DMinus
  rw [smul_mul_smul]
  have hprod : (1 + J) * (1 - J) = 0 := by
    calc
      (1 + J) * (1 - J) = 1 - J + J - J * J := by
        noncomm_ring
      _ = 1 - J + J - 1 := by
        rw [hJ]
      _ = 0 := by
        abel
  rw [hprod, smul_zero]

/-- The complementary projectors are orthogonal in the reverse order. -/
@[simp]
theorem DMinus_mul_DPlus
    (J : A)
    (hJ : J * J = 1) :
    DMinus (K := K) J * DPlus (K := K) J = 0 := by
  unfold DPlus DMinus
  rw [smul_mul_smul]
  have hprod : (1 - J) * (1 + J) = 0 := by
    calc
      (1 - J) * (1 + J) = 1 + J - J - J * J := by
        noncomm_ring
      _ = 1 + J - J - 1 := by
        rw [hJ]
      _ = 0 := by
        abel
  rw [hprod, smul_zero]

/-- The positive mode squares to zero. -/
@[simp]
theorem GPlus_square_zero
    (I j : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    GPlus (K := K) I j * GPlus (K := K) I j = 0 := by
  unfold GPlus
  rw [smul_mul_smul]
  have hsq : (I + j) * (I + j) = 0 := by
    calc
      (I + j) * (I + j) = I * I + I * j + j * I + j * j := by
        noncomm_ring
      _ = 1 + (I * j + j * I) - 1 := by
        rw [hI, hj]
        abel
      _ = 0 := by
        rw [hanti]
        abel
  rw [hsq, smul_zero]

/-- The negative mode squares to zero. -/
@[simp]
theorem GMinus_square_zero
    (I j : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    GMinus (K := K) I j * GMinus (K := K) I j = 0 := by
  unfold GMinus
  rw [smul_mul_smul]
  have hsq : (I - j) * (I - j) = 0 := by
    calc
      (I - j) * (I - j) = I * I - I * j - j * I + j * j := by
        noncomm_ring
      _ = 1 - (I * j + j * I) - 1 := by
        rw [hI, hj]
        abel
      _ = 0 := by
        rw [hanti]
        abel
  rw [hsq, smul_zero]

/-- The ordered nilpotent product gives the negative projector. -/
@[simp]
theorem GPlus_mul_GMinus
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    GPlus (K := K) I j * GMinus (K := K) I j =
      DMinus (K := K) J := by
  unfold GPlus GMinus DMinus
  rw [smul_mul_smul]
  have hprod :
      (I + j) * (I - j) = (2 : K) • (1 - J) := by
    calc
      (I + j) * (I - j) = I * I - I * j + j * I - j * j := by
        noncomm_ring
      _ = 1 - I * j - I * j + 1 := by
        rw [hI, hj, hcross]
        abel
      _ = (2 : K) • (1 - J) := by
        rw [hJ, show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
        abel
  rw [hprod, smul_smul, inv_two_sq_mul_two h2]

/-- The reverse nilpotent product gives the positive projector. -/
@[simp]
theorem GMinus_mul_GPlus
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    GMinus (K := K) I j * GPlus (K := K) I j =
      DPlus (K := K) J := by
  unfold GPlus GMinus DPlus
  rw [smul_mul_smul]
  have hprod :
      (I - j) * (I + j) = (2 : K) • (1 + J) := by
    calc
      (I - j) * (I + j) = I * I + I * j - j * I - j * j := by
        noncomm_ring
      _ = 1 + I * j + I * j + 1 := by
        rw [hI, hj, hcross]
        abel
      _ = (2 : K) • (1 + J) := by
        rw [hJ, show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
        abel
  rw [hprod, smul_smul, inv_two_sq_mul_two h2]

/-- Exact modewise canonical anticommutation relation. -/
theorem GPlus_GMinus_CAR
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    GPlus (K := K) I j * GMinus (K := K) I j +
      GMinus (K := K) I j * GPlus (K := K) I j = 1 := by
  rw [GPlus_mul_GMinus h2 I j J hI hj hcross hJ,
    GMinus_mul_GPlus h2 I j J hI hj hcross hJ]
  simpa [add_comm] using DPlus_add_DMinus h2 J

/-- Complete finite CAR packet, with every projector law derived from the
split-triad hypotheses. -/
theorem full_car_packet
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    J * J = 1 ∧
      DPlus (K := K) J * DPlus (K := K) J = DPlus (K := K) J ∧
      DMinus (K := K) J * DMinus (K := K) J = DMinus (K := K) J ∧
      DPlus (K := K) J * DMinus (K := K) J = 0 ∧
      DMinus (K := K) J * DPlus (K := K) J = 0 ∧
      GPlus (K := K) I j * GPlus (K := K) I j = 0 ∧
      GMinus (K := K) I j * GMinus (K := K) I j = 0 ∧
      GPlus (K := K) I j * GMinus (K := K) I j = DMinus (K := K) J ∧
      GMinus (K := K) I j * GPlus (K := K) I j = DPlus (K := K) J ∧
      DPlus (K := K) J + DMinus (K := K) J = 1 ∧
      GPlus (K := K) I j * GMinus (K := K) I j +
        GMinus (K := K) I j * GPlus (K := K) I j = 1 := by
  have hJsq : J * J = 1 := J_square_one I j J hI hj hcross hJ
  have hanti : I * j + j * I = 0 := by
    rw [hcross]
    abel
  exact
    ⟨hJsq,
      DPlus_idempotent h2 J hJsq,
      DMinus_idempotent h2 J hJsq,
      DPlus_mul_DMinus J hJsq,
      DMinus_mul_DPlus J hJsq,
      GPlus_square_zero I j hI hj hanti,
      GMinus_square_zero I j hI hj hanti,
      GPlus_mul_GMinus h2 I j J hI hj hcross hJ,
      GMinus_mul_GPlus h2 I j J hI hj hcross hJ,
      DPlus_add_DMinus h2 J,
      GPlus_GMinus_CAR h2 I j J hI hj hcross hJ⟩

/-! ## Compatibility aliases for the original frozen API -/

abbrev D_plus := DPlus
abbrev D_minus := DMinus
abbrev G_plus := GPlus
abbrev G_minus := GMinus

theorem D_plus_add_D_minus
    (h2 : (2 : K) ≠ 0) (J : A) :
    D_plus (K := K) J + D_minus (K := K) J = 1 :=
  DPlus_add_DMinus h2 J

theorem D_plus_idempotent
    (h2 : (2 : K) ≠ 0) (J : A) (hJ : J * J = 1) :
    D_plus (K := K) J * D_plus (K := K) J = D_plus (K := K) J :=
  DPlus_idempotent h2 J hJ

theorem D_minus_idempotent
    (h2 : (2 : K) ≠ 0) (J : A) (hJ : J * J = 1) :
    D_minus (K := K) J * D_minus (K := K) J = D_minus (K := K) J :=
  DMinus_idempotent h2 J hJ

theorem D_plus_mul_D_minus
    (J : A) (hJ : J * J = 1) :
    D_plus (K := K) J * D_minus (K := K) J = 0 :=
  DPlus_mul_DMinus J hJ

theorem D_minus_mul_D_plus
    (J : A) (hJ : J * J = 1) :
    D_minus (K := K) J * D_plus (K := K) J = 0 :=
  DMinus_mul_DPlus J hJ

theorem G_plus_square_zero
    (I j : A) (hI : I * I = 1) (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    G_plus (K := K) I j * G_plus (K := K) I j = 0 :=
  GPlus_square_zero I j hI hj hanti

theorem G_minus_square_zero
    (I j : A) (hI : I * I = 1) (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    G_minus (K := K) I j * G_minus (K := K) I j = 0 :=
  GMinus_square_zero I j hI hj hanti

theorem G_plus_mul_G_minus
    (h2 : (2 : K) ≠ 0) (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1)
    (hcross : j * I = -(I * j)) (hJ : J = I * j) :
    G_plus (K := K) I j * G_minus (K := K) I j =
      D_minus (K := K) J :=
  GPlus_mul_GMinus h2 I j J hI hj hcross hJ

theorem G_minus_mul_G_plus
    (h2 : (2 : K) ≠ 0) (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1)
    (hcross : j * I = -(I * j)) (hJ : J = I * j) :
    G_minus (K := K) I j * G_plus (K := K) I j =
      D_plus (K := K) J :=
  GMinus_mul_GPlus h2 I j J hI hj hcross hJ

theorem G_plus_G_minus_CAR
    (h2 : (2 : K) ≠ 0) (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1)
    (hcross : j * I = -(I * j)) (hJ : J = I * j) :
    G_plus (K := K) I j * G_minus (K := K) I j +
      G_minus (K := K) I j * G_plus (K := K) I j = 1 :=
  GPlus_GMinus_CAR h2 I j J hI hj hcross hJ

end GogberashviliNilpotentCARBridge

namespace ZornNormSchurScalarSpecialization

variable {F : Type*} [Field F]

/-- Scalar `2 × 2` block. -/
def blockMatrix (α β u v : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α, u; v, β]

/-- Scalar Schur complement with respect to the lower-right entry. -/
def schurComplement (α β u v : F) : F :=
  α - u * β⁻¹ * v

/-- Scalar Berezinian convention `Ber = Schur / β`. -/
def berezinianScalar (α β u v : F) : F :=
  schurComplement α β u v / β

/-- Scalar Zorn composition-norm/determinant shadow. -/
def zornNorm (α β u v : F) : F :=
  α * β - u * v

@[simp]
theorem det_blockMatrix
    (α β u v : F) :
    Matrix.det (blockMatrix α β u v) =
      zornNorm α β u v := by
  simp [blockMatrix, zornNorm, Matrix.det_fin_two]

/-- The Schur complement is the Zorn norm divided by the pivot. -/
theorem schur_scalar_formula
    (α β u v : F)
    (hβ : β ≠ 0) :
    schurComplement α β u v =
      zornNorm α β u v / β := by
  unfold schurComplement zornNorm
  field_simp [hβ]
  ring

/-- The Zorn norm reconstructs from the Schur complement and the pivot. -/
theorem zornNorm_eq_schur_mul_beta
    (α β u v : F)
    (hβ : β ≠ 0) :
    zornNorm α β u v =
      schurComplement α β u v * β := by
  rw [schur_scalar_formula α β u v hβ]
  exact (div_mul_cancel₀ (zornNorm α β u v) hβ).symm

/-- Scalar Berezinian equals the Zorn norm divided by the squared pivot. -/
theorem berezinian_eq_zornNorm_div_sq
    (α β u v : F)
    (hβ : β ≠ 0) :
    berezinianScalar α β u v =
      zornNorm α β u v / β ^ 2 := by
  unfold berezinianScalar
  rw [schur_scalar_formula α β u v hβ]
  field_simp [hβ]
  ring

/-- Scalar Berezinian equals the ordinary determinant divided by the squared
lower-right block. -/
theorem berezinian_eq_det_div_sq
    (α β u v : F)
    (hβ : β ≠ 0) :
    berezinianScalar α β u v =
      Matrix.det (blockMatrix α β u v) / β ^ 2 := by
  rw [det_blockMatrix]
  exact berezinian_eq_zornNorm_div_sq α β u v hβ

/-- Complete scalar Schur/Berezinian packet. -/
theorem scalar_schur_berezinian_packet
    (α β u v : F)
    (hβ : β ≠ 0) :
    Matrix.det (blockMatrix α β u v) =
        zornNorm α β u v ∧
      schurComplement α β u v =
        zornNorm α β u v / β ∧
      zornNorm α β u v =
        schurComplement α β u v * β ∧
      berezinianScalar α β u v =
        zornNorm α β u v / β ^ 2 ∧
      berezinianScalar α β u v =
        Matrix.det (blockMatrix α β u v) / β ^ 2 := by
  exact
    ⟨det_blockMatrix α β u v,
      schur_scalar_formula α β u v hβ,
      zornNorm_eq_schur_mul_beta α β u v hβ,
      berezinian_eq_zornNorm_div_sq α β u v hβ,
      berezinian_eq_det_div_sq α β u v hβ⟩

/-! ## Compatibility aliases for the original scalar API -/

abbrev zorn_norm := zornNorm

theorem berezinian_eq_zorn_norm_div_sq
    (α β u v : F)
    (hβ : β ≠ 0) :
    berezinianScalar α β u v =
      zorn_norm α β u v / β ^ 2 :=
  berezinian_eq_zornNorm_div_sq α β u v hβ

theorem zorn_norm_eq_schur_mul_beta
    (α β u v : F)
    (hβ : β ≠ 0) :
    zorn_norm α β u v =
      schurComplement α β u v * β :=
  zornNorm_eq_schur_mul_beta α β u v hβ

end ZornNormSchurScalarSpecialization

namespace BdGSchurBerezinianCompatibility

open ZornNormSchurScalarSpecialization

variable {F : Type*} [Field F]

/-- Scalar particle-hole/BdG block. -/
def bdgBlock (h Δ : F) :
    Matrix (Fin 2) (Fin 2) F :=
  blockMatrix h (-h) Δ Δ

/-- The scalar BdG determinant is the negative quadratic gap. -/
@[simp]
theorem det_bdgBlock
    (h Δ : F) :
    Matrix.det (bdgBlock h Δ) =
      -(h ^ 2 + Δ ^ 2) := by
  rw [bdgBlock, det_blockMatrix]
  unfold zornNorm
  ring

/-- The lower-right Schur complement of the scalar BdG block. -/
theorem schur_bdgBlock
    (h Δ : F)
    (hh : h ≠ 0) :
    schurComplement h (-h) Δ Δ =
      (h ^ 2 + Δ ^ 2) / h := by
  rw [schur_scalar_formula]
  · unfold zornNorm
    field_simp [hh]
    ring
  · exact neg_ne_zero.mpr hh

/-- The scalar BdG Berezinian is the negative normalized quadratic gap. -/
theorem berezinian_bdgBlock
    (h Δ : F)
    (hh : h ≠ 0) :
    berezinianScalar h (-h) Δ Δ =
      -(h ^ 2 + Δ ^ 2) / h ^ 2 := by
  rw [berezinian_eq_zornNorm_div_sq]
  · unfold zornNorm
    field_simp [hh]
    ring
  · exact neg_ne_zero.mpr hh

/-- Exact scalar BdG compatibility packet. -/
theorem bdg_schur_berezinian_packet
    (h Δ : F)
    (hh : h ≠ 0) :
    Matrix.det (bdgBlock h Δ) =
        -(h ^ 2 + Δ ^ 2) ∧
      schurComplement h (-h) Δ Δ =
        (h ^ 2 + Δ ^ 2) / h ∧
      berezinianScalar h (-h) Δ Δ =
        -(h ^ 2 + Δ ^ 2) / h ^ 2 := by
  exact
    ⟨det_bdgBlock h Δ,
      schur_bdgBlock h Δ hh,
      berezinian_bdgBlock h Δ hh⟩

end BdGSchurBerezinianCompatibility

end InfoGeometry.Algebra

end noncomputable section