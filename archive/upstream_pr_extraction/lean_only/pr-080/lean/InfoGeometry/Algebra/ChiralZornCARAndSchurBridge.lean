import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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

abbrev D_plus (J : A) : A := DPlus (K := K) J
abbrev D_minus (J : A) : A := DMinus (K := K) J
abbrev G_plus (I j : A) : A := GPlus (K := K) I j
abbrev G_minus (I j : A) : A := GMinus (K := K) I j

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

theorem D_plus_add_D_minus
    (h2 : (2 : K) ≠ 0)
    (J : A) :
    D_plus (K := K) J + D_minus (K := K) J = 1 :=
  DPlus_add_DMinus h2 J

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

theorem D_plus_idempotent
    (h2 : (2 : K) ≠ 0)
    (J : A)
    (hJ : J * J = 1) :
    D_plus (K := K) J * D_plus (K := K) J = D_plus (K := K) J :=
  DPlus_idempotent h2 J hJ

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

theorem D_minus_idempotent
    (h2 : (2 : K) ≠ 0)
    (J : A)
    (hJ : J * J = 1) :
    D_minus (K := K) J * D_minus (K := K) J = D_minus (K := K) J :=
  DMinus_idempotent h2 J hJ

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

theorem D_plus_mul_D_minus
    (J : A)
    (hJ : J * J = 1) :
    D_plus (K := K) J * D_minus (K := K) J = 0 :=
  DPlus_mul_DMinus J hJ

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

theorem D_minus_mul_D_plus
    (J : A)
    (hJ : J * J = 1) :
    D_minus (K := K) J * D_plus (K := K) J = 0 :=
  DMinus_mul_DPlus J hJ

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
      (I + j) * (I + j) = I * I + (I * j + j * I) + j * j := by
        noncomm_ring
      _ = 1 + (I * j + j * I) - 1 := by
        rw [hI, hj]
        abel
      _ = 0 := by
        rw [hanti]
        abel
  rw [hsq, smul_zero]

theorem G_plus_square_zero
    (I j : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    G_plus (K := K) I j * G_plus (K := K) I j = 0 :=
  GPlus_square_zero I j hI hj hanti

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
      (I - j) * (I - j) = I * I - (I * j + j * I) + j * j := by
        noncomm_ring
      _ = 1 - (I * j + j * I) - 1 := by
        rw [hI, hj]
        abel
      _ = 0 := by
        rw [hanti]
        abel
  rw [hsq, smul_zero]

theorem G_minus_square_zero
    (I j : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hanti : I * j + j * I = 0) :
    G_minus (K := K) I j * G_minus (K := K) I j = 0 :=
  GMinus_square_zero I j hI hj hanti

/-- The product `GPlus * GMinus` yields the negative projector. -/
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

theorem G_plus_mul_G_minus
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    G_plus (K := K) I j * G_minus (K := K) I j =
      D_minus (K := K) J :=
  GPlus_mul_GMinus h2 I j J hI hj hcross hJ

/-- The product `GMinus * GPlus` yields the positive projector. -/
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

theorem G_minus_mul_G_plus
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    G_minus (K := K) I j * G_plus (K := K) I j =
      D_plus (K := K) J :=
  GMinus_mul_GPlus h2 I j J hI hj hcross hJ

/-- The nilpotent modes satisfy the full CAR anticommutation relation. -/
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
    GMinus_mul_GPlus h2 I j J hI hj hcross hJ,
    add_comm]
  exact DPlus_add_DMinus h2 J

theorem G_plus_G_minus_CAR
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    G_plus (K := K) I j * G_minus (K := K) I j +
        G_minus (K := K) I j * G_plus (K := K) I j = 1 :=
  GPlus_GMinus_CAR h2 I j J hI hj hcross hJ

end GogberashviliNilpotentCARBridge

namespace ZornNormSchurScalarSpecialization

variable {F : Type*} [Field F]

/-- The scalar Schur complement for a 2×2 block with scalar entries -/
def schurComplement (α β u v : F) : F :=
  α - u * β⁻¹ * v

/-- The scalar Berezinian supervolume ratio: Ber(M) = (α - u β⁻¹ v) / β -/
def berezinianScalar (α β u v : F) : F :=
  (schurComplement α β u v) / β

/-- The classical 2×2 determinant (Zorn norm) -/
def zornNorm (α β u v : F) : F :=
  α * β - u * v

/--
THEOREM 1: The scalar Schur complement equals the ratio (α β - u v) / β.
-/
theorem schur_scalar_formula (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α β u v = (zornNorm α β u v) / β := by
  dsimp [schurComplement, zornNorm]
  field_simp

/--
THEOREM 2: The scalar Berezinian is exactly the normalized Zorn norm:
  Ber(M) = (α β - u v) / β² = det(M) / β².
-/
theorem berezinian_eq_zorn_norm_div_sq (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v = (zornNorm α β u v) / (β ^ 2) := by
  dsimp [berezinianScalar]
  rw [schur_scalar_formula α β u v hβ]
  field_simp

/--
THEOREM 3: Exact Reconstruction of the Zorn Determinant from the Schur Complement:
  det(M) = N(Z) = β • (α - u β⁻¹ v).
-/
theorem zorn_norm_eq_schur_mul_beta (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = (schurComplement α β u v) * β := by
  rw [schur_scalar_formula α β u v hβ]
  exact (div_mul_cancel₀ (zornNorm α β u v) hβ).symm

end ZornNormSchurScalarSpecialization

end InfoGeometry.Algebra

end noncomputable section
