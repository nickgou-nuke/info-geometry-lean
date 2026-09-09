import Mathlib.Tactic

/-!
# Moore--Penrose inverse of a retrocirculant

Theorem-safe Lean scaffold for Ronald L. Smith,
"The Moore-Penrose Inverse of a Retrocirculant", Linear Algebra Appl. 22,
1--8 (1978).

Smith proves that a retrocirculant `A = P C`, where `P` is a Fourier-commuting
involutory permutation matrix and `C` is circulant, has Moore--Penrose inverse
`A⁺ = C⁺ Pᵀ`; moreover `A⁺` is again retrocirculant and the nonzero eigenvalues
are reciprocals.  The analytic/unitary Fourier layer is kept as explicit
certificates.  A concrete exact `2 × 2` Penrose calculation is proved directly.
-/

namespace InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose

noncomputable section

universe u

/-- Algebraic doubly-sided Penrose equations without conjugation.  This is the
finite exact-rational form used by the CAS witnesses; the complex/unitary
Moore--Penrose interpretation is supplied by owner certificates below. -/
def AlgebraicMoorePenrosePair {K : Type u} [Field K] {n : ℕ}
    (A Aplus : Matrix (Fin n) (Fin n) K) : Prop :=
  A * Aplus * A = A ∧
    Aplus * A * Aplus = Aplus ∧
      Matrix.transpose (A * Aplus) = A * Aplus ∧
        Matrix.transpose (Aplus * A) = Aplus * A

/-- The `2 × 2` retrocirculant block `P * diag(a,b)`. -/
def retro2 {K : Type u} [Zero K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, b; a, 0]

/-- Its inverse/Penrose inverse when `a` and `b` are nonzero. -/
def retro2Plus {K : Type u} [DivisionSemiring K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, a⁻¹; b⁻¹, 0]

/-- Exact Penrose equations for the nonzero `2 × 2` retrocirculant block. -/
theorem retro2_penrose {K : Type u} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicMoorePenrosePair (retro2 a b) (retro2Plus a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]

/-- Smith retrocirculant data: `A = P C`, with Fourier-commutation and
circulant status left as explicit predicates owned by the spectral layer. -/
structure RetrocirculantData (K : Type u) [Field K] {n : ℕ}
    (A P C : Matrix (Fin n) (Fin n) K) where
  isCirculant : Matrix (Fin n) (Fin n) K → Prop
  commutesWithFourier : Matrix (Fin n) (Fin n) K → Prop
  permutationInvolution : P * P = 1
  P_commutesWithFourier : commutesWithFourier P
  C_circulant : isCirculant C
  retro_readout : A = P * C

namespace RetrocirculantData

variable {K : Type u} [Field K] {n : ℕ}
variable {A P C : Matrix (Fin n) (Fin n) K}
/-- Read out Smith's definition of a retrocirculant. -/
theorem as_product (R : RetrocirculantData K A P C) : A = P * C := by
  cases R with
  | mk isCirculant commutesWithFourier permutationInvolution P_commutesWithFourier C_circulant retro_readout =>
      exact retro_readout

end RetrocirculantData

/-- Certificate for Smith Theorem 1: `A = P C` is retrocirculant iff `A⁺` is
retrocirculant, and in that case `A⁺ = C⁺ Pᵀ`. -/
structure SmithMoorePenroseRetrocirculantCertificate
    (K : Type u) [Field K] {n : ℕ}
    (A Aplus P C Cplus : Matrix (Fin n) (Fin n) K) where
  retro : RetrocirculantData K A P C
  penroseC : AlgebraicMoorePenrosePair C Cplus
  penroseA : AlgebraicMoorePenrosePair A Aplus
  formula : Aplus = Cplus * Matrix.transpose P
  /-- Smith closure as actual retrocirculant factorization data for `A⁺`. -/
  Aplus_retro :
    RetrocirculantData K Aplus (Matrix.transpose P) Cplus

namespace SmithMoorePenroseRetrocirculantCertificate

variable {K : Type u} [Field K] {n : ℕ}
variable {A Aplus P C Cplus : Matrix (Fin n) (Fin n) K}
/-- Smith's Moore--Penrose inverse formula. -/
theorem moorePenrose_formula (S : SmithMoorePenroseRetrocirculantCertificate K A Aplus P C Cplus) : Aplus = Cplus * Matrix.transpose P := by
  cases S with
  | mk retro penroseC penroseA formula Aplus_retro =>
      exact formula

/-- Historical predicate name, now the actual existence of the stored
retrocirculant factorization. -/
abbrev Aplus_is_retrocirculant
    (S : SmithMoorePenroseRetrocirculantCertificate K A Aplus P C Cplus) : Prop :=
  Nonempty (RetrocirculantData K Aplus (Matrix.transpose P) Cplus)

/-- Smith's retrocirculant closure readout for the Moore--Penrose inverse. -/
theorem plus_is_retrocirculant
    (S : SmithMoorePenroseRetrocirculantCertificate K A Aplus P C Cplus) :
    S.Aplus_is_retrocirculant :=
  ⟨S.Aplus_retro⟩

end SmithMoorePenroseRetrocirculantCertificate

/-- Block diagonal similarity/eigenvalue certificate from Smith Lemma 4 and
Theorem 3. -/
structure RetrocirculantSpectralBlockCertificate
    (K : Type u) [Field K] [StarRing K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) where
  /-- Concrete block normal form and its change of basis. -/
  blockMatrix : Matrix (Fin n) (Fin n) K
  unitary : Matrix (Fin n) (Fin n) K
  unitary_star_mul : star unitary * unitary = 1
  unitary_mul_star : unitary * star unitary = 1
  similarity :
    A = unitary * blockMatrix * star unitary
  eigenvalueReadout : K → Prop
  reciprocalEigenvalueReadout : K → Prop
  theorem3_readout : eigenvalueReadout 0 ∨ ∃ μ, eigenvalueReadout μ
  corollary2_readout : ∀ μ, μ ≠ 0 → eigenvalueReadout μ → reciprocalEigenvalueReadout μ⁻¹

namespace RetrocirculantSpectralBlockCertificate

variable {K : Type u} [Field K] [StarRing K] {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) K}
variable (S : RetrocirculantSpectralBlockCertificate K A)

/-- Historical similarity name, now the explicit unitary conjugation
equality carried by the certificate. -/
abbrev unitarilySimilarToBlocks : Prop :=
  A = S.unitary * S.blockMatrix * star S.unitary

/-- The stored block model is genuinely unitarily similar to `A`. -/
theorem unitarilySimilarToBlocks_proof :
    S.unitarilySimilarToBlocks :=
  S.similarity

/-- Smith's spectral alternative read directly from the block theorem. -/
theorem eigenvalue_alternative :
    S.eigenvalueReadout 0 ∨ ∃ μ, S.eigenvalueReadout μ :=
  S.theorem3_readout

/-- Nonzero eigenvalues of the Moore--Penrose inverse are supplied reciprocals. -/
theorem reciprocal_nonzero_readout {μ : K} (hμ : μ ≠ 0) (h : S.eigenvalueReadout μ) :
    S.reciprocalEigenvalueReadout μ⁻¹ :=
  S.corollary2_readout μ hμ h

end RetrocirculantSpectralBlockCertificate

/-- Algebraic closure system for Smith Theorems 4 and 5. -/
structure RetrocirculantClosureSystem
    (K : Type u) [Field K] {n : ℕ} where
  isCirculant : Matrix (Fin n) (Fin n) K → Prop
  isRetrocirculant : Matrix (Fin n) (Fin n) K → Prop
  adjointClosure : ∀ A, isRetrocirculant A → isRetrocirculant (Matrix.transpose A)
  addClosure : ∀ A B, isRetrocirculant A → isRetrocirculant B → isRetrocirculant (A + B)
  productCirculant : ∀ A B, isRetrocirculant A → isRetrocirculant B → isCirculant (A * B)
  evenPowerCirculant : ∀ A k, isRetrocirculant A → isCirculant (A ^ (2 * k))
  oddPowerRetrocirculant : ∀ A k, isRetrocirculant A → isRetrocirculant (A ^ (2 * k + 1))

namespace RetrocirculantClosureSystem

variable {K : Type u} [Field K] {n : ℕ}
variable (C : RetrocirculantClosureSystem K (n := n))

/-- Product of two retrocirculants is circulant. -/
theorem product_circulant {A B : Matrix (Fin n) (Fin n) K}
    (hA : C.isRetrocirculant A) (hB : C.isRetrocirculant B) :
    C.isCirculant (A * B) :=
  C.productCirculant A B hA hB

end RetrocirculantClosureSystem

end

end InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose
