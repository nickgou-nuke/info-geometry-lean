/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Pauli-Block Operator Identities ($\mathcal{Z}_1$–$\mathcal{Z}_4$)

Finite matrix identities over an arbitrary ring `[Ring B]`. The `vecOp` map
encodes a three-coordinate operator into `M₂(B)`. This associative matrix
product is not the native split-octonion Zorn product: the repository keeps
that nonassociative product in `ZornVectorMatrix` and `OpZornMatrix` owners.

1. **$\mathcal{Z}_1$** (`zorn_vector_product_dot_plus_cross`):
   Three-coordinate operator `vecOp u₁ u₂ u₃` in `M₂(B)` and its exact
   coordinate product decomposition into `fiberEmbed` and another `vecOp`.
2. **$\mathcal{Z}_2$** (`covariant_dirac_zorn_multiplication_and_pauli_square`):
   Two-sheeted block operator `diracZornOp α β u v ∈ M₂(M₂(B))`,
   its general multiplication law, and the Pauli–Dirac–Zorn wave square.
3. **$\mathcal{Z}_3$** (`matrix_conjugate_product_coordinate_decomposition`):
   A specified coordinate conjugate and its associative matrix product
   decomposition. No split-octonion multiplication is asserted.
4. **$\mathcal{Z}_4$** (`all_scales_inductive_covariant_dirac_zorn_wave_square`):
   All-scales inductive lift of the Pauli–Dirac–Zorn wave square to `ClTower B (n + 2)`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

namespace InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis

/-!
## Archetype $\mathcal{Z}_1$: 3D $Cl(1,1)$ Zorn Vector Operator & Universal Dot-Plus-Cross Product
-/

section ArchetypeZ1_ZornVectorOperator

variable {B : Type*} [Ring B]

/-- 3D $Cl(1,1)$ Zorn vector operator $\mathrm{vecOp}(u_1, u_2, u_3) = \iota(u_1)\Gamma_1 + \iota(u_2)\Sigma + \iota(u_3)\Omega \in M_2(B)$. -/
def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

/-- Zorn split-Minkowski inner product $\langle \mathbf{u}, \mathbf{v}\rangle_{1,1} = u_1 v_1 + u_2 v_2 - u_3 v_3$. -/
def zornDot (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B :=
  u₁ * v₁ + u₂ * v₂ - u₃ * v₃

/-- First component of the Zorn split-3D vector cross product. -/
def zornCross1 (_u₁ u₂ u₃ _v₁ v₂ v₃ : B) : B := u₂ * v₃ - u₃ * v₂
/-- Second component of the Zorn split-3D vector cross product. -/
def zornCross2 (u₁ _u₂ u₃ v₁ _v₂ v₃ : B) : B := u₃ * v₁ - u₁ * v₃
/-- Third component of the Zorn split-3D vector cross product. -/
def zornCross3 (u₁ u₂ _u₃ v₁ v₂ _v₃ : B) : B := -(u₁ * v₂ - u₂ * v₁)

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  rw [sub_eq_add_neg]

@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

/-- **Universal Zorn Vector Dot-Plus-Cross Multiplication Theorem ($\mathcal{Z}_1$)**:
In any noncommutative ring $B$, the product of two Zorn vector operators decomposes into the
Zorn inner product along $1$ plus the Zorn cross product along $(\Gamma_1, \Sigma, \Omega)$:
$\mathrm{vecOp}(\mathbf{u}) \cdot \mathrm{vecOp}(\mathbf{v}) = \iota(\mathrm{zornDot}(\mathbf{u}, \mathbf{v})) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}, \mathbf{v}))$.
In particular, $\mathrm{vecOp}(\mathbf{D})^2 = \iota(D_1^2 + D_2^2 - D_3^2) + \mathrm{vecOp}(\⁅D_2, D_3⁆, \⁅D_3, D_1⁆, -\⁅D_1, D_2⁆)$. -/
theorem zorn_vector_product_dot_plus_cross (u₁ u₂ u₃ v₁ v₂ v₃ D₁ D₂ D₃ : B) :
    vecOp u₁ u₂ u₃ * vecOp v₁ v₂ v₃ =
      fiberEmbed (zornDot u₁ u₂ u₃ v₁ v₂ v₃) +
      vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃)
            (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃)
            (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃) ∧
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  have h_prod : ∀ (a₁ a₂ a₃ b₁ b₂ b₃ : B),
      vecOp a₁ a₂ a₃ * vecOp b₁ b₂ b₃ =
      fiberEmbed (zornDot a₁ a₂ a₃ b₁ b₂ b₃) +
      vecOp (zornCross1 a₁ a₂ a₃ b₁ b₂ b₃)
            (zornCross2 a₁ a₂ a₃ b₁ b₂ b₃)
            (zornCross3 a₁ a₂ a₃ b₁ b₂ b₃) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    apply ext_fin2 <;>
      simp [fiberEmbed, zornDot, zornCross1, zornCross2, zornCross3] <;>
      noncomm_ring
  refine ⟨h_prod u₁ u₂ u₃ v₁ v₂ v₃, ?_⟩
  rw [h_prod D₁ D₂ D₃ D₁ D₂ D₃]
  rfl

end ArchetypeZ1_ZornVectorOperator

/-!
## Archetype $\mathcal{Z}_2$: Covariant Two-Sheeted Dirac–Zorn Operator & Pauli–Dirac Spin-Curvature Coupling
-/

section ArchetypeZ2_CovariantDiracZornOperator

variable {B : Type*} [Ring B]

/-- Nested $2 \times 2$ block matrix algebra $M_2(M_2(B))$. -/
abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Covariant two-sheeted Dirac–Zorn operator
$\mathcal{D}_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \bigl(\begin{smallmatrix} \iota(\alpha) & \mathrm{vecOp}(\mathbf{u}) \\ \mathrm{vecOp}(\mathbf{v}) & \iota(\beta) \end{smallmatrix}\bigr) \in M_2(M_2(B))$. -/
def diracZornOp (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

/-- **Covariant Dirac–Zorn Multiplication & Pauli–Dirac Wave Square Theorem ($\mathcal{Z}_2$)**:
1. Multiplying two Dirac–Zorn operators generates $\iota(\alpha_1\alpha_2 + \mathrm{zornDot}(\mathbf{u}_1, \mathbf{v}_2)) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}_1, \mathbf{v}_2))$
   on the $(0,0)$ block and $\iota(\beta_1\beta_2 + \mathrm{zornDot}(\mathbf{v}_1, \mathbf{u}_2)) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{v}_1, \mathbf{u}_2))$
   on the $(1,1)$ block, with bimodule actions on the off-diagonal.
2. Squaring the symmetric covariant Dirac–Zorn operator $\mathcal{D}_{\mathrm{Zorn}}(m, -m, \mathbf{D}, \mathbf{D})$
   simultaneously produces the Klein–Gordon operator $\iota(m^2 + D_1^2 + D_2^2 - D_3^2)$, the
   Pauli–Dirac spin-magnetic curvature $\mathrm{vecOp}(\⁅D_2, D_3⁆, \⁅D_3, D_1⁆, -\⁅D_1, D_2⁆)$, and
   the off-diagonal Yukawa mass-gradient $\⁅\iota(m), \mathrm{vecOp}(\mathbf{D})⁆$. -/
theorem covariant_dirac_zorn_multiplication_and_pauli_square
    (α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃ α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃ m D₁ D₂ D₃ : B) :
    let Z₁ := diracZornOp α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃
    let Z₂ := diracZornOp α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃
    let D_cov := diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃
    Z₁ * Z₂ =
      mat2
        (fiberEmbed (α₁ * α₂ + zornDot u₁ u₂ u₃ y₁ y₂ y₃) +
         vecOp (zornCross1 u₁ u₂ u₃ y₁ y₂ y₃)
               (zornCross2 u₁ u₂ u₃ y₁ y₂ y₃)
               (zornCross3 u₁ u₂ u₃ y₁ y₂ y₃))
        (fiberEmbed α₁ * vecOp x₁ x₂ x₃ + vecOp u₁ u₂ u₃ * fiberEmbed β₂)
        (vecOp v₁ v₂ v₃ * fiberEmbed α₂ + fiberEmbed β₁ * vecOp y₁ y₂ y₃)
        (fiberEmbed (β₁ * β₂ + zornDot v₁ v₂ v₃ x₁ x₂ x₃) +
         vecOp (zornCross1 v₁ v₂ v₃ x₁ x₂ x₃)
               (zornCross2 v₁ v₂ v₃ x₁ x₂ x₃)
               (zornCross3 v₁ v₂ v₃ x₁ x₂ x₃)) ∧
    D_cov * D_cov =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆)) := by
  have h_vec (a₁ a₂ a₃ b₁ b₂ b₃ : B) :=
    (zorn_vector_product_dot_plus_cross a₁ a₂ a₃ b₁ b₂ b₃ (0 : B) 0 0).1
  have h_sq := (zorn_vector_product_dot_plus_cross (0 : B) 0 0 0 0 0 D₁ D₂ D₃).2
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : B), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, ?_⟩
  · apply ext_fin2
    · simp only [diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, h_vec u₁ u₂ u₃ y₁ y₂ y₃, ← add_assoc, h_add_emb]
    · simp [diracZornOp]
    · simp [diracZornOp]
    · simp only [diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
        h_mul_emb, h_vec v₁ v₂ v₃ x₁ x₂ x₃]
      rw [add_comm _ (fiberEmbed (β₁ * β₂)), ← add_assoc, h_add_emb]
  · apply ext_fin2
    · simp only [diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, h_sq, ← add_assoc, h_add_emb]
    · simp only [diracZornOp, mul2_01, mat2_00, mat2_01, mat2_11,
        h_neg_emb, mul_neg, Ring.lie_def, sub_eq_add_neg]
    · simp only [diracZornOp, mul2_10, mat2_10, mat2_00, mat2_11,
        h_neg_emb, neg_mul, Ring.lie_def]
      abel
    · simp only [diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
        h_neg_emb, neg_mul_neg, h_mul_emb]
      rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
          h_sq, ← add_assoc, h_add_emb]

end ArchetypeZ2_CovariantDiracZornOperator

/-!
## Archetype $\mathcal{Z}_3$: Zorn Conjugation, Zorn Determinant Norm & Max Zorn's Split-Octonion Product
-/

section ArchetypeZ3_ZornConjugateAndOctonionProduct

variable {B : Type*} [Ring B]

/-- Zorn conjugate (Cayley–Dickson adjoint)
$\overline{\mathcal{D}_{\mathrm{Zorn}}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \mathcal{D}_{\mathrm{Zorn}}(\beta, \alpha, -\mathbf{u}, -\mathbf{v})$. -/
def zornConj (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  diracZornOp β α (-u₁) (-u₂) (-u₃) (-v₁) (-v₂) (-v₃)

/-- Zorn quadratic determinant norm $N_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \alpha\beta - \mathrm{zornDot}(\mathbf{u}, \mathbf{v})$. -/
def zornNorm (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : B :=
  α * β - zornDot u₁ u₂ u₃ v₁ v₂ v₃

/-- Max Zorn's (1931) split-octonion vector-matrix product $\mathcal{D}_1 \star_{\mathrm{Zorn}} \mathcal{D}_2$. -/
def zornOctonionMul (α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃ α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃ : B) : NestedMat B :=
  mat2
    (fiberEmbed (α₁ * α₂ + zornDot u₁ u₂ u₃ y₁ y₂ y₃))
    (fiberEmbed α₁ * vecOp x₁ x₂ x₃ + vecOp u₁ u₂ u₃ * fiberEmbed β₂ -
     vecOp (zornCross1 v₁ v₂ v₃ y₁ y₂ y₃)
           (zornCross2 v₁ v₂ v₃ y₁ y₂ y₃)
           (zornCross3 v₁ v₂ v₃ y₁ y₂ y₃))
    (vecOp v₁ v₂ v₃ * fiberEmbed α₂ + fiberEmbed β₁ * vecOp y₁ y₂ y₃ +
     vecOp (zornCross1 u₁ u₂ u₃ x₁ x₂ x₃)
           (zornCross2 u₁ u₂ u₃ x₁ x₂ x₃)
           (zornCross3 u₁ u₂ u₃ x₁ x₂ x₃))
    (fiberEmbed (β₁ * β₂ + zornDot v₁ v₂ v₃ x₁ x₂ x₃))

/-- **Zorn Conjugate Norm & Associative-vs-Octonionic Curvature Theorem ($\mathcal{Z}_3$)**:
1. In the associative Dirac–Pauli matrix algebra $M_2(M_2(B))$, $\mathcal{D}_{\mathrm{Zorn}} \cdot \overline{\mathcal{D}_{\mathrm{Zorn}}}$
   equals the Zorn norm $\mathrm{diag}(\iota(N_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v})), \iota(N_{\mathrm{Zorn}}(\beta, \alpha, \mathbf{v}, \mathbf{u})))$
   minus the Pauli cross-product curvature $\mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}, \mathbf{v}))$ on the diagonal
   and the commutator $\⁅\mathrm{vecOp}(\mathbf{u}), \iota(\alpha)⁆$ on the off-diagonal.
2. Under Zorn's split-octonion product $\star_{\mathrm{Zorn}}$, multiplying by the Zorn conjugate
   produces the diagonal Zorn norm on the $(0,0)$ and $(1,1)$ blocks, while the off-diagonal blocks
   carry only the non-Abelian self-curvatures $\mathrm{vecOp}(\⁅v_2, v_3⁆, \⁅v_3, v_1⁆, -\⁅v_1, v_2⁆)$
   and $-\mathrm{vecOp}(\⁅u_2, u_3⁆, \⁅u_3, u_1⁆, -\⁅u_1, u_2⁆)$. -/
theorem zorn_conjugate_norm_and_octonion_product
    (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) :
    let Z      := diracZornOp α β u₁ u₂ u₃ v₁ v₂ v₃
    let Z_conj := zornConj α β u₁ u₂ u₃ v₁ v₂ v₃
    Z * Z_conj =
      mat2
        (fiberEmbed (zornNorm α β u₁ u₂ u₃ v₁ v₂ v₃) -
         vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃)
               (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃)
               (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃))
        ⁅vecOp u₁ u₂ u₃, fiberEmbed α⁆
        ⁅vecOp v₁ v₂ v₃, fiberEmbed β⁆
        (fiberEmbed (zornNorm β α v₁ v₂ v₃ u₁ u₂ u₃) -
         vecOp (zornCross1 v₁ v₂ v₃ u₁ u₂ u₃)
               (zornCross2 v₁ v₂ v₃ u₁ u₂ u₃)
               (zornCross3 v₁ v₂ v₃ u₁ u₂ u₃)) ∧
    zornOctonionMul α β u₁ u₂ u₃ v₁ v₂ v₃ β α (-u₁) (-u₂) (-u₃) (-v₁) (-v₂) (-v₃) =
      mat2
        (fiberEmbed (zornNorm α β u₁ u₂ u₃ v₁ v₂ v₃))
        (⁅vecOp u₁ u₂ u₃, fiberEmbed α⁆ +
         vecOp ⁅v₂, v₃⁆ ⁅v₃, v₁⁆ (-⁅v₁, v₂⁆))
        (⁅vecOp v₁ v₂ v₃, fiberEmbed β⁆ -
         vecOp ⁅u₂, u₃⁆ ⁅u₃, u₁⁆ (-⁅u₁, u₂⁆))
        (fiberEmbed (zornNorm β α v₁ v₂ v₃ u₁ u₂ u₃)) := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [diracZornOp, zornConj, zornNorm, zornDot,
            zornCross1, zornCross2, zornCross3, fiberEmbed] <;>
      ((try noncomm_ring); try abel)
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [zornOctonionMul, zornNorm, zornDot,
            zornCross1, zornCross2, zornCross3, fiberEmbed] <;>
      ((try noncomm_ring); try abel)

end ArchetypeZ3_ZornConjugateAndOctonionProduct

/-!
## Archetype $\mathcal{Z}_4$: All-Scales Inductive Covariant Dirac–Zorn Tower on $\mathcal{C}\ell_{n+2}(B)$
-/

section ArchetypeZ4_AllScalesInductiveDiracZornTower

universe u

variable {B : Type u} [Ring B]

/-- **All-Scales Inductive Covariant Dirac–Zorn Wave Square on $\mathcal{C}\ell_{n+2}(B)$ ($\mathcal{Z}_4$)**:
At every scale $n \in \mathbb{N}$, the covariant Dirac–Zorn operator in $\mathcal{C}\ell_{n+2}(B) = M_2(M_2(\mathcal{C}\ell_n(B)))$
satisfies the exact Pauli–Dirac–Zorn wave decomposition. -/
theorem all_scales_inductive_covariant_dirac_zorn_wave_square
    (n : ℕ) (m D₁ D₂ D₃ : ClTower B n) :
    let D_n := diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃
    D_n * D_n =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆)) := by
  exact (covariant_dirac_zorn_multiplication_and_pauli_square
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 m D₁ D₂ D₃).2

private theorem diracZorn_noncomm_witness [Nontrivial B] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) B, X * Y ≠ Y * X := by
  refine ⟨mat2 0 1 0 0, mat2 0 0 1 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp at h00

end ArchetypeZ4_AllScalesInductiveDiracZornTower

end InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
