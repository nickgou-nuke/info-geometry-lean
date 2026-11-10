/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

/-!
# Non-Commutative Zorn Vector-Matrix, Split-Octonion Associator, Flexibility–Alternativity Equivalence,
# Corner-Intertwining Moufang Laws, and Bilateral Active Moufang Duality Poset
# (`Stages D₆₅–D₆₆` and `D₇₀–D₇₆`: Archetypes `ZO₁ → ZO₁₀`, `ZM₁ → ZM₂₅`, `ZS₁ → ZS₅`)

This module formalizes the complete non-commutative Zorn vector-matrix, Kantor–Zorn homotope,
and contravariant split-octonion Moufang poset over an arbitrary associative ring `[Ring B]`
(and `[StarRing B]` for contravariant star-duality), with zero scalar, diagonal, or commuting
simplifications:

1. **Zorn Vector-Matrix Decomposition, Cubic Grading Operator (`Δ_sc³ = 4 Δ_sc`), Orthogonal Grade
   Projectors & Corner Commutator Factorization (`ZO₁ → ZO₁₀`, Stages `D₆₅–D₆₆`):**
   - `zornMatrix`, `zornScalarPart`, `zornVectorPart`, `zornPotential`: exact block multiplication
     and square decomposition into even and odd Peircean grades.
   - `superCommDelta P X = comm (invS P) X` satisfies `Δ_sc³(X) = 4 • Δ_sc(X)` and generates
     polynomial grade projectors `superProj0`, `superProjPlus2`, `superProjMinus2` with
     `2 • superProj0 P X + superProjPlus2 P X + superProjMinus2 P X = 8 • X`.
   - `cornerThirdOrder P C₀ A₁ A₂ C₀ = comm (qgtPlus P A₁ C₀) (qgtPlus P A₂ C₀)`.
2. **Contravariant Star-Duality of `kantorWedge` and `kantorVee`, Homotope Jacobi vs. Contravariant `zornMulOct` (`ZM₁ → ZM₁₀`, Stages `D₇₀–D₇₁`):**
   - `star (kantorWedge P c₀ X Y) = -kantorVee P (star c₀) (star X) (star Y)`.
   - Same-cone homotope product `zornMulKZ` satisfies cyclic Jacobi `assocKZ x y z + assocKZ y z x + assocKZ z x y = 0`.
   - Contravariant Zorn split-octonion product `zornMulOct` satisfies the full 3-vector associator
     orthogonal corner split into `P B P ⊕ (1 - P) B (1 - P)`, unconditional 3-term cyclic
     flexibility `[x, x, y] + [x, y, x] + [y, x, x] = 0`, and opposite-cone Moufang closure
     `((x ⋆ w) ⋆ x) ⋆ w₂ = x ⋆ (w ⋆ (x ⋆ w₂))`.
3. **Equivalence of Flexibility and Full Alternativity on the Peircean Cone, Half-Alternative Corner Laws,
   `S₃` Associator Sum Vanishing, and 4-Body Kantor–Moufang Sandwich (`ZM₁₁ → ZM₁₅`, Stage `D₇₂`):**
   - `diagPlus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ x x y` and
     `diagMinus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ y x x`, proving
     `assocOct P c₀ a₀ x y x = 0 ↔ (assocOct P c₀ a₀ x x y = 0 ∧ assocOct P c₀ a₀ y x x = 0)`.
   - Unconditional half-alternative corner laws `diagPlus P ([x, y, z] + [x, z, y]) = 0` and
     `diagMinus P ([x, y, z] + [y, x, z]) = 0`, and 6-permutation `S₃` sum vanishing.
   - 4-body Kantor–Moufang sandwich `assocOct P c₀ a₀ x (y ⋆ z) x = 0` with both bracketings equal
     to `kantorGp2 P A₁ (y ⋆ z)`.
4. **Socratic Aporia of Un-Symmetrized Alternativity, Universal Jordan–Lie Telescoping, and
   Jordan-Symmetrized Zorn Split-Octonion Product (`ZS₁ → ZS₅`, Stage `D₇₃`):**
   - Un-symmetrized left alternativity with left-invertible `Q_-(C, A₁)` on `(1 - P) B` forces
     `kantorWedge P c₀ x y = 0`.
   - Universal Jordan–Lie telescoping `anticomm Q₁ (comm Q₁ Q₂) = comm (Q₁ * Q₁) Q₂`.
   - Jordan-symmetrized product `zornMulSymOct` and associator `assocSymOct` evaluate to
     `assocSymOct P c₀ a₀ x x y = x * star (kantorWedge P c₀ x y) + kantorWedge P c₀ x y * coneMinus P (star A₁)`.
5. **Corner-Intertwining Moufang Law, Double-Star Anchor Coupling, Native `kantorWedge` Reconstruction,
   and Bilateral Left/Right Active Moufang Duality (`ZM₁₆ → ZM₂₅`, Stages `D₇₄–D₇₆`):**
   - Corner-intertwining identity `x * diagMinus P [y, z, x] = -diagPlus P [x, y, z] * x`.
   - Native opposite-cone reconstruction `(x ⋆ w) ⋆ y - y ⋆ (w ⋆ x) = kantorWedge P C₁ A₁ A₂` and
     `(x ⋆ w) ⋆ y + y ⋆ (w ⋆ x) = kantorTriple x w y`.
   - Double-star Middle Moufang LHS `(x ⋆ y) ⋆ (z ⋆ x) = kantorWedge P (star a₀) (kantorWedge P c₀ A₁ A₂) (kantorWedge P c₀ A₃ A₁)`
     and unconditional symmetric closure `(x ⋆ y) ⋆ (y ⋆ x) = 0`.
   - Bilateral active Moufang duality: `((x ⋆ y) ⋆ x) ⋆ w = -[y, x, x] * w` vs. `w ⋆ (x ⋆ (y ⋆ x)) = w * [x, x, y]`,
     and dual lower-cone corner intertwining `w₁ * diagPlus P [w₂, w₃, w₁] = -diagMinus P [w₁, w₂, w₃] * w₁`.

## Three-Bucket Audit Classification

- **BUCKET 1 (`KERNEL_PROVED`):**
  All stages `ZO₁ → ZO₁₀`, `ZM₁ → ZM₂₅`, and `ZS₁ → ZS₅`: Zorn vector-matrix decomposition,
  cubic grading law `Δ_sc³ = 4 Δ_sc`, contravariant split-octonion associator, flexibility–alternativity
  equivalence, 4-body Kantor–Moufang sandwich, and bilateral active Moufang duality in `[Ring B] [StarRing B]`.
- **BUCKET 2 (`EXPLICIT_HYPOTHESIS`):**
  Idempotency `hP : P * P = P` and self-adjointness `hPsym : star P = P` on `[Ring B] [StarRing B]`.
- **BUCKET 3 (`OPEN_HORIZON`):**
  Exceptional Jordan algebra `J₃(𝕆)` Freudenthal–Tits magic square extension over three-sheeted Peircean cones.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornSplitOctonionMoufangPoset

section RingPrimitives

variable {B : Type*} [Ring B]

/-! ### Stage 0: Core Non-Commutative Peircean, Zorn Matrix, and Kantor Primitives -/

/-- Associative ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Associative ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Peircean grading involution `S_P = P - (1 - P)`. -/
def invS (P : B) : B := P - (1 - P)

/-- Even Peircean grade component `P X P + (1 - P) X (1 - P)`. -/
def evenGrade (P X : B) : B := P * X * P + (1 - P) * X * (1 - P)

/-- Odd Peircean grade component `P X (1 - P) + (1 - P) X P`. -/
def oddGrade (P X : B) : B := P * X * (1 - P) + (1 - P) * X * P

/-- Upper-left Peircean corner `P X P`. -/
def diagPlus (P X : B) : B := P * X * P

/-- Lower-right Peircean corner `(1 - P) X (1 - P)`. -/
def diagMinus (P X : B) : B := (1 - P) * X * (1 - P)

/-- Upper-right nilpotent Peircean cone `N_+(X) = P X (1 - P)`. -/
def conePlus (P X : B) : B := P * X * (1 - P)

/-- Lower-left nilpotent Peircean cone `N_-(X) = (1 - P) X P`. -/
def coneMinus (P X : B) : B := (1 - P) * X * P

/-- Upper-corner round-trip operator `Q_+(X, Y) = N_+(X) N_-(Y)`. -/
def qgtPlus (P X Y : B) : B := conePlus P X * coneMinus P Y

/-- Lower-corner round-trip operator `Q_-(X, Y) = N_-(X) N_+(Y)`. -/
def qgtMinus (P X Y : B) : B := coneMinus P X * conePlus P Y

/-- Symmetric bridge `Φ(X, Y) = N_+(X) + N_-(Y)`. -/
def genPhi (P X Y : B) : B := conePlus P X + coneMinus P Y

/-- Symmetric metric block `V(X, Y) = {N_+(X), N_-(Y)}`. -/
def genV (P X Y : B) : B := anticomm (conePlus P X) (coneMinus P Y)

/-- Antisymmetric curvature block `Σ(X, Y) = [N_+(X), N_-(Y)]`. -/
def genSig (P X Y : B) : B := comm (conePlus P X) (coneMinus P Y)

/-- Grade-`+2` Kantor sandwich `G_{+2}(P, A, X) = N_+(A) X N_+(A)`. -/
def kantorGp2 (P A X : B) : B := conePlus P A * X * conePlus P A

/-- Skew-symmetric Kantor cross-product `x ∧_{c₀} y = N_+(X) N_-(c₀) N_+(Y) - N_+(Y) N_-(c₀) N_+(X)` in `P B (1 - P)`. -/
def kantorWedge (P c₀ X Y : B) : B :=
  conePlus P X * coneMinus P c₀ * conePlus P Y -
  conePlus P Y * coneMinus P c₀ * conePlus P X

/-- Dual skew-symmetric Kantor cross-product `w₁ ∨_{a₀} w₂ = N_-(X) N_+(a₀) N_-(Y) - N_-(Y) N_+(a₀) N_-(X)` in `(1 - P) B P`. -/
def kantorVee (P a₀ X Y : B) : B :=
  coneMinus P X * conePlus P a₀ * coneMinus P Y -
  coneMinus P Y * conePlus P a₀ * coneMinus P X

/-- Symmetric Jordan–Kantor triple product `{X, Y, Z} = X Y Z + Z Y X`. -/
def kantorTriple (X Y Z : B) : B := X * Y * Z + Z * Y * X

/-- Zorn 4-sector decomposition `Z_P(A, B_+, C_-, D) = diagPlus A + conePlus B_+ + coneMinus C_- + diagMinus D`. -/
def zornMatrix (P A Bp Cm D : B) : B :=
  diagPlus P A + conePlus P Bp + coneMinus P Cm + diagMinus P D

/-- Zorn diagonal part `P φ P + (1 - P) ψ (1 - P)`. -/
def zornScalarPart (P phi psi : B) : B :=
  P * phi * P + (1 - P) * psi * (1 - P)

/-- Zorn off-diagonal part `N_+(A) + N_-(C)`. -/
def zornVectorPart (P A C : B) : B :=
  conePlus P A + coneMinus P C

/-- Full Zorn element `zornScalarPart P φ ψ + zornVectorPart P A C`. -/
def zornPotential (P phi psi A C : B) : B :=
  zornScalarPart P phi psi + zornVectorPart P A C

/-- Third-order alternating product `(N_+(A₁) N_-(C₀) N_+(A₂) - N_+(A₂) N_-(C₀) N_+(A₁)) N_-(C₃)` in `P B P`. -/
def cornerThirdOrder (P C₀ A₁ A₂ C₃ : B) : B :=
  kantorWedge P C₀ A₁ A₂ * coneMinus P C₃

/-- Adjoint grading derivation `Δ_sc(P, X) = [S_P, X]`. -/
def superCommDelta (P X : B) : B := comm (invS P) X

/-- Unnormalized Grade-`0` projector `4 X_0 = 4 X - Δ_sc²(X)`. -/
def superProj0 (P X : B) : B :=
  (4 : ℤ) • X - superCommDelta P (superCommDelta P X)

/-- Unnormalized Grade-`+2` projector `8 N_+(X) = Δ_sc²(X) + 2 Δ_sc(X)`. -/
def superProjPlus2 (P X : B) : B :=
  superCommDelta P (superCommDelta P X) + (2 : ℤ) • superCommDelta P X

/-- Unnormalized Grade-`-2` projector `8 N_-(X) = Δ_sc²(X) - 2 Δ_sc(X)`. -/
def superProjMinus2 (P X : B) : B :=
  superCommDelta P (superCommDelta P X) - (2 : ℤ) • superCommDelta P X

/-- Same-cone Kantor–Zorn homotope product `X ⋆_{KZ} Y = X Y + kantorWedge P c₀ X Y + kantorVee P a₀ X Y`. -/
def zornMulKZ (P c₀ a₀ X Y : B) : B :=
  X * Y + kantorWedge P c₀ X Y + kantorVee P a₀ X Y

/-- Associator of `zornMulKZ`. -/
def assocKZ (P c₀ a₀ X Y Z : B) : B :=
  zornMulKZ P c₀ a₀ (zornMulKZ P c₀ a₀ X Y) Z -
  zornMulKZ P c₀ a₀ X (zornMulKZ P c₀ a₀ Y Z)

/-- Left-multiplication absorption `P * (P * X) = P * X` for an idempotent `P`. -/
lemma P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

macro "gursey_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [cornerThirdOrder, superProj0, superProjPlus2, superProjMinus2,
               superCommDelta, zornPotential, zornVectorPart, zornScalarPart,
               zornMatrix, kantorWedge, kantorVee, evenGrade, oddGrade,
               genPhi, genV, genSig, qgtPlus, qgtMinus,
               diagPlus, diagMinus, conePlus, coneMinus, invS,
               comm, anticomm,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

macro "zorn_kz_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [assocKZ, zornMulKZ, kantorWedge, kantorVee,
               genPhi, qgtPlus, qgtMinus, conePlus, coneMinus,
               comm, anticomm,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

/-! ### Stages D₆₅–D₆₆ (Archetypes ZO₁ → ZO₁₀): Zorn Matrix Multiplication, Cubic Grading & Corner Factorization -/

/-- **Lemma ZO₁.1–ZO₁₀.1 (Zorn Matrix Multiplication Table, Cubic Grading Law `Δ_sc³ = 4 Δ_sc`,
Orthogonal Grade Projectors, and Corner Commutator Factorization):** -/
lemma zorn_matrix_cubic_grading_and_corner_factorization
    {P : B} (hP : P * P = P)
    (X phi psi A C A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ C₀ C₃ : B) :
    zornMatrix P X X X X = X ∧
    zornMatrix P A₁ B₁ C₁ D₁ * zornMatrix P A₂ B₂ C₂ D₂ =
      zornMatrix P (diagPlus P A₁ * diagPlus P A₂ + qgtPlus P B₁ C₂)
        (diagPlus P A₁ * conePlus P B₂ + conePlus P B₁ * diagMinus P D₂)
        (coneMinus P C₁ * diagPlus P A₂ + diagMinus P D₁ * coneMinus P C₂)
        (qgtMinus P C₁ B₂ + diagMinus P D₁ * diagMinus P D₂) ∧
    evenGrade P (zornPotential P phi psi A C * zornPotential P phi psi A C) =
      zornScalarPart P phi psi * zornScalarPart P phi psi + genV P A C ∧
    oddGrade P (zornPotential P phi psi A C * zornPotential P phi psi A C) =
      anticomm (zornScalarPart P phi psi) (zornVectorPart P A C) ∧
    superCommDelta P (superCommDelta P (superCommDelta P X)) =
      (4 : ℤ) • superCommDelta P X ∧
    superProj0 P X = (4 : ℤ) • evenGrade P X ∧
    superProjPlus2 P X = (8 : ℤ) • conePlus P X ∧
    superProjMinus2 P X = (8 : ℤ) • coneMinus P X ∧
    (2 : ℤ) • superProj0 P X + superProjPlus2 P X + superProjMinus2 P X =
      (8 : ℤ) • X ∧
    superCommDelta P (kantorWedge P C₀ A₁ A₂) =
      (2 : ℤ) • kantorWedge P C₀ A₁ A₂ ∧
    superCommDelta P (cornerThirdOrder P C₀ A₁ A₂ C₃) = 0 ∧
    cornerThirdOrder P C₀ A₁ A₂ C₀ = comm (qgtPlus P A₁ C₀) (qgtPlus P A₂ C₀) := by
  dsimp only []
  refine ⟨by gursey_abel hP, by gursey_abel hP, by gursey_abel hP, by gursey_abel hP,
          by gursey_abel hP, by gursey_abel hP, by gursey_abel hP, by gursey_abel hP,
          by gursey_abel hP, by gursey_abel hP, by gursey_abel hP, by gursey_abel hP⟩

/-- **Helper Lemma: Evaluation of `zornMulKZ` and `assocKZ` on the Upper Cone:** -/
lemma assocKZ_conePlus_formula
    {P : B} (hP : P * P = P) (c₀ a₀ A₁ A₂ A₃ : B) :
    assocKZ P c₀ a₀ (conePlus P A₁) (conePlus P A₂) (conePlus P A₃) =
      kantorWedge P c₀ (kantorWedge P c₀ A₁ A₂) A₃ -
      kantorWedge P c₀ A₁ (kantorWedge P c₀ A₂ A₃) := by
  have hPair : ∀ U V : B, zornMulKZ P c₀ a₀ (conePlus P U) (conePlus P V) = kantorWedge P c₀ U V := by
    intro U V; zorn_kz_abel hP
  have hConeW : ∀ U V : B, kantorWedge P c₀ U V = conePlus P (kantorWedge P c₀ U V) := by
    intro U V; zorn_kz_abel hP
  unfold assocKZ
  rw [hPair A₁ A₂, hPair A₂ A₃, hConeW A₁ A₂, hConeW A₂ A₃,
      hPair (kantorWedge P c₀ A₁ A₂) A₃, hPair A₁ (kantorWedge P c₀ A₂ A₃),
      ← hConeW A₁ A₂, ← hConeW A₂ A₃]

/-- **Lemma ZM₃.1 (Same-Cone Kantor–Zorn Homotope Product `zornMulKZ` Satisfies the Cyclic Jacobi Identity):** -/
lemma same_cone_homotope_jacobi_and_aporia
    {P : B} (hP : P * P = P) (c₀ a₀ A₁ A₂ A₃ : B) :
    assocKZ P c₀ a₀ (conePlus P A₁) (conePlus P A₂) (conePlus P A₃) =
      kantorWedge P c₀ (kantorWedge P c₀ A₁ A₂) A₃ -
      kantorWedge P c₀ A₁ (kantorWedge P c₀ A₂ A₃) ∧
    assocKZ P c₀ a₀ (conePlus P A₁) (conePlus P A₂) (conePlus P A₃) +
      assocKZ P c₀ a₀ (conePlus P A₂) (conePlus P A₃) (conePlus P A₁) +
      assocKZ P c₀ a₀ (conePlus P A₃) (conePlus P A₁) (conePlus P A₂) = 0 ∧
    assocKZ P c₀ a₀ (conePlus P A₁) (conePlus P A₁) (conePlus P A₂) =
      -(qgtPlus P A₁ c₀ * kantorWedge P c₀ A₁ A₂ -
        kantorWedge P c₀ A₁ A₂ * qgtMinus P c₀ A₁) := by
  have h123 := assocKZ_conePlus_formula hP c₀ a₀ A₁ A₂ A₃
  have h231 := assocKZ_conePlus_formula hP c₀ a₀ A₂ A₃ A₁
  have h312 := assocKZ_conePlus_formula hP c₀ a₀ A₃ A₁ A₂
  have h112 := assocKZ_conePlus_formula hP c₀ a₀ A₁ A₁ A₂
  refine ⟨h123,
          by rw [h123, h231, h312]; zorn_kz_abel hP,
          by rw [h112]; zorn_kz_abel hP⟩

end RingPrimitives

/-! ### Stages D₇₀–D₇₆: Contravariant Star-Duality, Split-Octonion Product `zornMulOct` & Moufang Laws -/

section StarRingPrimitives

variable {B : Type*} [Ring B] [StarRing B]

/-- Contravariant Zorn Split-Octonion Product on `B`:
`X ⋆_{O_s} Y = X * Y - star (kantorVee P a₀ X Y) + star (kantorWedge P c₀ X Y)`. -/
def zornMulOct (P c₀ a₀ X Y : B) : B :=
  X * Y - star (kantorVee P a₀ X Y) + star (kantorWedge P c₀ X Y)

/-- Split-Octonion Associator `[X, Y, Z]_{⋆_{O_s}} = (X ⋆ Y) ⋆ Z - X ⋆ (Y ⋆ Z)`. -/
def assocOct (P c₀ a₀ X Y Z : B) : B :=
  zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ X Y) Z -
  zornMulOct P c₀ a₀ X (zornMulOct P c₀ a₀ Y Z)

/-- Self-adjoint Jordan-symmetrized upper corner dot product (`Stage D₇₃`, `ZS₃`). -/
def symDotPlus (P X Y : B) : B :=
  qgtPlus P X Y + qgtPlus P (star Y) (star X)

/-- Self-adjoint Jordan-symmetrized lower corner dot product (`Stage D₇₃`, `ZS₃`). -/
def symDotMinus (P X Y : B) : B :=
  qgtMinus P X Y + qgtMinus P (star Y) (star X)

/-- Jordan-Symmetrized Zorn Split-Octonion Product (`Stage D₇₃`, `ZS₄`). -/
def zornMulSymOct (P c₀ a₀ X Y : B) : B :=
  diagPlus P X * diagPlus P Y + diagMinus P X * diagMinus P Y +
  diagPlus P X * conePlus P Y + conePlus P X * diagMinus P Y +
  diagMinus P X * coneMinus P Y + coneMinus P X * diagPlus P Y -
  symDotPlus P X Y - symDotMinus P X Y -
  star (kantorVee P a₀ X Y) + star (kantorWedge P c₀ X Y)

/-- Associator of `zornMulSymOct`. -/
def assocSymOct (P c₀ a₀ X Y Z : B) : B :=
  zornMulSymOct P c₀ a₀ (zornMulSymOct P c₀ a₀ X Y) Z -
  zornMulSymOct P c₀ a₀ X (zornMulSymOct P c₀ a₀ Y Z)

macro "zorn_oct_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [kantorTriple, kantorWedge, kantorVee, kantorGp2,
               genV, qgtPlus, qgtMinus, diagPlus, diagMinus, conePlus, coneMinus,
               comm, anticomm,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

macro "zorn_sym_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [symDotPlus, symDotMinus, kantorWedge, kantorVee,
               genPhi, qgtPlus, qgtMinus,
               diagPlus, diagMinus, conePlus, coneMinus,
               comm, anticomm,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

/-- When both Kantor brackets `kantorWedge` and `kantorVee` vanish, `zornMulOct` reduces to associative multiplication `X * Y`. -/
lemma zornMulOct_eq_mul {P : B} (c₀ a₀ X Y : B)
    (hW : kantorWedge P c₀ X Y = 0) (hV : kantorVee P a₀ X Y = 0) :
    zornMulOct P c₀ a₀ X Y = X * Y := by
  unfold zornMulOct
  rw [hW, hV, star_zero, sub_zero, add_zero]

/-- **Lemma ZM₁.1 (Contravariant Star-Duality of `conePlus`, `coneMinus`, `kantorWedge`, and `kantorVee`):** -/
lemma star_duality_of_peirce_cones_and_kantor_brackets
    {P : B} (hPsym : star P = P) (c₀ X Y : B) :
    star (conePlus P X) = coneMinus P (star X) ∧
    star (coneMinus P Y) = conePlus P (star Y) ∧
    star (kantorWedge P c₀ X Y) = -kantorVee P (star c₀) (star X) (star Y) ∧
    star (kantorVee P c₀ X Y) = -kantorWedge P (star c₀) (star X) (star Y) := by
  have hSP : ∀ Z : B, star (conePlus P Z) = coneMinus P (star Z) := by
    intro Z; unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hSM : ∀ Z : B, star (coneMinus P Z) = conePlus P (star Z) := by
    intro Z; unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  refine ⟨hSP X, hSM Y, ?_, ?_⟩
  · unfold kantorWedge kantorVee
    rw [star_sub, star_mul, star_mul, star_mul, star_mul, hSP X, hSP Y, hSM c₀]
    simp only [mul_assoc]; abel
  · unfold kantorVee kantorWedge
    rw [star_sub, star_mul, star_mul, star_mul, star_mul, hSM X, hSM Y, hSP c₀]
    simp only [mul_assoc]; abel

/-- **Helper Lemma 1: Upper Cone Product and 3-Vector Split-Octonion Associator Expansion:** -/
lemma upper_associator_expansion
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ A₁ A₂ A₃ : B) :
    zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂) =
      star (kantorWedge P c₀ A₁ A₂) ∧
    zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂) =
      -kantorVee P (star c₀) (coneMinus P (star A₁)) (coneMinus P (star A₂)) ∧
    assocOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂) (conePlus P A₃) =
      (qgtPlus P A₁ (star A₂) * qgtPlus P (star c₀) (star A₃) -
       qgtPlus P A₁ (star A₃) * qgtPlus P (star c₀) (star A₂)) +
      (qgtMinus P (star A₂) (star c₀) * qgtMinus P (star A₁) A₃ -
       qgtMinus P (star A₁) (star c₀) * qgtMinus P (star A₂) A₃) := by
  have hSP : ∀ Z : B, star (conePlus P Z) = coneMinus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).1
  have hSM : ∀ Z : B, star (coneMinus P Z) = conePlus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).2.1
  have hStarForm : ∀ U V : B,
      zornMulOct P c₀ a₀ (conePlus P U) (conePlus P V) = star (kantorWedge P c₀ U V) := by
    intro U V
    have hProd0 : conePlus P U * conePlus P V = 0 := by zorn_oct_abel hP
    have hVee0 : kantorVee P a₀ (conePlus P U) (conePlus P V) = 0 := by zorn_oct_abel hP
    have hW : kantorWedge P c₀ (conePlus P U) (conePlus P V) = kantorWedge P c₀ U V := by
      zorn_oct_abel hP
    unfold zornMulOct
    rw [hProd0, hVee0, star_zero, sub_zero, zero_add, hW]
  have hPairPlus : ∀ U V : B,
      zornMulOct P c₀ a₀ (conePlus P U) (conePlus P V) =
        -kantorVee P (star c₀) (coneMinus P (star U)) (coneMinus P (star V)) := by
    intro U V
    rw [hStarForm U V]
    unfold kantorWedge
    rw [star_sub, star_mul, star_mul, star_mul, star_mul, hSP U, hSP V, hSM c₀]
    zorn_oct_abel hP
  refine ⟨hStarForm A₁ A₂, hPairPlus A₁ A₂, ?_⟩
  unfold assocOct
  rw [hPairPlus A₁ A₂, hPairPlus A₂ A₃]
  unfold zornMulOct
  have hW1 : kantorWedge P c₀
      (-kantorVee P (star c₀) (coneMinus P (star A₁)) (coneMinus P (star A₂)))
      (conePlus P A₃) = 0 := by zorn_oct_abel hP
  have hV1 : kantorVee P a₀
      (-kantorVee P (star c₀) (coneMinus P (star A₁)) (coneMinus P (star A₂)))
      (conePlus P A₃) = 0 := by zorn_oct_abel hP
  have hW2 : kantorWedge P c₀ (conePlus P A₁)
      (-kantorVee P (star c₀) (coneMinus P (star A₂)) (coneMinus P (star A₃))) = 0 := by
    zorn_oct_abel hP
  have hV2 : kantorVee P a₀ (conePlus P A₁)
      (-kantorVee P (star c₀) (coneMinus P (star A₂)) (coneMinus P (star A₃))) = 0 := by
    zorn_oct_abel hP
  rw [hW1, hV1, hW2, hV2, star_zero]
  zorn_oct_abel hP

/-- **Helper Lemma 2: Lower Cone Product and 3-Vector Split-Octonion Associator Expansion:** -/
lemma lower_associator_expansion
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ C₁ C₂ C₃ : B) :
    zornMulOct P c₀ a₀ (coneMinus P C₁) (coneMinus P C₂) =
      kantorWedge P (star a₀) (conePlus P (star C₁)) (conePlus P (star C₂)) ∧
    assocOct P c₀ a₀ (coneMinus P C₁) (coneMinus P C₂) (coneMinus P C₃) =
      (qgtPlus P (star C₁) (star a₀) * qgtPlus P (star C₂) C₃ -
       qgtPlus P (star C₂) (star a₀) * qgtPlus P (star C₁) C₃) +
      (qgtMinus P C₁ (star C₃) * qgtMinus P (star a₀) (star C₂) -
       qgtMinus P C₁ (star C₂) * qgtMinus P (star a₀) (star C₃)) := by
  have hSP : ∀ Z : B, star (conePlus P Z) = coneMinus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).1
  have hSM : ∀ Z : B, star (coneMinus P Z) = conePlus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).2.1
  have hPairMinus : ∀ U V : B,
      zornMulOct P c₀ a₀ (coneMinus P U) (coneMinus P V) =
        kantorWedge P (star a₀) (conePlus P (star U)) (conePlus P (star V)) := by
    intro U V
    have hProd0 : coneMinus P U * coneMinus P V = 0 := by zorn_oct_abel hP
    have hWedge0 : kantorWedge P c₀ (coneMinus P U) (coneMinus P V) = 0 := by zorn_oct_abel hP
    have hVeeEq : kantorVee P a₀ (coneMinus P U) (coneMinus P V) =
        coneMinus P U * conePlus P a₀ * coneMinus P V -
        coneMinus P V * conePlus P a₀ * coneMinus P U := by zorn_oct_abel hP
    unfold zornMulOct
    rw [hProd0, hWedge0, star_zero, add_zero, zero_sub, hVeeEq]
    rw [star_sub, star_mul, star_mul, star_mul, star_mul, hSM U, hSM V, hSP a₀]
    zorn_oct_abel hP
  refine ⟨hPairMinus C₁ C₂, ?_⟩
  unfold assocOct
  rw [hPairMinus C₁ C₂, hPairMinus C₂ C₃]
  unfold zornMulOct
  have hW1 : kantorWedge P c₀
      (kantorWedge P (star a₀) (conePlus P (star C₁)) (conePlus P (star C₂)))
      (coneMinus P C₃) = 0 := by zorn_oct_abel hP
  have hV1 : kantorVee P a₀
      (kantorWedge P (star a₀) (conePlus P (star C₁)) (conePlus P (star C₂)))
      (coneMinus P C₃) = 0 := by zorn_oct_abel hP
  have hW2 : kantorWedge P c₀ (coneMinus P C₁)
      (kantorWedge P (star a₀) (conePlus P (star C₂)) (conePlus P (star C₃))) = 0 := by
    zorn_oct_abel hP
  have hV2 : kantorVee P a₀ (coneMinus P C₁)
      (kantorWedge P (star a₀) (conePlus P (star C₂)) (conePlus P (star C₃))) = 0 := by
    zorn_oct_abel hP
  rw [hW1, hV1, hW2, hV2, star_zero]
  zorn_oct_abel hP

/-- **Lemma ZM₆.1–ZM₁₀.1 (Full 3-Vector Split-Octonion Associator Corner Split, Unconditional
Ternary Flexibility, and Opposite-Cone Moufang Identity):** -/
lemma three_vector_associator_and_mixed_cone_moufang
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ A₁ A₂ A₃ C₁ C₂ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    let z := conePlus P A₃
    let w := coneMinus P C₁
    let w₂ := coneMinus P C₂
    diagPlus P (assocOct P c₀ a₀ x y z) =
      qgtPlus P A₁ (star A₂) * qgtPlus P (star c₀) (star A₃) -
      qgtPlus P A₁ (star A₃) * qgtPlus P (star c₀) (star A₂) ∧
    diagMinus P (assocOct P c₀ a₀ x y z) =
      qgtMinus P (star A₂) (star c₀) * qgtMinus P (star A₁) A₃ -
      qgtMinus P (star A₁) (star c₀) * qgtMinus P (star A₂) A₃ ∧
    diagPlus P (assocOct P c₀ a₀ x y z) + diagMinus P (assocOct P c₀ a₀ x y z) =
      assocOct P c₀ a₀ x y z ∧
    assocOct P c₀ a₀ x x y + assocOct P c₀ a₀ x y x + assocOct P c₀ a₀ y x x = 0 ∧
    assocOct P c₀ a₀ x w x = 0 ∧
    assocOct P c₀ a₀ w x w = 0 ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) x) w₂ =
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ w (zornMulOct P c₀ a₀ x w₂)) := by
  intro x y z w w₂
  have h123 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₃).2.2
  have h112 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₁ A₂).2.2
  have h121 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₁).2.2
  have h211 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₁ A₁).2.2
  have hW_xw : ∀ C : B, kantorWedge P c₀ x (coneMinus P C) = 0 := by
    intro C; dsimp [x]; zorn_oct_abel hP
  have hV_xw : ∀ C : B, kantorVee P a₀ x (coneMinus P C) = 0 := by
    intro C; dsimp [x]; zorn_oct_abel hP
  have hW_wx : kantorWedge P c₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
  have hV_wx : kantorVee P a₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
  have hMul_xw : ∀ C : B, zornMulOct P c₀ a₀ x (coneMinus P C) = qgtPlus P A₁ C := by
    intro C; unfold zornMulOct
    rw [hW_xw C, hV_xw C, star_zero, sub_zero, add_zero]; rfl
  have hMul_wx : zornMulOct P c₀ a₀ w x = qgtMinus P C₁ A₁ := by
    unfold zornMulOct
    rw [hW_wx, hV_wx, star_zero, sub_zero, add_zero]; rfl
  have hW_qx : kantorWedge P c₀ (qgtPlus P A₁ C₁) x = 0 := by dsimp [x]; zorn_oct_abel hP
  have hV_qx : kantorVee P a₀ (qgtPlus P A₁ C₁) x = 0 := by dsimp [x]; zorn_oct_abel hP
  have hMul_qx : zornMulOct P c₀ a₀ (qgtPlus P A₁ C₁) x = qgtPlus P A₁ C₁ * x := by
    unfold zornMulOct; rw [hW_qx, hV_qx, star_zero, sub_zero, add_zero]
  have hW_xqm : kantorWedge P c₀ x (qgtMinus P C₁ A₁) = 0 := by dsimp [x]; zorn_oct_abel hP
  have hV_xqm : kantorVee P a₀ x (qgtMinus P C₁ A₁) = 0 := by dsimp [x]; zorn_oct_abel hP
  have hMul_xqm : zornMulOct P c₀ a₀ x (qgtMinus P C₁ A₁) = x * qgtMinus P C₁ A₁ := by
    unfold zornMulOct; rw [hW_xqm, hV_xqm, star_zero, sub_zero, add_zero]
  have hW_qmw : kantorWedge P c₀ (qgtMinus P C₁ A₁) w = 0 := by dsimp [w]; zorn_oct_abel hP
  have hV_qmw : kantorVee P a₀ (qgtMinus P C₁ A₁) w = 0 := by dsimp [w]; zorn_oct_abel hP
  have hMul_qmw : zornMulOct P c₀ a₀ (qgtMinus P C₁ A₁) w = qgtMinus P C₁ A₁ * w := by
    unfold zornMulOct; rw [hW_qmw, hV_qmw, star_zero, sub_zero, add_zero]
  have hW_wqp : ∀ C : B, kantorWedge P c₀ w (qgtPlus P A₁ C) = 0 := by
    intro C; dsimp [w]; zorn_oct_abel hP
  have hV_wqp : ∀ C : B, kantorVee P a₀ w (qgtPlus P A₁ C) = 0 := by
    intro C; dsimp [w]; zorn_oct_abel hP
  have hMul_wqp : ∀ C : B, zornMulOct P c₀ a₀ w (qgtPlus P A₁ C) = w * qgtPlus P A₁ C := by
    intro C; unfold zornMulOct; rw [hW_wqp C, hV_wqp C, star_zero, sub_zero, add_zero]
  have hW_qxw2 : kantorWedge P c₀ (qgtPlus P A₁ C₁ * x) w₂ = 0 := by
    dsimp [x, w₂]; zorn_oct_abel hP
  have hV_qxw2 : kantorVee P a₀ (qgtPlus P A₁ C₁ * x) w₂ = 0 := by
    dsimp [x, w₂]; zorn_oct_abel hP
  have hMul_qxw2 : zornMulOct P c₀ a₀ (qgtPlus P A₁ C₁ * x) w₂ = (qgtPlus P A₁ C₁ * x) * w₂ := by
    unfold zornMulOct; rw [hW_qxw2, hV_qxw2, star_zero, sub_zero, add_zero]
  have hW_xwqp : kantorWedge P c₀ x (w * qgtPlus P A₁ C₂) = 0 := by
    dsimp [x, w]; zorn_oct_abel hP
  have hV_xwqp : kantorVee P a₀ x (w * qgtPlus P A₁ C₂) = 0 := by
    dsimp [x, w]; zorn_oct_abel hP
  have hMul_xwqp : zornMulOct P c₀ a₀ x (w * qgtPlus P A₁ C₂) = x * (w * qgtPlus P A₁ C₂) := by
    unfold zornMulOct; rw [hW_xwqp, hV_xwqp, star_zero, sub_zero, add_zero]
  refine ⟨by dsimp [x, y, z]; rw [h123]; zorn_oct_abel hP,
          by dsimp [x, y, z]; rw [h123]; zorn_oct_abel hP,
          by dsimp [x, y, z]; rw [h123]; zorn_oct_abel hP,
          by dsimp [x, y]; rw [h112, h121, h211]; abel,
          by unfold assocOct; rw [hMul_xw C₁, hMul_wx, hMul_qx, hMul_xqm]; dsimp [x]; zorn_oct_abel hP,
          by unfold assocOct; rw [hMul_wx, hMul_xw C₁, hMul_qmw, hMul_wqp C₁]; dsimp [w]; zorn_oct_abel hP,
          by rw [hMul_xw C₁, hMul_qx, hMul_qxw2, hMul_xw C₂, hMul_wqp C₂, hMul_xwqp]; dsimp [x, w, w₂]; zorn_oct_abel hP⟩

omit [StarRing B] in
/-- Six-permutation signed telescoping cancellation in an additive group. -/
private lemma six_perm_cancel (u123 u132 u231 u213 u312 u321 v123 v213 v231 v321 v312 v132 : B) :
    ((u123 - u132) + (v123 - v213)) +
    ((u231 - u213) + (v231 - v321)) +
    ((u312 - u321) + (v312 - v132)) +
    ((u132 - u123) + (v132 - v312)) +
    ((u321 - u312) + (v321 - v231)) +
    ((u213 - u231) + (v213 - v123)) = 0 := by
  abel

/-- **Lemma ZM₁₁.1–ZM₁₅.1 (Equivalence of Flexibility and Simultaneous Left+Right Alternativity,
Half-Alternative Corner Laws, Full 6-Permutation `S₃` Vanishing, and 4-Body Kantor–Moufang Sandwich):** -/
lemma flexibility_alternativity_equivalence_and_kantor_moufang_sandwich
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ A₁ A₂ A₃ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    let z := conePlus P A₃
    diagPlus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ x x y ∧
    diagMinus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ y x x ∧
    (assocOct P c₀ a₀ x y x = 0 ↔
      (assocOct P c₀ a₀ x x y = 0 ∧ assocOct P c₀ a₀ y x x = 0)) ∧
    diagPlus P (assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ x z y) = 0 ∧
    diagPlus P (assocOct P c₀ a₀ x y y) = 0 ∧
    diagMinus P (assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ y x z) = 0 ∧
    diagMinus P (assocOct P c₀ a₀ x x y) = 0 ∧
    assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ y z x + assocOct P c₀ a₀ z x y +
      assocOct P c₀ a₀ x z y + assocOct P c₀ a₀ z y x + assocOct P c₀ a₀ y x z = 0 ∧
    assocOct P c₀ a₀ x (zornMulOct P c₀ a₀ y z) x = 0 ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y z)) x =
      kantorGp2 P A₁ (zornMulOct P c₀ a₀ y z) ∧
    zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y z) x) =
      kantorGp2 P A₁ (zornMulOct P c₀ a₀ y z) := by
  intro x y z
  have hDP_gen : ∀ U₁ U₂ U₃ : B,
      diagPlus P (assocOct P c₀ a₀ (conePlus P U₁) (conePlus P U₂) (conePlus P U₃)) =
        qgtPlus P U₁ (star U₂) * qgtPlus P (star c₀) (star U₃) -
        qgtPlus P U₁ (star U₃) * qgtPlus P (star c₀) (star U₂) :=
    fun U₁ U₂ U₃ => (three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ U₁ U₂ U₃ 0 0).1
  have hDM_gen : ∀ U₁ U₂ U₃ : B,
      diagMinus P (assocOct P c₀ a₀ (conePlus P U₁) (conePlus P U₂) (conePlus P U₃)) =
        qgtMinus P (star U₂) (star c₀) * qgtMinus P (star U₁) U₃ -
        qgtMinus P (star U₁) (star c₀) * qgtMinus P (star U₂) U₃ :=
    fun U₁ U₂ U₃ => (three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ U₁ U₂ U₃ 0 0).2.1
  have hDP_add : ∀ X Y : B, diagPlus P (X + Y) = diagPlus P X + diagPlus P Y := by
    intro X Y; unfold diagPlus; simp only [mul_add, add_mul]
  have hDM_add : ∀ X Y : B, diagMinus P (X + Y) = diagMinus P X + diagMinus P Y := by
    intro X Y; unfold diagMinus; simp only [mul_add, add_mul]
  have h123 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₃).2.2
  have h231 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₃ A₁).2.2
  have h312 := (upper_associator_expansion hP hPsym c₀ a₀ A₃ A₁ A₂).2.2
  have h132 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₃ A₂).2.2
  have h321 := (upper_associator_expansion hP hPsym c₀ a₀ A₃ A₂ A₁).2.2
  have h213 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₁ A₃).2.2
  have h112 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₁ A₂).2.2
  have h121 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₁).2.2
  have h211 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₁ A₁).2.2
  have hyz := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₃ A₁).2.1
  have hDP : diagPlus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ x x y := by
    dsimp [x, y]; rw [hDP_gen A₁ A₂ A₁, h112]; abel
  have hDM : diagMinus P (assocOct P c₀ a₀ x y x) = -assocOct P c₀ a₀ y x x := by
    dsimp [x, y]; rw [hDM_gen A₁ A₂ A₁, h211]; abel
  have hSum : assocOct P c₀ a₀ x y x = -assocOct P c₀ a₀ x x y - assocOct P c₀ a₀ y x x := by
    dsimp [x, y]; rw [h121, h112, h211]; abel
  have hIff : assocOct P c₀ a₀ x y x = 0 ↔
      (assocOct P c₀ a₀ x x y = 0 ∧ assocOct P c₀ a₀ y x x = 0) := by
    constructor
    · intro hF0
      have hL : -assocOct P c₀ a₀ x x y = 0 := by
        rw [← hDP, hF0]; unfold diagPlus; rw [mul_zero, zero_mul]
      have hR : -assocOct P c₀ a₀ y x x = 0 := by
        rw [← hDM, hF0]; unfold diagMinus; rw [mul_zero, zero_mul]
      exact ⟨neg_eq_zero.mp hL, neg_eq_zero.mp hR⟩
    · rintro ⟨hL0, hR0⟩
      rw [hSum, hL0, hR0, neg_zero, sub_self]
  have hSandL : ∀ V : B,
      zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x (coneMinus P V)) x =
        kantorGp2 P A₁ (coneMinus P V) := by
    intro V
    have hW1 : kantorWedge P c₀ x (coneMinus P V) = 0 := by dsimp [x]; zorn_oct_abel hP
    have hV1 : kantorVee P a₀ x (coneMinus P V) = 0 := by dsimp [x]; zorn_oct_abel hP
    have hW2 : kantorWedge P c₀ (x * coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
    have hV2 : kantorVee P a₀ (x * coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ x (coneMinus P V) hW1 hV1,
        zornMulOct_eq_mul c₀ a₀ (x * coneMinus P V) x hW2 hV2]
    rfl
  have hSandR : ∀ V : B,
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (coneMinus P V) x) =
        kantorGp2 P A₁ (coneMinus P V) := by
    intro V
    have hW1 : kantorWedge P c₀ (coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
    have hV1 : kantorVee P a₀ (coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
    have hW2 : kantorWedge P c₀ x (coneMinus P V * x) = 0 := by dsimp [x]; zorn_oct_abel hP
    have hV2 : kantorVee P a₀ x (coneMinus P V * x) = 0 := by dsimp [x]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ (coneMinus P V) x hW1 hV1,
        zornMulOct_eq_mul c₀ a₀ x (coneMinus P V * x) hW2 hV2]
    unfold kantorGp2; rw [mul_assoc]
  have hyz_cone : coneMinus P (zornMulOct P c₀ a₀ y z) = zornMulOct P c₀ a₀ y z := by
    dsimp [y, z]; rw [hyz]; zorn_oct_abel hP
  have hLHS :
      zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y z)) x =
        kantorGp2 P A₁ (zornMulOct P c₀ a₀ y z) := by
    have h := hSandL (zornMulOct P c₀ a₀ y z)
    rwa [hyz_cone] at h
  have hRHS :
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y z) x) =
        kantorGp2 P A₁ (zornMulOct P c₀ a₀ y z) := by
    have h := hSandR (zornMulOct P c₀ a₀ y z)
    rwa [hyz_cone] at h
  refine ⟨hDP, hDM, hIff,
          by dsimp [x, y, z]; rw [hDP_add, hDP_gen A₁ A₂ A₃, hDP_gen A₁ A₃ A₂]; abel,
          by dsimp [x, y]; rw [hDP_gen A₁ A₂ A₂]; abel,
          by dsimp [x, y, z]; rw [hDM_add, hDM_gen A₁ A₂ A₃, hDM_gen A₂ A₁ A₃]; abel,
          by dsimp [x, y]; rw [hDM_gen A₁ A₁ A₂]; abel,
          by dsimp [x, y, z]; rw [h123, h231, h312, h132, h321, h213];
             exact six_perm_cancel _ _ _ _ _ _ _ _ _ _ _ _,
          by unfold assocOct; rw [hLHS, hRHS, sub_self],
          hLHS, hRHS⟩

/-- **Lemma ZS₁.1–ZS₅.1 (Socratic Aporia of Un-Symmetrized Alternativity, Universal Jordan–Lie Telescoping,
and Jordan-Symmetrized Zorn Split-Octonion Alternativity):** -/
lemma unsymmetrized_aporia_and_symmetrized_zorn_alternativity
    {P L : B} (hP : P * P = P) (hPsym : star P = P)
    (Q₁ Q₂ c₀ a₀ C X Y A₁ A₂ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    coneMinus P C * assocOct P c₀ a₀ x x y =
      -qgtMinus P C A₁ * star (kantorWedge P c₀ x y) ∧
    (L * qgtMinus P C A₁ = 1 - P →
      assocOct P c₀ a₀ x x y = 0 →
      kantorWedge P c₀ x y = 0) ∧
    anticomm Q₁ (comm Q₁ Q₂) = comm (Q₁ * Q₁) Q₂ ∧
    anticomm (qgtPlus P A₁ c₀) (kantorWedge P c₀ A₁ A₂ * coneMinus P c₀) =
      comm (qgtPlus P A₁ c₀ * qgtPlus P A₁ c₀) (qgtPlus P A₂ c₀) ∧
    star (symDotPlus P X Y) = symDotPlus P X Y ∧
    assocSymOct P c₀ a₀ x x y =
      x * star (kantorWedge P c₀ x y) +
      kantorWedge P c₀ x y * coneMinus P (star A₁) := by
  intro x y
  have hSP : ∀ Z : B, star (conePlus P Z) = coneMinus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).1
  have hSM : ∀ Z : B, star (coneMinus P Z) = conePlus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).2.1
  have hStarQp : ∀ U V : B, star (qgtPlus P U V) = qgtPlus P (star V) (star U) := by
    intro U V; unfold qgtPlus; rw [star_mul, hSP U, hSM V]
  have hStarW := (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ x y).2.2.1
  have hVee0 : ∀ U V : B, kantorVee P a₀ (conePlus P U) (conePlus P V) = 0 := by
    intro U V; zorn_sym_abel hP
  have hWedgeSelf : kantorWedge P c₀ x x = 0 := by dsimp [x]; zorn_sym_abel hP
  have hMulSelf : zornMulOct P c₀ a₀ x x = 0 := by
    unfold zornMulOct
    rw [hVee0 A₁ A₁, hWedgeSelf, star_zero, sub_zero, add_zero]
    dsimp [x]; zorn_sym_abel hP
  have hMul0L : ∀ Z : B, zornMulOct P c₀ a₀ 0 Z = 0 := by
    intro Z; unfold zornMulOct kantorWedge kantorVee conePlus coneMinus
    simp only [mul_zero, zero_mul, sub_self, star_zero, add_zero]
  have hxy : zornMulOct P c₀ a₀ x y = star (kantorWedge P c₀ x y) := by
    unfold zornMulOct
    rw [hVee0 A₁ A₂, star_zero, sub_zero]
    have h0 : x * y = 0 := by dsimp [x, y]; zorn_sym_abel hP
    rw [h0, zero_add]
  have hAssocEq : assocOct P c₀ a₀ x x y = -x * star (kantorWedge P c₀ x y) := by
    unfold assocOct
    rw [hMulSelf, hMul0L, hxy]
    unfold zornMulOct
    rw [hStarW]
    dsimp [x, y]
    rw [hSP A₁, hSP A₂]
    have hW2 : kantorWedge P c₀ (conePlus P A₁)
        (-kantorVee P (star c₀) (coneMinus P (star A₁)) (coneMinus P (star A₂))) = 0 := by
      zorn_sym_abel hP
    have hV2 : kantorVee P a₀ (conePlus P A₁)
        (-kantorVee P (star c₀) (coneMinus P (star A₁)) (coneMinus P (star A₂))) = 0 := by
      zorn_sym_abel hP
    rw [hW2, hV2, star_zero]
    zorn_sym_abel hP
  have hMultC : coneMinus P C * assocOct P c₀ a₀ x x y =
      -qgtMinus P C A₁ * star (kantorWedge P c₀ x y) := by
    rw [hAssocEq]
    dsimp [x]
    unfold qgtMinus
    simp only [neg_mul, mul_neg, mul_assoc]
  have hSymSelf : zornMulSymOct P c₀ a₀ x x = 0 := by
    unfold zornMulSymOct symDotPlus symDotMinus
    have hW0 : kantorWedge P c₀ x x = 0 := by dsimp [x]; zorn_sym_abel hP
    have hV0 : kantorVee P a₀ x x = 0 := by dsimp [x]; zorn_sym_abel hP
    rw [hW0, hV0, star_zero]
    dsimp [x]; rw [hSP A₁]; zorn_sym_abel hP
  have hSym0L : ∀ Z : B, zornMulSymOct P c₀ a₀ 0 Z = 0 := by
    intro Z
    unfold zornMulSymOct symDotPlus symDotMinus kantorWedge kantorVee
           diagPlus diagMinus qgtPlus qgtMinus conePlus coneMinus
    simp only [mul_zero, zero_mul, sub_self, star_zero, add_zero]
  have hSym_xy : zornMulSymOct P c₀ a₀ x y = star (kantorWedge P c₀ x y) := by
    unfold zornMulSymOct symDotPlus symDotMinus
    have hV0 : kantorVee P a₀ x y = 0 := by dsimp [x, y]; zorn_sym_abel hP
    rw [hV0, star_zero]
    dsimp [x, y]; rw [hSP A₁, hSP A₂]; zorn_sym_abel hP
  have hAssocSym : assocSymOct P c₀ a₀ x x y =
      x * star (kantorWedge P c₀ x y) +
      kantorWedge P c₀ x y * coneMinus P (star A₁) := by
    unfold assocSymOct
    rw [hSymSelf, hSym0L, hSym_xy]
    set W := kantorWedge P c₀ x y
    unfold zornMulSymOct symDotPlus symDotMinus
    have hW_in_cone : P * W * (1 - P) = W := by dsimp [W, x, y]; zorn_sym_abel hP
    have hStarW_in_cone : (1 - P) * star W * P = star W := by
      rw [hStarW]; dsimp [x, y]; zorn_sym_abel hP
    have hW2 : kantorWedge P c₀ x (star W) = 0 := by
      rw [← hStarW_in_cone]; dsimp [x]; zorn_sym_abel hP
    have hV2 : kantorVee P a₀ x (star W) = 0 := by
      rw [← hStarW_in_cone]; dsimp [x]; zorn_sym_abel hP
    rw [hW2, hV2, star_zero, star_star]
    dsimp [x]
    rw [hSP A₁]
    have hDP_x : diagPlus P (conePlus P A₁) = 0 := by zorn_sym_abel hP
    have hDM_x : diagMinus P (conePlus P A₁) = 0 := by zorn_sym_abel hP
    have hCM_x : coneMinus P (conePlus P A₁) = 0 := by zorn_sym_abel hP
    have hCP_x : conePlus P (conePlus P A₁) = conePlus P A₁ := by zorn_sym_abel hP
    have hDM_sW : diagMinus P (star W) = 0 := by rw [← hStarW_in_cone]; zorn_sym_abel hP
    have hCP_sW : conePlus P (star W) = 0 := by rw [← hStarW_in_cone]; zorn_sym_abel hP
    have hCM_sW : coneMinus P (star W) = star W := by rw [← hStarW_in_cone]; zorn_sym_abel hP
    have hCP_W : conePlus P W = W := by rw [← hW_in_cone]; zorn_sym_abel hP
    have hCM_W : coneMinus P W = 0 := by rw [← hW_in_cone]; zorn_sym_abel hP
    unfold qgtPlus qgtMinus
    rw [hDP_x, hDM_x, hCM_x, hCP_x, hDM_sW, hCP_sW, hCM_sW, hCP_W, hCM_W]
    zorn_sym_abel hP
  refine ⟨hMultC, fun hInv hAssoc0 => ?_, ?_, by zorn_sym_abel hP, ?_, hAssocSym⟩
  · have hStarW0 : star (kantorWedge P c₀ x y) = 0 := by
      have h1 : L * (coneMinus P C * assocOct P c₀ a₀ x x y) = 0 := by
        rw [hAssoc0, mul_zero, mul_zero]
      rw [hMultC, neg_mul, mul_neg, ← mul_assoc L, hInv, neg_eq_zero] at h1
      have hAbsorb : (1 - P) * star (kantorWedge P c₀ x y) = star (kantorWedge P c₀ x y) := by
        rw [hStarW]
        dsimp [x, y]; zorn_sym_abel hP
      rw [← hAbsorb]
      exact h1
    have h2 : star (star (kantorWedge P c₀ x y)) = star (0 : B) := by rw [hStarW0]
    rw [star_star, star_zero] at h2
    exact h2
  · unfold anticomm comm
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  · unfold symDotPlus
    rw [star_add, hStarQp X Y, hStarQp (star Y) (star X), star_star, star_star, add_comm]

/-- **Lemma ZM₁₆.1–ZM₂₀.1 (Corner-Intertwining Moufang Laws, Native Opposite-Cone Reconstruction
of `kantorWedge` & `kantorTriple`, and Complete Middle Moufang Defect Formula):** -/
lemma corner_intertwining_and_middle_moufang_identity
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ A₁ A₂ A₃ C₁ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    let z := conePlus P A₃
    let w := coneMinus P C₁
    x * diagMinus P (assocOct P c₀ a₀ y z x) =
      -diagPlus P (assocOct P c₀ a₀ x y z) * x ∧
    zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y z) x) =
      -diagPlus P (assocOct P c₀ a₀ x y z) * x ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) y -
      zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ w x) =
      kantorWedge P C₁ A₁ A₂ ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) y +
      zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ w x) =
      kantorTriple x w y ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) (zornMulOct P c₀ a₀ z x) -
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y z) x) =
      kantorWedge P (star a₀) (kantorWedge P c₀ A₁ A₂) (kantorWedge P c₀ A₃ A₁) +
      diagPlus P (assocOct P c₀ a₀ x y z) * x ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) (zornMulOct P c₀ a₀ y x) = 0 ∧
    zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y y) x) = 0 := by
  intro x y z w
  have hSP : ∀ Z : B, star (conePlus P Z) = coneMinus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).1
  have hSM : ∀ Z : B, star (coneMinus P Z) = conePlus P (star Z) :=
    fun Z => (star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ Z Z).2.1
  have h123 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₃).2.2
  have h231 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₃ A₁).2.2
  have h122 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₂ A₂).2.2
  have hStarForm : ∀ U V : B,
      zornMulOct P c₀ a₀ (conePlus P U) (conePlus P V) = star (kantorWedge P c₀ U V) :=
    fun U V => (upper_associator_expansion hP hPsym c₀ a₀ U V 0).1
  have hPair : ∀ U V : B,
      zornMulOct P c₀ a₀ (conePlus P U) (conePlus P V) =
        -kantorVee P (star c₀) (coneMinus P (star U)) (coneMinus P (star V)) :=
    fun U V => (upper_associator_expansion hP hPsym c₀ a₀ U V 0).2.1
  have hIntertwine :
      x * diagMinus P (assocOct P c₀ a₀ y z x) = -diagPlus P (assocOct P c₀ a₀ x y z) * x := by
    have hDM231 := (three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ A₂ A₃ A₁ 0 0).2.1
    have hDP123 := (three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ A₁ A₂ A₃ 0 0).1
    dsimp [x, y, z]; rw [hDM231, hDP123]; zorn_oct_abel hP
  have hMidRHS_gen : ∀ U₃ : B,
      zornMulOct P c₀ a₀ (conePlus P A₁)
        (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (conePlus P A₂) (conePlus P U₃)) (conePlus P A₁)) =
        -diagPlus P (assocOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂) (conePlus P U₃)) * conePlus P A₁ := by
    intro U₃
    have hDP12U := (three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ A₁ A₂ U₃ 0 0).1
    have hRHS_sand := (flexibility_alternativity_equivalence_and_kantor_moufang_sandwich hP hPsym c₀ a₀ A₁ A₂ U₃).2.2.2.2.2.2.2.2.2.2
    rw [hRHS_sand, hPair A₂ U₃, hDP12U]
    zorn_oct_abel hP
  have hMidLHS_gen : ∀ U₃ : B,
      zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂))
        (zornMulOct P c₀ a₀ (conePlus P U₃) (conePlus P A₁)) =
        kantorWedge P (star a₀) (kantorWedge P c₀ A₁ A₂) (kantorWedge P c₀ U₃ A₁) := by
    intro U₃
    set W₁₂ := kantorWedge P c₀ A₁ A₂
    set W₃₁ := kantorWedge P c₀ U₃ A₁
    have hW12_cone : conePlus P W₁₂ = W₁₂ := by dsimp [W₁₂]; zorn_oct_abel hP
    have hW31_cone : conePlus P W₃₁ = W₃₁ := by dsimp [W₃₁]; zorn_oct_abel hP
    have hStarW12 : zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂) = coneMinus P (star W₁₂) :=
      calc zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂)
        _ = star W₁₂ := hStarForm A₁ A₂
        _ = star (conePlus P W₁₂) := by rw [hW12_cone]
        _ = coneMinus P (star W₁₂) := hSP W₁₂
    have hStarW31 : zornMulOct P c₀ a₀ (conePlus P U₃) (conePlus P A₁) = coneMinus P (star W₃₁) :=
      calc zornMulOct P c₀ a₀ (conePlus P U₃) (conePlus P A₁)
        _ = star W₃₁ := hStarForm U₃ A₁
        _ = star (conePlus P W₃₁) := by rw [hW31_cone]
        _ = coneMinus P (star W₃₁) := hSP W₃₁
    have hLow := (lower_associator_expansion hP hPsym c₀ a₀ (star W₁₂) (star W₃₁) 0).1
    calc zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (conePlus P A₁) (conePlus P A₂))
           (zornMulOct P c₀ a₀ (conePlus P U₃) (conePlus P A₁))
      _ = zornMulOct P c₀ a₀ (coneMinus P (star W₁₂)) (coneMinus P (star W₃₁)) := by
            rw [hStarW12, hStarW31]
      _ = kantorWedge P (star a₀) (conePlus P (star (star W₁₂))) (conePlus P (star (star W₃₁))) := hLow
      _ = kantorWedge P (star a₀) W₁₂ W₃₁ := by
            rw [star_star, star_star, hW12_cone, hW31_cone]
  have h_xw : zornMulOct P c₀ a₀ x w = qgtPlus P A₁ C₁ := by
    have hW : kantorWedge P c₀ x w = 0 := by dsimp [x, w]; zorn_oct_abel hP
    have hV : kantorVee P a₀ x w = 0 := by dsimp [x, w]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ x w hW hV]; rfl
  have h_wx : zornMulOct P c₀ a₀ w x = qgtMinus P C₁ A₁ := by
    have hW : kantorWedge P c₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
    have hV : kantorVee P a₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ w x hW hV]; rfl
  have h_xwy :
      zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) y =
        conePlus P A₁ * coneMinus P C₁ * conePlus P A₂ := by
    have hW : kantorWedge P c₀ (qgtPlus P A₁ C₁) y = 0 := by dsimp [y]; zorn_oct_abel hP
    have hV : kantorVee P a₀ (qgtPlus P A₁ C₁) y = 0 := by dsimp [y]; zorn_oct_abel hP
    rw [h_xw, zornMulOct_eq_mul c₀ a₀ (qgtPlus P A₁ C₁) y hW hV]; dsimp [y]; zorn_oct_abel hP
  have h_ywx :
      zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ w x) =
        conePlus P A₂ * coneMinus P C₁ * conePlus P A₁ := by
    have hW : kantorWedge P c₀ y (qgtMinus P C₁ A₁) = 0 := by dsimp [y]; zorn_oct_abel hP
    have hV : kantorVee P a₀ y (qgtMinus P C₁ A₁) = 0 := by dsimp [y]; zorn_oct_abel hP
    rw [h_wx, zornMulOct_eq_mul c₀ a₀ y (qgtMinus P C₁ A₁) hW hV]; dsimp [y]; zorn_oct_abel hP
  have hDP122 := (flexibility_alternativity_equivalence_and_kantor_moufang_sandwich hP hPsym c₀ a₀ A₁ A₂ A₂).2.2.2.2.1
  have hSkew21 : kantorWedge P c₀ A₂ A₁ = -kantorWedge P c₀ A₁ A₂ := by zorn_oct_abel hP
  have hWedgeNeg : ∀ U : B, kantorWedge P (star a₀) U (-U) = 0 := fun U => by zorn_oct_abel hP
  refine ⟨hIntertwine, by dsimp [x, y, z]; exact hMidRHS_gen A₃,
          by rw [h_xwy, h_ywx]; rfl,
          by rw [h_xwy, h_ywx]; rfl,
          by dsimp [x, y, z]; rw [hMidLHS_gen A₃, hMidRHS_gen A₃, neg_mul, sub_neg_eq_add],
          by dsimp [x, y]; rw [hMidLHS_gen A₂, hSkew21, hWedgeNeg],
          by dsimp [x, y]; rw [hMidRHS_gen A₂, hDP122, neg_zero, zero_mul]⟩

/-- **Lemma ZM₂₁.1–ZM₂₅.1 (Bilateral Left/Right Active Moufang Duality, Dual Lower-Cone Corner
Intertwining, and Nested `kantorWedge` Jacobi Identity):** -/
lemma bilateral_active_moufang_duality_and_lower_intertwining
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ A₁ A₂ A₃ C₁ C₂ C₃ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    let w := coneMinus P C₁
    let w₂ := coneMinus P C₂
    let w₃ := coneMinus P C₃
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) x) w =
      -assocOct P c₀ a₀ y x x * w ∧
    zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ x w)) = 0 ∧
    zornMulOct P c₀ a₀ w (zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y x)) =
      w * assocOct P c₀ a₀ x x y ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ w x) y) x = 0 ∧
    w * diagPlus P (assocOct P c₀ a₀ w₂ w₃ w) =
      -diagMinus P (assocOct P c₀ a₀ w w₂ w₃) * w ∧
    kantorWedge P c₀ (kantorWedge P c₀ A₁ A₂) A₃ +
      kantorWedge P c₀ (kantorWedge P c₀ A₂ A₃) A₁ +
      kantorWedge P c₀ (kantorWedge P c₀ A₃ A₁) A₂ = 0 := by
  intro x y w w₂ w₃
  have h211 := (upper_associator_expansion hP hPsym c₀ a₀ A₂ A₁ A₁).2.2
  have h112 := (upper_associator_expansion hP hPsym c₀ a₀ A₁ A₁ A₂).2.2
  have hw231 := (lower_associator_expansion hP hPsym c₀ a₀ C₂ C₃ C₁).2
  have hw123 := (lower_associator_expansion hP hPsym c₀ a₀ C₁ C₂ C₃).2
  have hPair : ∀ U V : B,
      zornMulOct P c₀ a₀ (conePlus P U) (conePlus P V) =
        -kantorVee P (star c₀) (coneMinus P (star U)) (coneMinus P (star V)) :=
    fun U V => (upper_associator_expansion hP hPsym c₀ a₀ U V 0).2.1
  have h_xw : zornMulOct P c₀ a₀ x w = qgtPlus P A₁ C₁ := by
    have hW : kantorWedge P c₀ x w = 0 := by dsimp [x, w]; zorn_oct_abel hP
    have hV : kantorVee P a₀ x w = 0 := by dsimp [x, w]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ x w hW hV]; rfl
  have h_wx : zornMulOct P c₀ a₀ w x = qgtMinus P C₁ A₁ := by
    have hW : kantorWedge P c₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
    have hV : kantorVee P a₀ w x = 0 := by dsimp [x, w]; zorn_oct_abel hP
    rw [zornMulOct_eq_mul c₀ a₀ w x hW hV]; rfl
  refine ⟨?_, ?_, ?_, ?_,
          by dsimp [w, w₂, w₃]; rw [hw231, hw123]; zorn_oct_abel hP,
          by zorn_oct_abel hP⟩
  · have hMul_Vx_w : ∀ V : B,
        zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (coneMinus P V) x) w =
          (coneMinus P V * x) * w := by
      intro V
      have hW1 : kantorWedge P c₀ (coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
      have hV1 : kantorVee P a₀ (coneMinus P V) x = 0 := by dsimp [x]; zorn_oct_abel hP
      have hW2 : kantorWedge P c₀ (coneMinus P V * x) w = 0 := by dsimp [x, w]; zorn_oct_abel hP
      have hV2 : kantorVee P a₀ (coneMinus P V * x) w = 0 := by dsimp [x, w]; zorn_oct_abel hP
      rw [zornMulOct_eq_mul c₀ a₀ (coneMinus P V) x hW1 hV1,
          zornMulOct_eq_mul c₀ a₀ (coneMinus P V * x) w hW2 hV2]
    have hxy_cone : coneMinus P (zornMulOct P c₀ a₀ x y) = zornMulOct P c₀ a₀ x y := by
      dsimp [x, y]; rw [hPair A₁ A₂]; zorn_oct_abel hP
    have h_xy_x : zornMulOct P c₀ a₀ x y * x = -assocOct P c₀ a₀ y x x := by
      dsimp [x, y]; rw [hPair A₁ A₂, h211]; zorn_oct_abel hP
    have hStep := hMul_Vx_w (zornMulOct P c₀ a₀ x y)
    rw [hxy_cone, h_xy_x] at hStep
    exact hStep
  · rw [h_xw]
    have hW : kantorWedge P c₀ y (qgtPlus P A₁ C₁) = 0 := by dsimp [y]; zorn_oct_abel hP
    have hV : kantorVee P a₀ y (qgtPlus P A₁ C₁) = 0 := by dsimp [y]; zorn_oct_abel hP
    have h_y_qp : zornMulOct P c₀ a₀ y (qgtPlus P A₁ C₁) = 0 := by
      rw [zornMulOct_eq_mul c₀ a₀ y (qgtPlus P A₁ C₁) hW hV]; dsimp [y]; zorn_oct_abel hP
    have h_x_0 : zornMulOct P c₀ a₀ x 0 = 0 := by
      unfold zornMulOct kantorWedge kantorVee conePlus coneMinus
      simp only [mul_zero, zero_mul, sub_self, star_zero, add_zero]
    rw [h_y_qp, h_x_0]
  · have hMul_w_xV : ∀ V : B,
        zornMulOct P c₀ a₀ w (zornMulOct P c₀ a₀ x (coneMinus P V)) =
          w * (x * coneMinus P V) := by
      intro V
      have hW1 : kantorWedge P c₀ x (coneMinus P V) = 0 := by dsimp [x]; zorn_oct_abel hP
      have hV1 : kantorVee P a₀ x (coneMinus P V) = 0 := by dsimp [x]; zorn_oct_abel hP
      have hW2 : kantorWedge P c₀ w (x * coneMinus P V) = 0 := by dsimp [x, w]; zorn_oct_abel hP
      have hV2 : kantorVee P a₀ w (x * coneMinus P V) = 0 := by dsimp [x, w]; zorn_oct_abel hP
      rw [zornMulOct_eq_mul c₀ a₀ x (coneMinus P V) hW1 hV1,
          zornMulOct_eq_mul c₀ a₀ w (x * coneMinus P V) hW2 hV2]
    have hyx_cone : coneMinus P (zornMulOct P c₀ a₀ y x) = zornMulOct P c₀ a₀ y x := by
      dsimp [x, y]; rw [hPair A₂ A₁]; zorn_oct_abel hP
    have h_x_yx : x * zornMulOct P c₀ a₀ y x = assocOct P c₀ a₀ x x y := by
      dsimp [x, y]; rw [hPair A₂ A₁, h112]; zorn_oct_abel hP
    have hStep := hMul_w_xV (zornMulOct P c₀ a₀ y x)
    rw [hyx_cone, h_x_yx] at hStep
    exact hStep
  · rw [h_wx]
    have hW : kantorWedge P c₀ (qgtMinus P C₁ A₁) y = 0 := by dsimp [y]; zorn_oct_abel hP
    have hV : kantorVee P a₀ (qgtMinus P C₁ A₁) y = 0 := by dsimp [y]; zorn_oct_abel hP
    have h_qm_y : zornMulOct P c₀ a₀ (qgtMinus P C₁ A₁) y = 0 := by
      rw [zornMulOct_eq_mul c₀ a₀ (qgtMinus P C₁ A₁) y hW hV]; dsimp [y]; zorn_oct_abel hP
    have h_0_x : zornMulOct P c₀ a₀ 0 x = 0 := by
      unfold zornMulOct kantorWedge kantorVee conePlus coneMinus
      simp only [mul_zero, zero_mul, sub_self, star_zero, add_zero]
    rw [h_qm_y, h_0_x]

/-! ### Master Theorem (`Stages D₆₅–D₆₆` and `D₇₀–D₇₆`): Complete Zorn Split-Octonion & Moufang Synthesis -/

/-- **Master Theorem (`Stages D₆₅–D₆₆` & `D₇₀–D₇₆` — Complete Zorn Split-Octonion, Flexibility–Alternativity
Equivalence, Jordan-Symmetrized Alternativity, Corner-Intertwining Moufang Law, and Bilateral
Active Moufang Duality Synthesis):**
Unifies all 40 archetypes (`ZO₁ → ZO₁₀`, `ZM₁ → ZM₂₅`, `ZS₁ → ZS₅`) in native Mathlib4 over
`[Ring B] [StarRing B]` with zero `sorry`s and zero scalar/commuting assumptions. -/
theorem zorn_split_octonion_moufang_master_synthesis
    {P L : B} (hP : P * P = P) (hPsym : star P = P)
    (c₀ a₀ X Y A₁ A₂ A₃ C₁ C₂ C₃ Q₁ Q₂ : B) :
    let x := conePlus P A₁
    let y := conePlus P A₂
    let z := conePlus P A₃
    let w := coneMinus P C₁
    let w₂ := coneMinus P C₂
    let w₃ := coneMinus P C₃
    -- 1. Cubic Grading Quantization `Δ_sc³(X) = 4 • Δ_sc(X)` & Corner Commutator (`ZO₇, ZO₉`):
    superCommDelta P (superCommDelta P (superCommDelta P X)) =
      (4 : ℤ) • superCommDelta P X ∧
    cornerThirdOrder P C₁ A₁ A₂ C₁ = comm (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₁) ∧
    -- 2. Contravariant Star-Duality of `kantorWedge` and `kantorVee` (`ZM₁`):
    star (kantorWedge P c₀ A₁ A₂) = -kantorVee P (star c₀) (star A₁) (star A₂) ∧
    -- 3. Same-Cone Homotope Cyclic Jacobi Identity (`ZM₃`):
    assocKZ P c₀ a₀ x y z + assocKZ P c₀ a₀ y z x + assocKZ P c₀ a₀ z x y = 0 ∧
    -- 4. Full 3-Vector Split-Octonion Associator Orthogonal Corner Split & 3-Term Cyclic Flexibility (`ZM₆, ZM₇`):
    diagPlus P (assocOct P c₀ a₀ x y z) + diagMinus P (assocOct P c₀ a₀ x y z) =
      assocOct P c₀ a₀ x y z ∧
    assocOct P c₀ a₀ x x y + assocOct P c₀ a₀ x y x + assocOct P c₀ a₀ y x x = 0 ∧
    -- 5. Unconditional Opposite-Cone Moufang Identity (`ZM₈, ZM₉, ZM₁₀`):
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) x) w₂ =
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ w (zornMulOct P c₀ a₀ x w₂)) ∧
    -- 6. Equivalence of Flexibility and Simultaneous Left+Right Alternativity on the Cone (`ZM₁₁`):
    (assocOct P c₀ a₀ x y x = 0 ↔
      (assocOct P c₀ a₀ x x y = 0 ∧ assocOct P c₀ a₀ y x x = 0)) ∧
    -- 7. Unconditional Half-Alternative Corner Skew-Symmetries & 6-Permutation `S₃` Vanishing (`ZM₁₂, ZM₁₃`):
    diagPlus P (assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ x z y) = 0 ∧
    diagMinus P (assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ y x z) = 0 ∧
    assocOct P c₀ a₀ x y z + assocOct P c₀ a₀ y z x + assocOct P c₀ a₀ z x y +
      assocOct P c₀ a₀ x z y + assocOct P c₀ a₀ z y x + assocOct P c₀ a₀ y x z = 0 ∧
    -- 8. 4-Body Kantor–Moufang Sandwich (`ZM₁₄, ZM₁₅`):
    assocOct P c₀ a₀ x (zornMulOct P c₀ a₀ y z) x = 0 ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y z)) x =
      kantorGp2 P A₁ (zornMulOct P c₀ a₀ y z) ∧
    -- 9. Socratic Aporia, Universal Jordan–Lie Telescoping & Symmetrized Left Alternativity (`ZS₁, ZS₂, ZS₄`):
    (L * qgtMinus P C₁ A₁ = 1 - P →
      assocOct P c₀ a₀ x x y = 0 →
      kantorWedge P c₀ x y = 0) ∧
    anticomm Q₁ (comm Q₁ Q₂) = comm (Q₁ * Q₁) Q₂ ∧
    assocSymOct P c₀ a₀ x x y =
      x * star (kantorWedge P c₀ x y) +
      kantorWedge P c₀ x y * coneMinus P (star A₁) ∧
    -- 10. Corner-Intertwining Moufang Law & Native Opposite-Cone Reconstruction (`ZM₁₆, ZM₁₈, ZM₂₃`):
    x * diagMinus P (assocOct P c₀ a₀ y z x) =
      -diagPlus P (assocOct P c₀ a₀ x y z) * x ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) y -
      zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ w x) =
      kantorWedge P C₁ A₁ A₂ ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x w) y +
      zornMulOct P c₀ a₀ y (zornMulOct P c₀ a₀ w x) =
      kantorTriple x w y ∧
    -- 11. Complete Middle Moufang Defect & Unconditional Symmetric Closure (`ZM₁₉, ZM₂₀`):
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) (zornMulOct P c₀ a₀ z x) -
      zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ y z) x) =
      kantorWedge P (star a₀) (kantorWedge P c₀ A₁ A₂) (kantorWedge P c₀ A₃ A₁) +
      diagPlus P (assocOct P c₀ a₀ x y z) * x ∧
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) (zornMulOct P c₀ a₀ y x) = 0 ∧
    -- 12. Bilateral Left/Right Active Moufang Duality & Dual Lower-Cone Intertwining (`ZM₂₁, ZM₂₂, ZM₂₅`):
    zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ (zornMulOct P c₀ a₀ x y) x) w =
      -assocOct P c₀ a₀ y x x * w ∧
    zornMulOct P c₀ a₀ w (zornMulOct P c₀ a₀ x (zornMulOct P c₀ a₀ y x)) =
      w * assocOct P c₀ a₀ x x y ∧
    w * diagPlus P (assocOct P c₀ a₀ w₂ w₃ w) =
      -diagMinus P (assocOct P c₀ a₀ w w₂ w₃) * w := by
  intro x y z w w₂ w₃
  rcases zorn_matrix_cubic_grading_and_corner_factorization hP X X Y A₁ C₁ A₁ A₁ C₁ A₁ A₂ A₂ C₁ A₂ C₁ C₁ with
    ⟨_, _, _, _, hZ5, _, _, _, _, _, _, hZ12⟩
  rcases star_duality_of_peirce_cones_and_kantor_brackets hPsym c₀ A₁ A₂ with
    ⟨_, _, hS3, _⟩
  rcases same_cone_homotope_jacobi_and_aporia hP c₀ a₀ A₁ A₂ A₃ with
    ⟨_, hJ2, _⟩
  rcases three_vector_associator_and_mixed_cone_moufang hP hPsym c₀ a₀ A₁ A₂ A₃ C₁ C₂ with
    ⟨_, _, hM3, hM4, _, _, hM7⟩
  rcases flexibility_alternativity_equivalence_and_kantor_moufang_sandwich hP hPsym c₀ a₀ A₁ A₂ A₃ with
    ⟨_, _, hF3, hF4, _, hF6, _, hF8, hF9, hF10, _⟩
  rcases unsymmetrized_aporia_and_symmetrized_zorn_alternativity (L := L) hP hPsym Q₁ Q₂ c₀ a₀ C₁ X Y A₁ A₂ with
    ⟨_, hA2, hA3, _, _, hA6⟩
  rcases corner_intertwining_and_middle_moufang_identity hP hPsym c₀ a₀ A₁ A₂ A₃ C₁ with
    ⟨hI1, _, hI3, hI4, hI5, hI6, _⟩
  rcases bilateral_active_moufang_duality_and_lower_intertwining hP hPsym c₀ a₀ A₁ A₂ A₃ C₁ C₂ C₃ with
    ⟨hB1, _, hB3, _, hB5, _⟩
  exact ⟨hZ5, hZ12, hS3, hJ2, hM3, hM4, hM7, hF3, hF4, hF6, hF8, hF9, hF10,
         hA2, hA3, hA6, hI1, hI3, hI4, hI5, hI6, hB1, hB3, hB5⟩

end StarRingPrimitives

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornSplitOctonionMoufangPoset
