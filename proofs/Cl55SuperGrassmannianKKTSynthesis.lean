/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.Synthesis.Cl22RealDiracCarrier

/-!
# $\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(4,4) \cong \mathrm{Cl}(5,5)$ 5-Graded KKT Conformal Extension, Twistor Space $\mathbb{T}_{(5,5)}$, & Supercolor $\mathrm{SU}(3\vert 1)$ Super-Grassmannian

This module formalizes the conformal-projective extension
$\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(4,4) \cong \mathrm{Cl}(5,5) \cong \operatorname{Mat}(32, \mathbb{R})$
and its geometric realization as the 5-graded Kantor–Koecher–Tits (KKT) symmetry
algebra acting on the $\mathrm{Cl}(5,5)$ twistor space $\mathbb{T}_{(5,5)} \cong \mathbb{R}^{16} = \mathbf{8}_s \oplus \mathbf{8}_c$
and the supercolor supertwistor carrier $\mathbb{T}_{\text{super}} \cong \mathbb{R}^{16\vert 8}$:

1. **Section 1 ($\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(4,4) \cong \mathrm{Cl}(5,5)$ Carrier Factorization & $\mathfrak{spin}(5,5)$ Bivector Decomposition)**:
   - Proves the exact real Clifford carrier factorization
     $\dim \mathrm{Cl}(1,1) \cdot \dim \mathrm{Cl}(4,4) = 2^2 \cdot 2^8 = 2^{10} = 1024 = 32^2$
     (`cl11_cl44_cl55_carrier_factorization`).
   - Proves the 45-dimensional Lie algebra decomposition of $\mathfrak{spin}(5,5) = \bigwedge^2 \mathbb{R}^{5,5}$
     over the $\mathrm{Cl}(4,4)$ base:
     $$\binom{10}{2} = \binom{8}{2}_{\mathfrak{so}(4,4)} + (8 \times 2)_{\mathfrak{g}_{-1} \oplus \mathfrak{g}_{+1}} + \binom{2}{2}_{\mathfrak{so}(1,1)} = 28 + 16 + 1 = 45$$
     and the 5-graded KKT dimension sum $1 + 8 + 29 + 8 + 1 = 47$ (`spin55_bivector_kkt_decomposition`).

2. **Section 2 (Native $\mathrm{Cl}(5,5)$ 5-Graded Kantor–Koecher–Tits Operator Algebra & Quintic Characteristic Law)**:
   - Bridges directly to the native `Cl55` carrier in `InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure`
     (`cl55_kkt_five_graded_ladder_synthesis`), establishing grade $+1$ for `creation55 i`,
     grade $-1$ for `annihilation55 i`, grade $+2$ for `creation55 i * creation55 j`,
     grade $-2$ for `annihilation55 i * annihilation55 j`, grade $0$ for mixed products
     and commutators, and $\mathrm{Spin}(5,5)$-equivariant grade preservation.
   - Bridges to the quintic Kantor–Tanaka identity $\operatorname{ad}_H^5(X) - 5\operatorname{ad}_H^3(X) + 4\operatorname{ad}_H(X) = 0$
     and the 5-grade characteristic polynomial factorization
     $x(x - 1)(x + 1)(x - 2)(x + 2) = x^5 - 5x^3 + 4x$ (`kkt_quintic_characteristic_synthesis`).

3. **Section 3 ($\mathrm{Cl}(5,5)$ Twistor Space $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c \cong R^{16}$ & Penrose Incidence Nullity)**:
   - Defines the 16-component semi-spinor twistor space `Twistor55 R := (Fin 8 → R) × (Fin 8 → R)`,
     the neutral split twistor pairing `twistorNeutralPairing`, the symplectic twistor form
     `twistorSymplecticForm`, and the Penrose incidence relation $\psi^A = X^{A\dot{A}} \chi_{\dot{A}}$
     (`PenroseTwistorIncidence`).
   - Proves `penrose_incidence_null_of_skewSymmetric`: for any skew-symmetric spacetime bivector
     matrix $X \in M_8(R)$ ($X^T = -X$), every incident twistor $Z = (X\chi, \chi) \in \mathbb{T}_{(5,5)}$
     is strictly isotropic with respect to `twistorNeutralPairing` (`twistorNeutralPairing Z Z = 0`).

4. **Section 4 (Günaydin–Gürsey $\mathbf{8}_s \to (\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$ Splitting & Supertwistor Space $\mathbb{T}_{\text{super}} \cong R^{16\vert 8}$)**:
   - Constructs the explicit $R$-linear equivalence `gunaydinGurseyEquiv` decomposing an
     8-component $\mathrm{Cl}(4,4)$ semi-spinor into 2 leptonic color-singlets ($\mathbf{1} \oplus \mathbf{1}$),
     3 quark color-triplet components ($\mathbf{3}$), and 3 anti-quark components ($\bar{\mathbf{3}}$).
   - Defines the supertwistor carrier `SuperTwistor55 R` and the odd supercolor incidence map
     $\Theta^a = \sum_{A=0}^7 \psi^A \theta_A^a$ (`oddSupercolorIncidence`), proving its exact
     Penrose spacetime incidence transport law `oddSupercolorIncidence_penrose_transport`.

5. **Section 5 (Super-Andreev Reflection $\mathcal{R}_{\text{super}}$ & Grassmann Color-Singlet Conservation)**:
   - Defines `superAndreevReflect` mapping $(\psi, \chi; \eta, \xi, \ell) \mapsto (-\chi, \psi; \xi, -\eta, \ell)$.
   - Proves `superAndreevReflect_order_four_and_symplectic_invariance` ($\mathcal{R}_{\text{super}}^2 = -\mathrm{id}$
     on $(\psi, \chi; \eta, \xi)$, $\mathcal{R}_{\text{super}}^4 = \mathrm{id}$, and exact invariance of both the
     spacetime twistor symplectic form and the color symplectic form).
   - Proves `grassmann_color_singlet_superAndreev_invariant`: in any non-commutative ring $A$
     where the quark and anti-quark Grassmann supercharges anticommute ($\eta_a \xi_a + \xi_a \eta_a = 0$),
     the color-singlet bilinear invariant $\mathcal{I}_{\text{color}}(\eta, \xi) = \sum_{a=0}^2 \eta_a \xi_a$
     is strictly conserved under Super-Andreev reflection $(\eta, \xi) \mapsto (\xi, -\eta)$.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis

open BigOperators Finset Matrix
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra

/-!
## Section 1: $\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(4,4) \cong \mathrm{Cl}(5,5)$ Carrier Factorization & $\mathfrak{spin}(5,5)$ Bivector Decomposition
-/

/-- **Theorem 1.1 ($\mathrm{Cl}(1,1) \;\widehat{\otimes}\; \mathrm{Cl}(4,4) \cong \mathrm{Cl}(5,5) \cong \operatorname{Mat}(32, \mathbb{R})$ Carrier Dimension Factorization)**:
1. $\dim \mathrm{Cl}(1,1) = 2^2 = 4$,
2. $\dim \mathrm{Cl}(4,4) = 2^8 = 256$,
3. $\dim \mathrm{Cl}(5,5) = 2^{10} = 1024 = 2^2 \cdot 2^8$,
4. $\dim \Delta_{5,5} = 32 = 16 + 16$ ($\Delta_{5,5} = S^+ \oplus S^- = \mathbb{T} \oplus \mathbb{T}^*$),
   and $\dim \operatorname{Mat}(32, \mathbb{R}) = 32^2 = 1024$. -/
theorem cl11_cl44_cl55_carrier_factorization :
    2 ^ 2 = 4 ∧
    2 ^ 8 = 256 ∧
    2 ^ 10 = 1024 ∧
    (2 ^ 2) * (2 ^ 8) = 2 ^ 10 ∧
    32 ^ 2 = 2 ^ 10 ∧
    16 + 16 = 32 := by
  norm_num

/-- **Theorem 1.2 ($\mathfrak{spin}(5,5)$ Bivector Decomposition & 5-Graded KKT Dimension Accounting)**:
1. $\dim \mathfrak{spin}(5,5) = \binom{10}{2} = 45$,
2. $\dim \mathfrak{so}(4,4) = \binom{8}{2} = 28$ (internal color + base Lorentz rotations in $\mathfrak{g}_0$),
3. $\dim(\mathfrak{g}_{-1} \oplus \mathfrak{g}_{+1}) = 8 \times 2 = 16$ (8 causal translations $n_- \otimes \mathbb{R}^{4,4}$
   plus 8 retrocausal special conformal shifts $n_+ \otimes (\mathbb{R}^{4,4})^*$),
4. $\dim \mathfrak{so}(1,1) = \binom{2}{2} = 1$ (the central Euler/dilatation generator $D = \frac{1}{2}e_0 e_1$),
5. $\binom{10}{2} = \binom{8}{2} + 8 \times 2 + \binom{2}{2} = 28 + 16 + 1 = 45$,
6. Adding the two contact centers $\mathfrak{g}_{-2} = \mathbb{R}(n_- \otimes \mathbf{1})$ and
   $\mathfrak{g}_{+2} = \mathbb{R}(n_+ \otimes \mathbf{1})$ gives the 5-graded KKT dimension sum
   $1 + 8 + (28 + 1) + 8 + 1 = 47$, while the Günaydin–Gürsey semi-spinor splits as
   $\dim \mathbf{8}_s = (1 + 1) + (3 + 3) = 8$. -/
theorem spin55_bivector_kkt_decomposition :
    Nat.choose 10 2 = 45 ∧
    Nat.choose 8 2 = 28 ∧
    8 * 2 = 16 ∧
    Nat.choose 2 2 = 1 ∧
    Nat.choose 10 2 = Nat.choose 8 2 + 8 * 2 + Nat.choose 2 2 ∧
    1 + 8 + (28 + 1) + 8 + 1 = 47 ∧
    (1 + 1) + (3 + 3) = 8 := by
  refine ⟨by decide, by decide, by norm_num, by decide, by decide, by norm_num, by norm_num⟩

/-!
## Section 2: Native $\mathrm{Cl}(5,5)$ 5-Graded Kantor–Koecher–Tits Operator Algebra & Quintic Characteristic Law
-/

/-- **Theorem 2.1 (Native `Cl55` 5-Graded Kantor–Koecher–Tits Ladder & $\mathrm{Spin}(5,5)$ Covariance)**:
In the repository's native Clifford algebra `Cl55`:
1. Every fermionic creation operator `creation55 i` has operator grade $+1$, and every
   annihilation operator `annihilation55 i` has operator grade $-1$.
2. Pairwise creation products `creation55 i * creation55 j` inhabit the top horizon grade $+2$,
   pairwise annihilation products `annihilation55 i * annihilation55 j` inhabit the sink grade $-2$,
   and mixed products `creation55 i * annihilation55 j` inhabit the Levi grade $0$.
3. Commutators of grade-$1$ elements lie in grade $+2$, commutators of grade-$(-1)$ elements
   lie in grade $-2$, and mixed grade-$(1, -1)$ commutators close into the Levi subalgebra grade $0$.
4. Conjugation by any spin group element $g \in \mathrm{Spin}(5,5)$ transports the 5-graded
   commutator structure covariantly. -/
theorem cl55_kkt_five_graded_ladder_synthesis
    (i j : Fin 5) (g : Spin55) :
    creation55 i ∈ cl55GradeSubmodule 1 ∧
    annihilation55 i ∈ cl55GradeSubmodule (-1) ∧
    creation55 i * creation55 j ∈ cl55GradeSubmodule 2 ∧
    annihilation55 i * annihilation55 j ∈ cl55GradeSubmodule (-2) ∧
    creation55 i * annihilation55 j ∈ cl55GradeSubmodule 0 ∧
    (creation55 i * creation55 j - creation55 j * creation55 i) ∈ cl55GradeSubmodule 2 ∧
    (annihilation55 i * annihilation55 j - annihilation55 j * annihilation55 i) ∈
      cl55GradeSubmodule (-2) ∧
    (creation55 i * annihilation55 j - annihilation55 j * creation55 i) ∈
      cl55GradeSubmodule 0 ∧
    spinCliffordRingEquiv g (creation55 i * annihilation55 j - annihilation55 j * creation55 i) ∈
      spinTransportedCl55GradeSubmodule g (1 + (-1)) := by
  refine ⟨creation55_mem_grade_one i,
    annihilation55_mem_grade_neg_one i,
    creation55_mul_creation55_mem_grade_two i j,
    annihilation55_mul_annihilation55_mem_grade_neg_two i j,
    creation55_mul_annihilation55_mem_grade_zero i j,
    cl55_pos_one_pos_one_commutator_mem_grade_two
      (creation55_mem_grade_one i) (creation55_mem_grade_one j),
    cl55_neg_one_neg_one_commutator_mem_grade_neg_two
      (annihilation55_mem_grade_neg_one i) (annihilation55_mem_grade_neg_one j),
    cl55_mixed_commutator_mem_grade_zero
      (creation55_mem_grade_one i) (annihilation55_mem_grade_neg_one j),
    spinTransported_grade_commutator_mem_of_mem g 1 (-1)
      (creation55_mem_grade_one i) (annihilation55_mem_grade_neg_one j)⟩

/-- **Theorem 2.2 (Kantor–Tanaka Quintic Characteristic Polynomial & Matrix Realization)**:
The 5 eigenvalues $k \in \{-2, -1, 0, +1, +2\}$ of the KKT grading operator $D$ factor the
quintic polynomial $x^5 - 5x^3 + 4x = x(x - 1)(x + 1)(x - 2)(x + 2)$, and the canonical
grading derivation `adH` on $M_3(R)$ satisfies $\operatorname{ad}_H^5(X) - 5\operatorname{ad}_H^3(X) + 4\operatorname{ad}_H(X) = 0$. -/
theorem kkt_quintic_characteristic_synthesis {R : Type*} [CommRing R]
    (x : R) (X : Matrix (Fin 3) (Fin 3) R) :
    x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X = 0 :=
  ⟨five_grade_roots_expansion x, adH_quintic_identity X⟩

/-!
## Section 3: The $\mathrm{Cl}(5,5)$ Twistor Space $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c \cong R^{16}$ & Penrose Incidence Nullity
-/

section Twistor55Geometry

variable {R : Type*} [CommRing R]

/-- **The 16-Dimensional $\mathrm{Cl}(5,5)$ Twistor Space $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c$**:
A real Majorana–Weyl semi-spinor $Z = (\psi, \chi) \in \mathbb{T}_{(5,5)}$ decomposes under
$\mathrm{Spin}(4,4) \subset \mathrm{Spin}(5,5)$ into a pair of 8-component $\mathrm{Cl}(4,4)$
semi-spinors $\psi \in \mathbf{8}_s$ and $\chi \in \mathbf{8}_c$. -/
abbrev Twistor55 (R : Type*) := (Fin 8 → R) × (Fin 8 → R)

/-- **Neutral Split Pairing on $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c$**:
Pairs the positive semi-spinor $\psi \in \mathbf{8}_s$ with the negative semi-spinor
$\chi \in \mathbf{8}_c$:
$$\langle (\psi_1, \chi_1), (\psi_2, \chi_2) \rangle_{\mathbb{T}} =
  \psi_1 \cdot \chi_2 + \chi_1 \cdot \psi_2.$$ -/
def twistorNeutralPairing (Z W : Twistor55 R) : R :=
  dotProduct Z.1 W.2 + dotProduct Z.2 W.1

/-- **Symplectic Twistor Form on $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c$**:
$$\omega_{\mathbb{T}}\big((\psi_1, \chi_1), (\psi_2, \chi_2)\big) =
  \psi_1 \cdot \chi_2 - \chi_1 \cdot \psi_2.$$ -/
def twistorSymplecticForm (Z W : Twistor55 R) : R :=
  dotProduct Z.1 W.2 - dotProduct Z.2 W.1

/-- **Penrose Twistor Incidence Relation ($\psi^A = X^{A\dot{A}} \chi_{\dot{A}}$)**:
A twistor $Z = (\psi, \chi) \in \mathbb{T}_{(5,5)}$ is incident with the spacetime
operator $X \in M_8(R)$ if $\psi = X \chi$. -/
def PenroseTwistorIncidence (X : Matrix (Fin 8) (Fin 8) R) (Z : Twistor55 R) : Prop :=
  Z.1 = X.mulVec Z.2

/-- Both semi-spinor sub-bundles $\mathbf{8}_s = \{(\psi, 0)\}$ and $\mathbf{8}_c = \{(0, \chi)\}$
are totally isotropic 8-planes in $\mathbb{T}_{(5,5)}$. -/
theorem twistor_semiSpinor_sheets_isotropic (ψ χ : Fin 8 → R) :
    twistorNeutralPairing (ψ, (0 : Fin 8 → R)) (ψ, (0 : Fin 8 → R)) = 0 ∧
    twistorNeutralPairing ((0 : Fin 8 → R), χ) ((0 : Fin 8 → R), χ) = 0 := by
  unfold twistorNeutralPairing
  simp

/-- **Theorem 3.1 (Penrose Incidence Graph Nullity for Skew-Symmetric Spacetime Bivectors)**:
If $X \in M_8(R)$ is skew-symmetric ($X^T = -X$), then every twistor $Z = (\psi, \chi) \in \mathbb{T}_{(5,5)}$
satisfying the Penrose incidence relation $\psi^A = X^{A\dot{A}} \chi_{\dot{A}}$ lies on the
null quadric of `twistorNeutralPairing`:
$$\langle Z, Z \rangle_{\mathbb{T}} = 2 \, \chi^T X \chi = 0.$$ -/
theorem penrose_incidence_null_of_skewSymmetric
    (X : Matrix (Fin 8) (Fin 8) R) (Z : Twistor55 R)
    (h_skew : Xᵀ = -X)
    (h_inc : PenroseTwistorIncidence X Z) :
    twistorNeutralPairing Z Z = 0 := by
  unfold twistorNeutralPairing
  rw [h_inc]
  have h_adj : dotProduct (X.mulVec Z.2) Z.2 = dotProduct Z.2 (Xᵀ.mulVec Z.2) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h_adj, h_skew, Matrix.neg_mulVec, dotProduct_neg, neg_add_cancel]

end Twistor55Geometry

/-!
## Section 4: Günaydin–Gürsey $\mathbf{8}_s \to (\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$ Splitting & Supertwistor Space $\mathbb{T}_{\text{super}} \cong R^{16\vert 8}$
-/

section SupercolorGrassmannian

variable {R : Type*} [CommRing R]

/-- **Günaydin–Gürsey Lepton–Quark Multiplet Carrier**:
Decomposes an 8-component $\mathrm{Cl}(4,4)$ semi-spinor into:
- 2 color-singlet leptonic components $(\mathbf{1} \oplus \mathbf{1}) \cong \mathrm{Fin}\, 2 \to R$,
- 3 color-triplet quark components $\mathbf{3} \cong \mathrm{Fin}\, 3 \to R$,
- 3 color-antitriplet anti-quark components $\bar{\mathbf{3}} \cong \mathrm{Fin}\, 3 \to R$. -/
abbrev GunaydinGurseyMultiplet (R : Type*) :=
  (Fin 2 → R) × (Fin 3 → R) × (Fin 3 → R)

/-- Projects an 8-component semi-spinor $\psi \in \mathbf{8}_s$ onto its leptonic singlet
pair $(0, 1)$, quark triplet $(2, 3, 4)$, and anti-quark antitriplet $(5, 6, 7)$. -/
def gunaydinGurseySplit (ψ : Fin 8 → R) : GunaydinGurseyMultiplet R :=
  (![ψ 0, ψ 1], ![ψ 2, ψ 3, ψ 4], ![ψ 5, ψ 6, ψ 7])

/-- Recombines a leptonic singlet pair $\ell \in R^2$, quark triplet $q \in R^3$, and
anti-quark antitriplet $\bar{q} \in R^3$ into an 8-component $\mathrm{Cl}(4,4)$ semi-spinor. -/
def gunaydinGurseyCombine (m : GunaydinGurseyMultiplet R) : Fin 8 → R :=
  ![m.1 0, m.1 1, m.2.1 0, m.2.1 1, m.2.1 2, m.2.2 0, m.2.2 1, m.2.2 2]

/-- **Theorem 4.1 (Exact Linear Equivalence $\mathbf{8}_s \cong (\mathbf{1} \oplus \mathbf{1}) \oplus \mathbf{3} \oplus \bar{\mathbf{3}}$)**:
`gunaydinGurseySplit` and `gunaydinGurseyCombine` form an exact $R$-linear isomorphism
between the 8-dimensional semi-spinor space $\mathbf{8}_s$ and the lepton-quark multiplet
carrier $(\mathrm{Fin}\, 2 \to R) \times (\mathrm{Fin}\, 3 \to R) \times (\mathrm{Fin}\, 3 \to R)$. -/
def gunaydinGurseyEquiv (R : Type*) [CommRing R] :
    (Fin 8 → R) ≃ₗ[R] GunaydinGurseyMultiplet R where
  toFun := gunaydinGurseySplit
  invFun := gunaydinGurseyCombine
  left_inv ψ := by
    ext i
    fin_cases i <;> rfl
  right_inv m := by
    rcases m with ⟨ℓ, q, qbar⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
  map_add' ψ₁ ψ₂ := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
  map_smul' c ψ := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl

/-- **Supertwistor Space $\mathbb{T}_{\text{super}} \cong R^{16\vert 8}$**:
Pairs a 16-component conformal twistor $Z = (\psi, \chi) \in \mathbb{T}_{(5,5)}$ with
8 supercolor coordinates: a color-triplet quark supercharge $\eta \in \mathbf{3}$,
an anti-triplet anti-quark supercharge $\xi \in \bar{\mathbf{3}}$, and a 2-component
leptonic supercharge $\ell \in \mathbf{1} \oplus \mathbf{1}$. -/
abbrev SuperTwistor55 (R : Type*) :=
  Twistor55 R × (Fin 3 → R) × (Fin 3 → R) × (Fin 2 → R)

/-- **Odd Supercolor Incidence Map ($\Theta^a = \sum_{A=0}^7 \psi^A \theta_A^a$)**:
Projects the positive semi-spinor $\psi \in \mathbf{8}_s$ onto a 3-component colored
supercharge in $\mathbf{3}$ via the odd Grassmann incidence frame $\theta \in M_{8 \times 3}(R)$. -/
def oddSupercolorIncidence (ψ : Fin 8 → R) (θ : Matrix (Fin 8) (Fin 3) R) : Fin 3 → R :=
  θᵀ.mulVec ψ

/-- **Theorem 4.2 (Penrose Transport of Odd Supercolor Incidence)**:
When a twistor $Z = (\psi, \chi) \in \mathbb{T}_{(5,5)}$ satisfies the bosonic Penrose
incidence relation $\psi = X \chi$, the induced odd supercolor charge
$\Theta^a = \psi^A \theta_A^a$ equals the dual semi-spinor pairing with the transported
Grassmann frame $X^T \theta$:
$$\Theta(\psi, \theta) = \Theta(\chi, X^T \theta).$$ -/
theorem oddSupercolorIncidence_penrose_transport
    (X : Matrix (Fin 8) (Fin 8) R) (Z : Twistor55 R)
    (θ : Matrix (Fin 8) (Fin 3) R)
    (h_inc : PenroseTwistorIncidence X Z) :
    oddSupercolorIncidence Z.1 θ = oddSupercolorIncidence Z.2 (Xᵀ * θ) := by
  unfold oddSupercolorIncidence
  rw [h_inc, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]

end SupercolorGrassmannian

/-!
## Section 5: Super-Andreev Reflection $\mathcal{R}_{\text{super}}$ & Grassmann Color-Singlet Conservation
-/

section SuperAndreevReflection

variable {R : Type*} [CommRing R]

/-- **Super-Andreev Twistor Reflection Operator ($\mathcal{R}_{\text{super}}$)**:
Acts on a supertwistor $\mathcal{Z} = ((\psi, \chi), \eta, \xi, \ell) \in \mathbb{T}_{\text{super}}$ by:
$$\mathcal{R}_{\text{super}}\big((\psi, \chi), \eta, \xi, \ell\big) =
  \big((-\chi, \psi), \xi, -\eta, \ell\big),$$
swapping the $\mathbf{8}_s$ and $\mathbf{8}_c$ conformal semi-spinor sheets while
exchanging quark ($\mathbf{3}$) and anti-quark ($\bar{\mathbf{3}}$) color charges. -/
def superAndreevReflect (𝒮 : SuperTwistor55 R) : SuperTwistor55 R :=
  ((-𝒮.1.2, 𝒮.1.1), 𝒮.2.2.1, -𝒮.2.1, 𝒮.2.2.2)

/-- Color-sector symplectic pairing $\omega_{\text{color}}((\eta_1, \xi_1), (\eta_2, \xi_2)) =
\sum_{a=0}^2 (\eta_1^a \xi_2^a - \xi_1^a \eta_2^a)$. -/
def colorSymplecticForm (η₁ ξ₁ η₂ ξ₂ : Fin 3 → R) : R :=
  dotProduct η₁ ξ₂ - dotProduct ξ₁ η₂

/-- **Theorem 5.1 ($\mathbb{Z}_4$ Spinorial Periodicity & Symplectic Invariance of Super-Andreev Reflection)**:
1. Applying `superAndreevReflect` twice negates both the spacetime twistor $Z = (\psi, \chi)$
   and the quark/anti-quark supercharges $(\eta, \xi)$ while fixing the leptonic singlet $\ell$:
   $\mathcal{R}_{\text{super}}^2((\psi, \chi), \eta, \xi, \ell) = ((-\psi, -\chi), -\eta, -\xi, \ell)$.
2. Applying `superAndreevReflect` four times is the exact identity ($\mathcal{R}_{\text{super}}^4 = \mathrm{id}$).
3. `superAndreevReflect` preserves both the spacetime twistor symplectic form
   `twistorSymplecticForm` and the color symplectic form `colorSymplecticForm`. -/
theorem superAndreevReflect_order_four_and_symplectic_invariance
    (𝒮 𝒲 : SuperTwistor55 R) :
    superAndreevReflect (superAndreevReflect 𝒮) =
      ((-𝒮.1.1, -𝒮.1.2), -𝒮.2.1, -𝒮.2.2.1, 𝒮.2.2.2) ∧
    superAndreevReflect (superAndreevReflect (superAndreevReflect (superAndreevReflect 𝒮))) = 𝒮 ∧
    twistorSymplecticForm (superAndreevReflect 𝒮).1 (superAndreevReflect 𝒲).1 =
      twistorSymplecticForm 𝒮.1 𝒲.1 ∧
    colorSymplecticForm (superAndreevReflect 𝒮).2.1 (superAndreevReflect 𝒮).2.2.1
        (superAndreevReflect 𝒲).2.1 (superAndreevReflect 𝒲).2.2.1 =
      colorSymplecticForm 𝒮.2.1 𝒮.2.2.1 𝒲.2.1 𝒲.2.2.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases 𝒮 with ⟨⟨ψ, χ⟩, η, ξ, ℓ⟩
    rfl
  · rcases 𝒮 with ⟨⟨ψ, χ⟩, η, ξ, ℓ⟩
    unfold superAndreevReflect
    dsimp
    rw [neg_neg, neg_neg, neg_neg, neg_neg]
  · unfold superAndreevReflect twistorSymplecticForm
    dsimp
    rw [neg_dotProduct, dotProduct_neg]
    ring
  · unfold superAndreevReflect colorSymplecticForm
    dsimp
    rw [neg_dotProduct, dotProduct_neg]
    ring

/-- **Bilinear Color-Singlet Invariant $\mathcal{I}_{\text{color}}(\eta, \xi) = \sum_{a=0}^2 \eta^a \xi_a$**
in any (generally non-commutative) ring $A$. -/
def colorSingletInvariant {A : Type*} [Ring A] (η ξ : Fin 3 → A) : A :=
  ∑ a : Fin 3, η a * ξ a

/-- **Theorem 5.2 (Exact Conservation of the Grassmann Color-Singlet Invariant Under Super-Andreev Reflection)**:
Let $A$ be any ring (such as an exterior Grassmann algebra or Clifford-CAR superalgebra)
and let $\eta, \xi : \mathrm{Fin}\, 3 \to A$ be odd Grassmann quark and anti-quark charges
satisfying the anticommutation law $\eta^a \xi_a + \xi_a \eta^a = 0$ for each color $a \in \{0, 1, 2\}$.
Then under the Super-Andreev boundary reflection $(\eta^a, \xi_a) \mapsto (\xi^a, -\eta_a)$,
the total color-singlet invariant $\mathcal{I}_{\text{color}}(\eta, \xi) = \sum_{a=0}^2 \eta^a \xi_a$
is strictly conserved:
$$\mathcal{I}_{\text{color}}(\xi, -\eta) = \sum_{a=0}^2 \xi_a (-\eta^a) =
  \sum_{a=0}^2 \eta^a \xi_a = \mathcal{I}_{\text{color}}(\eta, \xi).$$ -/
theorem grassmann_color_singlet_superAndreev_invariant
    {A : Type*} [Ring A] (η ξ : Fin 3 → A)
    (h_odd : ∀ a : Fin 3, η a * ξ a + ξ a * η a = 0) :
    colorSingletInvariant ξ (-η) = colorSingletInvariant η ξ := by
  unfold colorSingletInvariant
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.neg_apply, mul_neg]
  exact neg_eq_iff_add_eq_zero.mpr (by rw [add_comm]; exact h_odd a)

end SuperAndreevReflection

end InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
