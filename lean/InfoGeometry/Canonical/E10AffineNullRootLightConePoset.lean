/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.E10LorentzianDecomposition
import InfoGeometry.Lie.D5E10SerreInclusion
import InfoGeometry.Lie.E10SerrePresentation

/-!
# The $E_8 \subset E_9 \subset E_{10}$ Affine Null Root $\delta$, Hyperbolic Light-Cone Plane, & $D_5$ Embedding Poset

This canonical module formalizes the exact root-lattice light-cone geometry governing the
transition from the affine Kac–Moody algebra $E_9 = E_8^{(1)}$ to the hyperbolic Kac–Moody
algebra $E_{10} = E_8^{(1)\wedge}$, uniting `InfoGeometry.Lie.E10HyperbolicSignature`,
`InfoGeometry.Lie.E10LorentzianDecomposition`, `InfoGeometry.Lie.D5E10SerreInclusion`, and
the E₁₀ Serre presentation:

1. **The Canonical $E_9$ Affine Imaginary Null Root $\delta$ (`e9AffineNullRoot`):**
   $\delta = (6, 3, 4, 2, 5, 4, 3, 2, 1, 0) \in \mathbb{Z}^{10}$ has total root height
   $\mathrm{ht}(\delta) = 30$ (the Coxeter number $h(E_8) = 30$), lies on the null light-cone
   $\langle \delta, \delta \rangle_{E_{10}} = 0$, and pairs with the over-extending root
   $\alpha_9 = e_9$ as $\langle \delta, \alpha_9 \rangle_{E_{10}} = -1$.
2. **Exact Hyperbolic Light-Cone Law on $\mathrm{Span}_{\mathbb{Z}}(\delta, \alpha_9)$ (`hyperbolicLightCone_quadratic_law`):**
   For every $k, m \in \mathbb{Z}$, the vector $v(k, m) = k\delta + m\alpha_9$ has exact
   $E_{10}$ Cartan quadratic norm
   $$\langle k\delta + m\alpha_9,\; k\delta + m\alpha_9 \rangle_{E_{10}} = 2m(m - k).$$
   This single polynomial law classifies all causal sectors in the $(\delta, \alpha_9)$
   hyperbolic plane:
   - **First Null Ray ($m = 0$, $E_9$ affine null line):** $\langle k\delta, k\delta \rangle = 0$;
   - **Second Null Ray ($k = m$, over-extended null line):** $\langle m(\delta + \alpha_9), m(\delta + \alpha_9) \rangle = 0$;
   - **Minimal Timelike Imaginary Root ($k = 2, m = 1$):** $\langle 2\delta + \alpha_9, 2\delta + \alpha_9 \rangle = -2$;
   - **Canonical Timelike Witness ($k = 3, m = 1$):** $\langle 3\delta + \alpha_9, 3\delta + \alpha_9 \rangle = -4$ (`timelikeRoot`);
   - **General Timelike Interior ($0 < m < k$):** $\langle k\delta + m\alpha_9, k\delta + m\alpha_9 \rangle < 0$;
   - **Spacelike Exterior ($0 < m$ and $k < m$):** $0 < \langle k\delta + m\alpha_9, k\delta + m\alpha_9 \rangle$.
3. **Completed-Square Balance at the Trivalent Vertex (`e9AffineNullRootReal_completed_square_balance`):**
   In the real completed-square decomposition
   `cartanQuadraticFormReal x = positiveArmPart x - (x 0)^2 / 42`
   (`InfoGeometry.Lie.E10LorentzianDecomposition`), on the $E_9$ null root $\delta$ the positive
   contribution of the three $A$-type arms $(1, 2, 6)$ equals $+6/7$, which cancels the
   trivalent Schur complement $-6^2 / 42 = -6/7$ to yield `cartanQuadraticFormReal δ = 0`.
4. **$D_5 \subset E_{10}$ Core Trace & $E_{10}$ Non-Commutative Matrix Witness:**
   Proves $\mathrm{Tr}(A_{D_5}) = 10 = \frac{1}{2}\mathrm{Tr}(A_{E_{10}})$ and exhibits an
   explicit non-commutativity witness for the $10 \times 10$ $E_{10}$ Cartan matrix.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Root-Lattice, Light-Cone, & Matrix Theorems (`[kernel_verified]`):**
  - `e9_affine_null_root_and_overextended_pairing`: $\mathrm{ht}(\delta) = 30$,
    $\langle \delta, \delta \rangle = 0$, $\langle \alpha_9, \alpha_9 \rangle = 2$,
    $\langle \delta, \alpha_9 \rangle = -1$, and `timelikeRoot = 3 • δ + α₉`.
  - `hyperbolicLightCone_quadratic_law` and `hyperbolicLightCone_causal_sectors`:
    Universal identity $\langle k\delta + m\alpha_9, k\delta + m\alpha_9 \rangle = 2m(m - k)$
    and causal sector classification (null rays, minimal timelike root $-2$, timelike cone $< 0$,
    spacelike cone $> 0$).
  - `e9AffineNullRootReal_completed_square_balance`: Exact arm-vs-vertex balance
    `positiveArmPart δ = 6 / 7` and `(δ 0)^2 / 42 = 6 / 7`.
  - `d5_in_e10_cartan_trace_splitting` and `e10_cartanMatrix_noncommutative`:
    $\mathrm{Tr}(A_{D_5}) = 10$, $\mathrm{Tr}(A_{E_{10}}) = 20$, and non-commutativity of
    `cartanMatrix` with the over-extended root shift matrix.

* **BUCKET 2 — Eliminated Wrappers & Unverified Heuristics (Zero Remaining):**
  - All quadratic-form and bilinear-form identities are proved directly on the $10 \times 10$
    Cartan matrix carrier without `Prop`-wrappers or axioms.

* **BUCKET 3 — Full Weyl Group Orbit Enumeration for $E_{10}$ (`[bucket_3_open_debt]`):**
  - Infinite hyperbolic Weyl group $W(E_{10})$ tessellations and root multiplicities
    $\dim \mathfrak{g}_\alpha$ at higher imaginary levels $k \ge 3$ remain outside this
    root-lattice quadratic-form scope.
-/

namespace InfoGeometry.Canonical.E10AffineNullRootLightConePoset

open scoped BigOperators
open Matrix
open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10Hyperbolic
open InfoGeometry.Lie.E10LorentzianDecomposition
open InfoGeometry.Lie.D5E10Inclusion

-- ============================================================================
-- SECTION 1: The E₉ Affine Null Root δ & Over-Extending Root α₉ in E₁₀
-- ============================================================================

/-- Symmetric bilinear form $\langle u, v \rangle_{E_{10}} = \sum_{i,j} u_i A_{ij} v_j$
associated with the $10 \times 10$ $E_{10}$ generalized Cartan matrix `cartanMatrix`. -/
def e10CartanBilinearForm (u v : Fin 10 → ℤ) : ℤ :=
  ∑ i : Fin 10, ∑ j : Fin 10, u i * cartanMatrix i j * v j

/-- The canonical $E_9 = E_8^{(1)}$ affine imaginary null root
$\delta = (6, 3, 4, 2, 5, 4, 3, 2, 1, 0) \in \mathbb{Z}^{10}$ supported on the first 9 nodes
$\{0, \dots, 8\}$ of the $E_{10}$ Dynkin diagram. -/
def e9AffineNullRoot : Fin 10 → ℤ :=
  ![6, 3, 4, 2, 5, 4, 3, 2, 1, 0]

/-- The 10th (over-extending) simple root $\alpha_9 = (0, 0, 0, 0, 0, 0, 0, 0, 0, 1) \in \mathbb{Z}^{10}$
at the tip of the 6-node arm of $E_{10}$. -/
def e10OverExtendedRoot : Fin 10 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The second independent null root $\delta' = \delta + \alpha_9 = (6, 3, 4, 2, 5, 4, 3, 2, 1, 1)$
spanning the opposite null ray of the hyperbolic plane $\mathrm{Span}_{\mathbb{Z}}(\delta, \alpha_9)$. -/
def e10SecondNullRoot : Fin 10 → ℤ :=
  ![6, 3, 4, 2, 5, 4, 3, 2, 1, 1]

/-- The minimal fundamental timelike imaginary root
$v_{\min} = 2\delta + \alpha_9 = (12, 6, 8, 4, 10, 8, 6, 4, 2, 1) \in \mathbb{Z}^{10}$
having negative norm squared $\langle v_{\min}, v_{\min} \rangle = -2$. -/
def e10MinimalTimelikeRoot : Fin 10 → ℤ :=
  ![12, 6, 8, 4, 10, 8, 6, 4, 2, 1]

/-- **The $E_9$ Affine Null Root & Over-Extended Pairing Theorem (`e9_affine_null_root_and_overextended_pairing`):**
1. **Coxeter Root Height:** $\sum_{i=0}^9 \delta_i = 30 = h(E_8)$;
2. **First Null Ray:** $\langle \delta, \delta \rangle_{E_{10}} = 0$;
3. **Second Null Ray:** $\langle \delta + \alpha_9, \delta + \alpha_9 \rangle_{E_{10}} = 0$;
4. **Over-Extended Simple Root Norm:** $\langle \alpha_9, \alpha_9 \rangle_{E_{10}} = 2$;
5. **Hyperbolic Null-Simple Pairing:** $\langle \delta, \alpha_9 \rangle_{E_{10}} = -1$ and
   $\langle \alpha_9, \delta \rangle_{E_{10}} = -1$;
6. **Minimal Timelike Root Norm:** $\langle 2\delta + \alpha_9, 2\delta + \alpha_9 \rangle_{E_{10}} = -2$;
7. **Decomposition of `timelikeRoot`:** `timelikeRoot = (3 : ℤ) • e9AffineNullRoot + e10OverExtendedRoot`. -/
theorem e9_affine_null_root_and_overextended_pairing :
    (∑ i : Fin 10, e9AffineNullRoot i) = 30 ∧
    cartanQuadraticForm e9AffineNullRoot = 0 ∧
    cartanQuadraticForm e10SecondNullRoot = 0 ∧
    cartanQuadraticForm e10OverExtendedRoot = 2 ∧
    e10CartanBilinearForm e9AffineNullRoot e10OverExtendedRoot = -1 ∧
    e10CartanBilinearForm e10OverExtendedRoot e9AffineNullRoot = -1 ∧
    cartanQuadraticForm e10MinimalTimelikeRoot = -2 ∧
    timelikeRoot = (3 : ℤ) • e9AffineNullRoot + e10OverExtendedRoot := by
  have hDecomp : timelikeRoot = (3 : ℤ) • e9AffineNullRoot + e10OverExtendedRoot := by
    ext i
    fin_cases i <;> rfl
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, hDecomp⟩

-- ============================================================================
-- SECTION 2: Universal Hyperbolic Light-Cone Law on Span_ℤ(δ, α₉)
-- ============================================================================

/-- Two-parameter root-lattice vector $v(k, m) = k\delta + m\alpha_9 \in \mathbb{Z}^{10}$ in the
hyperbolic plane spanned by the $E_9$ affine null root $\delta$ and the over-extending root $\alpha_9$. -/
def hyperbolicLightConeVector (k m : ℤ) : Fin 10 → ℤ :=
  fun i => k * e9AffineNullRoot i + m * e10OverExtendedRoot i

/-- **Universal Hyperbolic Light-Cone Quadratic Theorem (`hyperbolicLightCone_quadratic_law`):**
For all integers $k, m \in \mathbb{Z}$, the $E_{10}$ Cartan quadratic form on
$v(k, m) = k\delta + m\alpha_9$ evaluates to the exact factored hyperbolic polynomial:
$$\mathrm{cartanQuadraticForm}\bigl(\mathrm{hyperbolicLightConeVector}\;k\;m\bigr) = 2 m (m - k).$$ -/
theorem hyperbolicLightCone_quadratic_law (k m : ℤ) :
    cartanQuadraticForm (hyperbolicLightConeVector k m) = 2 * m * (m - k) := by
  unfold cartanQuadraticForm hyperbolicLightConeVector e9AffineNullRoot e10OverExtendedRoot
  simp [cartanMatrix, Adjacent, edges, Fin.sum_univ_succ]
  ring

/-- **Causal Sector Classification in the $(\delta, \alpha_9)$ Hyperbolic Plane (`hyperbolicLightCone_causal_sectors`):**
For all $k, m \in \mathbb{Z}$:
1. **First Null Ray ($m = 0$):** $\mathrm{cartanQuadraticForm}(k\delta) = 0$;
2. **Second Null Ray ($k = m$):** $\mathrm{cartanQuadraticForm}(m\delta + m\alpha_9) = 0$;
3. **Timelike Interior ($0 < m$ and $m < k$):**
   $\mathrm{cartanQuadraticForm}(k\delta + m\alpha_9) < 0$ (imaginary roots inside the light cone);
4. **Spacelike Exterior ($0 < m$ and $k < m$):**
   $0 < \mathrm{cartanQuadraticForm}(k\delta + m\alpha_9)$ (real/spacelike vectors outside the light cone). -/
theorem hyperbolicLightCone_causal_sectors (k m : ℤ) :
    cartanQuadraticForm (hyperbolicLightConeVector k 0) = 0 ∧
    cartanQuadraticForm (hyperbolicLightConeVector m m) = 0 ∧
    (0 < m → m < k → cartanQuadraticForm (hyperbolicLightConeVector k m) < 0) ∧
    (0 < m → k < m → 0 < cartanQuadraticForm (hyperbolicLightConeVector k m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hyperbolicLightCone_quadratic_law]
    ring
  · rw [hyperbolicLightCone_quadratic_law]
    ring
  · intro hm hmk
    rw [hyperbolicLightCone_quadratic_law]
    have h2m : 0 < 2 * m := by linarith
    have hsub : m - k < 0 := by linarith
    exact mul_neg_of_pos_of_neg h2m hsub
  · intro hm hkm
    rw [hyperbolicLightCone_quadratic_law]
    have h2m : 0 < 2 * m := by linarith
    have hsub : 0 < m - k := by linarith
    exact mul_pos h2m hsub

-- ============================================================================
-- SECTION 3: Completed-Square Balance of the E₉ Null Root at the Trivalent Vertex
-- ============================================================================

/-- Real embedding of the $E_9$ affine imaginary null root $\delta \in \mathbb{R}^{10}$. -/
def e9AffineNullRootReal : Fin 10 → ℝ :=
  fun i => (e9AffineNullRoot i : ℝ)

/-- **Completed-Square Arm vs. Trivalent Schur Complement Balance (`e9AffineNullRootReal_completed_square_balance`):**
In the completed-square identity
`cartanQuadraticFormReal x = positiveArmPart x - (x 0)^2 / 42`
(`InfoGeometry.Lie.E10LorentzianDecomposition`):
1. On $\delta$, the three $A$-type arms $(1, 2, 6)$ contribute `positiveArmPart e9AffineNullRootReal = 6 / 7`;
2. The trivalent central vertex $x_0 = 6$ contributes `(e9AffineNullRootReal 0)^2 / 42 = 36 / 42 = 6 / 7`;
3. The two contributions cancel identically: `cartanQuadraticFormReal e9AffineNullRootReal = 0`. -/
theorem e9AffineNullRootReal_completed_square_balance :
    positiveArmPart e9AffineNullRootReal = 6 / 7 ∧
    (e9AffineNullRootReal 0) ^ 2 / 42 = 6 / 7 ∧
    cartanQuadraticFormReal e9AffineNullRootReal = 0 := by
  have hArm : positiveArmPart e9AffineNullRootReal = 6 / 7 := by
    unfold positiveArmPart a1 a2 a3 a4 a5 a6 a7 a8 a9 e9AffineNullRootReal e9AffineNullRoot
    norm_num
  have hCenter : (e9AffineNullRootReal 0) ^ 2 / 42 = 6 / 7 := by
    unfold e9AffineNullRootReal e9AffineNullRoot
    norm_num
  refine ⟨hArm, hCenter, ?_⟩
  rw [cartan_form_eq_arm_squares_sub_central, hArm, hCenter, sub_self]

-- ============================================================================
-- SECTION 4: D₅ ⊂ E₁₀ Cartan Trace Splitting & Non-Commutative 10×10 Witness
-- ============================================================================

/-- Elementary $10 \times 10$ root-transition matrix $E_{8,9}$ coupling the affine node $8$
to the over-extending node $9$ in `Matrix (Fin 10) (Fin 10) ℤ`. -/
def e10AffineToOverExtendedShift : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of (fun i j : Fin 10 => if i.val = 8 ∧ j.val = 9 then 1 else 0)

/-- **$D_5 \subset E_{10}$ Cartan Trace Splitting (`d5_in_e10_cartan_trace_splitting`):**
The trace of the 5-node $D_5$ Cartan core `d5CartanMatrix` equals $10$ (matching the 10-dimensional
$(5,5)$ horizon bulk), which is exactly half of the 10-node $E_{10}$ Cartan trace
$\mathrm{Tr}(A_{E_{10}}) = 20$. -/
theorem d5_in_e10_cartan_trace_splitting :
    Matrix.trace d5CartanMatrix = 10 ∧
    Matrix.trace cartanMatrix = 20 ∧
    2 * Matrix.trace d5CartanMatrix = Matrix.trace cartanMatrix := by
  have hD5 : Matrix.trace d5CartanMatrix = 10 := by decide
  have hE10 : Matrix.trace cartanMatrix = 20 := cartanMatrix_trace
  refine ⟨hD5, hE10, by norm_num [hD5, hE10]⟩

/-- Explicit non-commutativity witness for the $10 \times 10$ $E_{10}$ Cartan matrix carrier
`Matrix (Fin 10) (Fin 10) ℤ`: `cartanMatrix` does not commute with the affine-to-overextended
shift $E_{8,9}$. -/
theorem e10_cartanMatrix_noncommutative :
    cartanMatrix * e10AffineToOverExtendedShift ≠
      e10AffineToOverExtendedShift * cartanMatrix := by
  intro hEq
  have h79 := congr_fun (congr_fun hEq ⟨7, by decide⟩) ⟨9, by decide⟩
  revert h79
  decide

end InfoGeometry.Canonical.E10AffineNullRootLightConePoset
