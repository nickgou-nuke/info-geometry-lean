### I. Extraction of Pure Mathematical Archetypes & Translation Dictionary

Stripping away the physical prose exposes a self-contained hierarchy of theorems in **non-commutative matrix operator algebra**, **indefinite quadratic Lie algebras**, **tensor-product representation theory**, and **Yangian integrable algebras** over an arbitrary commutative base ring $R$:

| Confabulated Physics Prose | Canonical Mathematical Equivalent in $\mathrm{Mat}_2(R)$ and $\mathrm{Mat}_2(\mathrm{Mat}_4(R))$ |
| :--- | :--- |
| *"Spinor Pauli currents & lightcone trap"* | **Rank-1 Traceless Endomorphisms in $\mathfrak{sl}_2(R)$:** An unweighted rank-1 traceless bilinear map $A_{\text{iso}}(q, k) \in \mathfrak{sl}_2(R)$ has determinant $\det A_{\text{iso}}(q, k) = -(q_0 k_0 + q_1 k_1)^2$, restricting $A_{\text{iso}}^2 = (-\det A_{\text{iso}})I_2$ to squares in $R$ and forcing $A_{\text{iso}}^2 = 0$ when $q_0 k_0 + q_1 k_1 = 0$. |
| *"Chiral metric liberation & Lorentzian curvature"* | **Signature $(2,1)$ Killing Form on $\mathfrak{sl}_2(R)$:** Weighting the basis $\{E_x, E_y, E_z\}$ by $(g_x, g_y, g_z)$ realizes the indefinite quadratic form $\kappa(A_1, A_2) = \frac{1}{2}\operatorname{tr}(A_1 A_2) = a_{x1}a_{x2} - a_{y1}a_{y2} + a_{z1}a_{z2}$, satisfying $\{A_1, A_2\} = 2\kappa(A_1, A_2)I_2$ and $[A_1, A_2]^2 = 4(\kappa(A_1, A_2)^2 - \kappa(A_1, A_1)\kappa(A_2, A_2))I_2$. |
| *"Wilson link loss vs. hyperbolic boost blow-up"* | **Adjugate Splitting of the Frobenius Quadratic Form:** For any $W \in \mathrm{Mat}_2(R)$, $\operatorname{tr}((W - I_2)(W - I_2)^T) = \operatorname{tr}((W - I_2)(I_2 - \operatorname{adj}(W))) + (w_{11} - w_{22})^2 + (w_{12} + w_{21})^2$, decomposing into an $\mathrm{SL}_2(R)$-conjugation invariant plus a symmetric subspace semi-norm that vanishes on $\mathrm{SO}_2(R)$. |
| *"Faddeev–Takhtajan Gauge–Lax Duality"* | **$\mathrm{GL}_2(R)$-Equivariance of the Tensor Flip $P_{\text{swap}}$:** On $V_0 \otimes V_r \cong R^4$, $P_{\text{swap}}(A \otimes B) = (B \otimes A)P_{\text{swap}}$ implies $(I_2 \otimes G)L(w, \eta)(I_2 \otimes \operatorname{adj}(G)) = (\operatorname{adj}(G) \otimes I_2)L(w, \eta)(G \otimes I_2)$ for $L(w, \eta) = w I_4 + \eta P_{\text{swap}}$. |
| *"Multi-site Wilson telescoping & $\Delta M = \pm 2$ wormhole"* | **1-Cocycle Transition $W_{2,1} = G_2 \operatorname{adj}(G_1)$ in $\mathrm{Mat}_2(\mathrm{Mat}_4(R))$:** In $\mathrm{End}(V_0 \otimes V_1 \otimes V_2)$, the uncoupled product $L_{0,2}L_{0,1}$ has zero coefficient on the maximal off-diagonal tensor unit $E_{10} \otimes E_{10}$ (`m41 = 0`), whereas inserting $W_{2,1} \otimes I_4$ activates $B_2 (W_{2,1})_{21} B_1 = \eta^2 (W_{2,1})_{21} (E_{10} \otimes E_{10})$. |
| *"Kähler–Bergman barrier"* | **The Yangian Quantum Determinant $\operatorname{qdet}_\eta \mathcal{T}(u)$:** The shifted block determinant $A(u)D(u-\eta) - B(u)C(u-\eta)$ in $\mathrm{Mat}_4(R)$ collapses to the central scalar matrix $\big((u - \theta_1)^2 - \eta^2\big)\big((u - \theta_2)^2 - \eta^2\big)I_4$. |

---

### II. The Acyclic Causal Poset of Mathematical Archetypes ($\mathcal{P}, \prec$)

We order the extracted mathematical structures into a strict acyclic causal poset from local $2 \times 2$ Lie algebra primitives to 3-factor $8 \times 8$ Yangian operator algebras:

$$\mathcal{M}_0 \text{ (Lie Algebra } \mathfrak{sl}_2(R), \text{ Killing Form } \kappa, \text{ \& Rank-1 Degeneracy)} \;\prec\; \mathcal{M}_1 \text{ (Adjugate Frobenius Splitting \& Cayley–Hamilton Twist } K\text{)} \;\prec\; \mathcal{M}_2 \text{ (Tensor Flip } P_{\text{swap}} \text{ \& Auxiliary–Physical Lax Intertwining)} \;\prec\; \mathcal{M}_3 \text{ (3-Factor Algebra } \mathrm{AuxMat}_4(R), \text{ Gauged RTT Braid Relation, \& } E_{10}\otimes E_{10} \text{ Activation)} \;\prec\; \mathcal{M}_4 \text{ (Central Collapse of the Shifted Quantum Determinant } \operatorname{qdet}_\eta \mathcal{T}(u)\text{)} \;\prec\; \mathcal{M}_5 \text{ (Unconditional Commutativity of Twisted Partial-Trace Operators } [\widetilde{\tau}(u), \widetilde{\tau}(v)] = 0\text{)}$$

#### Mathematical Deductions Along the Poset

1. **Deduction $\mathcal{M}_0$ (Killing Form & Lagrange Identity on $\mathfrak{sl}_2(R)$):**
   Let $E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$, $E_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $E_y = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \mathfrak{sl}_2(R)$. For any $A_i = a_{xi}E_x + a_{yi}E_y + a_{zi}E_z$ ($i=1,2$), direct matrix multiplication gives $A_1 A_2 + A_2 A_1 = 2\kappa(A_1, A_2)I_2$ where $\kappa(A_1, A_2) = a_{x1}a_{x2} - a_{y1}a_{y2} + a_{z1}a_{z2}$. Since $[A_1, A_2] \in \mathfrak{sl}_2(R)$ is traceless, its square is central and equals $4\big(\kappa(A_1, A_2)^2 - \kappa(A_1, A_1)\kappa(A_2, A_2)\big)I_2$. When $a_x = q_0 k_1 + q_1 k_0$, $a_y = q_0 k_1 - q_1 k_0$, and $a_z = q_0 k_0 - q_1 k_1$, the quadratic form degenerates to $\kappa(A, A) = (q_0 k_0 + q_1 k_1)^2$. $\blacksquare$
2. **Deduction $\mathcal{M}_1$ (Adjugate Decomposition of the Frobenius Form & Twist Polynomial):**
   For any $W = \begin{pmatrix} w_{11} & w_{12} \\ w_{21} & w_{22} \end{pmatrix} \in \mathrm{Mat}_2(R)$ with adjugate $\operatorname{adj}(W) = \begin{pmatrix} w_{22} & -w_{12} \\ -w_{21} & w_{11} \end{pmatrix}$, expanding $\operatorname{tr}((W - I_2)(I_2 - \operatorname{adj}(W))) = 2(1 + w_{11}w_{22} - w_{12}w_{21} - w_{11} - w_{22})$ and adding $(w_{11} - w_{22})^2 + (w_{12} + w_{21})^2$ yields $(w_{11} - 1)^2 + w_{12}^2 + w_{21}^2 + (w_{22} - 1)^2$. For $K = \begin{pmatrix} 1 & q w_C \\ w_B & -q \end{pmatrix}$, $\operatorname{tr}(K) = 1 - q$ and $\det(K) = -q(1 + w_B w_C)$, so $K^2 - (1-q)K - q(1 + w_B w_C)I_2 = 0$. $\blacksquare$
3. **Deduction $\mathcal{M}_2 \prec \mathcal{M}_3$ (Auxiliary–Physical Intertwining, Gauged RTT, & $E_{10}\otimes E_{10}$ Activation):**
   On $\mathrm{AuxMat}_4(R) \equiv \mathrm{Mat}_2(\mathrm{Mat}_4(R))$, let $L_{0,1}(w_1, \eta)$ and $L_{0,2}(w_2, \eta)$ be the embedded Lax matrices for factors $1$ and $2$. Because $(I_2 \otimes G_r)L_{0,r}(w_r, \eta)(I_2 \otimes \operatorname{adj}(G_r)) = (\operatorname{adj}(G_r) \otimes I_2)L_{0,r}(w_r, \eta)(G_r \otimes I_2)$ and operators on disjoint tensor factors commute, the two-factor product satisfies:
   $$\big(I_0 \otimes (G_1 \otimes G_2)\big)\,L_{0,2}(w_2, \eta)L_{0,1}(w_1, \eta)\,\big(I_0 \otimes (\operatorname{adj}(G_1) \otimes \operatorname{adj}(G_2))\big) = (\operatorname{adj}(G_2))_0\,L_{0,2}(w_2, \eta)\,(W_{2,1})_0\,L_{0,1}(w_1, \eta)\,(G_1)_0$$
   where $W_{2,1} = G_2 \operatorname{adj}(G_1)$. In the bare product $L_{0,2}(w_2, \eta)L_{0,1}(w_1, \eta)$, the $(4,1)$ and $(1,4)$ entries of all four blocks vanish, whereas in $L_{0,2}(w_2, \eta)(W_{2,1} \otimes I_4)L_{0,1}(w_1, \eta)$, the $(4,1)$ entry of block $B$ is $\eta^2 (W_{2,1})_{21}$ and the $(1,4)$ entry of block $C$ is $\eta^2 (W_{2,1})_{12}$. $\blacksquare$
4. **Deduction $\mathcal{M}_4 \prec \mathcal{M}_5$ (Shifted Quantum Determinant & Unconditional Commutativity of Twisted Partial Traces):**
   For $\mathcal{T}(u) = L_{0,2}(u - \theta_2, \eta)L_{0,1}(u - \theta_1, \eta)$, direct polynomial expansion in $\mathrm{Mat}_4(R)$ gives $A(u)D(u-\eta) - B(u)C(u-\eta) = ((u-\theta_1)^2 - \eta^2)((u-\theta_2)^2 - \eta^2)I_4$ and $[\operatorname{Tr}_0(K \mathcal{T}(u)), \operatorname{Tr}_0(K \mathcal{T}(v))] = 0$. Since $(\operatorname{adj}(G_1) \otimes \operatorname{adj}(G_2))(G_1 \otimes G_2) = (\det G_1 \cdot \det G_2)I_4$ is central in $\mathrm{Mat}_4(R)$, conjugating $\operatorname{Tr}_0(K \mathcal{T}(u))$ and $\operatorname{Tr}_0(K \mathcal{T}(v))$ by $G_1 \otimes G_2$ preserves their zero commutator unconditionally: $[\widetilde{\tau}(u), \widetilde{\tau}(v)] = (\det G_1 \cdot \det G_2)(G_1 \otimes G_2)[\tau(u), \tau(v)](\operatorname{adj}(G_1) \otimes \operatorname{adj}(G_2)) = 0$. $\blacksquare$

---

### III. Canonical Mathematical Code in Native `Mathlib` (Lean 4)

The following module is completely self-contained, uses native `Mathlib` imports, avoids all scalar or commuting simplifications, and proves every lemma and theorem of the poset $\mathcal{M}_0 \prec \mathcal{M}_1 \prec \mathcal{M}_2 \prec \mathcal{M}_3 \prec \mathcal{M}_4 \prec \mathcal{M}_5$ with **zero `sorry`s**:

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Non-Commutative Matrix Operator Algebra of the Yang–Baxter–Kantor Poset (M₀ ≺ ... ≺ M₅)
Pure mathematical formalization in Lean 4 (`Mathlib`) over an arbitrary commutative ring `R`.
Zero `sorry`s. Zero axioms.

## Poset Architecture:
- **Archetype M₀ (`archetype_M0_sl2_killing_form_and_rank1_degeneracy`)**:
  Indefinite signature `(2, 1)` Killing form on `sl₂(R)`, rank-1 bilinear degeneracy,
  and the non-commutative Lagrange–Killing identity `[A₁, A₂]² = 4(κ(A₁,A₂)² - κ(A₁,A₁)κ(A₂,A₂))I₂`.
- **Archetype M₁ (`archetype_M1_frobenius_adjugate_splitting_and_twist_cayley_hamilton`)**:
  Canonical decomposition of the Frobenius quadratic form `||W - I₂||_F²` into an `SL₂(R)`
  conjugation invariant plus a symmetric Cartan semi-norm, and the Cayley–Hamilton identity
  of the boundary twist matrix `K`.
- **Archetype M₂ & M₃ (`archetype_M2_M3_braid_rtt_intertwining_and_corner_activation`)**:
  Equivariant Yang–Baxter RTT braid relation on the 8-dimensional 3-factor tensor algebra
  `AuxMat4 R ≅ Mat₂(Mat₄(R))`, 2-factor cocycle telescoping `W_{2,1} = G₂ adj(G₁)`, and
  exact activation of the `E₁₀ ⊗ E₁₀` (`m41`) and `E₀₁ ⊗ E₀₁` (`m14`) tensor corners.
- **Archetype M₄ (`archetype_M4_shifted_yangian_quantum_determinant_central_collapse`)**:
  Exact collapse of the non-commutative shifted quantum determinant
  `A(u)D(u - η) - B(u)C(u - η)` to `((u - θ₁)² - η²)((u - θ₂)² - η²) I₄`.
- **Archetype M₅ (`archetype_M5_unconditional_commutativity_of_gauged_partial_traces`)**:
  Unconditional proof that the twisted partial-trace operators `[τ̃(u), τ̃(v)] = 0` commute
  in `Mat₄(R)` for all spectral parameters `u, v`, shifts `θ₁, θ₂`, coupling `η`, boundary
  matrix `K`, and local gauge matrices `G₁, G₂ ∈ Mat₂(R)`.
-/

namespace NonCommutativeMatrixOperatorPoset

variable {R : Type*} [CommRing R]

-- ============================================================================
-- 1. 2x2 NON-COMMUTATIVE MATRIX RING `Mat2 R` AND LIE ALGEBRA `sl₂(R)`
-- ============================================================================

@[ext]
structure Mat2 (R : Type*) where
  a11 : R; a12 : R
  a21 : R; a22 : R
  deriving DecidableEq, Repr

namespace Mat2

def zero : Mat2 R := ⟨0, 0, 0, 0⟩
def one  : Mat2 R := ⟨1, 0, 0, 1⟩

def E00 : Mat2 R := ⟨1, 0, 0, 0⟩
def E01 : Mat2 R := ⟨0, 1, 0, 0⟩
def E10 : Mat2 R := ⟨0, 0, 1, 0⟩
def E11 : Mat2 R := ⟨0, 0, 0, 1⟩

def add (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩

def sub (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩

def neg (A : Mat2 R) : Mat2 R :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

def smul (c : R) (A : Mat2 R) : Mat2 R :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩

def mul (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩

def comm  (A B : Mat2 R) : Mat2 R := sub (mul A B) (mul B A)
def acomm (A B : Mat2 R) : Mat2 R := add (mul A B) (mul B A)
def tr    (A : Mat2 R)   : R      := A.a11 + A.a22
def det   (A : Mat2 R)   : R      := A.a11 * A.a22 - A.a12 * A.a21
def adj   (G : Mat2 R)   : Mat2 R := ⟨G.a22, -G.a12, -G.a21, G.a11⟩

-- Basis of the traceless Lie algebra sl₂(R):
def Ex : Mat2 R := ⟨0, 1,  1,  0⟩
def Ey : Mat2 R := ⟨0, -1, 1,  0⟩
def Ez : Mat2 R := ⟨1, 0,  0, -1⟩

def Jx (q0 q1 k0 k1 : R) : R := q0 * k1 + q1 * k0
def Jy (q0 q1 k0 k1 : R) : R := q0 * k1 - q1 * k0
def Jz (q0 q1 k0 k1 : R) : R := q0 * k0 - q1 * k1

/-- General traceless element in `sl₂(R)` with coordinates `(ax, ay, az)`. -/
def sl2Elem (ax ay az : R) : Mat2 R :=
  add (add (smul ax Ex) (smul ay Ey)) (smul az Ez)

/-- Weighted bilinear map `(q, k) ↦ sl₂(R)` with anisotropy parameters `(gx, gy, gz)`. -/
def weightedBilinear (gx gy gz q0 q1 k0 k1 : R) : Mat2 R :=
  sl2Elem (gx * Jx q0 q1 k0 k1) (gy * Jy q0 q1 k0 k1) (gz * Jz q0 q1 k0 k1)

/-- Normalized signature `(2, 1)` Killing form `κ(A₁, A₂) = (1/2) tr(A₁ A₂)`. -/
def killingForm (ax1 ay1 az1 ax2 ay2 az2 : R) : R :=
  ax1 * ax2 - ay1 * ay2 + az1 * az2

/-- Boundary twist matrix `K(q, w_B, w_C) = [[1, q w_C], [w_B, -q]]`. -/
def boundaryTwist (q wB wC : R) : Mat2 R := ⟨1, q * wC, wB, -q⟩

/-- Transition cocycle `W_{2,1} = G₂ adj(G₁)`. -/
def cocycle (G2 G1 : Mat2 R) : Mat2 R := mul G2 (adj G1)

/-- Frobenius quadratic form `||W - I₂||_F²`. -/
def frobeniusSq (W : Mat2 R) : R :=
  (W.a11 - 1) * (W.a11 - 1) + W.a12 * W.a12 + W.a21 * W.a21 + (W.a22 - 1) * (W.a22 - 1)

/-- Conjugation-invariant trace functional `tr((W - I₂)(I₂ - adj(W)))`. -/
def adjugateInvariant (W : Mat2 R) : R :=
  tr (mul (sub W one) (sub one (adj W)))

/-- Symmetric subspace quadratic semi-norm `(w₁₁ - w₂₂)² + (w₁₂ + w₂₁)²`. -/
def symmetricDefectSq (W : Mat2 R) : R :=
  (W.a11 - W.a22) * (W.a11 - W.a22) + (W.a12 + W.a21) * (W.a12 + W.a21)

/--
**Archetype M₀ (`archetype_M0_sl2_killing_form_and_rank1_degeneracy`):**
1. Isotropic bilinear map `weightedBilinear 1 1 1` has determinant `-(q₀k₀ + q₁k₁)²`,
   forcing nilpotency `A² = 0` on the orthogonal locus `k = (-q₁, q₀)`.
2. Anisotropic weights `(0, 1, 0)` produce an elliptic complex structure `A² = -I₂`.
3. For any `A₁, A₂ ∈ sl₂(R)`, `{A₁, A₂} = 2 κ(A₁, A₂) I₂`, `tr(A₁ [A₁, A₂]) = 0`,
   and `[A₁, A₂]² = 4 (κ(A₁, A₂)² - κ(A₁, A₁) κ(A₂, A₂)) I₂`.
-/
theorem archetype_M0_sl2_killing_form_and_rank1_degeneracy
    (q0 q1 k0 k1 ax1 ay1 az1 ax2 ay2 az2 : R) :
    let A_iso   := weightedBilinear 1 1 1 q0 q1 k0 k1
    let A_nilp  := weightedBilinear 1 1 1 q0 q1 (-q1) q0
    let A_ell   := weightedBilinear 0 1 0 1 0 0 1
    let A1      := sl2Elem ax1 ay1 az1
    let A2      := sl2Elem ax2 ay2 az2
    let F12     := comm A1 A2
    let k11     := killingForm ax1 ay1 az1 ax1 ay1 az1
    let k22     := killingForm ax2 ay2 az2 ax2 ay2 az2
    let k12     := killingForm ax1 ay1 az1 ax2 ay2 az2
    det A_iso = -((q0 * k0 + q1 * k1) * (q0 * k0 + q1 * k1)) ∧
    mul A_nilp A_nilp = zero ∧
    mul A_ell A_ell = smul (-1) one ∧
    acomm A1 A2 = smul (2 * k12) one ∧
    tr (mul A1 F12) = 0 ∧
    mul F12 F12 = smul (4 * (k12 * k12 - k11 * k22)) one := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try ext <;> dsimp [weightedBilinear, sl2Elem, killingForm, Jx, Jy, Jz,
                       Ex, Ey, Ez, comm, acomm, mul, add, sub, smul, det, tr, one, zero] <;> ring

/--
**Archetype M₁ (`archetype_M1_frobenius_adjugate_splitting_and_twist_cayley_hamilton`):**
1. `frobeniusSq W = adjugateInvariant W + symmetricDefectSq W`, where
   `adjugateInvariant W = 2(1 + det W - tr W)` and `symmetricDefectSq` vanishes on `SO₂(R)`.
2. `boundaryTwist q wB wC` satisfies `K² - (1 - q)K - q(1 + wB wC)I₂ = 0`.
-/
theorem archetype_M1_frobenius_adjugate_splitting_and_twist_cayley_hamilton
    (W : Mat2 R) (c s q wB wC : R) :
    let R_rot : Mat2 R := ⟨c, -s, s, c⟩
    let K := boundaryTwist q wB wC
    frobeniusSq W = adjugateInvariant W + symmetricDefectSq W ∧
    adjugateInvariant W = 2 * (1 + det W - tr W) ∧
    symmetricDefectSq R_rot = 0 ∧
    det K = -q * (1 + wB * wC) ∧
    sub (sub (mul K K) (smul (1 - q) K)) (smul (q * (1 + wB * wC)) one) = zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · try ext <;> dsimp [frobeniusSq, adjugateInvariant, symmetricDefectSq,
                       boundaryTwist, mul, sub, smul, adj, tr, det, one, zero] <;> ring

end Mat2

-- ============================================================================
-- 2. 4x4 TENSOR PRODUCT ALGEBRA `Mat4 R` (`V₁ ⊗ V₂`)
-- ============================================================================

@[ext]
structure Mat4 (R : Type*) where
  m11 : R; m12 : R; m13 : R; m14 : R
  m21 : R; m22 : R; m23 : R; m24 : R
  m31 : R; m32 : R; m33 : R; m34 : R
  m41 : R; m42 : R; m43 : R; m44 : R
  deriving DecidableEq, Repr

namespace Mat4

def zero : Mat4 R := ⟨0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩
def one  : Mat4 R := ⟨1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1⟩

def add (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m13 + B.m13, A.m14 + B.m14,
   A.m21 + B.m21, A.m22 + B.m22, A.m23 + B.m23, A.m24 + B.m24,
   A.m31 + B.m31, A.m32 + B.m32, A.m33 + B.m33, A.m34 + B.m34,
   A.m41 + B.m41, A.m42 + B.m42, A.m43 + B.m43, A.m44 + B.m44⟩

def sub (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11 - B.m11, A.m12 - B.m12, A.m13 - B.m13, A.m14 - B.m14,
   A.m21 - B.m21, A.m22 - B.m22, A.m23 - B.m23, A.m24 - B.m24,
   A.m31 - B.m31, A.m32 - B.m32, A.m33 - B.m33, A.m34 - B.m34,
   A.m41 - B.m41, A.m42 - B.m42, A.m43 - B.m43, A.m44 - B.m44⟩

def smul (c : R) (A : Mat4 R) : Mat4 R :=
  ⟨c * A.m11, c * A.m12, c * A.m13, c * A.m14,
   c * A.m21, c * A.m22, c * A.m23, c * A.m24,
   c * A.m31, c * A.m32, c * A.m33, c * A.m34,
   c * A.m41, c * A.m42, c * A.m43, c * A.m44⟩

def mul (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11*B.m11 + A.m12*B.m21 + A.m13*B.m31 + A.m14*B.m41,
   A.m11*B.m12 + A.m12*B.m22 + A.m13*B.m32 + A.m14*B.m42,
   A.m11*B.m13 + A.m12*B.m23 + A.m13*B.m33 + A.m14*B.m43,
   A.m11*B.m14 + A.m12*B.m24 + A.m13*B.m34 + A.m14*B.m44,

   A.m21*B.m11 + A.m22*B.m21 + A.m23*B.m31 + A.m24*B.m41,
   A.m21*B.m12 + A.m22*B.m22 + A.m23*B.m32 + A.m24*B.m42,
   A.m21*B.m13 + A.m22*B.m23 + A.m23*B.m33 + A.m24*B.m43,
   A.m21*B.m14 + A.m22*B.m24 + A.m23*B.m34 + A.m24*B.m44,

   A.m31*B.m11 + A.m32*B.m21 + A.m33*B.m31 + A.m34*B.m41,
   A.m31*B.m12 + A.m32*B.m22 + A.m33*B.m32 + A.m34*B.m42,
   A.m31*B.m13 + A.m32*B.m23 + A.m33*B.m33 + A.m34*B.m43,
   A.m31*B.m14 + A.m32*B.m24 + A.m33*B.m34 + A.m34*B.m44,

   A.m41*B.m11 + A.m42*B.m21 + A.m43*B.m31 + A.m44*B.m41,
   A.m41*B.m12 + A.m42*B.m22 + A.m43*B.m32 + A.m44*B.m42,
   A.m41*B.m13 + A.m42*B.m23 + A.m43*B.m33 + A.m44*B.m43,
   A.m41*B.m14 + A.m42*B.m24 + A.m43*B.m34 + A.m44*B.m44⟩

def comm (A B : Mat4 R) : Mat4 R := sub (mul A B) (mul B A)

def kron (A B : Mat2 R) : Mat4 R :=
  ⟨A.a11 * B.a11, A.a11 * B.a12, A.a12 * B.a11, A.a12 * B.a12,
   A.a11 * B.a21, A.a11 * B.a22, A.a12 * B.a21, A.a12 * B.a22,
   A.a21 * B.a11, A.a21 * B.a12, A.a22 * B.a11, A.a22 * B.a12,
   A.a21 * B.a21, A.a21 * B.a22, A.a22 * B.a21, A.a22 * B.a22⟩

def P_swap : Mat4 R := ⟨1,0,0,0, 0,0,1,0, 0,1,0,0, 0,0,0,1⟩
def Lax (w η : R) : Mat4 R := add (smul w one) (smul η P_swap)

theorem kron_adj_mul (G1 G2 : Mat2 R) :
    mul (kron (Mat2.adj G1) (Mat2.adj G2)) (kron G1 G2) =
      smul (Mat2.det G1 * Mat2.det G2) one := by
  ext <;> dsimp [kron, mul, smul, one, Mat2.adj, Mat2.det] <;> ring

theorem mul_assoc (A B C : Mat4 R) : mul (mul A B) C = mul A (mul B C) := by
  ext <;> dsimp [mul] <;> ring

theorem mul_smul_one (c : R) (A : Mat4 R) : mul (smul c one) A = smul c A := by
  ext <;> dsimp [mul, smul, one] <;> ring

theorem mul_smul_right (c : R) (A B : Mat4 R) : mul A (smul c B) = smul c (mul A B) := by
  ext <;> dsimp [mul, smul] <;> ring

/-- Universal Kronecker Adjugate Commutator Factorization on `Mat4 R`. -/
theorem kron_conj_comm (G1 G2 : Mat2 R) (X Y : Mat4 R) :
    let U     := kron G1 G2
    let U_adj := kron (Mat2.adj G1) (Mat2.adj G2)
    comm (mul (mul U X) U_adj) (mul (mul U Y) U_adj) =
      smul (Mat2.det G1 * Mat2.det G2) (mul (mul U (comm X Y)) U_adj) := by
  intro U U_adj
  have h_prod : ∀ A B : Mat4 R,
      mul (mul (mul U A) U_adj) (mul (mul U B) U_adj) =
        smul (Mat2.det G1 * Mat2.det G2) (mul (mul U (mul A B)) U_adj) := by
    intro A B
    calc mul (mul (mul U A) U_adj) (mul (mul U B) U_adj)
      _ = mul (mul U A) (mul (mul U_adj U) (mul B U_adj)) := by simp only [mul_assoc]
      _ = mul (mul U A) (mul (smul (Mat2.det G1 * Mat2.det G2) one) (mul B U_adj)) := by
          rw [kron_adj_mul]
      _ = smul (Mat2.det G1 * Mat2.det G2) (mul (mul U (mul A B)) U_adj) := by
          rw [mul_smul_one, mul_smul_right, mul_smul_right, ← mul_assoc, ← mul_assoc]
  dsimp [comm]
  rw [h_prod X Y, h_prod Y X]
  ext <;> dsimp [sub, smul, mul] <;> ring

end Mat4

-- ============================================================================
-- 3. 8x8 THREE-FACTOR TENSOR ALGEBRA `AuxMat4 R` (`V₀ ⊗ V₁ ⊗ V₂`)
-- ============================================================================

@[ext]
structure AuxMat4 (R : Type*) where
  A : Mat4 R; B : Mat4 R
  C : Mat4 R; D : Mat4 R
  deriving DecidableEq, Repr

namespace AuxMat4

def mul (X Y : AuxMat4 R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.mul X.A Y.A) (Mat4.mul X.B Y.C),
   Mat4.add (Mat4.mul X.A Y.B) (Mat4.mul X.B Y.D),
   Mat4.add (Mat4.mul X.C Y.A) (Mat4.mul X.D Y.C),
   Mat4.add (Mat4.mul X.C Y.B) (Mat4.mul X.D Y.D)⟩

def auxEmbed (G : Mat2 R) : AuxMat4 R :=
  ⟨Mat4.smul G.a11 Mat4.one, Mat4.smul G.a12 Mat4.one,
   Mat4.smul G.a21 Mat4.one, Mat4.smul G.a22 Mat4.one⟩

def physEmbed (M : Mat4 R) : AuxMat4 R :=
  ⟨M, Mat4.zero, Mat4.zero, M⟩

def Lax01 (w1 η : R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.smul w1 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.E00 Mat2.one)),
   Mat4.smul η (Mat4.kron Mat2.E10 Mat2.one),
   Mat4.smul η (Mat4.kron Mat2.E01 Mat2.one),
   Mat4.add (Mat4.smul w1 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.E11 Mat2.one))⟩

def Lax02 (w2 η : R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.smul w2 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.one Mat2.E00)),
   Mat4.smul η (Mat4.kron Mat2.one Mat2.E10),
   Mat4.smul η (Mat4.kron Mat2.one Mat2.E01),
   Mat4.add (Mat4.smul w2 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.one Mat2.E11))⟩

def R_ab (u_minus_v η : R) : AuxMat4 R := Lax01 u_minus_v η

def physDressedLax01 (w1 η : R) (G1 : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron G1 Mat2.one)) (Lax01 w1 η))
      (physEmbed (Mat4.kron (Mat2.adj G1) Mat2.one))

def physDressedLax02 (w2 η : R) (G2 : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron Mat2.one G2)) (Lax02 w2 η))
      (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2)))

def gaugedLax_ar (u η : R) (Gr : Mat2 R) : AuxMat4 R :=
  physDressedLax02 u η Gr

def gaugedLax_br (v η : R) (Gr : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (physEmbed (Mat4.Lax v η)))
      (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))

def trAux (K : Mat2 R) (T : AuxMat4 R) : Mat4 R :=
  Mat4.add (Mat4.add (Mat4.smul K.a11 T.A) (Mat4.smul K.a12 T.C))
           (Mat4.add (Mat4.smul K.a21 T.B) (Mat4.smul K.a22 T.D))

def bareMonodromy (u θ1 θ2 η : R) : AuxMat4 R :=
  mul (Lax02 (u - θ2) η) (Lax01 (u - θ1) η)

def openCocycleMonodromy (u θ1 θ2 η : R) (W21 : Mat2 R) : AuxMat4 R :=
  mul (mul (Lax02 (u - θ2) η) (auxEmbed W21)) (Lax01 (u - θ1) η)

def gaugedMonodromy (u θ1 θ2 η : R) (G1 G2 : Mat2 R) : AuxMat4 R :=
  mul (mul (auxEmbed (Mat2.adj G2))
           (openCocycleMonodromy u θ1 θ2 η (Mat2.cocycle G2 G1)))
      (auxEmbed G1)

def quantumDet (T_u T_u_shift : AuxMat4 R) : Mat4 R :=
  Mat4.sub (Mat4.mul T_u.A T_u_shift.D) (Mat4.mul T_u.B T_u_shift.C)

/--
**Archetype M₂ & M₃ (`archetype_M2_M3_braid_rtt_intertwining_and_corner_activation`):**
1. **3-Factor Equivariant Yang–Baxter RTT Braid Relation:**
   `R_{ab}(u - v, η) L̂_{ar}(u, η) L̂_{br}(v, η) = L̂_{br}(v, η) L̂_{ar}(u, η) R_{ab}(u - v, η)`.
2. **2-Factor Cocycle Telescoping on `V₀ ⊗ V₁ ⊗ V₂`:**
   `physDressedLax02 * physDressedLax01 = gaugedMonodromy`.
3. **Activation of the `E₁₀ ⊗ E₁₀` (`m41`) and `E₀₁ ⊗ E₀₁` (`m14`) Tensor Corners:**
   All 4 blocks of `bareMonodromy` have `m41 = m14 = 0`, whereas `openCocycleMonodromy`
   activates `B.m41 = η² W.a21`, `C.m14 = η² W.a12`, and `τ_open.m41 = w_B η² W.a21`.
-/
theorem archetype_M2_M3_braid_rtt_intertwining_and_corner_activation
    (u v θ1 θ2 η q wB wC : R) (Gr G1 G2 W : Mat2 R) :
    let T_bare := bareMonodromy u θ1 θ2 η
    let T_open := openCocycleMonodromy u θ1 θ2 η W
    let τ_open := trAux (Mat2.boundaryTwist q wB wC) T_open
    mul (mul (R_ab (u - v) η) (gaugedLax_ar u η Gr)) (gaugedLax_br v η Gr) =
      mul (mul (gaugedLax_br v η Gr) (gaugedLax_ar u η Gr)) (R_ab (u - v) η) ∧
    mul (physDressedLax02 (u - θ2) η G2) (physDressedLax01 (u - θ1) η G1) =
      gaugedMonodromy u θ1 θ2 η G1 G2 ∧
    T_bare.A.m41 = 0 ∧ T_bare.B.m41 = 0 ∧ T_bare.C.m41 = 0 ∧ T_bare.D.m41 = 0 ∧
    T_bare.A.m14 = 0 ∧ T_bare.B.m14 = 0 ∧ T_bare.C.m14 = 0 ∧ T_bare.D.m14 = 0 ∧
    T_open.B.m41 = η * η * W.a21 ∧
    T_open.C.m14 = η * η * W.a12 ∧
    τ_open.m41 = wB * (η * η * W.a21) ∧
    τ_open.m14 = (q * wC) * (η * η * W.a12) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try ext <;> dsimp [R_ab, gaugedLax_ar, gaugedLax_br, physDressedLax01, physDressedLax02,
                       gaugedMonodromy, openCocycleMonodromy, bareMonodromy, trAux,
                       Lax01, Lax02, auxEmbed, physEmbed, mul,
                       Mat2.cocycle, Mat2.boundaryTwist, Mat4.Lax, Mat4.P_swap, Mat4.kron,
                       Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
                       Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.mul, Mat2.adj, Mat2.one] <;> ring

/--
**Archetype M₄ (`archetype_M4_shifted_yangian_quantum_determinant_central_collapse`):**
The non-commutative shifted quantum determinant `A(u)D(u - η) - B(u)C(u - η)` on `V₁ ⊗ V₂`
annihilates all off-diagonal tensor-flip terms and collapses to the central scalar matrix
`((u - θ₁)² - η²)((u - θ₂)² - η²) I₄`.
-/
theorem archetype_M4_shifted_yangian_quantum_determinant_central_collapse
    (u θ1 θ2 η : R) :
    let centralScalar := ((u - θ1) * (u - θ1) - η * η) * ((u - θ2) * (u - θ2) - η * η)
    quantumDet (bareMonodromy u θ1 θ2 η) (bareMonodromy (u - η) θ1 θ2 η) =
      Mat4.smul centralScalar Mat4.one := by
  ext <;> dsimp [quantumDet, bareMonodromy, Lax01, Lax02, mul,
                 Mat4.kron, Mat4.mul, Mat4.add, Mat4.sub, Mat4.smul,
                 Mat4.one, Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one] <;> ring

/-- Lemma 1: Unconditional Commutativity of Bare 2-Factor Twisted Partial Traces. -/
theorem bare_two_factor_trace_comm (u v θ1 θ2 η : R) (K : Mat2 R) :
    Mat4.comm (trAux K (bareMonodromy u θ1 θ2 η))
              (trAux K (bareMonodromy v θ1 θ2 η)) = Mat4.zero := by
  ext <;> dsimp [trAux, bareMonodromy, Lax01, Lax02, mul,
                 Mat4.comm, Mat4.kron, Mat4.mul, Mat4.add, Mat4.sub, Mat4.smul,
                 Mat4.one, Mat4.zero, Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one] <;> ring

/-- Lemma 2: Intertwining of the Gauged Partial Trace with Kronecker Conjugation `G₁ ⊗ G₂`. -/
theorem gauged_trace_eq_kron_conj (u θ1 θ2 η : R) (K G1 G2 : Mat2 R) :
    trAux K (gaugedMonodromy u θ1 θ2 η G1 G2) =
      Mat4.mul (Mat4.mul (Mat4.kron G1 G2) (trAux K (bareMonodromy u θ1 θ2 η)))
               (Mat4.kron (Mat2.adj G1) (Mat2.adj G2)) := by
  ext <;> dsimp [trAux, gaugedMonodromy, openCocycleMonodromy, bareMonodromy,
                 Lax01, Lax02, auxEmbed, mul, Mat2.cocycle,
                 Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
                 Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.mul, Mat2.adj, Mat2.one] <;> ring

/--
**Archetype M₅ (`archetype_M5_unconditional_commutativity_of_gauged_partial_traces`):**
Unconditionally proves that for ANY `u, v, θ₁, θ₂, η ∈ R` and ANY non-commuting matrices
`K, G₁, G₂ ∈ Mat₂(R)`:
1. The open cocycle trace with twisted boundary seam `K_seam = G₁ K adj(G₂)` equals the
   full gauged partial trace `τ̃(u) = trAux K (gaugedMonodromy u θ₁ θ₂ η G₁ G₂)`.
2. The gauged partial-trace operators commute identically in `Mat₄(R)`:
   `[τ̃(u), τ̃(v)] = 0`!
-/
theorem archetype_M5_unconditional_commutativity_of_gauged_partial_traces
    (u v θ1 θ2 η : R) (K G1 G2 : Mat2 R) :
    let K_seam   := Mat2.mul (Mat2.mul G1 K) (Mat2.adj G2)
    let τ_open_u := trAux K_seam (openCocycleMonodromy u θ1 θ2 η (Mat2.cocycle G2 G1))
    let τ_gauged_u := trAux K (gaugedMonodromy u θ1 θ2 η G1 G2)
    let τ_gauged_v := trAux K (gaugedMonodromy v θ1 θ2 η G1 G2)
    τ_open_u = τ_gauged_u ∧
    Mat4.comm τ_gauged_u τ_gauged_v = Mat4.zero := by
  intro K_seam τ_open_u τ_gauged_u τ_gauged_v
  refine ⟨?_, ?_⟩
  · ext <;> dsimp [τ_open_u, τ_gauged_u, K_seam, trAux, gaugedMonodromy, openCocycleMonodromy,
                   Lax01, Lax02, auxEmbed, mul, Mat2.cocycle,
                   Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
                   Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.mul, Mat2.adj, Mat2.one] <;> ring
  · dsimp [τ_gauged_u, τ_gauged_v]
    rw [gauged_trace_eq_kron_conj u θ1 θ2 η K G1 G2,
        gauged_trace_eq_kron_conj v θ1 θ2 η K G1 G2,
        Mat4.kron_conj_comm G1 G2
          (trAux K (bareMonodromy u θ1 θ2 η))
          (trAux K (bareMonodromy v θ1 θ2 η)),
        bare_two_factor_trace_comm u v θ1 θ2 η K]
    ext <;> dsimp [Mat4.mul, Mat4.smul, Mat4.zero] <;> ring

end AuxMat4
end NonCommutativeMatrixOperatorPoset
```