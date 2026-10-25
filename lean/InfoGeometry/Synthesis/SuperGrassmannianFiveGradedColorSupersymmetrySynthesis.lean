/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.ArnoldParaKahlerBCFW
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
import InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
import InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

/-!
# Frontier 103: 5-Graded Super-Grassmannian, $\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry, Günaydin–Gürsey Superbracket Closure, and Super-Berezinian Souriau–Massieu Synthesis

This module formalizes the operator-algebraic and supergeometric closure of Frontier 103 uniting
the 5-graded Kantor–Koecher–Tits (KKT) decomposition
$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$,
Günaydin–Gürsey $\mathbb{Z}_2 \times \mathbb{Z}_2$ color supersymmetry, and the supersymmetric
Souriau–Massieu surprisal potential:

1. **$\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry Bi-Grading (`z2z2KoszulSign`)**:
   - Assigns bi-degrees $(\deg_e, \deg_c) \in \mathrm{Fin}\, 2 \times \mathrm{Fin}\, 2$ to the
     gauge sector `gradeGauge0 = (0, 0)`, leptonic sector `gradeLepton = (1, 0)`, quark sector
     `gradeQuark = (1, 1)`, and color-adjoint bosonic sector `gradeColorBoson = (0, 1)`.
   - Proves symmetry, involutive unit square, and the exact sectoral commutation signs
     $(-1)^{\deg_e(A)\deg_e(B) + \deg_c(A)\deg_c(B)}$ (`z2z2_color_supersymmetry_sign_laws`).

2. **Closure of the $\mathfrak{g}_{\pm 1}$ and $\mathfrak{g}_{\pm 2}$ Günaydin–Gürsey Superbrackets**:
   - **Grade $\pm 1 \times \pm 1 \to \mathfrak{g}_0 = \mathfrak{sl}_3(\mathbb{R}) \oplus \mathfrak{gl}_1(\mathbb{R})$**:
     Defines the quark–antiquark outer-product matrix `quarkAntiquarkOuter`, its trace-free
     $\mathfrak{sl}_3(\mathbb{R})$ projection `quarkAntiquarkTracelessSL3`, and its dilatation
     scalar trace `quarkAntiquarkDilatationTrace`, proving exact trace-zero closure in the
     Peirce color algebra `SL3` and recovery of the Zorn meson singlet pairing
     (`gunaydin_gursey_g1_gm1_superbracket_closure`).
   - **Grade $\pm 1 \times \pm 1 \to \mathfrak{g}_{\pm 2}$ (Diquark Cross-Product & Baryon Singlet)**:
     Proves that multiplying two pure quark triplets in `ZornSplitOctonion ℝ` lands purely in the
     anti-quark sector via the 3D cross product $\mathbf{u}_1 \times \mathbf{u}_2$, and pairing
     with a third quark triplet yields the alternating baryon determinant
     (`zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure`).
   - **Bidirectional Odd Supercolor Generator $\delta_{\epsilon, \bar{\epsilon}}$ (`oddSupercolorFull`)**:
     Proves that the square $\delta_{\epsilon, \bar{\epsilon}}^2$ of the odd lepton–quark
     supercolor generator closes directly onto the even bosonic socle $\mathfrak{g}_0$: scaling
     the leptonic singlets $\mathfrak{g}_{\pm 2}$ by the color contraction
     $\langle \epsilon, \bar{\epsilon} \rangle$ while acting on the quark/antiquark triplets
     $\mathfrak{g}_{\pm 1}$ by the rank-1 outer-product operators $\epsilon \otimes \bar{\epsilon}^T$
     and $\bar{\epsilon} \otimes \epsilon^T$ (`oddSupercolorFull_sq_closes_on_even_bosonic_socle`).

3. **`super_berezinian_gauge_invariance` & Supersymmetric Souriau–Massieu UV Cancellation**:
   - Defines `superBerezinian23` and `superTrace23` on the $(2\vert 3)$ lepton–quark super-carrier.
   - Proves `super_berezinian_gauge_invariance`: exact multiplicativity, invariance under
     Weyl light-cone boosts $\operatorname{diag}(\lambda, \lambda^{-1})$ on $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$
     and $\mathrm{SL}(3, \mathbb{R})$ color gauge transformations on $\mathfrak{g}_{\pm 1}$, and
     exact vanishing of the logarithmic Berezinian and supertrace under matched bosonic/fermionic
     UV vacuum shifts.
   - Defines `superSouriauMassieuPotential` and proves
     `superSouriauMassieu_uv_cancellation_and_moment_readout`.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

noncomputable section

open scoped BigOperators Matrix
open Finset Matrix
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
open InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

/-!
## Section 1: $\mathbb{Z}_2 \times \mathbb{Z}_2$ Bi-Graded Color Supersymmetry Sign Laws
-/

/-- A bi-degree $(\deg_e, \deg_c) \in \mathrm{Fin}\, 2 \times \mathrm{Fin}\, 2$ encoding electric
(fermionic) parity $\deg_e$ and color triality parity $\deg_c$. -/
abbrev Z2Z2ColorGrade : Type := Fin 2 × Fin 2

/-- Grade $0$ gauge boson bi-degree $(0, 0)$. -/
def gradeGauge0 : Z2Z2ColorGrade := (0, 0)

/-- Grade $\pm 2$ leptonic color-singlet bi-degree $(1, 0)$ ($\deg_e = 1, \deg_c = 0$). -/
def gradeLepton : Z2Z2ColorGrade := (1, 0)

/-- Grade $\pm 1$ quark color-triplet bi-degree $(1, 1)$ ($\deg_e = 1, \deg_c = 1$). -/
def gradeQuark : Z2Z2ColorGrade := (1, 1)

/-- Pure color-odd bosonic bi-degree $(0, 1)$ ($\deg_e = 0, \deg_c = 1$). -/
def gradeColorBoson : Z2Z2ColorGrade := (0, 1)

/-- Symmetric $\mathbb{Z}_2 \times \mathbb{Z}_2$ exponent
$\langle g_1, g_2 \rangle = \deg_e(g_1)\deg_e(g_2) + \deg_c(g_1)\deg_c(g_2)$. -/
def z2z2Pairing (g₁ g₂ : Z2Z2ColorGrade) : ℕ :=
  g₁.1.val * g₂.1.val + g₁.2.val * g₂.2.val

/-- Color supersymmetry commutation sign
$\varepsilon(g_1, g_2) = (-1)^{\deg_e(g_1)\deg_e(g_2) + \deg_c(g_1)\deg_c(g_2)}$. -/
def z2z2KoszulSign (g₁ g₂ : Z2Z2ColorGrade) : ℝ :=
  (-1 : ℝ) ^ (z2z2Pairing g₁ g₂)

/-- Fundamental $\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry Sign Theorem:
1. Symmetry: $\varepsilon(g_1, g_2) = \varepsilon(g_2, g_1)$,
2. Involutive unit square: $\varepsilon(g_1, g_2)^2 = 1$,
3. Gauge boson transparency: $\varepsilon((0,0), g) = +1$,
4. Lepton–Quark odd anticommutation: $\varepsilon(\text{quark}, \text{lepton}) = -1$,
5. Lepton–Lepton fermionic anticommutation: $\varepsilon(\text{lepton}, \text{lepton}) = -1$,
6. Quark–Quark bi-odd transmutation sign: $\varepsilon(\text{quark}, \text{quark}) = (-1)^{1+1} = +1$. -/
theorem z2z2_color_supersymmetry_sign_laws (g₁ g₂ : Z2Z2ColorGrade) :
    z2z2KoszulSign g₁ g₂ = z2z2KoszulSign g₂ g₁ ∧
    z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₂ = 1 ∧
    z2z2KoszulSign gradeGauge0 g₁ = 1 ∧
    z2z2KoszulSign gradeQuark gradeLepton = -1 ∧
    z2z2KoszulSign gradeLepton gradeLepton = -1 ∧
    z2z2KoszulSign gradeQuark gradeQuark = 1 := by
  have h_symm : z2z2Pairing g₁ g₂ = z2z2Pairing g₂ g₁ := by
    dsimp [z2z2Pairing]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [z2z2KoszulSign]
    rw [h_symm]
  · dsimp [z2z2KoszulSign]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeGauge0]
    simp
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeQuark, gradeLepton]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeLepton]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeQuark]
    norm_num

/-!
## Section 2: Closure of the $\mathfrak{g}_{\pm 1}$ and $\mathfrak{g}_{\pm 2}$ Günaydin–Gürsey Superbrackets
-/

/-- Rank-1 quark–antiquark outer-product matrix $(u \otimes v^T)_{ij} = u_i v_j$ in $M_3(\mathbb{R})$. -/
def quarkAntiquarkOuter (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => u i * v j

/-- Trace-free $\mathfrak{sl}_3(\mathbb{R})$ color generator extracted from the quark–antiquark
superbracket:
$$M_{\mathfrak{sl}_3}(u, v) = u \otimes v^T - \frac{1}{3} \langle u, v \rangle I_3.$$ -/
def quarkAntiquarkTracelessSL3 (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  quarkAntiquarkOuter u v -
    ((1 / 3 : ℝ) * vec3Dot u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- Grade-$0$ dilatation / hypercharge trace invariant $\langle u, v \rangle = \sum_{a=0}^2 u_a v_a$. -/
def quarkAntiquarkDilatationTrace (u v : Fin 3 → ℝ) : ℝ :=
  vec3Dot u v

/-- The trace of `quarkAntiquarkTracelessSL3 u v` vanishes identically, so it defines a valid
element of the Peirce stabilizer Lie algebra `SL3`. -/
theorem quarkAntiquarkTracelessSL3_trace_zero (u v : Fin 3 → ℝ) :
    Matrix.trace (quarkAntiquarkTracelessSL3 u v) = 0 := by
  dsimp [quarkAntiquarkTracelessSL3, quarkAntiquarkOuter, vec3Dot,
    Matrix.trace, Matrix.diag]
  simp only [Fin.sum_univ_three, Matrix.one_apply, ↓reduceIte]
  ring

/-- Bundled element of `SL3` generated by the odd quark–antiquark superbracket
$\{\mathfrak{g}_{+1}, \mathfrak{g}_{-1}\} \to \mathfrak{sl}_3(\mathbb{R}) \subset \mathfrak{g}_0$. -/
def quarkAntiquarkToSL3 (u v : Fin 3 → ℝ) : SL3 :=
  ⟨quarkAntiquarkTracelessSL3 u v, quarkAntiquarkTracelessSL3_trace_zero u v⟩

/-- **Closure of the $\{\mathfrak{g}_{+1}, \mathfrak{g}_{-1}\} \to \mathfrak{g}_0$ Superbracket**:
1. The outer product $u \otimes v^T$ decomposes into the trace-free $\mathfrak{sl}_3(\mathbb{R})$
   color generator plus the $\mathfrak{gl}_1(\mathbb{R})$ dilatation trace $\frac{1}{3}\langle u, v \rangle I_3$.
2. The $\mathfrak{sl}_3(\mathbb{R})$ projection has strictly vanishing trace.
3. In `ZornSplitOctonion ℝ`, the product of the projected quark triplet $P_{\mathbf{3}}(z)$ and
   anti-quark antitriplet $P_{\bar{\mathbf{3}}}(z)$ lands in the diagonal leptonic idempotent
   sector with coefficient $+\langle u, v \rangle$. -/
theorem gunaydin_gursey_g1_gm1_superbracket_closure
    (u v : Fin 3 → ℝ) (z : ZornSplitOctonion ℝ) :
    quarkAntiquarkOuter u v =
      quarkAntiquarkTracelessSL3 u v +
        ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    Matrix.trace (quarkAntiquarkToSL3 u v).1 = 0 ∧
    (zornMul (zornProjQuark z) (zornProjAntiQuark z)).a =
      quarkAntiquarkDilatationTrace z.u z.v ∧
    (zornMul (zornProjAntiQuark z) (zornProjQuark z)).b =
      quarkAntiquarkDilatationTrace z.u z.v := by
  refine ⟨?_, quarkAntiquarkTracelessSL3_trace_zero u v, ?_, ?_⟩
  · ext i j
    dsimp [quarkAntiquarkTracelessSL3, quarkAntiquarkDilatationTrace]
    ring
  · dsimp [zornProjQuark, zornProjAntiQuark, zornMul,
      quarkAntiquarkDilatationTrace, vec3Dot]
    ring
  · dsimp [zornProjQuark, zornProjAntiQuark, zornMul,
      quarkAntiquarkDilatationTrace, vec3Dot]
    ring

/-- Pure quark triplet embedding $\mathbf{u} \mapsto \begin{pmatrix} 0 & \mathbf{u} \\ 0 & 0 \end{pmatrix}$
in `ZornSplitOctonion ℝ`. -/
def embedPureQuarkZorn (u : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, u, ![0, 0, 0], 0⟩

/-- Pure anti-quark antitriplet embedding $\mathbf{v} \mapsto \begin{pmatrix} 0 & 0 \\ \mathbf{v} & 0 \end{pmatrix}$
in `ZornSplitOctonion ℝ`. -/
def embedPureAntiQuarkZorn (v : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, ![0, 0, 0], v, 0⟩

/-- **Diquark Cross-Product & Baryon Singlet Closure ($\mathfrak{g}_{+1} \times \mathfrak{g}_{+1} \to \mathfrak{g}_{-1}$ and $\mathfrak{g}_{+1}^3 \to \mathfrak{g}_{\pm 2}$)**:
1. Multiplying two pure quark triplets in `ZornSplitOctonion ℝ` produces a pure anti-quark
   antitriplet given by the 3D cross product $\mathbf{u}_1 \times \mathbf{u}_2$:
   `zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) = embedPureAntiQuarkZorn (vec3Cross u₁ u₂)`.
2. Multiplying a third quark triplet `embedPureQuarkZorn u₃` with this diquark composite lands
   in the upper-left leptonic singlet slot $e_+$ with scalar value $\langle \mathbf{u}_3, \mathbf{u}_1 \times \mathbf{u}_2 \rangle$,
   which vanishes whenever two quark vectors coincide ($\mathbf{u}_1 = \mathbf{u}_2$, Fermi/Pauli exclusion). -/
theorem zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure
    (u₁ u₂ u₃ : Fin 3 → ℝ) :
    zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) =
      embedPureAntiQuarkZorn (vec3Cross u₁ u₂) ∧
    (zornMul (embedPureQuarkZorn u₃)
      (zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂))).a =
      vec3Dot u₃ (vec3Cross u₁ u₂) ∧
    (zornMul (embedPureQuarkZorn u₃)
      (zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₁))).a = 0 := by
  have h_diq :
      zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) =
        embedPureAntiQuarkZorn (vec3Cross u₁ u₂) := by
    ext k
    · dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]; ring
    · fin_cases k <;>
        (dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Cross]; ring)
    · dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]; ring
  refine ⟨h_diq, ?_, ?_⟩
  · rw [h_diq]
    dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]
    ring
  · dsimp [embedPureQuarkZorn, zornMul, vec3Dot, vec3Cross]
    ring

/-- Full bidirectional odd $\mathfrak{su}(3\vert 1)$ supercolor generator
$\delta_{\epsilon, \bar{\epsilon}}$ coupling the leptonic singlets $\mathfrak{g}_{\pm 2} = (\mathbf{1} \oplus \mathbf{1})$
and the quark/antiquark color triplets $\mathfrak{g}_{\pm 1} = (\mathbf{3} \oplus \bar{\mathbf{3}})$. -/
def oddSupercolorFull (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  (![∑ a : Fin 3, epsBar a * M.2.1 a, ∑ a : Fin 3, eps a * M.2.2 a],
   (fun a => eps a * M.1 0, fun a => epsBar a * M.1 1))

/-- **Odd Superbracket Closure ($\{\mathfrak{g}_{\pm 1}, \mathfrak{g}_{\pm 1}\} \to \mathfrak{g}_0 \oplus \mathfrak{g}_{\pm 2}$)**:
Applying the bidirectional odd supercolor generator `oddSupercolorFull eps epsBar` twice
closes directly onto the even bosonic gauge socle:
1. Each leptonic singlet coordinate $\ell_0, \ell_1 \in \mathfrak{g}_{\pm 2}$ is scaled by the
   color-singlet contraction $\langle \epsilon, \bar{\epsilon} \rangle = \sum_{a=0}^2 \epsilon_a \bar{\epsilon}_a$,
2. The quark triplet $q \in \mathbf{3}$ is transformed by the rank-1 outer-product matrix
   `quarkAntiquarkOuter eps epsBar`,
3. The anti-quark antitriplet $\bar{q} \in \bar{\mathbf{3}}$ is transformed by the transposed
   outer-product matrix `quarkAntiquarkOuter epsBar eps`. -/
theorem oddSupercolorFull_sq_closes_on_even_bosonic_socle
    (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).1 0 =
      vec3Dot eps epsBar * M.1 0 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).1 1 =
      vec3Dot eps epsBar * M.1 1 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).2.1 =
      (quarkAntiquarkOuter eps epsBar).mulVec M.2.1 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).2.2 =
      (quarkAntiquarkOuter epsBar eps).mulVec M.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [oddSupercolorFull, vec3Dot]
    simp only [Fin.sum_univ_three]
    ring
  · dsimp [oddSupercolorFull, vec3Dot]
    simp only [Fin.sum_univ_three]
    ring
  · funext a
    dsimp [oddSupercolorFull, quarkAntiquarkOuter, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_three]
    ring
  · funext a
    dsimp [oddSupercolorFull, quarkAntiquarkOuter, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_three]
    ring

/-!
## Section 3: `super_berezinian_gauge_invariance` & Supersymmetric Souriau–Massieu UV Cancellation
-/

/-- Berezinian superdeterminant $\mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}) = \det(A_{\text{bos}}) / \det(D_{\text{fer}})$
on the $(2\vert 3)$-graded lepton–quark super-carrier ($\mathbf{1}\oplus\mathbf{1}$ bosonic leptons
over $\mathbf{3}$ fermionic quark color modes). -/
def superBerezinian23
    (A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A_bos.det / D_fer.det

/-- Supertrace $\mathrm{STr}(A_{\text{bos}}, D_{\text{fer}}) = \mathrm{Tr}(A_{\text{bos}}) - \mathrm{Tr}(D_{\text{fer}})$
on the $(2\vert 3)$-graded lepton–quark super-carrier. -/
def superTrace23
    (A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A_bos.trace - D_fer.trace

/-- Diagonal Weyl scale boost matrix $\operatorname{diag}(\lambda, \lambda^{-1})$ on the
leptonic $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ sector. -/
def leptonWeylScaleMatrix (lam invLam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![lam, 0], ![0, invLam]]

/-- **`super_berezinian_gauge_invariance` (Super-Berezinian Gauge Invariance & UV Zero-Point Cancellation)**:
1. **Multiplicative Homomorphism**:
   $\mathrm{Ber}(A_1 A_2, D_1 D_2) = \mathrm{Ber}(A_1, D_1) \cdot \mathrm{Ber}(A_2, D_2)$.
2. **Weyl $\mathfrak{so}(1,1)$ & Color $\mathrm{SL}(3, \mathbb{R})$ Gauge Invariance**:
   For any Weyl boost $\operatorname{diag}(\lambda, \lambda^{-1})$ ($\lambda \lambda^{-1} = 1$) on
   $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ and any color transformation $U_C \in M_3(\mathbb{R})$
   with $\det(U_C) = 1$,
   $$\mathrm{Ber}(\operatorname{diag}(\lambda, \lambda^{-1}) A_{\text{bos}}, \, U_C D_{\text{fer}})
     = \mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}).$$
3. **Trace-Free $\mathfrak{sl}_3(\mathbb{R})$ Supertrace Invariance**:
   Adding any Peirce color generator $M \in \mathrm{SL}_3$ to the fermionic block leaves
   `superTrace23` strictly invariant:
   $\mathrm{STr}(A_{\text{bos}}, D_{\text{fer}} + M.1) = \mathrm{STr}(A_{\text{bos}}, D_{\text{fer}})$.
4. **Logarithmic Berezinian & Supertrace UV Cancellation**:
   Whenever the bosonic and fermionic blocks carry matched determinant scales
   ($\det(A_{\text{bos}}) = \det(D_{\text{fer}}) \neq 0$), the logarithmic Berezinian vanishes
   identically ($\ln \mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}) = 0$). -/
theorem super_berezinian_gauge_invariance
    (A₁ A₂ A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D₁ D₂ D_fer U_C : Matrix (Fin 3) (Fin 3) ℝ)
    (M_color : SL3)
    (lam invLam : ℝ)
    (h_weyl : lam * invLam = 1)
    (h_color_det : U_C.det = 1)
    (h_match_det : A₁.det = D₁.det)
    (hD₁_ne : D₁.det ≠ 0) :
    superBerezinian23 (A₁ * A₂) (D₁ * D₂) =
      superBerezinian23 A₁ D₁ * superBerezinian23 A₂ D₂ ∧
    superBerezinian23 (leptonWeylScaleMatrix lam invLam * A_bos) (U_C * D_fer) =
      superBerezinian23 A_bos D_fer ∧
    superTrace23 A_bos (D_fer + M_color.1) = superTrace23 A_bos D_fer ∧
    Real.log (superBerezinian23 A₁ D₁) = 0 := by
  have h_weyl_det : (leptonWeylScaleMatrix lam invLam).det = 1 := by
    dsimp [leptonWeylScaleMatrix]
    rw [Matrix.det_fin_two_of]
    linarith [h_weyl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [superBerezinian23]
    rw [Matrix.det_mul, Matrix.det_mul, mul_div_mul_comm]
  · dsimp [superBerezinian23]
    rw [Matrix.det_mul, Matrix.det_mul, h_weyl_det, h_color_det, one_mul, one_mul]
  · dsimp [superTrace23]
    rw [Matrix.trace_add, M_color.2, add_zero]
  · dsimp [superBerezinian23]
    rw [h_match_det, div_self hD₁_ne, Real.log_one]

/-- Discrete Supersymmetric Souriau–Massieu Surprisal Potential
$\Phi_{\text{super}}(s_{\text{bos}}, b_{\text{fer}}) = \ln \sum_{j} (\exp(s_{\text{bos}, j}) + b_{\text{fer}, j})$. -/
def superSouriauMassieuPotential {m : ℕ} (s_bos b_fer : Fin m → ℝ) : ℝ :=
  Real.log (∑ j : Fin m, (Real.exp (s_bos j) + b_fer j))

/-- **Supersymmetric Souriau–Massieu UV Defect Cancellation & Moment Map Recovery**:
If a bosonic partition sum suffers a mode-wise additive UV vacuum defect $\Delta_{\text{UV}}(j)$
and the odd Berezinian counterterm $b_{\text{fer}}(j) = -\Delta_{\text{UV}}(j)$ cancels it
(`h_cancel : ∀ j, b_fer j + Δ_UV j = 0`), then:
1. The perturbed supersymmetric partition sum reduces identically to the finite Souriau–Massieu
   free entropy potential $\Phi(s_{\text{bos}})$:
   $$\ln \sum_{j} \big(\exp(s_{\text{bos}, j}) + \Delta_{\text{UV}}(j) + b_{\text{fer}}(j)\big)
     = \Phi(s_{\text{bos}}).$$
2. Its coordinate derivative with respect to $s_{\text{bos}, j}$ recovers the exact canonical
   Souriau attention weight $A_j(s_{\text{bos}})$. -/
theorem superSouriauMassieu_uv_cancellation_and_moment_readout
    {m : ℕ} [Nonempty (Fin m)]
    (s_bos b_fer Δ_UV : Fin m → ℝ) (j : Fin m)
    (h_cancel : ∀ k : Fin m, b_fer k + Δ_UV k = 0) :
    superSouriauMassieuPotential s_bos (fun k => Δ_UV k + b_fer k) =
      souriauMassieuPotential s_bos ∧
    HasDerivAt
      (fun t : ℝ =>
        superSouriauMassieuPotential (Function.update s_bos j t)
          (fun k => Δ_UV k + b_fer k))
      (souriauAttentionWeight s_bos j) (s_bos j) := by
  have h_eq :
      ∀ s : Fin m → ℝ,
        superSouriauMassieuPotential s (fun k => Δ_UV k + b_fer k) =
          souriauMassieuPotential s := by
    intro s
    dsimp [superSouriauMassieuPotential, souriauMassieuPotential, gibbsPartitionSum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk := h_cancel k
    linarith
  refine ⟨h_eq s_bos, ?_⟩
  have h_fun :
      (fun t : ℝ =>
        superSouriauMassieuPotential (Function.update s_bos j t)
          (fun k => Δ_UV k + b_fer k)) =
      (fun t : ℝ => souriauMassieuPotential (Function.update s_bos j t)) := by
    funext t
    exact h_eq (Function.update s_bos j t)
  rw [h_fun]
  exact hasDerivAt_souriauMassieuPotential_coord s_bos j

/-!
## Section 4: Canonical Spine Carrier Equivalences & Operation Intertwining (`OpZornMatrix R ≃ GunaydinGurseyMultiplet R ≃ (Fin 8 → R)` and `ZornVectorMatrix R ≃ ZornSplitOctonion R`)

This section explicitly links the noncommutative operator-algebraic spine
(`AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R`, `ArnoldParaKahlerBCFW`, and
`InfoGeometry.Algebra.ZornVectorMatrix R`) with the `Fin 8` / `Fin 3` matrix synthesis carriers
(`ZornSplitOctonion R`, `GunaydinGurseyMultiplet R`, `quarkAntiquarkOuter`, and `superTrace23`).
-/

/-- Canonical 3-vector carrier equivalence between `OpVec3 R` and `Fin 3 → R`. -/
def opVec3Fin3Equiv (R : Type*) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3 R ≃ (Fin 3 → R) where
  toFun u := ![u.x, u.y, u.z]
  invFun f := ⟨f 0, f 1, f 2⟩
  left_inv u := by cases u; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

/-- Canonical 8D split-octonion carrier equivalence between `ZornVectorMatrix R`
(`InfoGeometry.Algebra.ZornAlternativeLaws`) and `ZornSplitOctonion R`
(`InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge`). -/
def zornVectorMatrixSplitOctonionEquiv (R : Type*) :
    InfoGeometry.Algebra.ZornVectorMatrix R ≃ ZornSplitOctonion R where
  toFun X := ⟨X.a, X.v, X.w, X.b⟩
  invFun z := ⟨z.a, z.u, z.v, z.b⟩
  left_inv X := by cases X; rfl
  right_inv z := by cases z; rfl

/-- **`zornVectorMatrixSplitOctonionEquiv` Multiplicative, Norm, & 5-Graded KKT Bridge**:
1. `zornVectorMatrixSplitOctonionEquiv` is an exact algebra and quadratic-norm isomorphism between
   `ZornVectorMatrix R` (`ZornVectorMatrix.mul`, `ZornVectorMatrix.norm`) and `ZornSplitOctonion R`
   (`zornMul`, `zornNorm`).
2. Every element $X \in \mathrm{ZornVectorMatrix}\;R$ satisfies the degree-5 Kantor–Koecher–Tits
   characteristic identity $\mathcal{E}_5^5(X) - 5\,\mathcal{E}_5^3(X) + 4\,\mathcal{E}_5(X) = 0$
   (`InfoGeometry.Algebra.ZornVectorMatrix.zorn_euler_five_grading_kkt_and_supercolor_cancellation`). -/
theorem zornVectorMatrixSplitOctonionEquiv_mul_norm_and_kkt
    {R : Type*} [CommRing R] (X Y : InfoGeometry.Algebra.ZornVectorMatrix R) :
    zornVectorMatrixSplitOctonionEquiv R (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) =
      zornMul (zornVectorMatrixSplitOctonionEquiv R X) (zornVectorMatrixSplitOctonionEquiv R Y) ∧
    zornNorm (zornVectorMatrixSplitOctonionEquiv R X) =
      InfoGeometry.Algebra.ZornVectorMatrix.norm X ∧
    (let E1 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading X
     let E2 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E1
     let E3 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E2
     let E4 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E3
     let E5 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E4
     E5 + -(E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0) := by
  refine ⟨?_, ?_,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_euler_five_grading_kkt_and_supercolor_cancellation
      X 0 0 0 0 0 0 X.v Y.w).2.1⟩
  · ext k
    · dsimp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
        zornMul, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
      simp only [Fin.sum_univ_three]
    · fin_cases k <;>
        simp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          zornMul, InfoGeometry.Algebra.ZornVec3.cross, vec3Cross]
    · fin_cases k <;>
        simp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          zornMul, InfoGeometry.Algebra.ZornVec3.cross, vec3Cross]
    · dsimp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
        zornMul, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
      simp only [Fin.sum_univ_three]
      ring
  · dsimp [zornVectorMatrixSplitOctonionEquiv, zornNorm,
      InfoGeometry.Algebra.ZornVectorMatrix.norm, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
    simp only [Fin.sum_univ_three]

/-- Canonical 8D carrier equivalence between the noncommutative operator-algebraic Zorn matrix
`OpZornMatrix R` (`AlbertCayleyDickson.lean`) and the Günaydin–Gürsey lepton–quark multiplet
`GunaydinGurseyMultiplet R = (Fin 2 → R) × (Fin 3 → R) × (Fin 3 → R)` (`Cl55SuperGrassmannianKKTSynthesis.lean`). -/
def opZornGunaydinGurseyEquiv (R : Type*) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R ≃
      GunaydinGurseyMultiplet R where
  toFun X := (![X.a, X.b], opVec3Fin3Equiv R X.v, opVec3Fin3Equiv R X.w)
  invFun M := ⟨M.1 0, (opVec3Fin3Equiv R).symm M.2.1, (opVec3Fin3Equiv R).symm M.2.2, M.1 1⟩
  left_inv X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    rfl
  right_inv M := by
    rcases M with ⟨ℓ, q, qbar⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl

/-- Canonical 8D equivalence between `OpZornMatrix R` and the 8-component $\mathrm{Cl}(4,4)$
semi-spinor carrier `Fin 8 → R`. -/
def opZornFin8SemiSpinorEquiv (R : Type*) [CommRing R] :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R ≃ (Fin 8 → R) :=
  (opZornGunaydinGurseyEquiv R).trans (gunaydinGurseyEquiv R).toEquiv.symm

/-- **Canonical Spine Intertwining Theorem (`OpZornMatrix` ↔ `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`)**:
1. **Color Outer-Product Intertwining**: Under `opVec3Fin3Equiv ℝ`, the `OpZornMatrix` color
   outer-product entries `opColorOuterMat u v` coincide entrywise with `quarkAntiquarkOuter`:
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 0 0 = opColorOuterMat u v 0 0`,
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 1 1 = opColorOuterMat u v 1 1`,
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 2 2 = opColorOuterMat u v 2 2`.
2. **Dilatation Trace & Quark Trace Intertwining**: Both `OpVec3.dot u v` and
   `opQuarkTrace (opColorOuterMat u v)` equal `quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)`.
3. **$(2|3)$ Lepton–Quark Supertrace Intertwining & UV Cancellation**:
   `superTrace23 (Matrix.of ![![OpVec3.dot u v, 0], ![0, 0]]) (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) = opSuperTrace23 (opGradeZero (OpVec3.dot u v) 0) (opColorOuterMat u v) = 0`.
4. **Euler 5-Grading KKT Polynomial on `OpZornMatrix ℝ`**:
   Every `X : OpZornMatrix ℝ` satisfies $\mathcal{E}_5^5(X) - 5\,\mathcal{E}_5^3(X) + 4\,\mathcal{E}_5(X) = 0$
   (`ArnoldParaKahlerBCFW.operator_super_grassmannian_kkt_and_supercolor_master_bridge`). -/
theorem opZorn_supergrassmannian_color_and_supertrace_intertwining
    (u v : InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3 ℝ)
    (X : InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ) :
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 0 0 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 0 0 ∧
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 1 1 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 1 1 ∧
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 2 2 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 2 2 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v =
      quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v) =
      quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) ∧
    superTrace23
        (Matrix.of ![![InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v, 0], ![0, 0]])
        (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSuperTrace23
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero
          (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v) 0)
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v) ∧
    superTrace23
        (Matrix.of ![![InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v, 0], ![0, 0]])
        (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) = 0 ∧
    (let E1 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading X
     let E2 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E1
     let E3 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E2
     let E4 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E3
     let E5 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E4
     E5 - (E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0) ∧
    ((InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmS1 :
        InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmS0) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmR1 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmR0 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_super_grassmannian_kkt_and_supercolor_master_bridge
      X 0 0 0 0 0 0 0 0 0 0 0 0 u v u v u v 1).1.2.2.2.2.2.2.2,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_dahm_projective_line_geometry_pg32_and_sl2h_master_bridge
      u v u v X 0 0 0 0 0 0 0 0).2.2.2.2.2.2.2.2.1⟩
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [opVec3Fin3Equiv,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      quarkAntiquarkDilatationTrace, vec3Dot]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [opVec3Fin3Equiv,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat,
      quarkAntiquarkDilatationTrace, vec3Dot]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [superTrace23, Matrix.trace, Matrix.diag, opVec3Fin3Equiv, quarkAntiquarkOuter,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSuperTrace23,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCartanDiag,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat,
      Fin.sum_univ_two, Fin.sum_univ_three]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [superTrace23, Matrix.trace, Matrix.diag, opVec3Fin3Equiv, quarkAntiquarkOuter,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      Fin.sum_univ_two, Fin.sum_univ_three]

end

end InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
